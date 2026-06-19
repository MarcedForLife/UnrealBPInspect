//! Statement-level opcode decoders.
//!
//! `decode_one_or_branch` decodes a single opcode at a cursor, recognising
//! flat statement shapes (Assignment via EX_Let*, Call via EX_*Function /
//! EX_CallMath, Return) and control-flow shapes (Branch via EX_JumpIfNot,
//! EventCall via EX_Jump). Multi-opcode constructs (Loop, Sequence, IsValid,
//! cascades) are recognised by delegating to their sibling modules. The
//! region-tree walker in `region_decode` drives these per-block.

use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::{advance_expr, opcode_length_at};
use crate::bytecode::readers::read_bc_i32;
use crate::bytecode::stmt::Stmt;

use super::branch::{decode_branch, decode_jump};
use super::cascade_decode::{
    try_decode_jumpifnot_cascade, try_decode_jumpifnot_cascade_shared,
    try_decode_jumpifnot_cascade_shared_via_trampoline,
};
use super::ctx::DecodeCtx;
use super::expr_decode::decode_expr;
use super::loop_decode::try_decode_loop;
use super::naked_if::try_decode_naked_if;
use super::sequence::try_decode_sequence;
use super::switch_decode::try_decode_switch;

/// Decode a single opcode at `*pos`, recognising both flat statement
/// shapes (Assignment, Call, Return) and control-flow shapes (Branch,
/// EventCall).
///
/// Returns:
/// - `Ok(Some(stmt))` for any decoded statement;
/// - `Ok(None)` for opcodes that act as pure structural markers within
///   the current block (e.g. an unconditional `EX_JUMP` that's part of
///   a recognised but already-consumed construct);
/// - `Err(Box<Stmt::Unknown>)` for unrecognised opcodes, with `pos`
///   advanced past the bytes the length scanner reports.
pub(crate) fn decode_one_or_branch(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Result<Option<Stmt>, Box<Stmt>> {
    if *pos >= ctx.bytecode.len() {
        return Err(Box::new(make_unknown(
            *pos,
            ctx,
            "unexpected end of bytecode",
        )));
    }
    let opcode = ctx.bytecode[*pos];
    // Explicit switch dispatch runs before Loop/Branch so an
    // `EX_SwitchValue` doesn't misclassify on a downstream opcode.
    if opcode == EX_SWITCH_VALUE {
        if let Some(stmt) = try_decode_switch(pos, range_end, ctx) {
            return Ok(Some(stmt));
        }
    }
    // Dispatch-table recognition runs before Loop / Branch when the
    // head is either `EX_LET_BOOL` (start of an assigned-temp pair) or
    // `EX_JUMP_IF_NOT` (start of an inline-cond pair). The recognizer
    // returns `None` and leaves `*pos` untouched when the bytes don't
    // form a complete dispatch table, so non-cascade shapes fall
    // through to the regular dispatchers below.
    if matches!(opcode, EX_LET_BOOL | EX_JUMP_IF_NOT) {
        if let Some(stmt) = try_decode_jumpifnot_cascade(pos, range_end, ctx) {
            return Ok(Some(stmt));
        }
        // Shared-target variant: same `[Assign Ne; JumpIfNot]` chain but
        // multiple cases converge to one body and the dispatch is
        // terminated by `EX_POP_EXECUTION_FLOW` instead of an `EX_JUMP`.
        // This is the shape Blueprint emits for "Switch on Enum" wired
        // through a Sequence shared by several pin values.
        if let Some(stmt) = try_decode_jumpifnot_cascade_shared(pos, range_end, ctx) {
            return Ok(Some(stmt));
        }
        // Trampoline-shared variant: every cascade JIN targets the same
        // backward thunk whose own `EX_JUMP` forwards to a convergence
        // body in another (lower-disk) section of the event. Recognised
        // only when predecessor verification confirms the body has no
        // other inbound edges.
        if let Some(stmt) = try_decode_jumpifnot_cascade_shared_via_trampoline(pos, range_end, ctx)
        {
            return Ok(Some(stmt));
        }
    }
    match opcode {
        EX_JUMP_IF_NOT => {
            // Loop recognition runs first: an EX_JUMP_IF_NOT whose body
            // ends in a back-edge `EX_JUMP` is a While/ForC loop, not
            // an if/else. If the bytes don't match a loop shape, fall
            // through to the regular branch decoder.
            if let Some(stmt) = try_decode_loop(pos, range_end, ctx) {
                return Ok(Some(stmt));
            }
            let outcome = decode_branch(pos, range_end, ctx);
            Ok(Some(outcome.stmt))
        }
        EX_JUMP => Ok(decode_jump(pos, range_end, ctx)),
        EX_PUSH_EXECUTION_FLOW => {
            // Try Sequence recognition first; chain heads compile
            // push_flow + EX_JUMP and the chain decoder consumes its
            // own bytes wholesale.
            if let Some(stmt) = try_decode_sequence(pos, range_end, ctx) {
                return Ok(Some(stmt));
            }
            decode_one(pos, ctx)
        }
        EX_POP_FLOW_IF_NOT => {
            // Form B naked-if: `pop_flow_if_not(cond) + body +
            // pop_flow` inside a partition (the parent push_flow lives
            // outside the partition's range). Bails on claimed-range
            // membership (DoOnce init-block tail) and on literal
            // conditions, then walks forward to the matching pop.
            if let Some(stmt) = try_decode_naked_if(pos, range_end, ctx) {
                return Ok(Some(stmt));
            }
            decode_one(pos, ctx)
        }
        EX_POP_EXECUTION_FLOW => {
            // A bare EX_POP_EXECUTION_FLOW outside a recognised Sequence
            // is a structural marker (the Sequence decoder consumes the
            // ones inside its scope). Skip silently.
            *pos += 1;
            Ok(None)
        }
        _ => decode_one(pos, ctx),
    }
}

/// Decode a function body as a flat opcode stream, one `Stmt` per
/// recognised opcode, in disk order from `start` to the end of the
/// bytecode.
///
/// Unlike the region-tree walk, this runs no BFS, no prescans, and no
/// multi-opcode construct recognisers (Branch, Loop, Sequence). It walks
/// `decode_one` until the stream ends, so it is only suitable for flat
/// dispatch stubs whose entire body is assignments, calls, and a trailing
/// return (the `ExecuteUbergraph_*` dispatch functions). Branchy bodies
/// would mis-decode their jump operands as opcodes; callers must restrict
/// this to known-flat exports.
///
/// `Stmt::Unknown` placeholders from unrecognised opcodes are kept so the
/// caller can distinguish a clean dispatch stub from one carrying real
/// logic.
pub(crate) fn decode_linear(start: usize, ctx: &DecodeCtx) -> Vec<Stmt> {
    let mut stmts = Vec::new();
    let mut pos = start;
    while pos < ctx.bytecode.len() {
        let before = pos;
        match decode_one(&mut pos, ctx) {
            Ok(Some(stmt)) => stmts.push(stmt),
            Ok(None) => {}
            Err(unknown) => stmts.push(*unknown),
        }
        // `decode_one` always advances `pos` past the instruction it
        // examined; guard against a zero-advance to avoid an infinite loop.
        if pos <= before {
            break;
        }
    }
    stmts
}

/// Attempt to decode one opcode at `pos`, advancing `pos` past it.
///
/// Returns:
/// - `Ok(Some(stmt))` for recognised opcodes (Assignment, Call, Return).
/// - `Ok(None)` for instrumentation opcodes (EX_WIRE_TRACEPOINT, EX_TRACEPOINT,
///   EX_INSTRUMENTATION_EVENT) that should be silently dropped.
/// - `Err(Box<Stmt::Unknown>)` for all other unrecognised opcodes. The `Err`
///   variant still advances `pos` past the instruction so the caller can
///   continue. Boxed to keep size below `clippy::result_large_err`.
///
/// Handles:
/// - Assignment: EX_LET, EX_LET_BOOL, EX_LET_OBJ, EX_LET_WEAK_OBJ_PTR,
///   EX_LET_MULTICAST_DELEGATE, EX_LET_DELEGATE, EX_LET_VALUE_ON_PERSISTENT_FRAME
/// - Call (statement position): EX_FINAL_FUNCTION, EX_LOCAL_FINAL_FUNCTION,
///   EX_CALL_MATH, EX_VIRTUAL_FUNCTION, EX_LOCAL_VIRTUAL_FUNCTION
/// - Return: EX_RETURN
/// - Instrumentation (dropped): EX_WIRE_TRACEPOINT, EX_TRACEPOINT, EX_INSTRUMENTATION_EVENT
fn decode_one(pos: &mut usize, ctx: &DecodeCtx) -> Result<Option<Stmt>, Box<Stmt>> {
    let offset = *pos;
    if offset >= ctx.bytecode.len() {
        return Err(Box::new(make_unknown(
            offset,
            ctx,
            "unexpected end of bytecode",
        )));
    }

    let opcode = ctx.bytecode[offset];

    match opcode {
        // Assignment opcodes.
        EX_LET
        | EX_LET_MULTICAST_DELEGATE
        | EX_LET_DELEGATE
        | EX_LET_BOOL
        | EX_LET_OBJ
        | EX_LET_WEAK_OBJ_PTR
        | EX_LET_VALUE_ON_PERSISTENT_FRAME => Ok(Some(decode_assignment(pos, ctx))),

        // Call opcodes: final/local-final/math take a 4-byte object ref;
        // virtual/local-virtual take an FName (8 bytes on disk).
        // Context-prefixed calls (recv.member(args)) route through the same
        // helper; decode_expr resolves the context shape and decode_call
        // canonicalises it (static-library MethodCall to Var func, etc.).
        // Delegate opcodes (bind / add / remove / clear / multicast call)
        // also produce typed `Expr::Call` nodes from the expression decoder
        // and route through the same wrapper.
        EX_FINAL_FUNCTION
        | EX_LOCAL_FINAL_FUNCTION
        | EX_CALL_MATH
        | EX_VIRTUAL_FUNCTION
        | EX_LOCAL_VIRTUAL_FUNCTION
        | EX_CONTEXT
        | EX_CLASS_CONTEXT
        | EX_CONTEXT_FAIL_SILENT
        | EX_BIND_DELEGATE
        | EX_ADD_MULTICAST_DELEGATE
        | EX_REMOVE_MULTICAST_DELEGATE
        | EX_CLEAR_MULTICAST_DELEGATE
        | EX_CALL_MULTICAST_DELEGATE
        | EX_SET_ARRAY
        | EX_SET_SET
        | EX_SET_MAP => Ok(Some(decode_call(pos, ctx))),

        // Return: optional sub-expression then done.
        EX_RETURN => Ok(Some(decode_return(pos, ctx))),

        // Instrumentation noise: EX_WIRE_TRACEPOINT (0x5A), EX_TRACEPOINT (0x5E),
        // EX_INSTRUMENTATION_EVENT (0x6A). These appear between real opcodes and
        // carry no semantic content. Advance past them and return None so they
        // are silently dropped from the decoded statement list.
        EX_WIRE_TRACEPOINT | EX_TRACEPOINT | EX_INSTRUMENTATION_EVENT => {
            advance_expr(ctx.bytecode, pos, ctx.ue5, ctx.name_table);
            Ok(None)
        }

        // EX_END_OF_SCRIPT (0x53) is the 1-byte sentinel emitted after every
        // function's implicit final return. Consume the byte and emit no Stmt.
        EX_END_OF_SCRIPT => {
            *pos = offset + 1;
            Ok(None)
        }

        // Flow-stack markers (EX_PUSH_EXECUTION_FLOW 0x4C, EX_POP_FLOW_IF_NOT
        // 0x4F). Sequence / Latch / IsValid recognisers run earlier as
        // try_decode_* paths and consume these when they form a recognised
        // shape. Stragglers at this dispatch point have no surviving structural
        // role and are stripped here. Use opcode_length_at to consume the
        // variable-size pop_flow_if_not sub-expression in one step.
        EX_PUSH_EXECUTION_FLOW | EX_POP_FLOW_IF_NOT => {
            let opcode_len = opcode_length_at(offset, ctx.bytecode, ctx.ue5, ctx.name_table);
            *pos = offset + opcode_len;
            Ok(None)
        }

        // Everything else is unrecognised by the statement decoder.
        _ => {
            let opcode_len = opcode_length_at(offset, ctx.bytecode, ctx.ue5, ctx.name_table);
            *pos = offset + opcode_len;
            Err(Box::new(make_unknown_len(
                offset,
                ctx,
                "opcode not recognised by statement decoder",
                opcode_len,
            )))
        }
    }
}

/// Decode an assignment opcode. Handles all EX_Let* variants by decoding lhs
/// and rhs via `decode_expr`.
///
/// Opcode-specific operand layout:
/// - `EX_LET`, `EX_LET_MULTICAST_DELEGATE`, `EX_LET_DELEGATE`: field-path + lhs + rhs
/// - `EX_LET_BOOL`, `EX_LET_OBJ`, `EX_LET_WEAK_OBJ_PTR`: lhs + rhs (no field-path)
/// - `EX_LET_VALUE_ON_PERSISTENT_FRAME`: field-path + rhs (no lhs expr in stream)
///
/// The `Expr::Out` wrapper on an out-parameter lhs is preserved through the
/// pipeline; it's the ABI signal that this slot is a return value, and
/// downstream passes (dead_stmt, inline_single_use_temps) gate on it to
/// keep the assignment alive. Stripping happens at emit time.
pub(super) fn decode_assignment(pos: &mut usize, ctx: &DecodeCtx) -> Stmt {
    let offset = *pos;
    let opcode = ctx.bytecode[offset];
    *pos += 1;

    match opcode {
        EX_LET | EX_LET_MULTICAST_DELEGATE | EX_LET_DELEGATE => {
            // field-path (lhs property descriptor) + lhs expr + rhs expr
            let mut dummy_adj: i32 = 0;
            let field_name = crate::bytecode::resolve::read_bc_field_path(
                ctx.bytecode,
                pos,
                ctx.name_table,
                &mut dummy_adj,
            );
            let lhs_expr = decode_expr(pos, ctx);
            let rhs = decode_expr(pos, ctx);
            // Prefer the decoded lhs_expr; use field_name as fallback Var if Unknown.
            let lhs = match lhs_expr {
                Expr::Unknown { .. } => Expr::Var(field_name),
                other => other,
            };
            Stmt::Assignment { lhs, rhs, offset }
        }
        EX_LET_BOOL | EX_LET_OBJ | EX_LET_WEAK_OBJ_PTR => {
            let lhs = decode_expr(pos, ctx);
            let rhs = decode_expr(pos, ctx);
            Stmt::Assignment { lhs, rhs, offset }
        }
        EX_LET_VALUE_ON_PERSISTENT_FRAME => {
            // field-path names the persistent slot, rhs is the value.
            let mut dummy_adj: i32 = 0;
            let field_name = crate::bytecode::resolve::read_bc_field_path(
                ctx.bytecode,
                pos,
                ctx.name_table,
                &mut dummy_adj,
            );
            let rhs_expr = decode_expr(pos, ctx);
            let lhs = Expr::Var(field_name);
            let rhs = Expr::Persistent(Box::new(rhs_expr));
            Stmt::Assignment { lhs, rhs, offset }
        }
        _ => {
            // Fallback: shouldn't be reached given decode_one's dispatch table,
            // but skip the whole opcode and produce an Unknown assignment.
            advance_expr(ctx.bytecode, pos, ctx.ue5, ctx.name_table);
            Stmt::Assignment {
                lhs: Expr::Unknown {
                    reason: format!("unexpected assignment opcode 0x{:02x}", opcode),
                    raw_bytes: vec![opcode],
                    offset,
                },
                rhs: Expr::Unknown {
                    reason: "skipped due to unexpected opcode".into(),
                    raw_bytes: vec![],
                    offset,
                },
                offset,
            }
        }
    }
}

/// Decode a call opcode. Delegates to `decode_expr` which handles all
/// EX_*Function and EX_CallMath variants and decodes the full argument list.
///
/// Static-library MethodCalls (receiver is a class literal in the
/// `STATIC_LIBRARY_CLASSES` list) collapse to canonical `Stmt::Call {
/// func: Var(name), .. }` here so downstream matchers see one shape.
/// The Expr-level `lower_static_library_calls` pass handles the same
/// collapse for nested expressions; both share the predicate so the
/// recognised-class set stays in one place.
///
/// After canonicalisation, arguments at OUT-parameter positions of the
/// callee wrap in `Expr::Out`. The lookup keys on the resolved callee
/// name against `ctx.function_signatures`. Imported (cross-asset)
/// callees aren't represented there and pass through unwrapped.
pub(super) fn decode_call(pos: &mut usize, ctx: &DecodeCtx) -> Stmt {
    use crate::bytecode::transforms::lower_static_library_calls::is_static_library_class_literal;

    let offset = *pos;
    let expr = decode_expr(pos, ctx);
    let stmt = match expr {
        Expr::Call { name, args } => Stmt::Call {
            func: Expr::Var(name),
            args,
            offset,
        },
        Expr::MethodCall { recv, name, args } if is_static_library_class_literal(&recv) => {
            Stmt::Call {
                func: Expr::Var(name),
                args,
                offset,
            }
        }
        Expr::MethodCall { recv, name, args } => Stmt::Call {
            func: Expr::FieldAccess { recv, field: name },
            args,
            offset,
        },
        other => Stmt::Call {
            func: other,
            args: vec![],
            offset,
        },
    };
    wrap_out_args(stmt, ctx)
}

/// Wrap call-site arguments at OUT-parameter positions in `Expr::Out`,
/// using the signature recorded on `ParsedAsset` for the callee.
///
/// Returns the input unchanged when:
/// - the statement is not a `Stmt::Call`,
/// - the callee name resolves through more than a `FieldAccess` field
///   or `Var` (no signature key),
/// - `ctx.function_signatures` is absent (unit-test contexts),
/// - the callee isn't in the signature map (imported / unknown),
/// - the argument is already `Expr::Out` (avoid double-wrap).
pub(super) fn wrap_out_args(stmt: Stmt, ctx: &DecodeCtx) -> Stmt {
    const CPF_OUT_PARM: u64 = 0x100;
    let signatures = match ctx.function_signatures {
        Some(map) => map,
        None => return stmt,
    };
    let Stmt::Call { func, args, offset } = stmt else {
        return stmt;
    };
    let callee_name = match &func {
        Expr::Var(name) => name.as_str(),
        Expr::FieldAccess { field, .. } => field.as_str(),
        _ => {
            return Stmt::Call { func, args, offset };
        }
    };
    let Some(signature) = signatures.get(callee_name) else {
        return Stmt::Call { func, args, offset };
    };
    let wrapped: Vec<Expr> = args
        .into_iter()
        .enumerate()
        .map(|(idx, arg)| {
            let param = match signature.params.get(idx) {
                Some(p) => p,
                None => return arg,
            };
            if param.flags & CPF_OUT_PARM == 0 {
                return arg;
            }
            if matches!(arg, Expr::Out(_)) {
                return arg;
            }
            Expr::Out(Box::new(arg))
        })
        .collect();
    Stmt::Call {
        func,
        args: wrapped,
        offset,
    }
}

/// Decode a return opcode. The sub-expression is decoded via `decode_expr`;
/// `EX_NOTHING` / `EX_NOTHING_INT32` sub-expressions are dropped (no value).
fn decode_return(pos: &mut usize, ctx: &DecodeCtx) -> Stmt {
    let offset = *pos;
    *pos += 1; // consume EX_RETURN
               // Peek at the sub-expression opcode to decide if there's a real value.
    let value = if *pos < ctx.bytecode.len() {
        let sub_opcode = ctx.bytecode[*pos];
        match sub_opcode {
            EX_NOTHING => {
                *pos += 1;
                None
            }
            EX_NOTHING_INT32 => {
                *pos += 1; // consume the opcode
                let _ = read_bc_i32(ctx.bytecode, pos); // skip the 4-byte operand
                None
            }
            _ => {
                let expr = decode_expr(pos, ctx);
                match expr {
                    Expr::Unknown { .. } => None,
                    other => Some(other),
                }
            }
        }
    } else {
        None
    };
    Stmt::Return { value, offset }
}

/// Build a `Stmt::Unknown` from the raw bytes at `offset` with the given byte
/// length.
fn make_unknown_len(offset: usize, ctx: &DecodeCtx, reason: &str, length: usize) -> Stmt {
    let end = (offset + length).min(ctx.bytecode.len());
    let raw_bytes = ctx.bytecode[offset..end].to_vec();
    Stmt::Unknown {
        reason: reason.to_string(),
        raw_bytes,
        offset,
        length,
    }
}

/// Build a `Stmt::Unknown` using the opcode-length scanner to determine the
/// byte length, advancing `pos` past the instruction.
fn make_unknown(offset: usize, ctx: &DecodeCtx, reason: &str) -> Stmt {
    let length = if offset < ctx.bytecode.len() {
        opcode_length_at(offset, ctx.bytecode, ctx.ue5, ctx.name_table)
    } else {
        0
    };
    make_unknown_len(offset, ctx, reason, length)
}
