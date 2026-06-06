//! Naked-if recognizer for the bytecode decoder (Form B).
//!
//! A naked `if (cond) { body }` Blueprint construct (no else arm, no
//! latch macro wrapping it) compiles to:
//!
//! ```text
//! EX_PUSH_EXECUTION_FLOW <continuation>   // continuation = address after matching POP
//! [ EX_TRACEPOINT / EX_WIRE_TRACEPOINT? ] // optional instrumentation
//! EX_POP_FLOW_IF_NOT <cond_expr>          // skip body when cond is false
//! ... body opcodes ...                    // statements that run when cond is true
//! EX_POP_EXECUTION_FLOW                   // close frame on the cond=true path
//! ```
//!
//! Form B enters at the `EX_POP_FLOW_IF_NOT` rather than the parent
//! `EX_PUSH_EXECUTION_FLOW`. That entry point matches the observed
//! Sequence pin partition layout (the parent push_flow chain header
//! lives outside the partition, so a Form A entry at `EX_PUSH_EXECUTION_FLOW`
//! never fires inside a Sequence pin body).
//!
//! Two safety layers keep Form B from mistaking DoOnce init-block
//! scaffolding for a naked-if:
//!
//! - The `prescan_doonce_claims` pre-pass marks the
//!   `pop_flow_if_not(true|false) + IsClosed_Variable_<N> = true +
//!   pop_flow` triple as claimed. Form B checks `claimed_end_for`
//!   before walking and bails when the entry sits inside a claim.
//! - As defense-in-depth, Form B bails when the `pop_flow_if_not`
//!   condition decodes to a literal (`Expr::Literal("true"|"false")`).
//!   A user-visible naked-if always carries a non-literal cond.
//!
//! FlipFlop scaffolding uses `EX_JUMP_IF_NOT` (not
//! `EX_POP_FLOW_IF_NOT`) for its gate-check, so Form B never enters
//! inside FlipFlop bytes in observed fixtures and needs no dedicated
//! prescan.

use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;
use crate::bytecode::stmt::Stmt;

use super::ctx::{claimed_end_for, mark_claimed, DecodeCtx, LoopBreakGuard};
use super::expr_decode::decode_expr;

/// Bound on the body-walk so a malformed stream can't drive an
/// unbounded scan. Naked-if bodies in observed fixtures terminate
/// within a handful of opcodes; 256 is comfortably above that and
/// matches the order of magnitude used elsewhere in the decoder.
const MAX_BODY_OPCODES: usize = 256;

/// Total byte length of an `EX_JUMP` instruction (opcode + 4-byte target).
const JUMP_INSTR_BYTES: usize = 1 + 4;

/// Resolve a jump target from mem to disk via `ctx.mem_to_disk`, falling
/// back to the raw mem coordinate when the position has no drift entry.
fn jump_target_disk(target_mem: usize, ctx: &DecodeCtx) -> usize {
    ctx.mem_to_disk
        .and_then(|map| map.get(&target_mem).copied())
        .unwrap_or(target_mem)
}

/// Scan `[body_start, tail)` for the loop-break guard's own terminating
/// FORWARD break-jump: an `EX_JUMP` whose target disk lands at or past the
/// loop tail (the displaced terminator / loop epilogue). Returns the disk
/// offset of the byte immediately after that jump so the guard body can be
/// bounded there (the jump itself becomes the body's trailing `break`),
/// leaving the bytes after it (the enclosing branch's else arm) unclaimed.
///
/// Returns `None` for a single-guard loop whose body runs straight to the
/// tail with no such jump, so the body bound stays at `tail` and no break
/// is emitted (single-guard loops take this path).
fn forward_break_after(body_start: usize, tail: usize, ctx: &DecodeCtx) -> Option<usize> {
    let scan_end = tail.min(ctx.bytecode.len());
    let mut cursor = body_start;
    while cursor < scan_end {
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_JUMP && cursor + JUMP_INSTR_BYTES <= scan_end {
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let target_disk = jump_target_disk(target_mem, ctx);
            if target_disk >= tail {
                return Some(cursor + JUMP_INSTR_BYTES);
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// Try to decode a naked `if (cond) { body }` at `*pos`. Returns
/// `Some(Stmt::Branch)` on success with `*pos` advanced one byte past
/// the matching `EX_POP_EXECUTION_FLOW`. Returns `None` and leaves
/// `*pos` unchanged when the bytes don't form a recognisable naked-if
/// shape so the caller can fall through to other handlers.
///
/// Entry contract: the byte at `*pos` must be `EX_POP_FLOW_IF_NOT`.
/// The recogniser does NOT consult any preceding `EX_PUSH_EXECUTION_FLOW`
/// because the parent push lives outside the body decode's range
/// (sequence pin partitions, IsValid then-bodies, etc. all start
/// AFTER their owner's chain head).
pub(crate) fn try_decode_naked_if(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let pop_flow_if_not_disk = *pos;
    if pop_flow_if_not_disk >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode.get(pop_flow_if_not_disk)? != &EX_POP_FLOW_IF_NOT {
        return None;
    }

    // If the entry sits inside a claimed range whose owner is NOT the
    // current decode owner, it's part of a recognised scaffold (most
    // commonly the DoOnce init-block tail registered by
    // `prescan_doonce_claims`). Bail so the linear sweep's claim-skip
    // logic moves past the scaffold without synthesising a bogus
    // Branch.
    if claimed_end_for(ctx, pop_flow_if_not_disk).is_some() {
        return None;
    }

    let opcode_byte_count = 1;
    let mut cond_cursor = pop_flow_if_not_disk + opcode_byte_count;
    if cond_cursor >= ctx.bytecode.len() {
        return None;
    }
    let cond = decode_expr(&mut cond_cursor, ctx);
    if cond_cursor > range_end {
        return None;
    }

    // Constant-cond bail (defense in depth): a literal-cond
    // pop_flow_if_not is never a user-visible if-block. The DoOnce
    // init-block tail is the canonical case where this fires; the
    // claim check above usually catches it first, but the literal
    // guard also covers pathologies where the scaffold prescan
    // declines to claim.
    if matches!(&cond, Expr::Literal(text) if text == "true" || text == "false") {
        return None;
    }

    let body_start_disk = cond_cursor;

    // Balanced shape: the guard's true-body closes with its own
    // `EX_POP_EXECUTION_FLOW`. This is the common naked-if and the path
    // every passing fixture takes.
    if let Some(matching_pop_disk) =
        find_matching_pop_execution_flow(body_start_disk, range_end, ctx)
    {
        // A nested naked-if whose inner guard shares the outer's single
        // closing `EX_POP_EXECUTION_FLOW` needs the inner recursive
        // decode to see that shared pop so its own
        // `find_matching_pop_execution_flow` can balance depth back to
        // zero. Extending the body decode's end bound one byte past the
        // pop lets the inner walker reach it; the inner decode then
        // consumes through it and advances the body cursor to the same
        // termination point. Cases where the inner guard owns its own
        // closing pop are unaffected: the inner walker finds that pop
        // first, well before this extension.
        let body_end_disk = matching_pop_disk + 1;
        let then_body = decode_naked_if_body(body_start_disk, body_end_disk, ctx);
        let pop_byte_count = 1;
        *pos = matching_pop_disk + pop_byte_count;
        return Some(Stmt::Branch {
            cond,
            then_body,
            else_body: Vec::new(),
            offset: pop_flow_if_not_disk,
        });
    }

    // Loop break-guard fallback: no balancing pop because the guard's
    // false path pops the enclosing loop's trampoline frame and resumes
    // the loop increment. Recover the guard bounded by the loop tail.
    try_decode_loop_break_guard(pos, pop_flow_if_not_disk, body_start_disk, cond, ctx)
}

/// Recover a loop-internal `if` break-guard whose `EX_POP_FLOW_IF_NOT`
/// has no balancing `EX_POP_EXECUTION_FLOW`.
///
/// Fires only when a loop-break-guard context is active
/// (`ctx.loop_break_guard`, set by `try_decode_loop` around an absorbed
/// ForEach loop's displaced-body decode) AND the discriminator passes:
/// the guard's false-path continuation (the trampoline frame's pushed
/// target, the loop increment) lands inside the innermost active loop's
/// scope `[scope_start, scope_end)`. That confirms the false path
/// resumes the loop, not some unrelated outer frame.
///
/// The guard's true-body runs to the loop tail (`guard.tail`, the
/// displaced terminator). The recovered body range is claimed under the
/// loop region owner so the region walker's disk-order re-walk skips it
/// instead of re-emitting the body as a dead post-loop tail.
fn try_decode_loop_break_guard(
    pos: &mut usize,
    guard_offset: usize,
    body_start_disk: usize,
    cond: Expr,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let guard: LoopBreakGuard = ctx.loop_break_guard.get()?;

    // Discriminator: the false-path continuation must resume the
    // innermost active loop. A guard whose continuation lands outside the
    // loop scope is some other unbalanced flow shape, not a loop break.
    let continuation_in_scope =
        guard.scope_start <= guard.continuation && guard.continuation < guard.scope_end;
    if !continuation_in_scope {
        return None;
    }

    // The body cannot extend past the loop tail.
    let mut body_end_disk = guard.tail;
    if body_end_disk <= body_start_disk {
        return None;
    }

    // The body must be a flat terminal block. A guard whose true-body
    // itself contains an `EX_PUSH_EXECUTION_FLOW` spans a nested flow
    // construct (e.g. an inner loop's own break trampoline) whose
    // displaced statements live outside `[body_start, tail)`. The simple
    // tail bound cannot reconstruct that nesting, it would emit a
    // statement-stripped guard with the body scattered into a dead tail.
    //
    // When the nested flow is a single self-contained SequenceChain
    // trampoline whose JUMP targets the loop exit (`tail + 1`), the body IS
    // recoverable: `decode_naked_if_body` already routes the trampoline's
    // displaced LET through `decode_one_or_branch` (production emits both
    // LETs today, just unguarded), and a `break` is synthesized from the
    // loop-break-guard semantic (the cond=true path exits the loop). Any
    // other nested-flow shape, or a trampoline that does not jump to the
    // loop exit, still bails (recovering it here would be unsound).
    let mut synthesize_break = false;
    if body_contains_nested_flow(body_start_disk, body_end_disk, ctx) {
        match classify_nested_flow(body_start_disk, body_end_disk, ctx) {
            NestedFlowShape::TrampolineOnly {
                jump_to_loop_exit: true,
            } => {
                synthesize_break = true;
            }
            // Not a loop-exiting trampoline: bail (recovery would be unsound).
            _ => return None,
        }
    }

    // Multi-break shape: the guard's true-body terminates with its
    // own FORWARD break-jump (an `EX_JUMP` to the loop tail / epilogue)
    // before reaching `tail`. The default tail bound over-runs that jump
    // and swallows the enclosing branch's else arm. Bound the body at the
    // break-jump instead and append a trailing `Stmt::Break`. A
    // single-guard loop runs straight to `tail` with no such jump, so
    // `forward_break_after` returns `None` and the body bound is unchanged.
    let mut trailing_break: Option<Stmt> = None;
    if let Some(end) = forward_break_after(body_start_disk, guard.tail, ctx) {
        body_end_disk = end;
        trailing_break = Some(Stmt::Break {
            offset: end - JUMP_INSTR_BYTES,
        });
    }

    let mut then_body = decode_naked_if_body(body_start_disk, body_end_disk, ctx);
    if let Some(break_stmt) = trailing_break {
        then_body.push(break_stmt);
    } else if synthesize_break {
        // The break is synthesized from the loop-break-guard semantic
        // (the trampoline carries no forward break-jump; the cond=true path
        // exits the loop). Offset at the guard so emit ordering is stable.
        then_body.push(Stmt::Break {
            offset: guard_offset,
        });
    }

    // Claim the recovered body so the region walker's disk-order re-walk
    // (`decode_region_block_if_unclaimed`, gated on `claimed_end_for_disk_sweep`)
    // skips these bytes instead of re-emitting them as a dead tail after
    // the loop. The loop's own displaced-body decode runs without a
    // matching decoding owner and is unaffected (it has already produced
    // this Branch); only the later re-walk consults the claim.
    mark_claimed(ctx, body_start_disk, body_end_disk, guard.owner);

    // Advance past the guard's true-body. The displaced terminator
    // (`EX_POP_EXECUTION_FLOW` at the loop tail) is consumed by the loop's
    // own framing, so stop at the tail rather than one byte past it.
    *pos = body_end_disk;

    Some(Stmt::Branch {
        cond,
        then_body,
        else_body: Vec::new(),
        offset: guard_offset,
    })
}

/// Walk forward from `body_start` tracking flow-stack depth (starting
/// at 1 to represent the open frame the matching pop must close).
/// Returns the disk offset of the `EX_POP_EXECUTION_FLOW` that brings
/// depth back to zero.
///
/// Returns `None` when:
/// - the walk reaches `range_end` without depth dropping to zero;
/// - it encounters a zero-length opcode (defensive against malformed
///   streams);
/// - the opcode budget is exhausted before the matching pop is found.
fn find_matching_pop_execution_flow(
    body_start: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<usize> {
    let scan_end = range_end.min(ctx.bytecode.len());
    let mut cursor = body_start;
    let mut depth: i32 = 1;
    let mut visited = 0usize;
    while cursor < scan_end && visited < MAX_BODY_OPCODES {
        let opcode = ctx.bytecode[cursor];
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        match opcode {
            EX_PUSH_EXECUTION_FLOW => depth += 1,
            EX_POP_EXECUTION_FLOW => {
                depth -= 1;
                if depth == 0 {
                    return Some(cursor);
                }
            }
            _ => {}
        }
        cursor += length;
        visited += 1;
    }
    None
}

/// True when the byte range `[body_start, body_end)` contains an
/// `EX_PUSH_EXECUTION_FLOW` at any opcode boundary. Used by the loop
/// break-guard fallback to decline guards whose body spans a nested flow
/// construct (an inner loop's break trampoline), where the simple
/// tail-bounded body recovery would scatter the body's statements.
fn body_contains_nested_flow(body_start: usize, body_end: usize, ctx: &DecodeCtx) -> bool {
    let scan_end = body_end.min(ctx.bytecode.len());
    let mut cursor = body_start;
    while cursor < scan_end {
        if ctx.bytecode[cursor] == EX_PUSH_EXECUTION_FLOW {
            return true;
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return false;
        }
        cursor += length;
    }
    false
}

/// Outcome of classifying a loop-break-guard body whose statements span a
/// nested flow construct. Decides whether the nested flow is a recoverable
/// SequenceChain trampoline and whether a synthesized `break` is sound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NestedFlowShape {
    /// The body's only nested flow is a single self-contained SequenceChain
    /// trampoline (one `EX_PUSH_EXECUTION_FLOW` whose resume target sits
    /// inside `[body_start, tail)`, paired with an `EX_JUMP` to a displaced
    /// block). `jump_to_loop_exit` is true when that trampoline `EX_JUMP`
    /// targets the loop exit landing (`tail + 1`), which is the
    /// discriminator that makes a synthesized `break` sound.
    TrampolineOnly { jump_to_loop_exit: bool },
    /// The body holds something other than a single trampoline (multiple
    /// pushes, a push whose resume escapes the body, or an unbalanced
    /// shape). Not recoverable; the caller bails.
    Other,
}

/// Classify the nested flow inside a loop-break-guard body `[body_start,
/// tail)`. The recoverable shape is a single SequenceChain trampoline: one
/// `EX_PUSH_EXECUTION_FLOW` (resume target inside the body) immediately
/// followed by an `EX_JUMP` to a displaced block, with no other flow
/// opcodes in the body.
///
/// Caller contract: only invoked after `body_contains_nested_flow` returned
/// true, so at least one `EX_PUSH_EXECUTION_FLOW` is present.
fn classify_nested_flow(body_start: usize, tail: usize, ctx: &DecodeCtx) -> NestedFlowShape {
    let scan_end = tail.min(ctx.bytecode.len());
    let mut cursor = body_start;
    let mut push_count = 0usize;
    let mut push_resume_in_body = false;
    let mut jump_to_loop_exit = false;
    let mut saw_pop = false;
    while cursor < scan_end {
        let opcode = ctx.bytecode[cursor];
        match opcode {
            EX_PUSH_EXECUTION_FLOW => {
                push_count += 1;
                let mut peek = cursor + 1;
                let resume_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
                let resume_disk = jump_target_disk(resume_mem, ctx);
                if body_start <= resume_disk && resume_disk < tail {
                    push_resume_in_body = true;
                }
            }
            EX_JUMP if cursor + JUMP_INSTR_BYTES <= scan_end => {
                let mut peek = cursor + 1;
                let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
                let target_disk = jump_target_disk(target_mem, ctx);
                // The trampoline jump to the loop-exit landing one past the
                // tail is the break discriminator. A jump landing elsewhere
                // means this is not a loop-exiting trampoline.
                if target_disk == tail + 1 {
                    jump_to_loop_exit = true;
                }
            }
            EX_POP_EXECUTION_FLOW => saw_pop = true,
            _ => {}
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return NestedFlowShape::Other;
        }
        cursor += length;
    }

    // Exactly one trampoline push, its resume reentry inside the body, and
    // no stray pop closing a frame the body opened. The displaced LET that
    // the resume points at is decoded by `decode_naked_if_body` via
    // `decode_one_or_branch`, the same path production already uses to emit
    // both LETs in order.
    if push_count == 1 && push_resume_in_body && !saw_pop {
        NestedFlowShape::TrampolineOnly { jump_to_loop_exit }
    } else {
        NestedFlowShape::Other
    }
}

/// Decode the naked-if body at `[body_start, body_end)` into a flat
/// statement list. Uses `decode_one_or_branch` per opcode so nested
/// constructs (Sequence, IsValid, Latch, inner Branches) recurse via
/// the same dispatch chain that decoded the outer if.
fn decode_naked_if_body(body_start: usize, body_end: usize, ctx: &DecodeCtx) -> Vec<Stmt> {
    use super::block::decode_one_or_branch;
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut cursor = body_start;
    while cursor < body_end {
        let before = cursor;
        match decode_one_or_branch(&mut cursor, body_end, ctx) {
            Ok(Some(stmt)) => stmts.push(stmt),
            Ok(None) => {}
            Err(unknown) => stmts.push(*unknown),
        }
        if cursor == before {
            cursor += 1;
        }
        if cursor > body_end {
            break;
        }
    }
    stmts
}
