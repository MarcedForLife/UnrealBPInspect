//! Sequence-node recognition for the bytecode decoder.
//!
//! A Blueprint Sequence node with N execution pins compiles to a chain of
//! `EX_PUSH_EXECUTION_FLOW` opcodes followed by pin-0's body and a chain
//! of `EX_POP_EXECUTION_FLOW`-terminated pin bodies. Two surface forms
//! exist:
//!
//! 1. **Grouped** — pushes are contiguous, pin-0 body starts after the
//!    last push.
//! 2. **Interleaved** — pushes are separated by side-effect statements
//!    (also handled here in the same scan).
//!
//! Push order is reversed relative to pin-execution order: the last push
//! sits on top of the runtime stack, so it pops first and runs as pin 1
//! after pin 0 falls through. This module produces a `Stmt::Sequence`
//! whose `pins` are listed in execution order (pin 0 first).
//!
//! Pin convergence (the offset where execution resumes after the whole
//! Sequence) is the maximum end of the per-pin partition, looked up from
//! the pre-built `StructureSkeleton` keyed by the chain head's disk offset.

use std::ops::Range;

use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::stmt::Stmt;

use super::branch::decode_subrange;
use super::ctx::{DecodeCtx, OwnerId};

/// Try to decode a Sequence at `*pos`. Returns `Some(Stmt::Sequence)` on
/// success, with `*pos` advanced past the entire construct (including
/// every pin body). Returns `None` if the bytes don't form a recognisable
/// Sequence, leaving `*pos` unchanged so the caller can fall through to
/// other handlers.
///
/// Pin partitioning comes from `ctx.skeleton`: the structural skeleton is
/// pre-built per event/function and keyed by chain-head disk offset, so
/// each lookup is a single map probe. Returns `None` when the skeleton
/// has no entry for this head (the position isn't a recognised chain
/// head), letting the caller fall through to non-Sequence handlers.
///
/// `range_end` is the exclusive upper bound of the enclosing decode
/// range; the recogniser never reads past it.
pub(crate) fn try_decode_sequence(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    if *pos >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode.get(*pos)? != &EX_PUSH_EXECUTION_FLOW {
        return None;
    }
    let construct_offset = *pos;

    let skeleton = ctx.skeleton?;
    let node = skeleton.push_chains.get(&construct_offset)?;

    // The skeleton spans `owner_start..owner_end` for the event, which is
    // the union span of its disjoint owned ranges. A chain head's
    // interleaved-push lookahead and BFS reachability can pick up bytes
    // belonging to a sibling event that sits between two of this event's
    // segments. Two checks together reject those false matches:
    //
    // * The chain's `[head, after_chain)` extent must fit within one
    //   contiguous owned segment, because side-effect interleaving can't
    //   legally skip across owned-range gaps.
    // * Every pin partition byte must lie inside `ctx.owned_ranges`,
    //   guarding against pin bodies that bleed into a sibling event's
    //   bytes during BFS reachability.
    if !chain_extent_in_one_segment(construct_offset, node.after_chain, range_end, ctx) {
        return None;
    }
    if !pin_partitions_within_owned(&node.pin_partitions, range_end, ctx) {
        return None;
    }

    let after_chain_disk = node.after_chain;
    let pre_pin_stmts = decode_pre_pin_stmts(construct_offset, after_chain_disk, range_end, ctx);

    let resume_disk = node
        .pin_partitions
        .iter()
        .flat_map(|segments| segments.iter().map(|range| range.end))
        .max()
        .unwrap_or(after_chain_disk);

    let chain_owner = OwnerId::SequenceChain {
        head_disk: construct_offset,
    };
    let mut pins: Vec<Vec<Stmt>> = Vec::with_capacity(node.pin_partitions.len());
    for segments in &node.pin_partitions {
        // Override owned_ranges with the pin's own partition while we
        // decode this pin. Nested constructs (Branches, inner Sequences)
        // then see only the pin's bytes as in-scope, so a Branch
        // displaced into another segment of the same pin still
        // classifies InRange and an inner Sequence with seeds in
        // multiple pin segments can find them all.
        let pin_ctx = ctx_with_owned_ranges(ctx, segments);
        // Decode each pin body under the CFG-region owner derived from
        // the pin's first segment, so the claim lookup bypasses any
        // prescan claim sitting inside that region. Falls back to the
        // SequenceChain owner when no region tree is available
        // (synthetic contexts, standalone functions). The chain owner
        // by itself once sufficed because absorbed claims propagated
        // SequenceChain ownership; with CfgRegion, bypass is uniform
        // across prescan owners.
        let pin_start = segments.first().map(|range| range.start).unwrap_or(0);
        let pin_owner = pin_ctx
            .region_id_for(pin_start)
            .map(|region_id| OwnerId::CfgRegion { region_id })
            .unwrap_or(chain_owner);
        let _guard = pin_ctx.with_decoding_owner(pin_owner);
        let pin_end = segments.last().map(|range| range.end).unwrap_or(pin_start);
        pins.push(decode_subrange(pin_start, pin_end, &pin_ctx));
    }

    // Interleaved form: side-effect statements gathered between pushes
    // run unconditionally before pin 0, so they prepend to pin 0's body
    // and execute in the same order they appeared in the bytecode.
    if !pre_pin_stmts.is_empty() {
        if let Some(pin0) = pins.first_mut() {
            let mut combined = pre_pin_stmts;
            combined.append(pin0);
            *pin0 = combined;
        }
    }

    *pos = resume_disk;

    // Blueprint-emitted for-loop scaffolds reuse the 2-PUSH Sequence
    // shape (counter init in pin[0], loop body in pin[1]). Recognise
    // that shape and emit a single-pin Sequence holding both pieces in
    // execution order so refine_loops sees init+Loop together when
    // promoting to ForC / ForEach.
    //
    // Defensive coverage: under the current chain-head-floor partitioning
    // every for-loop site in the test fixtures already promotes correctly
    // without this fold (toggling the recognizer off produces a zero output
    // diff), but the recognizer is preserved so future shape changes that
    // surface a 2-pin scaffold at this layer still merge cleanly.
    if matches_for_loop_scaffold(&pins) {
        let mut iter = pins.into_iter();
        let mut merged = iter.next().unwrap_or_default();
        if let Some(pin1) = iter.next() {
            merged.extend(pin1);
        }
        return Some(Stmt::Sequence {
            pins: vec![merged],
            offset: construct_offset,
        });
    }

    Some(Stmt::Sequence {
        pins,
        offset: construct_offset,
    })
}

/// Recognise a Blueprint for-loop scaffold encoded as a 2-pin Sequence.
///
/// Signature:
/// 1. Exactly 2 pins.
/// 2. `pin[0]` starts with `Assignment { lhs: Var(counter), rhs: Literal("0") }`.
///    The counter name is the BP-emitted `Temp_int_Variable` /
///    `Temp_int_Loop_Counter_Variable*` family or any var ending in
///    `_Counter_Variable` (the criterion is structural: literal-zero init
///    of an `int` temp).
/// 3. `pin[1]` body contains a `Stmt::Loop` whose cond top-level references
///    `counter` (bare `Var(counter)` chain or a `Binary` whose operands
///    transitively reach `counter`). The chain check is deliberately
///    conservative: free-var search inside the cond expression, no scope-
///    walking, since the counter is the loop's gating variable and is
///    visible inside the cond directly.
///
/// Caller merges the two pins on match. User-authored 2-pin Sequences
/// emit the regular 2-pin shape via the caller's fall-through branch.
fn matches_for_loop_scaffold(pins: &[Vec<Stmt>]) -> bool {
    if pins.len() != 2 {
        return false;
    }
    let counter = match pin_zero_counter_init_name(&pins[0]) {
        Some(name) => name,
        None => return false,
    };
    pin_one_loop_references_counter(&pins[1], &counter)
}

/// First statement of `pin0` is `Assignment { lhs: Var(name), rhs: Literal("0") }`?
/// Returns the counter `name` on match.
fn pin_zero_counter_init_name(pin0: &[Stmt]) -> Option<String> {
    let first = pin0.first()?;
    let Stmt::Assignment {
        lhs:
            crate::bytecode::expr::Expr::Var(name)
            | crate::bytecode::expr::Expr::FieldAccess { field: name, .. },
        rhs: crate::bytecode::expr::Expr::Literal(literal),
        ..
    } = first
    else {
        return None;
    };
    if literal != "0" {
        return None;
    }
    Some(name.clone())
}

/// `pin1` contains a `Stmt::Loop` whose `cond` references `counter`?
/// Searches the body in execution order; the first `Loop` is sufficient
/// because the for-loop scaffold emits its loop directly inside the pin.
fn pin_one_loop_references_counter(pin1: &[Stmt], counter: &str) -> bool {
    pin1.iter().any(|stmt| match stmt {
        Stmt::Loop { cond, .. } => cond
            .as_ref()
            .map(|expr| expr_mentions_var(expr, counter))
            .unwrap_or(false),
        _ => false,
    })
}

/// True when `expr` mentions `Var(name)` or `FieldAccess { field: name }`
/// anywhere in its sub-tree. Used by [`pin_one_loop_references_counter`]
/// to decide whether the loop's cond is gated on the counter.
fn expr_mentions_var(expr: &crate::bytecode::expr::Expr, name: &str) -> bool {
    use crate::bytecode::expr::Expr;
    match expr {
        Expr::Var(other) => other == name,
        Expr::FieldAccess { recv, field } => field == name || expr_mentions_var(recv, name),
        Expr::Index { recv, idx } => expr_mentions_var(recv, name) || expr_mentions_var(idx, name),
        Expr::Binary { lhs, rhs, .. } => {
            expr_mentions_var(lhs, name) || expr_mentions_var(rhs, name)
        }
        Expr::Unary { operand, .. } => expr_mentions_var(operand, name),
        Expr::Cast { inner, .. } => expr_mentions_var(inner, name),
        Expr::Call { args, .. } => args.iter().any(|arg| expr_mentions_var(arg, name)),
        Expr::MethodCall { recv, args, .. } => {
            expr_mentions_var(recv, name) || args.iter().any(|arg| expr_mentions_var(arg, name))
        }
        Expr::ArrayLit(items) => items.iter().any(|item| expr_mentions_var(item, name)),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_mentions_var(cond, name)
                || expr_mentions_var(then_expr, name)
                || expr_mentions_var(else_expr, name)
        }
        Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
            expr_mentions_var(inner, name)
        }
        Expr::Resume { inner, .. } => expr_mentions_var(inner, name),
        Expr::StructConstruct { fields, .. } => fields
            .iter()
            .any(|(_, value)| expr_mentions_var(value, name)),
        Expr::Switch {
            index,
            cases,
            default,
        } => {
            expr_mentions_var(index, name)
                || cases.iter().any(|case| {
                    expr_mentions_var(&case.value, name) || expr_mentions_var(&case.body, name)
                })
                || expr_mentions_var(default, name)
        }
        Expr::Literal(_) | Expr::Unknown { .. } => false,
    }
}

/// True when `[head, after_chain)` fits inside a single segment of
/// `ctx.owned_ranges` (or `[0, range_end)` when no owned ranges are set).
/// The skeleton spans the union of disjoint owned ranges; without this
/// check, a chain head could pull in interleaved-push lookahead from
/// bytes belonging to a sibling event.
fn chain_extent_in_one_segment(
    head: usize,
    after_chain: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> bool {
    match ctx.owned_ranges {
        Some(ranges) => ranges
            .iter()
            .any(|range| range.start <= head && after_chain <= range.end),
        None => after_chain <= range_end,
    }
}

/// True when every byte covered by the per-pin partition lies inside one
/// of the caller's owned segments (or `[0, range_end)` when no owned
/// ranges are set). The skeleton's `partition_seeds` clips by a
/// contiguous BFS boundary, so a chain whose BFS reachability crossed
/// into a sibling event's bytes gets caught here.
fn pin_partitions_within_owned(
    partitions: &[Vec<Range<usize>>],
    range_end: usize,
    ctx: &DecodeCtx,
) -> bool {
    let in_owned = |range: &Range<usize>| match ctx.owned_ranges {
        Some(ranges) => ranges
            .iter()
            .any(|owned| owned.start <= range.start && range.end <= owned.end),
        None => range.end <= range_end,
    };
    partitions.iter().flatten().all(in_owned)
}

/// Walk the bytes from `head` to `after_chain` and decode any non-push
/// opcodes encountered. The skeleton's `after_chain` already accounts for
/// interleaved separators between push opcodes, so any non-push opcode in
/// this span is a pre-pin side-effect statement that runs unconditionally
/// before pin 0.
///
/// TODO(unify-shape-detection): the skeleton's `scan_push_chain_shape`
/// reproduces the canonical-shape walk used here. Consolidating would
/// require a byte-level core (no `DecodeCtx`, no recursive decoder) plus
/// a thin decoder-side wrapper for pre-pin statement extraction. Tractable
/// but deferred.
fn decode_pre_pin_stmts(
    head: usize,
    after_chain: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    use super::block::decode_one_or_branch;
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut cursor = head;
    while cursor < after_chain {
        let opcode = match ctx.bytecode.get(cursor) {
            Some(&op) => op,
            None => break,
        };
        if opcode == EX_PUSH_EXECUTION_FLOW {
            let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
            if length == 0 {
                break;
            }
            cursor += length;
            continue;
        }

        let before = cursor;
        match decode_one_or_branch(&mut cursor, range_end, ctx) {
            Ok(Some(stmt)) => stmts.push(stmt),
            Ok(None) => {}
            Err(unknown) => stmts.push(*unknown),
        }
        if cursor == before {
            break;
        }
    }
    stmts
}

/// Build a `DecodeCtx` that mirrors `ctx` but pins `owned_ranges` to the
/// supplied per-pin partition. Used to scope each Sequence pin body's
/// recursion: nested Branches and Sequences see only this pin's bytes
/// as in-scope, so cross-segment displaced bodies stay classified
/// `InRange` and nested constructs whose pieces span multiple pin
/// segments are recognised correctly.
fn ctx_with_owned_ranges<'a>(
    ctx: &'a DecodeCtx<'a>,
    owned: &'a [std::ops::Range<usize>],
) -> DecodeCtx<'a> {
    // Sequence sub-scope keeps the parent's claim set and owner; only the
    // owned-range slice narrows. child() copies the shared refs and resets
    // claimed/decoding_owner, so re-set both to the parent's here.
    DecodeCtx {
        owned_ranges: Some(owned),
        claimed: ctx.claimed,
        decoding_owner: std::cell::Cell::new(ctx.decoding_owner.get()),
        ..ctx.child()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::decode::test_fixtures::{
        empty_name_table, identity_map, stmt_kind, u32_le, ue4_ctx,
    };
    use crate::bytecode::structure::{build_skeleton, StructureSkeleton};
    use std::collections::BTreeMap;

    /// Build a skeleton spanning the full bytecode buffer and return a
    /// `DecodeCtx` that references it. Test helper for the synthetic
    /// streams below; production code builds the skeleton in
    /// `decode/mod.rs` per event/function.
    fn ctx_with_skeleton<'a>(
        stream: &'a [u8],
        names: &'a crate::binary::NameTable,
        map: &'a BTreeMap<usize, usize>,
        skeleton: &'a StructureSkeleton,
    ) -> DecodeCtx<'a> {
        let mut ctx = ue4_ctx(stream, names, map);
        ctx.skeleton = Some(skeleton);
        ctx
    }

    /// Build a synthetic 2-pin grouped Sequence:
    ///   0x00 EX_PUSH_EXECUTION_FLOW target=0x0C  (5 bytes)
    ///   0x05 EX_NOTHING                             (pin 0 body)
    ///   0x06 EX_POP_EXECUTION_FLOW                  (1 byte)
    ///   0x07 EX_NOTHING                             (filler, not in pin)
    ///   0x08 EX_END_OF_SCRIPT                       (filler)
    ///   0x0C EX_NOTHING                             (pin 1 body)
    ///   0x0D EX_POP_EXECUTION_FLOW                  (1 byte)
    fn two_pin_grouped_stream() -> (Vec<u8>, Vec<usize>) {
        let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
        stream.extend_from_slice(&u32_le(0x0C));
        stream.push(EX_NOTHING); // 0x05 pin 0
        stream.push(EX_POP_EXECUTION_FLOW); // 0x06 pin 0 pop
        stream.push(EX_NOTHING); // 0x07 filler
        stream.push(EX_NOTHING); // 0x08 filler (pad to 0x0C)
        stream.push(EX_NOTHING); // 0x09
        stream.push(EX_NOTHING); // 0x0A
        stream.push(EX_NOTHING); // 0x0B
        stream.push(EX_NOTHING); // 0x0C pin 1
        stream.push(EX_POP_EXECUTION_FLOW); // 0x0D pin 1 pop
        stream.push(EX_END_OF_SCRIPT);
        let boundaries = vec![0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
        (stream, boundaries)
    }

    #[test]
    fn two_pin_grouped_decodes_with_two_pins() {
        let (stream, boundaries) = two_pin_grouped_stream();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        let stmt =
            try_decode_sequence(&mut pos, stream.len(), &ctx).expect("expected Stmt::Sequence");
        match stmt {
            Stmt::Sequence { pins, .. } => {
                assert_eq!(pins.len(), 2, "expected exactly 2 pins, got {}", pins.len());
                assert!(!pins[0].is_empty(), "pin 0 should have stmts");
                assert!(!pins[1].is_empty(), "pin 1 should have stmts");
            }
            other => panic!("expected Stmt::Sequence, got {:?}", stmt_kind(&other)),
        }
        assert_eq!(pos, 0x0E, "should resume past pin 1's pop");
    }

    /// Build a synthetic 3-pin grouped Sequence with EX_NOTHING used as
    /// a stand-in separator between pushes. Real Blueprint bytecode
    /// emits `push; (something); push; (something);` rather than two
    /// pushes back-to-back; the latter shape is reserved for nested
    /// Sequence detection.
    ///
    ///   0x00 EX_PUSH target=0x18   pin 2 (pushed first, runs last)
    ///   0x05 EX_NOTHING            separator
    ///   0x06 EX_PUSH target=0x14   pin 1 (pushed second, runs second)
    ///   0x0B EX_NOTHING            pin 0 inline body
    ///   0x0C EX_POP                pin 0 pop
    ///   0x0D..0x13 filler
    ///   0x14 EX_NOTHING            pin 1 body
    ///   0x15 EX_POP
    ///   0x16..0x17 filler
    ///   0x18 EX_NOTHING            pin 2 body
    ///   0x19 EX_POP
    fn three_pin_grouped_stream() -> (Vec<u8>, Vec<usize>) {
        let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
        stream.extend_from_slice(&u32_le(0x18)); // pushed first
        stream.push(EX_NOTHING); // 0x05 separator
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x06
        stream.extend_from_slice(&u32_le(0x14)); // pushed second
        stream.push(EX_NOTHING); // 0x0B pin 0
        stream.push(EX_POP_EXECUTION_FLOW); // 0x0C
        stream.push(EX_NOTHING); // 0x0D
        stream.push(EX_NOTHING); // 0x0E
        stream.push(EX_NOTHING); // 0x0F
        stream.push(EX_NOTHING); // 0x10
        stream.push(EX_NOTHING); // 0x11
        stream.push(EX_NOTHING); // 0x12
        stream.push(EX_NOTHING); // 0x13
        stream.push(EX_NOTHING); // 0x14 pin 1
        stream.push(EX_POP_EXECUTION_FLOW); // 0x15
        stream.push(EX_NOTHING); // 0x16
        stream.push(EX_NOTHING); // 0x17
        stream.push(EX_NOTHING); // 0x18 pin 2
        stream.push(EX_POP_EXECUTION_FLOW); // 0x19
        stream.push(EX_END_OF_SCRIPT);
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        (stream, boundaries)
    }

    #[test]
    fn three_pin_grouped_orders_pins_by_execution() {
        let (stream, boundaries) = three_pin_grouped_stream();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        let stmt =
            try_decode_sequence(&mut pos, stream.len(), &ctx).expect("expected Stmt::Sequence");
        match stmt {
            Stmt::Sequence { pins, .. } => {
                assert_eq!(pins.len(), 3, "expected 3 pins, got {}", pins.len());
            }
            other => panic!("expected Stmt::Sequence, got {:?}", stmt_kind(&other)),
        }
        // Resume position should land past pin 2's pop (0x19 pop -> 0x1A).
        assert_eq!(pos, 0x1A, "resume should pass last pin's pop");
    }

    /// Build a synthetic 2-pin interleaved Sequence: a side-effect
    /// statement (EX_NOTHING) sits between two pushes. The decoder
    /// should attribute the side-effect to pin 0.
    ///
    /// Layout:
    ///   0x00 EX_PUSH target=0x14            (push pin 2)
    ///   0x05 EX_NOTHING                      (interleaved between pushes)
    ///   0x06 EX_PUSH target=0x10            (push pin 1)
    ///   0x0B EX_NOTHING                      (pin 0 body)
    ///   0x0C EX_POP                          (pin 0 pop)
    ///   0x0D..0x0F filler
    ///   0x10 EX_NOTHING                      (pin 1 body)
    ///   0x11 EX_POP
    ///   0x12..0x13 filler
    ///   0x14 EX_NOTHING                      (pin 2 body)
    ///   0x15 EX_POP
    fn three_pin_interleaved_stream() -> (Vec<u8>, Vec<usize>) {
        let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
        stream.extend_from_slice(&u32_le(0x14)); // pushes pin 2 first
        stream.push(EX_NOTHING); // 0x05 interleaved
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x06
        stream.extend_from_slice(&u32_le(0x10)); // pushes pin 1
        stream.push(EX_NOTHING); // 0x0B pin 0 body
        stream.push(EX_POP_EXECUTION_FLOW); // 0x0C pin 0 pop
        stream.push(EX_NOTHING); // 0x0D
        stream.push(EX_NOTHING); // 0x0E
        stream.push(EX_NOTHING); // 0x0F
        stream.push(EX_NOTHING); // 0x10 pin 1 body
        stream.push(EX_POP_EXECUTION_FLOW); // 0x11
        stream.push(EX_NOTHING); // 0x12
        stream.push(EX_NOTHING); // 0x13
        stream.push(EX_NOTHING); // 0x14 pin 2 body
        stream.push(EX_POP_EXECUTION_FLOW); // 0x15
        stream.push(EX_END_OF_SCRIPT);
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        (stream, boundaries)
    }

    #[test]
    fn interleaved_three_pin_attributes_side_effect_to_pin_zero() {
        let (stream, boundaries) = three_pin_interleaved_stream();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        let stmt = try_decode_sequence(&mut pos, stream.len(), &ctx)
            .expect("expected Stmt::Sequence for interleaved chain");
        match stmt {
            Stmt::Sequence { pins, .. } => {
                assert_eq!(pins.len(), 3, "expected 3 pins, got {}", pins.len());
                // Pin 0 should carry both the interleaved EX_NOTHING and
                // its inline body's EX_NOTHING, so it has at least 2 stmts.
                assert!(
                    pins[0].len() >= 2,
                    "pin 0 should have interleaved + inline stmts, got {}",
                    pins[0].len()
                );
            }
            other => panic!("expected Stmt::Sequence, got {:?}", stmt_kind(&other)),
        }
        assert_eq!(pos, 0x16, "resume past last pin's pop");
    }

    /// Build a 2-pin Sequence whose pin 0 contains a nested 2-pin
    /// Sequence. Verifies recursive decode handles nested pushes/pops.
    ///
    /// Outer: push target=0x14
    ///   pin 0 (inline) starts at 0x05 with another Sequence.
    ///     Inner push target=0x0B  (pin 1 inner)
    ///     Inner pin 0 inline at 0x0A: EX_NOTHING
    ///     0x0A EX_POP (inner pin 0 pop)  -- but wait, byte at 0x0A and 0x0B align
    /// Layout:
    ///   0x00 EX_PUSH target=0x14    (outer pushes pin 1)
    ///   0x05 EX_PUSH target=0x10    (inner pushes its pin 1)  -- but inner's pop is at 0x0B
    ///   0x0A EX_NOTHING             (inner pin 0 body)
    ///   0x0B EX_POP                 (inner pin 0 pop)
    ///   0x0C..0x0F filler
    ///   0x10 EX_NOTHING             (inner pin 1 body)
    ///   0x11 EX_POP                 (inner pin 1 pop -> outer pin 0 done)
    ///   0x12..0x13 filler
    ///   0x14 EX_NOTHING             (outer pin 1 body)
    ///   0x15 EX_POP                 (outer pin 1 pop)
    fn nested_two_pin_stream() -> (Vec<u8>, Vec<usize>) {
        let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
        stream.extend_from_slice(&u32_le(0x14)); // outer push -> pin 1
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x05 inner push
        stream.extend_from_slice(&u32_le(0x10)); // inner push -> inner pin 1
        stream.push(EX_NOTHING); // 0x0A inner pin 0
        stream.push(EX_POP_EXECUTION_FLOW); // 0x0B inner pin 0 pop
        stream.push(EX_NOTHING); // 0x0C
        stream.push(EX_NOTHING); // 0x0D
        stream.push(EX_NOTHING); // 0x0E
        stream.push(EX_NOTHING); // 0x0F
        stream.push(EX_NOTHING); // 0x10 inner pin 1 body
        stream.push(EX_POP_EXECUTION_FLOW); // 0x11 inner pin 1 pop -> outer pin 0 done
        stream.push(EX_NOTHING); // 0x12
        stream.push(EX_NOTHING); // 0x13
        stream.push(EX_NOTHING); // 0x14 outer pin 1
        stream.push(EX_POP_EXECUTION_FLOW); // 0x15
        stream.push(EX_END_OF_SCRIPT);
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        (stream, boundaries)
    }

    #[test]
    fn nested_sequence_decodes_via_recursion() {
        let (stream, boundaries) = nested_two_pin_stream();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        let stmt = try_decode_sequence(&mut pos, stream.len(), &ctx)
            .expect("expected outer Stmt::Sequence");
        match stmt {
            Stmt::Sequence { pins, .. } => {
                assert_eq!(pins.len(), 2, "outer should have 2 pins");
                // Outer pin 0 should contain a nested Sequence stmt.
                let inner = pins[0]
                    .iter()
                    .find(|s| matches!(s, Stmt::Sequence { .. }))
                    .expect("outer pin 0 should contain a nested Stmt::Sequence");
                if let Stmt::Sequence {
                    pins: inner_pins, ..
                } = inner
                {
                    assert_eq!(inner_pins.len(), 2, "inner Sequence should have 2 pins");
                }
            }
            other => panic!("expected outer Stmt::Sequence, got {:?}", stmt_kind(&other)),
        }
        assert_eq!(pos, 0x16, "resume past outer pin 1's pop");
    }

    #[test]
    fn non_push_opcode_returns_none() {
        let stream = vec![EX_NOTHING, EX_END_OF_SCRIPT];
        let map = identity_map(&[0, 1]);
        let names = empty_name_table();
        let skeleton = StructureSkeleton::default();
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        assert!(try_decode_sequence(&mut pos, stream.len(), &ctx).is_none());
        assert_eq!(pos, 0, "pos must be unchanged when None returned");
    }

    /// When the chain head has no skeleton entry (e.g. partition was
    /// rejected because the chain bleeds past the buffer), the decoder
    /// must return `None` and leave `*pos` unchanged so the caller falls
    /// through to non-Sequence handling.
    #[test]
    fn missing_skeleton_entry_returns_none() {
        let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
        stream.extend_from_slice(&u32_le(0xFFFF)); // target outside buffer
        stream.push(EX_END_OF_SCRIPT);
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
        let ctx = ctx_with_skeleton(&stream, &names, &map, &skeleton);

        let mut pos = 0;
        assert!(try_decode_sequence(&mut pos, stream.len(), &ctx).is_none());
        assert_eq!(pos, 0, "pos unchanged");
    }

    /// Build a synthetic 2-pin Sequence whose pin[0] starts with a
    /// counter init (`Temp_int_Variable = 0`) and whose pin[1] holds a
    /// `Stmt::Loop` whose cond references the counter. The recognizer
    /// must accept and merge.
    #[test]
    fn for_loop_scaffold_recognizer_merges_two_pins_into_one() {
        use crate::bytecode::expr::{BinaryOp, Expr};

        let counter = "Temp_int_Variable".to_string();
        let pin0: Vec<Stmt> = vec![Stmt::Assignment {
            lhs: Expr::Var(counter.clone()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        }];
        let cond = Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.clone())),
            rhs: Box::new(Expr::Literal("3".into())),
        };
        let pin1: Vec<Stmt> = vec![Stmt::Loop {
            kind: crate::bytecode::stmt::LoopKind::While,
            cond: Some(cond),
            body: Vec::new(),
            completion: None,
            offset: 0,
        }];
        let pins = vec![pin0, pin1];
        assert!(
            super::matches_for_loop_scaffold(&pins),
            "for-loop scaffold signature should match"
        );
    }

    /// A user-authored 2-pin Sequence whose pin[0] is NOT a counter
    /// init (a regular call statement) must NOT be folded to one pin;
    /// the recognizer falls through to the regular 2-pin shape.
    #[test]
    fn for_loop_scaffold_recognizer_rejects_user_two_pin_sequence() {
        use crate::bytecode::expr::Expr;

        let pin0: Vec<Stmt> = vec![Stmt::Call {
            func: Expr::Var("DoStuff".into()),
            args: Vec::new(),
            offset: 0,
        }];
        let pin1: Vec<Stmt> = vec![Stmt::Call {
            func: Expr::Var("DoOther".into()),
            args: Vec::new(),
            offset: 0,
        }];
        let pins = vec![pin0, pin1];
        assert!(
            !super::matches_for_loop_scaffold(&pins),
            "non-scaffold 2-pin Sequence must NOT match"
        );
    }

    /// pin[0] init is a literal-zero counter assignment but pin[1]
    /// has no Loop referencing it — recognizer must reject.
    #[test]
    fn for_loop_scaffold_recognizer_rejects_loop_without_counter_reference() {
        use crate::bytecode::expr::Expr;

        let pin0: Vec<Stmt> = vec![Stmt::Assignment {
            lhs: Expr::Var("Temp_int_Variable".into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        }];
        let pin1: Vec<Stmt> = vec![Stmt::Call {
            func: Expr::Var("Unrelated".into()),
            args: Vec::new(),
            offset: 0,
        }];
        let pins = vec![pin0, pin1];
        assert!(
            !super::matches_for_loop_scaffold(&pins),
            "init without matching loop must NOT match"
        );
    }
}
