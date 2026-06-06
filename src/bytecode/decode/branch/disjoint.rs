//! Disjoint-range (cross-event and displaced) jump decoding.
//!
//! Handles `EX_JUMP` targets that land outside the current inline range:
//! cross-event entries emit `EventCall`, displaced else-arms are inlined
//! and wrapped, and owned ranges are tracked to avoid re-emission.

use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::latch_recognition::{DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX};

use super::super::ctx::{DecodeCtx, OwnerId};
use super::super::expr_decode::decode_expr;
use super::inline_shared::try_cross_event_inline;
use super::layout::{arm_region_owner, scan_for_terminating_jump};
use super::subrange::decode_subrange;
use super::target::{classify_target, read_jump_target, skip_instrumentation, JumpTarget};

/// Decode a standalone `EX_JUMP` opcode at `*pos`. Emits either:
/// - `Stmt::EventCall` if the target is another event entry (exact mem
///   match against the event_entries table OR via the cross-event
///   inline classifier's `Schedule` arm),
/// - inlined target body wrapped in a single-pin `Stmt::Sequence` (or
///   the body's sole statement when only one was produced) when the
///   classifier returns `Inline` (the grip-shape shared-body case),
/// - inlined target body when the target sits in a DIFFERENT owned
///   range of the same event (disjoint-range pull). The target body's
///   claim, registered by the prescan, keeps the linear sweep from
///   re-emitting the same bytes at top level.
/// - `None` (i.e. structural marker, no statement emitted) if the
///   target is a known intra-block convergence point covered by an
///   enclosing construct,
/// - `Stmt::Unknown` otherwise (logged so we can spot unhandled jumps).
pub(crate) fn decode_jump(pos: &mut usize, range_end: usize, ctx: &DecodeCtx) -> Option<Stmt> {
    let jump_offset = *pos;
    let opcode_byte_count = 1;
    *pos += opcode_byte_count; // consume EX_JUMP

    let target_mem = read_jump_target(ctx.bytecode, pos);
    match classify_target(target_mem, jump_offset, range_end, ctx) {
        JumpTarget::EventEntry { event_name, mem } => Some(Stmt::EventCall {
            event_name,
            offset: mem,
        }),
        JumpTarget::OutOfRange => try_cross_event_inline(target_mem, ctx),
        JumpTarget::InRange {
            disk: target_disk, ..
        } => try_decode_disjoint_range_inline(jump_offset, target_disk, ctx),
        JumpTarget::Unresolved => {
            // Structural marker for a yet-unrecognised pattern. Skip
            // silently rather than emitting noise; the surrounding
            // statements still render.
            None
        }
    }
}

/// When an `EX_JUMP` source lies in one owned disk range and its
/// target lies in a DIFFERENT owned range of the same event,
/// inline-decode the target body region as the JUMP source's syntactic
/// continuation.
///
/// The body region must match the canonical `ResetDoOnce` gate-reset
/// shape (validated by `disjoint_body_extent`). Single-stmt results
/// emit as the sole statement; multi-stmt results wrap in a single-pin
/// `Stmt::Sequence` so the caller receives one node.
///
/// Returns `None` for same-range jumps, gap-resident sources/targets,
/// or non-ResetDoOnce target bodies.
fn try_decode_disjoint_range_inline(
    jump_offset: usize,
    target_disk: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let (body_start, body_end) = disjoint_jump_target_extent(jump_offset, target_disk, ctx)?;
    decode_disjoint_body(body_start, body_end, jump_offset, ctx)
}

/// Resolve the disjoint-range body region for a JUMP whose source is at
/// `jump_offset` and whose target lands at `target_disk`. Shared by
/// `try_decode_disjoint_range_inline` (used at JUMP decode time) and
/// the prescan that registers the body's claim before the linear sweep.
///
/// Returns `Some((body_start, body_end))` when the source and target
/// sit in DIFFERENT owned ranges of the same event and the target body
/// terminates within `MAX_DISJOINT_BODY_OPCODES`. Returns `None` for
/// same-range jumps (no relocation needed), gap-resident sources or
/// targets, or unbounded body walks.
pub(crate) fn disjoint_jump_target_extent(
    jump_offset: usize,
    target_disk: usize,
    ctx: &DecodeCtx,
) -> Option<(usize, usize)> {
    let source_range = owned_range_containing(jump_offset, ctx)?;
    let target_range = owned_range_containing(target_disk, ctx)?;
    if source_range == target_range {
        return None;
    }
    // Region-aware bound for the ResetDoOnce body's walk limit. When CFG
    // + region tree are populated, the SESE region exit reachable from
    // the JUMP target dominates the body; otherwise fall back to the
    // owned-range end.
    let body_walk_limit = ctx
        .region_arm_extents_for(jump_offset, &[target_disk])
        .and_then(|extents| extents.first().and_then(|arm| arm.last()).map(|r| r.end))
        .filter(|end| *end > target_disk)
        .unwrap_or(target_range.1);
    let body_end = disjoint_body_extent(target_disk, body_walk_limit, ctx)?;
    if body_end <= target_disk {
        return None;
    }
    // Skip the re-pull when an EARLIER segment of the arm currently being
    // decoded already covered this body directly. A later segment's
    // `EX_JUMP` can target a body the arm's own prior segment emitted,
    // which would duplicate it (a spurious leading `ResetDoOnce(Release)`
    // on the arm). The directly-decoded copy stays; only the disjoint
    // re-pull is dropped. A genuinely-disjoint body, not covered by any
    // earlier arm segment (e.g. an event's displaced reset), still
    // relocates here.
    if ctx.arm_segment_covers(target_disk, body_end) {
        return None;
    }
    Some((target_disk, body_end))
}

/// Decode `[body_start, body_end)` under a `DisjointJumpTarget` owner so
/// the prescan's claim on the same range is bypassed. Wraps multi-stmt
/// results in a single-pin `Stmt::Sequence`; returns the sole stmt when
/// the body produced exactly one. Returns `None` when no statements
/// were produced.
fn decode_disjoint_body(
    body_start: usize,
    body_end: usize,
    jump_disk: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let fallback_owner = OwnerId::DisjointJumpTarget { jump_disk };
    let owner = arm_region_owner(ctx, body_start).unwrap_or(fallback_owner);
    let _guard = ctx.with_decoding_owner(owner);
    let stmts = decode_subrange(body_start, body_end, ctx);
    wrap_inlined_stmts(stmts, body_start)
}

/// Collapse a freshly decoded inline body into a single `Stmt`: empty
/// returns `None`, single-stmt unwraps, multi-stmt wraps in a one-pin
/// `Stmt::Sequence` so the caller can splice one node into the parent.
pub(super) fn wrap_inlined_stmts(stmts: Vec<Stmt>, offset: usize) -> Option<Stmt> {
    match stmts.len() {
        0 => None,
        1 => stmts.into_iter().next(),
        _ => Some(Stmt::Sequence {
            pins: vec![stmts],
            offset,
        }),
    }
}

/// Find the owned range `[start, end)` containing `disk`. Returns
/// `None` when `ctx.owned_ranges` is absent or when `disk` falls in a
/// gap.
fn owned_range_containing(disk: usize, ctx: &DecodeCtx) -> Option<(usize, usize)> {
    let ranges = ctx.owned_ranges?;
    ranges
        .iter()
        .find(|range| disk >= range.start && disk < range.end)
        .map(|range| (range.start, range.end))
}

/// Walk forward from `body_start` looking for the canonical
/// `ResetDoOnce` gate-reset shape:
///
/// ```text
///   EX_LET_BOOL <Var(Temp_bool_IsClosed_Variable_*)>  <EX_FALSE>
///   EX_LET_BOOL <Var(Temp_bool_Has_Been_Initd_Variable_*)>  <EX_TRUE>
///   EX_POP_EXECUTION_FLOW
/// ```
///
/// Returns the disk position one past the trailing
/// `EX_POP_EXECUTION_FLOW` when the shape matches, `None` otherwise.
///
/// The ResetDoOnce-shape gate keeps the disjoint-range pull narrow:
/// arbitrary cross-range JUMPs (loop back-edges, IF/ELSE convergence
/// jumps, delay-resume jumps) keep their existing decode path. Only
/// disjoint blocks that are actually `ResetDoOnce(...)` macro
/// expansions get pulled into the JUMP source's syntactic
/// continuation.
fn disjoint_body_extent(body_start: usize, range_end: usize, ctx: &DecodeCtx) -> Option<usize> {
    let limit = range_end.min(ctx.bytecode.len());
    // Walk past any leading instrumentation tracepoints so the
    // signature check sees the first semantic opcode.
    let mut cursor = skip_instrumentation(body_start, limit, ctx);

    // First gate-reset assignment: Var(Temp_bool_IsClosed_Variable_*) = false.
    let first_end = match_gate_assignment(cursor, limit, ctx, false, DOONCE_GATE_PREFIX)?;
    cursor = skip_instrumentation(first_end, limit, ctx);

    // Second init-set assignment: Var(Temp_bool_Has_Been_Initd_Variable_*) = true.
    let second_end = match_gate_assignment(cursor, limit, ctx, true, DOONCE_INIT_PREFIX)?;
    cursor = skip_instrumentation(second_end, limit, ctx);

    // Trailing EX_POP_EXECUTION_FLOW.
    if cursor >= limit {
        return None;
    }
    if ctx.bytecode.get(cursor) != Some(&EX_POP_EXECUTION_FLOW) {
        return None;
    }
    let pop_length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
    if pop_length == 0 {
        return None;
    }
    Some(cursor + pop_length)
}

/// True when the opcode at `cursor` is `EX_LET_BOOL <var-prefix> <bool>`,
/// where `<bool>` is `EX_TRUE` (when `expect_true` is true) or
/// `EX_FALSE` (when false), and the lhs variable name starts with
/// `expected_prefix`. Returns the disk position one past the assignment
/// when matched, `None` otherwise.
///
/// Used by `disjoint_body_extent` to validate the two-assignment
/// gate-reset shape inside a disjoint-range body before claiming and
/// inlining it.
fn match_gate_assignment(
    cursor: usize,
    limit: usize,
    ctx: &DecodeCtx,
    expect_true: bool,
    expected_prefix: &str,
) -> Option<usize> {
    if cursor >= limit {
        return None;
    }
    if ctx.bytecode.get(cursor) != Some(&EX_LET_BOOL) {
        return None;
    }
    let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
    if length == 0 {
        return None;
    }
    let end = cursor + length;
    if end > limit || end > ctx.bytecode.len() {
        return None;
    }
    // The trailing byte of an EX_LET_BOOL with a literal bool rhs is
    // EX_TRUE / EX_FALSE; the lhs Var bytes carry the variable name in
    // the middle. Validate both ends.
    let expected_bool = if expect_true { EX_TRUE } else { EX_FALSE };
    if ctx.bytecode.get(end - 1) != Some(&expected_bool) {
        return None;
    }
    // Decode the lhs expression to read its Var name. The decoder
    // walks the rhs too and updates pos, but we only need the lhs's
    // first byte parse to extract the Var's FName.
    let mut pos = cursor + 1;
    let lhs = decode_expr(&mut pos, ctx);
    let var_name = match &lhs {
        Expr::Var(name) => name.as_str(),
        _ => return None,
    };
    if !var_name.starts_with(expected_prefix) {
        return None;
    }
    Some(end)
}

/// Probe-only variant: True when the JIN at `jin_disk` has its else
/// target in a different owned range than the JIN itself, AND the JIN's
/// inline THEN body has no terminating `EX_JUMP` that would close the
/// classic if/else shape. This is the disjoint-else-arm shape where the
/// linear sweep otherwise emits the else body at top level.
///
/// Returns the resolved else body region `(body_start, body_end)` when
/// the shape matches, or `None` to let other recognisers handle.
pub(crate) fn disjoint_else_arm_for_jin(
    jin_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    else_target_disk: usize,
    ctx: &DecodeCtx,
) -> Option<(usize, usize)> {
    let source_range = owned_range_containing(jin_offset, ctx)?;
    let target_range = owned_range_containing(else_target_disk, ctx)?;
    if source_range == target_range {
        return None;
    }
    // Skip when the THEN body has a clean terminating `EX_JUMP` that
    // would let the classic if/else path resolve naturally; only fire
    // when the existing recogniser can't.
    let then_terminator_end = if else_target_disk > range_end {
        range_end
    } else {
        else_target_disk
    };
    if scan_for_terminating_jump(ctx, body_start_disk, then_terminator_end).is_some() {
        return None;
    }
    // Region-aware bound for the ResetDoOnce body's walk limit. When CFG
    // + region tree are populated, the SESE region exit dominating the
    // else arm caps the shape-check's forward scan tightly; without it
    // we fall back to the owned-range end.
    let body_walk_limit = ctx
        .region_arm_extents_for(jin_offset, &[else_target_disk])
        .and_then(|extents| extents.first().and_then(|arm| arm.last()).map(|r| r.end))
        .filter(|end| *end > else_target_disk)
        .unwrap_or(target_range.1);
    let body_end = disjoint_body_extent(else_target_disk, body_walk_limit, ctx)?;
    if body_end <= else_target_disk {
        return None;
    }
    Some((else_target_disk, body_end))
}

/// Entry-anchor discriminator for the generalized cross-event inline.
///
/// A genuine shared-body trampoline lands at the convergence body's ENTRY:
/// the cross-event jump enters the shared region at its first statement,
/// after at most a gate-set / push / jump scaffold prologue. A spurious
/// "convergence" (two sibling events reaching the same downstream node)
/// instead lands MID-BODY, inside a preceding node's content that belongs
/// to the owning event rather than the shared region.
///
/// The reject case is narrow, three conditions must all hold:
/// 1. the target is EMBEDDED in another event's larger body
///    (`is_embedded_shared_target`, the event owning `target_disk` reaches
///    a different first DoOnce than `target_node`),
/// 2. the target carries NO byte-map footprint cluster, so the inline
///    decodes the raw `[entry..owning_end)` overshoot rather than a tightly
///    bounded shared body, and
/// 3. a user-visible statement (Call / EventCall / Branch / Loop / Switch /
///    Return / Latch) lands in the prefix `[entry..target_disk)`, proving
///    the landing is past the body's first statement.
///
/// Tight-body ELSE inlines pass condition 1 with `false`
/// (the owning event reaches the same first DoOnce as
/// the target), and footprint-backed nodes re-bind to their cluster in
/// [`decode_inlined_shared_body`] regardless of landing, so both stay
/// entry-anchored. The byte gap is NOT the signal: a spurious convergence
/// can land 0x2d into the body while legitimate shared-body inlines land
/// 0x89 in. Only the embedded + footprint-less + preceding-statement
/// combination separates a foreign-content landing from a shared-body
/// prologue.
pub(super) fn landing_is_entry_anchored(
    target_node: usize,
    target_disk: usize,
    ctx: &DecodeCtx,
) -> bool {
    use crate::bytecode::structure::build_skeleton;
    let Some(cei) = ctx.cross_event_inline else {
        return true;
    };
    let Some(mem_to_disk) = ctx.mem_to_disk else {
        return true;
    };
    // Resolve the K2Node's logical entry the same way the inline decode
    // does: the push-chain head wrapping `target_disk`, else the owning
    // event's contiguous range start.
    let owning_full = cei.event_owned_ranges.iter().find_map(|(_, ranges)| {
        ranges
            .iter()
            .any(|range| target_disk >= range.start && target_disk < range.end)
            .then(|| {
                let lo = ranges.iter().map(|range| range.start).min().unwrap_or(0);
                let hi = ranges.iter().map(|range| range.end).max().unwrap_or(0);
                lo..hi
            })
    });
    let Some(owning_full) = owning_full else {
        // No owning event: the classifier should already have dropped
        // this; treat as entry-anchored so we don't double-reject.
        return true;
    };
    let owning_skeleton = build_skeleton(
        ctx.bytecode,
        ctx.ue5,
        ctx.name_table,
        mem_to_disk,
        owning_full,
        &[],
        ctx.graph,
    );
    let entry = super::super::cross_event_inline::k2node_bytecode_range(
        target_node,
        target_disk,
        &owning_skeleton,
        cei.event_owned_ranges,
    )
    .map(|range| range.start)
    .unwrap_or(target_disk);
    // Condition 1: only embedded targets (the overshoot-decode shape) can
    // pull in foreign content; tight-body targets cannot.
    if !super::super::cross_event_inline::is_embedded_shared_target(target_node, target_disk, cei) {
        return true;
    }
    // Condition 2: a footprint cluster re-binds the inline to the shared
    // body in `decode_inlined_shared_body`, so the landing offset is moot.
    let footprint =
        super::super::cross_event_inline::embedded_inline_range(target_node, target_disk, cei);
    if footprint.is_some() {
        return true;
    }
    // Condition 3: a user-visible statement before the landing = mid-body.
    !prefix_has_user_stmt(entry, target_disk, ctx)
}

/// Decode the prefix region `[start..target_disk)` under a region-scoped
/// sub-context and report whether it produces any user-visible statement
/// (Call / EventCall / Branch / Loop / Switch / Return / Latch). Pure
/// scaffold (variable gate-sets, pushes, jumps) and an empty prefix report
/// `false`. Used by [`landing_is_entry_anchored`].
fn prefix_has_user_stmt(start: usize, target_disk: usize, ctx: &DecodeCtx) -> bool {
    use super::super::{build_event_cfg_and_region_tree, decode_region_body};
    use crate::bytecode::structure::build_skeleton;
    if start >= target_disk {
        return false;
    }
    let (Some(mem_to_disk), Some(graph)) = (ctx.mem_to_disk, ctx.graph) else {
        return false;
    };
    let prefix_range = start..target_disk;
    let prefix_skeleton = build_skeleton(
        ctx.bytecode,
        ctx.ue5,
        ctx.name_table,
        mem_to_disk,
        prefix_range.clone(),
        &[],
        Some(graph),
    );
    let prefix_slice = std::slice::from_ref(&prefix_range);
    // Mirror `decode_owner_event_body`: build a sub-CFG + SESE region tree
    // for the contiguous prefix range and decode via the region-tree path.
    // The boolean predicate below (any user-visible statement?) is invariant
    // regardless of how the prefix is decoded, so the cross-event landing
    // result is unchanged.
    let (prefix_cfg, prefix_region_tree, prefix_region_byte_ranges) =
        build_event_cfg_and_region_tree(
            start,
            prefix_slice,
            graph,
            ctx.bytecode,
            ctx.ue5,
            ctx.name_table,
            mem_to_disk,
        );
    let prefix_claimed: std::cell::RefCell<
        std::collections::BTreeMap<usize, super::super::ctx::Claim>,
    > = std::cell::RefCell::new(std::collections::BTreeMap::new());
    let prefix_ctx = DecodeCtx {
        mem_to_disk: ctx.mem_to_disk,
        event_entries: ctx.event_entries,
        function_signatures: ctx.function_signatures,
        owned_ranges: Some(prefix_slice),
        skeleton: Some(&prefix_skeleton),
        claimed: Some(&prefix_claimed),
        graph: ctx.graph,
        cfg: Some(&prefix_cfg),
        region_tree: Some(&prefix_region_tree),
        region_byte_ranges: Some(&prefix_region_byte_ranges),
        cross_event_inline: ctx.cross_event_inline,
        k2node_byte_map: ctx.k2node_byte_map,
        ..DecodeCtx::new(
            ctx.bytecode,
            ctx.name_table,
            ctx._imports,
            ctx._export_names,
            ctx.ue5,
        )
    };
    let stmts = decode_region_body(&prefix_region_tree, &prefix_cfg, &prefix_ctx);
    stmts.iter().any(|stmt| {
        matches!(
            stmt,
            Stmt::Call { .. }
                | Stmt::EventCall { .. }
                | Stmt::Branch { .. }
                | Stmt::Loop { .. }
                | Stmt::Switch { .. }
                | Stmt::Return { .. }
                | Stmt::Latch { .. }
        )
    })
}
