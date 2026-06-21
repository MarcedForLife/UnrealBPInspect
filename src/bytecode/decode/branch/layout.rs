//! Branch-layout decision and body decoding.
//!
//! Decides whether a branch decodes as a tail-JIN arm chain, a backward
//! IsValid macro, or a forward if/else, then decodes the then/else bodies
//! into statements.

use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;
use crate::bytecode::stmt::Stmt;

use super::super::ctx::{absorb_overlapping_chains, mark_claimed, DecodeCtx, OwnerId};
use super::super::expr_decode::decode_expr;
use super::disjoint::disjoint_else_arm_for_jin;
use super::subrange::decode_subrange;
use super::tail_jin::tail_jin_arm_ranges;
use super::target::{
    classify_target, event_scan_end, owned_segment_containing, peek_jump_after_instrumentation,
    read_jump_target, JumpTarget, JUMP_TARGET_BYTES,
};

/// End offset of the last segment of arm `index` in a region's arm extents,
/// or `None` when the arm is absent or empty. `extents` come from
/// [`DecodeCtx::region_arm_extents_for`].
pub(super) fn arm_last_end(extents: &[Vec<std::ops::Range<usize>>], index: usize) -> Option<usize> {
    extents
        .get(index)
        .and_then(|arm| arm.last())
        .map(|range| range.end)
}

/// Scan the else arm `[else_start, else_end)` of a multi-break loop-body branch
/// for its own terminating loop break-jump: an `EX_JUMP` whose resolved
/// target is either at/past the loop tail (forward break to the epilogue)
/// or a backward jump landing within the displaced body
/// `[displaced_start, tail]` (a jump back to a sibling break-guard). When
/// found, returns the jump's disk offset so the else arm can be bounded
/// there and a trailing `Stmt::Break` appended in its place. Returns
/// `None` (else arm decodes unchanged) when no loop-break-guard is active
/// or the arm has no such trailing jump.
///
/// Scoped to the else arm of the recogniser-confirmed multi-break branch,
/// so it cannot fire on unrelated jumps inside other loop bodies.
fn c2_else_break_jump(else_start: usize, else_end: usize, ctx: &DecodeCtx) -> Option<usize> {
    let guard = ctx.loop_break_guard.get()?;
    let scan_end = else_end.min(ctx.bytecode.len());
    let mut cursor = else_start;
    let mut found: Option<usize> = None;
    while cursor < scan_end {
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_JUMP && cursor + 1 + 4 <= scan_end {
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let target_disk = ctx
                .mem_to_disk
                .and_then(|map| map.get(&target_mem).copied())
                .unwrap_or(target_mem);
            let forward_break = target_disk >= guard.tail;
            let backward_break = target_disk < cursor
                && target_disk >= guard.displaced_start
                && target_disk <= guard.tail;
            if forward_break || backward_break {
                found = Some(cursor);
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }
    found
}

/// True when `[start, end)` contains an `EX_POP_FLOW_IF_NOT` at any
/// opcode boundary. The over-run region of a multi-break loop body holds
/// the sibling loop-break guard (a `pop_flow_if_not`), distinguishing it
/// from an unrelated large-else branch whose over-run is plain code.
fn range_contains_pop_flow_if_not(ctx: &DecodeCtx, start: usize, end: usize) -> bool {
    let scan_end = end.min(ctx.bytecode.len());
    let mut cursor = start;
    while cursor < scan_end {
        if ctx.bytecode[cursor] == EX_POP_FLOW_IF_NOT {
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

/// Build a region-bounded branch layout for the multi-break loop-body
/// shape. Fires only when the SESE region tree bounds the then-arm
/// strictly before the scan-picked terminating jump (`scan_jump_pos`),
/// which means the scan over-ran the convergence and would pull a sibling
/// loop-break guard inside the then-body while dropping the else arm.
///
/// On a match, bounds the then and else arms by the region extents and
/// resumes at the then-arm's region end (the convergence), so the guard
/// emits as a sibling after the branch. Returns `None` (caller keeps the
/// scan-bounded layout) when the gate is off, the region tree is absent,
/// the extents don't cover both arms, or no over-run is detected.
fn c2_region_bounded_layout(
    ctx: &DecodeCtx,
    construct_offset: usize,
    body_start_disk: usize,
    else_disk: usize,
    scan_jump_pos: Option<usize>,
) -> Option<BranchLayout> {
    let scan_jump_pos = scan_jump_pos?;
    let extents = ctx.region_arm_extents_for(construct_offset, &[body_start_disk, else_disk])?;
    let then_end = arm_last_end(&extents, 0)?;
    let else_arm = extents.get(1)?;
    let else_start = else_arm.first().map(|r| r.start)?;
    let else_end = else_arm.last().map(|r| r.end)?;
    // Over-run discriminator: the region's then-arm ends before the scan's
    // terminating jump. A single-arm branch whose scan jump sits inside the
    // region then-extent fails this and keeps the existing layout.
    if then_end >= scan_jump_pos {
        return None;
    }
    // Sanity: the bounded arms must be forward and non-empty, and resume
    // (the convergence) must sit after the then-body so the region walk's
    // outer pos advances.
    if then_end <= body_start_disk || else_end <= else_start || else_start < then_end {
        return None;
    }
    // Multi-break discriminators: this fires only inside a loop's displaced
    // body decode (`loop_break_guard` active) AND the over-run region
    // `[then_end, scan_jump_pos)` holds the sibling loop-break guard's
    // `EX_POP_FLOW_IF_NOT`. An unrelated large-else branch whose region
    // then-arm happens to be short fails both checks (its over-run is plain
    // code, and it is not inside a loop displaced body).
    let multi_break_shape = ctx.loop_break_guard.get().is_some()
        && range_contains_pop_flow_if_not(ctx, then_end, scan_jump_pos);
    if !multi_break_shape {
        return None;
    }
    // The else arm carries its own backward break-jump (`jump 0x1fa` back
    // to the sibling break-guard). Bound the arm at that jump and append a
    // trailing `Stmt::Break` in its place.
    let else_break = c2_else_break_jump(else_start, else_end, ctx);
    let else_range_end = else_break.unwrap_or(else_end);
    Some(BranchLayout {
        then_range: (body_start_disk, then_end),
        else_range: (else_start, else_range_end),
        resume_disk: then_end,
        else_trailing_break: else_break,
        ..Default::default()
    })
}

/// Outcome of decoding a single conditional construct.
pub(crate) struct BranchDecode {
    pub stmt: Stmt,
}

/// Decode an `EX_JUMP_IF_NOT` construct starting at `*pos` and produce
/// a `Stmt::Branch`.
///
/// On entry, `*pos` points at the `EX_JUMP_IF_NOT` opcode byte. On exit
/// it has advanced past the entire construct. `range_end` is the
/// inclusive upper bound for any nested decoding.
pub(crate) fn decode_branch(pos: &mut usize, range_end: usize, ctx: &DecodeCtx) -> BranchDecode {
    let construct_offset = *pos;
    let opcode_byte_count = 1;
    *pos += opcode_byte_count; // consume EX_JUMP_IF_NOT

    let target_mem = read_jump_target(ctx.bytecode, pos);
    let cond = decode_expr(pos, ctx);

    let body_start_disk = *pos;
    let target_class = classify_target(target_mem, body_start_disk, range_end, ctx);

    let (then_body, else_body, resume_disk) = match decide_branch_layout(
        target_class,
        construct_offset,
        body_start_disk,
        range_end,
        ctx,
    ) {
        Some(layout) => decode_branch_bodies(layout, ctx),
        None => {
            // Fallback: target unresolved or out of range. Treat the
            // remainder of the range as the then-body, leave else
            // empty, and resume at range_end. The then-body is decoded
            // up to `range_end`, not the cross-range scan end, because
            // the region walk will continue with the next owned range
            // independently.
            let then_body = decode_subrange(body_start_disk, range_end, ctx);
            (then_body, Vec::new(), range_end)
        }
    };

    *pos = resume_disk;

    BranchDecode {
        stmt: Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: construct_offset,
        },
    }
}

/// Per-shape layout describing the slice ranges to decode for then and
/// else bodies plus the post-construct resume point. Computed once,
/// then handed to `decode_branch_bodies` for the actual recursion.
///
/// `Default` lets each construction site spell out only the fields that
/// diverge from the empty/`None` baseline and fill the rest with
/// `..Default::default()`.
#[derive(Default)]
struct BranchLayout {
    /// Range to decode for the then-body. May be empty (start == end)
    /// when the conditional flows directly into the else-target.
    then_range: (usize, usize),
    /// Range to decode for the else-body. Empty when there's no else.
    else_range: (usize, usize),
    /// If `Some`, the then-body should be replaced by a single
    /// `Stmt::EventCall` to this event rather than decoded.
    then_event_call: Option<(String, usize)>,
    /// If `Some`, same as `then_event_call` but for the else side.
    else_event_call: Option<(String, usize)>,
    /// Disk position at which decoding resumes after the construct.
    resume_disk: usize,
    /// When `Some`, body decode runs with this owner installed so the
    /// claim lookup bypasses claims that this construct registered (or
    /// that overlapping claim-set propagation gave to it). `None` for
    /// classic if/else branches that don't claim bytes.
    body_owner: Option<OwnerId>,
    /// When `Some(offset)`, the else arm's bytes stop at this disk offset
    /// (the position of its terminating loop break-jump) and a trailing
    /// `Stmt::Break { offset }` is appended. Set only by the multi-break
    /// loop-body region-bounded layout; `None` everywhere else.
    else_trailing_break: Option<usize>,
}

/// Decide the body layout for a branch construct.
///
/// Encodes the supported shapes:
/// - Classic if/else: inline then-body whose terminator's
///   `EX_JUMP` jumps past the else target.
/// - Displaced-else: structurally identical to the classic if/else; the
///   terminating jump's target is the convergence offset.
/// - IsValid macro: immediately-following `EX_JUMP` makes
///   both branches displaced.
/// - IsValid macro, backward Then-body: the JIN's target lies before
///   the JIN in disk space and the chain at target ends in
///   `EX_POP_EXECUTION_FLOW`. The else-body is bounded by that POP,
///   the then-body covers the inline structural markers.
/// - Cross-event jump: the conditional's target is itself
///   an event entry. Modelled as a branch where the else-body is a
///   single `Stmt::EventCall`.
fn decide_branch_layout(
    target_class: JumpTarget,
    construct_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<BranchLayout> {
    // Tail-JIN displaced-arm shape (InpAxisEvt grip pattern). Runs
    // BEFORE the backward IsValid coercion so its claim takes precedence;
    // declines when the signature doesn't match so IsValid / DoOnce /
    // sentinel / inline can still fire on their shapes.
    if let Some(layout) = try_tail_jin_arm_layout(
        &target_class,
        construct_offset,
        body_start_disk,
        range_end,
        ctx,
    ) {
        return Some(layout);
    }

    // Distinguish two backward-target shapes for `EX_JUMP_IF_NOT`
    // (target's disk address < body_start_disk):
    //
    // - Loop back-edge: target lies in the loop body's entry / exit
    //   region; the chain at target reaches a JIN / PUSH_EXECUTION_FLOW
    //   / POP_FLOW_IF_NOT terminator before any POP_EXECUTION_FLOW, and
    //   the back-edge JUMP eventually returns to body_start_disk.
    //   Falling into the classic if/else path here would set
    //   `resume_disk = else_disk < construct_offset` and the region walk's
    //   outer pos would loop indefinitely. Coerce these targets to
    //   OutOfRange so the linear fallback consumes the rest of the range.
    //
    // - IsValid macro: target is a displaced Then-body whose chain ends
    //   with EX_POP_EXECUTION_FLOW first, returning control to the
    //   flow-stack frame pushed by the caller's Sequence. The Then-body
    //   bytes are physically backward from the JIN but logically a
    //   self-contained block bounded by its own POP. Allow InRange and
    //   record the body's exclusive end so we can build a bounded
    //   `else_range` and avoid wrapping the JIN itself.
    let mut backward_isvalid_else_end: Option<usize> = None;
    let target_class = match target_class {
        JumpTarget::InRange { disk, mem } if disk < body_start_disk => {
            match isvalid_else_body_end(disk, construct_offset, ctx) {
                Some(else_end) => {
                    backward_isvalid_else_end = Some(else_end);
                    JumpTarget::InRange { disk, mem }
                }
                None => JumpTarget::OutOfRange,
            }
        }
        other => other,
    };

    // Non-debug compilers prepend WIRE_TRACEPOINT / TRACEPOINT bytes
    // before the displaced-arm `EX_JUMP`. Skip past those so the IsValid
    // classifier sees the jump regardless of whether the asset was
    // compiled with instrumentation. Restricted to forward targets
    // because a backward target indicates a `if (X) goto <prior>` shape
    // (loop break / sentinel back-edge), not IsValid; routing a backward
    // `then_disk` into `decode_subrange` would loop the linear sweep.
    let immediate_jump = peek_jump_after_instrumentation(body_start_disk, range_end, ctx).filter(
        |(target_mem, _, _)| match classify_target(*target_mem, body_start_disk, range_end, ctx) {
            JumpTarget::InRange { disk, .. } => disk > body_start_disk,
            JumpTarget::OutOfRange | JumpTarget::Unresolved | JumpTarget::EventEntry { .. } => true,
        },
    );

    // Backward-target IsValid macro: the JIN's target is the displaced
    // Is-Not-Valid pin body, the inline body falls through to whatever
    // the parent Sequence's flow-stack frame holds. The macro emits
    // that body at lower disk offsets than the JIN itself, which means
    // the region walk's disk-order sweep would walk those bytes long before
    // it reaches the JIN at `construct_offset`. We mark them claimed
    // so the sweep skips past them, then build the layout directly so
    // we don't fall through to the Classic if/else arm which would
    // recurse on the same JIN. The displaced range is the
    // Is-Not-Valid pin payload (verified against editor graph), so it
    // belongs in `else_range`. Reads naturally as
    // `if (IsValid(x)) { /* fall-through */ } else { /* invalid */ }`.
    if let Some(layout) = try_backward_isvalid_layout(
        &target_class,
        backward_isvalid_else_end,
        construct_offset,
        body_start_disk,
        range_end,
        ctx,
    ) {
        return Some(layout);
    }

    decide_forward_branch_layout(
        target_class,
        immediate_jump,
        construct_offset,
        body_start_disk,
        range_end,
        ctx,
    )
}

/// Tail-JIN displaced-arm shape (the InpAxisEvt grip pattern): a backward
/// `EX_JUMP_IF_NOT` whose then/else arms are displaced blocks recovered by
/// [`tail_jin_arm_ranges`]. Returns `None` when the signature doesn't match
/// so IsValid / DoOnce / sentinel / inline shapes can still fire.
fn try_tail_jin_arm_layout(
    target_class: &JumpTarget,
    construct_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<BranchLayout> {
    if let JumpTarget::InRange { disk, .. } = *target_class {
        if disk < body_start_disk {
            if let Some(arms) = tail_jin_arm_ranges(construct_offset, range_end, ctx) {
                let owner = OwnerId::TailJinArm {
                    jin_disk: construct_offset,
                };
                let (then_start, then_end) = arms.then_range;
                let (else_start, else_end) = arms.else_range;
                mark_claimed(ctx, then_start, then_end, owner);
                mark_claimed(ctx, else_start, else_end, owner);
                return Some(BranchLayout {
                    then_range: arms.then_range,
                    else_range: arms.else_range,
                    resume_disk: range_end,
                    body_owner: Some(owner),
                    ..Default::default()
                });
            }
        }
    }
    None
}

/// Backward-target IsValid macro: the JIN's target is the displaced
/// Is-Not-Valid pin body (lower disk offsets than the JIN), the inline
/// body falls through to the parent Sequence's flow-stack frame. Claims
/// the displaced range, absorbs overlapping chains, and builds the
/// `if (IsValid(x)) { /* fall-through */ } else { /* invalid */ }` layout.
/// Returns `None` unless `target_class` is `InRange` with a resolved
/// `backward_isvalid_else_end`.
fn try_backward_isvalid_layout(
    target_class: &JumpTarget,
    backward_isvalid_else_end: Option<usize>,
    construct_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<BranchLayout> {
    let (
        JumpTarget::InRange {
            disk: cond_target_disk,
            ..
        },
        Some(else_end),
    ) = (target_class, backward_isvalid_else_end)
    else {
        return None;
    };
    let else_disk = *cond_target_disk;
    let owner = OwnerId::IsValid {
        jin_disk: construct_offset,
    };
    mark_claimed(ctx, else_disk, else_end, owner);
    // Add the IsValid owner to any SequenceChain claim already
    // registered inside the absorbed else-body so the IsValid
    // Branch's else-body decode (which sets `decoding_owner` to
    // this IsValid) bypasses those inner claims and emits the
    // nested chain inside its else_body.
    absorb_overlapping_chains(ctx, else_disk, else_end, owner);

    // Non-debug compilers emit the IsValid macro's valid-pin body as
    // a displaced block reached via an unconditional EX_JUMP placed
    // immediately after the JIN (modulo instrumentation tracepoints).
    // When that JUMP is present and its target classifies InRange,
    // the body extent is the owned segment that contains the target,
    // because the partition already bounded sibling pins via
    // stack-tracking BFS. Marking the segment claimed prevents the
    // outer linear sweep of the enclosing scope from re-emitting it
    // as a top-level sibling.
    if let Some((then_jump_target_mem, _, _)) =
        peek_jump_after_instrumentation(body_start_disk, range_end, ctx)
    {
        let then_target_class =
            classify_target(then_jump_target_mem, body_start_disk, range_end, ctx);
        if let JumpTarget::InRange {
            disk: then_target_disk,
            ..
        } = then_target_class
        {
            if let Some((seg_start, seg_end)) = owned_segment_containing(then_target_disk, ctx) {
                mark_claimed(ctx, seg_start, seg_end, owner);
                absorb_overlapping_chains(ctx, seg_start, seg_end, owner);
                return Some(BranchLayout {
                    then_range: (then_target_disk, seg_end),
                    else_range: (else_disk, else_end),
                    resume_disk: range_end,
                    body_owner: Some(owner),
                    ..Default::default()
                });
            }
        }
    }

    Some(BranchLayout {
        // Inline body decodes from body_start through range_end:
        // it's typically a few WIRE / TRACE markers and the
        // structural EX_POP that returns to the caller's frame.
        then_range: (body_start_disk, range_end),
        else_range: (else_disk, else_end),
        resume_disk: range_end,
        body_owner: Some(owner),
        ..Default::default()
    })
}

/// Decide the layout for forward-target branch shapes: IsValid macro
/// (JIN immediately followed by an unconditional jump, both arms
/// displaced), cross-event jump (conditional target is an event entry),
/// and classic if/else (inline then-body, JIN target is the else entry).
/// Returns `None` for out-of-range/unresolved targets so the caller falls
/// back to linear decode.
fn decide_forward_branch_layout(
    target_class: JumpTarget,
    immediate_jump: Option<(usize, usize, usize)>,
    construct_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<BranchLayout> {
    match (target_class, immediate_jump) {
        // IsValid macro shape: EX_JUMP_IF_NOT immediately followed by
        // EX_JUMP. Both bodies are displaced.
        (
            JumpTarget::InRange {
                disk: cond_target_disk,
                mem: _cond_target_mem,
            },
            Some((then_target_mem, _jump_pos, jump_end_disk)),
        ) => {
            let then_class = classify_target(then_target_mem, body_start_disk, range_end, ctx);
            // Mark the position after the unconditional jump as where
            // the else-body lives — i.e. the EX_JUMP_IF_NOT's target.
            // The convergence offset is whichever of the two displaced
            // bodies' terminating jumps comes later.
            let then_resolved = match then_class {
                JumpTarget::InRange { disk, .. } => Some(disk),
                _ => None,
            };
            let then_disk = then_resolved.unwrap_or(jump_end_disk);
            let else_disk = cond_target_disk;
            // Convergence may live in a later owned range when the event
            // is partitioned across disjoint disk ranges; widen the scan
            // bound past the current range when that's the case. The
            // floor `body_start_disk` rejects backward targets a widened
            // scan can pick up (back-edges that belong to other
            // constructs); without this guard, resume_disk could land
            // before the branch and the region walk's outer pos would
            // bounce backward forever.
            let scan_end = event_scan_end(range_end, ctx);
            let forward_floor = body_start_disk;
            let convergence = find_convergence_for_displaced(
                ctx,
                construct_offset,
                then_disk,
                else_disk,
                scan_end,
                forward_floor,
            );
            Some(BranchLayout {
                then_range: (then_disk, convergence),
                else_range: (else_disk, convergence),
                resume_disk: convergence,
                ..Default::default()
            })
        }

        // Cross-event jump as the conditional target: the else-side is
        // the EventCall (since EX_JUMP_IF_NOT means "jump to else when
        // cond is false").
        (JumpTarget::EventEntry { event_name, mem }, _) => {
            let then_end = range_end;
            Some(BranchLayout {
                then_range: (body_start_disk, then_end),
                else_event_call: Some((event_name, mem)),
                resume_disk: then_end,
                ..Default::default()
            })
        }

        // Classic if/else (and displaced-else as a structural variant):
        // inline then-body, EX_JUMP_IF_NOT target is the else entry.
        (
            JumpTarget::InRange {
                disk: else_disk,
                mem: _else_mem,
            },
            None,
        ) => classic_if_else_layout(ctx, construct_offset, body_start_disk, range_end, else_disk),

        // Out-of-range or unresolved target: caller falls back to
        // decoding the remainder linearly.
        _ => None,
    }
}

/// Decide the layout for the classic if/else shape (and the displaced-else
/// structural variant): an inline then-body whose `EX_JUMP_IF_NOT` target
/// `else_disk` is the else entry.
fn classic_if_else_layout(
    ctx: &DecodeCtx,
    construct_offset: usize,
    body_start_disk: usize,
    range_end: usize,
    else_disk: usize,
) -> Option<BranchLayout> {
    // When the else target lives in a later owned range, the
    // inline then-body still ends inside the current range; only
    // expand `then_terminator_end` to look up to the current
    // range's end in that case rather than into the gap.
    let then_terminator_end = if else_disk > range_end {
        range_end
    } else {
        else_disk
    };
    let then_terminator = scan_for_terminating_jump(ctx, body_start_disk, then_terminator_end);

    // Multi-break loop-body shape: the then-arm contains a
    // loop-break guard whose body the SESE region tree bounds
    // strictly before the terminating jump the scan picks up. The
    // scan-bounded then-arm over-runs that convergence and pulls the
    // guard (a sibling) inside the then-body, dropping the else arm.
    // When the region tree's then-extent ends before the scan jump,
    // bound the arms by the region extents and resume at the
    // convergence so the guard emits as a sibling.
    if let Some(layout) = c2_region_bounded_layout(
        ctx,
        construct_offset,
        body_start_disk,
        else_disk,
        then_terminator.as_ref().map(|jump| jump.jump_pos),
    ) {
        return Some(layout);
    }

    match then_terminator {
        Some(TerminatingJump {
            jump_pos,
            target_mem,
            after_jump_disk: _,
        }) => {
            let then_range_end = jump_pos;
            // Cross-range post-else may live in a later owned range,
            // so widen the classification scan; but a target that
            // resolves backward (before the else-body) means the
            // terminator's jump is NOT the construct's exit, it's
            // a back-edge or unrelated jump picked up by the wider
            // window. Fall back to `range_end.max(else_disk)` in
            // that case so resume_disk stays forward-monotonic and
            // `else_range` never inverts. Without the `.max`, a
            // cross-range layout with `else_disk > range_end` and a
            // backward terminator target would set
            // `post_else = range_end < else_disk` and feed an
            // inverted (start > end) range into `decode_subrange`,
            // which silently drops the else body.
            let post_else_scan = event_scan_end(range_end, ctx);
            let fallback_post_else = range_end.max(else_disk);
            let post_else = match classify_target(target_mem, body_start_disk, post_else_scan, ctx)
            {
                JumpTarget::InRange { disk, .. } if disk > else_disk => disk,
                JumpTarget::InRange { .. } => fallback_post_else,
                JumpTarget::OutOfRange | JumpTarget::Unresolved => fallback_post_else,
                JumpTarget::EventEntry { .. } => fallback_post_else,
            };
            Some(BranchLayout {
                then_range: (body_start_disk, then_range_end),
                else_range: (else_disk, post_else),
                resume_disk: post_else,
                ..Default::default()
            })
        }
        None => {
            // When else_disk lives in a different owned range
            // than the JIN itself AND the body at else_disk
            // matches the canonical ResetDoOnce gate-reset
            // shape, pull that body in as the construct's
            // else_body. The narrow body-shape check keeps the
            // pull from firing on regular forward jumps to
            // convergence points.
            if let Some((else_start, else_end)) = disjoint_else_arm_for_jin(
                construct_offset,
                body_start_disk,
                range_end,
                else_disk,
                ctx,
            ) {
                let owner = OwnerId::DisjointJumpTarget {
                    jump_disk: construct_offset,
                };
                // The prescan registered the same claim; this
                // re-mark is a no-op for matching tuples and
                // protects against decode contexts where the
                // prescan didn't run.
                mark_claimed(ctx, else_start, else_end, owner);
                let then_end = body_start_disk.max(else_disk).min(range_end);
                return Some(BranchLayout {
                    then_range: (body_start_disk, then_end),
                    else_range: (else_start, else_end),
                    resume_disk: then_end,
                    body_owner: Some(owner),
                    ..Default::default()
                });
            }
            // No terminating EX_JUMP -> then-body falls through
            // naturally. Empty else.
            Some(BranchLayout {
                then_range: (body_start_disk, else_disk),
                resume_disk: else_disk,
                ..Default::default()
            })
        }
    }
}

/// Decode the then/else bodies for a resolved branch layout.
///
/// When `layout.body_owner` is set, the bodies decode under an
/// `OwnerId::CfgRegion` owner derived from each arm's entry disk
/// offset, so the claim lookup bypasses any prescan claim whose extent
/// sits inside the arm's CFG region transitive coverage. Falls back to
/// the layout's recogniser-tagged owner when the context lacks a CFG /
/// region tree (synthetic test contexts, standalone function decode).
/// Classic if/else branches that don't carry a body_owner decode
/// without any owner installed.
fn decode_branch_bodies(layout: BranchLayout, ctx: &DecodeCtx) -> (Vec<Stmt>, Vec<Stmt>, usize) {
    let then_body = if let Some((event_name, mem)) = layout.then_event_call {
        vec![Stmt::EventCall {
            event_name,
            offset: mem,
        }]
    } else if let Some(fallback_owner) = layout.body_owner {
        let arm_owner = arm_region_owner(ctx, layout.then_range.0).unwrap_or(fallback_owner);
        let _guard = ctx.with_decoding_owner(arm_owner);
        decode_subrange(layout.then_range.0, layout.then_range.1, ctx)
    } else {
        decode_subrange(layout.then_range.0, layout.then_range.1, ctx)
    };

    let mut else_body = if let Some((event_name, mem)) = layout.else_event_call {
        vec![Stmt::EventCall {
            event_name,
            offset: mem,
        }]
    } else if layout.else_range.0 == layout.else_range.1 {
        Vec::new()
    } else if let Some(fallback_owner) = layout.body_owner {
        let arm_owner = arm_region_owner(ctx, layout.else_range.0).unwrap_or(fallback_owner);
        let _guard = ctx.with_decoding_owner(arm_owner);
        decode_subrange(layout.else_range.0, layout.else_range.1, ctx)
    } else {
        decode_subrange(layout.else_range.0, layout.else_range.1, ctx)
    };

    // Multi-break loop-body: the else arm's bytes stopped at its loop break-jump;
    // append the `break` in the jump's place.
    if let Some(break_offset) = layout.else_trailing_break {
        else_body.push(Stmt::Break {
            offset: break_offset,
        });
    }

    (then_body, else_body, layout.resume_disk)
}

/// Look up the CFG region containing `arm_entry_disk` and wrap it as an
/// `OwnerId::CfgRegion`. Returns `None` when the context has no CFG /
/// region tree or the address doesn't fall inside any block.
pub(super) fn arm_region_owner(ctx: &DecodeCtx, arm_entry_disk: usize) -> Option<OwnerId> {
    let region_id = ctx.region_id_for(arm_entry_disk)?;
    Some(OwnerId::CfgRegion { region_id })
}

/// Scan forward from `start` until either a terminating `EX_JUMP` is
/// found at depth zero or we reach `end`.
///
/// "Depth zero" means the scan ignores `EX_JUMP` opcodes that appear
/// inside nested if/else constructs. The implementation walks opcode
/// boundaries via `opcode_length_at`, so any nested branches can't
/// contribute false positives unless they share a target with the
/// outer construct (which is the actual displaced-else case).
pub(super) struct TerminatingJump {
    jump_pos: usize,
    target_mem: usize,
    after_jump_disk: usize,
}

pub(super) fn scan_for_terminating_jump(
    ctx: &DecodeCtx,
    start: usize,
    end: usize,
) -> Option<TerminatingJump> {
    let mut cursor = start;
    let mut last: Option<TerminatingJump> = None;
    while cursor < end {
        if cursor >= ctx.bytecode.len() {
            break;
        }
        let opcode_byte_count = 1;
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_JUMP && cursor + opcode_byte_count + JUMP_TARGET_BYTES <= end {
            let mut peek = cursor + opcode_byte_count;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            last = Some(TerminatingJump {
                jump_pos: cursor,
                target_mem,
                after_jump_disk: peek,
            });
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }

    // Only consider the jump terminating if it lands at the very end of
    // the scanned range. Otherwise we may have walked past the
    // EX_JUMP_IF_NOT's target without a clean exit.
    last.filter(|jump| jump.after_jump_disk == end)
}

/// When `target` is the start of an IsValid macro Then-body (a chain
/// that ends with `EX_POP_EXECUTION_FLOW` before any other control-flow
/// terminator), return the disk position immediately past the POP so
/// callers can use it as an `else_range` upper bound.
///
/// Returns `None` for loop / sequence shapes whose chain reaches a
/// different terminator first (`EX_JUMP_IF_NOT` loop head,
/// `EX_PUSH_EXECUTION_FLOW` sequence prologue, `EX_POP_FLOW_IF_NOT`
/// latch continuation, `EX_RETURN` / `EX_END_OF_SCRIPT` epilogue).
///
/// The walk is upper-bounded by `chain_limit` (the disk position of the
/// JIN whose target we're classifying, i.e. `construct_offset`) so the
/// scan can never walk past the current branch's own opcode and re-
/// include it in the resulting else-range — that would drive
/// `decode_subrange` to recurse on the same JIN.
///
/// The walk skips instrumentation opcodes (`EX_TRACEPOINT`,
/// `EX_WIRE_TRACEPOINT`, `EX_INSTRUMENTATION_EVENT`) and consumes
/// assignment / call opcodes via `opcode_length_at` so an IsValid body
/// whose displaced statements run several function calls before popping
/// is still recognised.
pub(crate) fn isvalid_else_body_end(
    target: usize,
    chain_limit: usize,
    ctx: &DecodeCtx,
) -> Option<usize> {
    // Region-aware path: when CFG + region tree are populated, the
    // SESE region exit dominated by the IsValid arm entry bounds the
    // displaced body without an opcode-pattern walk. The accessor
    // returns the union of reachable owned segments; we take the end
    // of the last segment as the body terminator.
    if let Some(extents) = ctx.region_arm_extents_for(chain_limit, &[target]) {
        if let Some(end) = arm_last_end(&extents, 0) {
            if end > target && end <= chain_limit {
                return Some(end);
            }
        }
    }
    /// Bound on chain walk so a malformed stream can't drive an
    /// unbounded scan. Every observed IsValid body terminates within
    /// a handful of opcodes; 32 is comfortably above that.
    const MAX_CHAIN_OPCODES: usize = 32;
    let scan_end = chain_limit.min(ctx.bytecode.len());
    let mut cursor = target;
    let mut visited = 0usize;
    while cursor < scan_end && visited < MAX_CHAIN_OPCODES {
        let opcode = ctx.bytecode[cursor];
        match opcode {
            EX_POP_EXECUTION_FLOW => {
                // EX_POP_EXECUTION_FLOW is a single byte. The else-body
                // includes the POP so decode_one consumes it as a
                // structural marker.
                return Some(cursor + 1);
            }
            EX_JUMP_IF_NOT
            | EX_JUMP
            | EX_PUSH_EXECUTION_FLOW
            | EX_POP_FLOW_IF_NOT
            | EX_RETURN
            | EX_END_OF_SCRIPT => return None,
            _ => {}
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
        visited += 1;
    }
    None
}

/// Walk forward from each displaced body to find the convergence
/// offset they share. Returns the smallest offset within the range
/// reachable from both that ends in a jump landing on the same disk
/// position. If the heuristic fails, returns `range_end`.
///
/// `forward_floor` is the lower bound for accepted convergence offsets.
/// Targets at or before `forward_floor` are rejected as back-edges or
/// unrelated jumps the widened scan picked up. Without this floor a
/// cross-range scan can resolve a terminator's target to a backward
/// disk position; the caller's `resume_disk` would land before the
/// branch and the region walk would loop forever.
fn find_convergence_for_displaced(
    ctx: &DecodeCtx,
    construct_offset: usize,
    then_start: usize,
    else_start: usize,
    range_end: usize,
    forward_floor: usize,
) -> usize {
    // Region-aware path: when the CFG accessor returns arm extents
    // bounded by the SESE region exit, that exit IS the convergence
    // point by dominance.
    if let Some(extents) = ctx.region_arm_extents_for(construct_offset, &[then_start, else_start]) {
        let arm_end = |index: usize| arm_last_end(&extents, index);
        if let Some(convergence) = match (arm_end(0), arm_end(1)) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            _ => None,
        } {
            if convergence > forward_floor && convergence <= range_end {
                return convergence;
            }
        }
    }
    let then_terminator = scan_for_terminating_jump(ctx, then_start, range_end);
    let else_terminator = scan_for_terminating_jump(ctx, else_start, range_end);

    let resolve = |jump: TerminatingJump| -> Option<usize> {
        match classify_target(jump.target_mem, 0, range_end, ctx) {
            JumpTarget::InRange { disk, .. } if disk > forward_floor => Some(disk),
            JumpTarget::InRange { .. } => None,
            JumpTarget::OutOfRange | JumpTarget::Unresolved | JumpTarget::EventEntry { .. } => None,
        }
    };

    let then_conv = then_terminator.and_then(resolve);
    let else_conv = else_terminator.and_then(resolve);

    match (then_conv, else_conv) {
        (Some(a), Some(b)) if a == b => a,
        (Some(a), _) => a,
        (_, Some(b)) => b,
        _ => range_end,
    }
}
