//! Recursive subrange decoding.
//!
//! Decodes a `[start, end)` disk range into statements, dispatching each
//! opcode through the per-opcode decoder and the branch recogniser, with
//! optional exclusion of already-owned segments.

use std::ops::Range;

use crate::bytecode::stmt::Stmt;

use super::super::ctx::DecodeCtx;

/// Recursively decode every opcode within `[start, end)` into a flat
/// `Vec<Stmt>`, applying construct recognition at every step.
///
/// This is the recursion target for both branch bodies. Decode logic
/// matches the region walk's per-block decode but operates on a single
/// contiguous range supplied directly rather than via the partition.
///
/// When `ctx.owned_ranges` is set and `[start, end)` straddles owned-range
/// boundaries, only the bytes belonging to the event's owned ranges are
/// decoded; bytes in the gaps (which belong to other events) are skipped.
/// The decoded statements from each owned-range slice are concatenated in
/// disk order. This is the cross-range body-decode fix that pairs with
/// the classifier extension.
pub(crate) fn decode_subrange(start: usize, end: usize, ctx: &DecodeCtx) -> Vec<Stmt> {
    decode_subrange_excluding(start, end, ctx, &[])
}

/// Like `decode_subrange`, but suppresses any top-level statement whose
/// start offset falls inside an `exclude` range. The opcode is still
/// decoded so the disk cursor advances correctly; only its emission is
/// dropped. Used by `decode_ifthenelse_arms` to prevent a sibling arm
/// from re-emitting statements a Sequence (or other construct) in the
/// first-decoded arm already pulled from a physically-displaced segment.
/// An empty `exclude` set is identical to `decode_subrange`.
pub(crate) fn decode_subrange_excluding(
    start: usize,
    end: usize,
    ctx: &DecodeCtx,
    exclude: &[Range<usize>],
) -> Vec<Stmt> {
    if start >= end {
        return Vec::new();
    }
    let segments = owned_segments_in(start, end, ctx);
    let mut stmts = Vec::new();
    for segment in segments {
        decode_segment_into(&mut stmts, segment.0, segment.1, ctx, exclude);
    }
    stmts
}

/// Decode the bytes of a single contiguous segment `[seg_start, seg_end)`
/// into `stmts`, applying construct recognition. The segment is assumed
/// to be wholly within one of the event's owned ranges (or the entire
/// range, when `owned_ranges` is `None`).
///
/// Consults the owner-tagged claim map: skips past claims whose owners
/// include an absorbing construct (IsValid macro, trampoline cascade)
/// when the current `decoding_owner` isn't one of them. Only fires
/// when the body decode runs UNDER an absorbing-owner context (i.e.
/// the current `decoding_owner` is itself an absorbing owner). Outside
/// such contexts, pin partition bytes belonging to a chain whose
/// dispatch hasn't installed an owner yet must decode normally so the
/// chain emits its content nested. Without this gate, ForLoop bodies
/// that contain a Sequence chain (the chain prescan claims the chain's
/// pin partitions; the loop body's `decode_subrange` runs without an
/// owner) would skip the chain entirely.
fn decode_segment_into(
    stmts: &mut Vec<Stmt>,
    seg_start: usize,
    seg_end: usize,
    ctx: &DecodeCtx,
    exclude: &[Range<usize>],
) {
    use super::super::block::decode_one_or_branch;
    use super::super::ctx::claimed_end_for;
    let owner_active = ctx.decoding_owner.get().is_some();
    let mut pos = seg_start;
    while pos < seg_end {
        if owner_active {
            if let Some(claim_end) = claimed_end_for(ctx, pos) {
                pos = claim_end.min(seg_end);
                continue;
            }
        }
        // Region-aware IfThenElse dispatch for loop body/completion
        // ranges. When the loop emitter is active and `pos` heads a nested
        // IfThenElse region carved under that loop, route it to the
        // structured emitter so both arms slice correctly, instead of the
        // byte-slice `decode_branch` (which drops a backward-converging
        // else). No-op outside the loop emitter (the
        // `loop_completion_region` hint is unset). See
        // `try_dispatch_loop_body_region_at`.
        if let Some((emitted, advance_end)) =
            super::super::region_decode::try_dispatch_loop_body_region_at(pos, seg_end, ctx)
        {
            stmts.extend(emitted);
            pos = advance_end.max(pos + 1).min(seg_end);
            continue;
        }
        // Region-aware Loop dispatch for the nested-ForEach-inside-
        // ForEach shape, where the inner loop is carved as a disk-order
        // SIBLING of the active loop. The discriminator (same-parent sibling
        // Loop + own-JIN head + own-back-edge + dual-role) scopes it to that
        // shape; no-op outside the loop emitter. See
        // `try_dispatch_loop_body_loop_region_at`.
        if let Some((emitted, advance_end)) =
            super::super::region_decode::try_dispatch_loop_body_loop_region_at(pos, seg_end, ctx)
        {
            stmts.extend(emitted);
            pos = advance_end.max(pos + 1).min(seg_end);
            continue;
        }
        let before = pos;
        let suppressed = exclude.iter().any(|range| range.contains(&before));
        match decode_one_or_branch(&mut pos, seg_end, ctx) {
            Ok(stmt_opt) => {
                if let Some(stmt) = stmt_opt {
                    if !suppressed {
                        stmts.push(stmt);
                    }
                }
            }
            Err(unknown) => {
                if !suppressed {
                    stmts.push(*unknown);
                }
                if pos == before {
                    pos += 1;
                }
            }
        }
        if pos > seg_end {
            pos = seg_end;
        }
    }
}

/// Intersect `[start, end)` with the event's owned disk ranges and return
/// the resulting segments in disk order. When `ctx.owned_ranges` is
/// `None`, returns `[(start, end)]` unchanged so single-range callers
/// (standalone functions, synthetic tests) keep their existing behavior.
fn owned_segments_in(start: usize, end: usize, ctx: &DecodeCtx) -> Vec<(usize, usize)> {
    let Some(owned) = ctx.owned_ranges else {
        return vec![(start, end)];
    };
    let mut segments: Vec<(usize, usize)> = Vec::new();
    for range in owned {
        let lower = range.start.max(start);
        let upper = range.end.min(end);
        if lower < upper {
            segments.push((lower, upper));
        }
    }
    if segments.is_empty() {
        // The body window doesn't intersect any owned range. This can
        // happen with synthetic test contexts that pass `owned_ranges`
        // not covering the test bytecode; fall back to the requested
        // window so callers don't lose all output.
        return vec![(start, end)];
    }
    segments.sort_by_key(|seg| seg.0);
    segments
}
