//! Region-tree decoder. This is the sole production decode path.
//!
//! Walks a `RegionTree` in DFS order, decoding each region's blocks using
//! the per-opcode decoders (`decode_one_or_branch`). Returns the emitted
//! `Vec<Stmt>` consumed by downstream passes.
//!
//! Per-region translation:
//! - **Trivial / Linear / IfThen / IfThenElse / Loop / Switch**: visit
//!   the region's entry block first, then DFS through child regions. At
//!   each block, decode opcodes via `decode_one_or_branch`. Multi-opcode
//!   recognisers (Branch, Loop, Sequence, Latch, IsValid, etc.) consume
//!   spans that overlap child regions, so a `consumed` tracker prevents
//!   re-emission when the DFS later visits those child blocks. The
//!   region kind drives only the DFS traversal order, not the per-opcode
//!   decoding logic.
//!
//! Region kinds carry no additional per-Stmt semantics
//! because the decoders already produce the correct typed
//! Stmts (Branch, Loop, Switch, etc.) at the terminator address.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Range;

use crate::bytecode::cfg::dom::compute_dominators;
use crate::bytecode::cfg::region::{Region, RegionId, RegionKind, RegionTree};
use crate::bytecode::cfg::{BasicBlock, BlockId, ControlFlowGraph};
use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::{
    EX_END_OF_SCRIPT, EX_JUMP, EX_JUMP_IF_NOT, EX_LET_BOOL, EX_POP_FLOW_IF_NOT,
    EX_PUSH_EXECUTION_FLOW, EX_RETURN, EX_SWITCH_VALUE,
};
use crate::bytecode::readers::read_bc_u32;
use crate::bytecode::stmt::{LatchKind, Stmt};

use super::block::decode_one_or_branch;
use super::branch::{decode_subrange, decode_subrange_excluding};
use super::cascade_decode::{
    try_decode_jumpifnot_cascade, try_decode_jumpifnot_cascade_shared,
    try_decode_jumpifnot_cascade_shared_via_trampoline,
};
use super::ctx::{claimed_end_for_disk_sweep, DecodeCtx, OwnerId};
use super::expr_decode::decode_expr;
use super::loop_decode::try_decode_loop;
use super::naked_if::try_decode_naked_if;
use super::switch_decode::try_decode_switch;

mod arm_decode;
mod dispatch;
mod doonce;
mod ifthen;
mod ifthenelse;
mod loop_region;
mod sequencechain;
mod shared;

use arm_decode::*;
use dispatch::*;
use doonce::*;
use ifthen::*;
use ifthenelse::*;
use loop_region::*;
use sequencechain::*;
use shared::*;

// External surface reachable as `region_decode::X` by consumers outside
// this directory module (decode/mod.rs, branch.rs). Re-exported explicitly
// so the paths resolve unchanged after the carve.
pub(crate) use loop_region::{
    try_dispatch_loop_body_loop_region_at, try_dispatch_loop_body_region_at,
};

/// Immutable per-walk context, the three references threaded through
/// every region-decode function. `DecodeCtx` carries the mutable
/// decode state via interior mutability, so a shared `&` is correct.
#[derive(Clone, Copy)]
pub(super) struct RegionWalkCtx<'a> {
    pub cfg: &'a ControlFlowGraph,
    pub ctx: &'a DecodeCtx<'a>,
    pub idom: &'a BTreeMap<BlockId, BlockId>,
}

/// Walk the region tree in DFS order from the root, decoding each
/// region's blocks via the existing per-opcode decoders. Returns the
/// emitted `Vec<Stmt>`.
///
/// `cfg` must be the CFG the `RegionTree` was built over. `ctx` is the
/// shared decode context (claims, skeleton, name table, etc.) already
/// populated before the walk; the walk reuses the existing claim map
/// rather than rebuilding it.
pub(super) fn decode_region_tree(
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut consumed: Vec<Range<usize>> = Vec::new();
    let mut visited_blocks: BTreeSet<BlockId> = BTreeSet::new();
    let idom = compute_dominators(cfg);
    walk_region(
        region_tree,
        region_tree.root,
        RegionWalkCtx {
            cfg,
            ctx,
            idom: &idom,
        },
        &mut stmts,
        &mut consumed,
        &mut visited_blocks,
    );
    stmts
}

/// Recursive DFS over the region tree. Each region first decodes its
/// entry block (when not already consumed), then recurses into child
/// regions in tree order. After children, any remaining blocks that
/// belong to this region but were not visited (irreducible or back-edge
/// shapes that fall outside child slices) get decoded as a sweep so the
/// region's byte coverage is complete.
pub(super) fn walk_region(
    region_tree: &RegionTree,
    region_id: RegionId,
    walk: RegionWalkCtx,
    stmts: &mut Vec<Stmt>,
    consumed: &mut Vec<Range<usize>>,
    visited_blocks: &mut BTreeSet<BlockId>,
) {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    // When the loop-body dispatch helper already emitted this
    // Loop region during the active loop's displaced-body decode, skip it
    // here so the sibling walk doesn't re-emit a duplicate `Stmt::Loop`. The
    // set is populated only by `try_dispatch_loop_body_loop_region_at`, so
    // this is a no-op for functions without the nested-sibling-loop shape.
    // Checked BEFORE any `try_emit_*` because a `CfgRegion` claim cannot
    // suppress the region's own structured emit (it self-bypasses under its
    // own owner).
    if ctx.dispatched_loop_regions.borrow().contains(&region_id) {
        return;
    }
    let region = &region_tree.regions[region_id];
    // When an outer IfThenElse R0 has an inner sibling R1
    // sharing R0's entry block (Blueprint IsValid macro dual-role pattern),
    // skip R0's per-kind emit. Otherwise mark_region_consumed(R0)
    // transitively drops every block under R1 and its siblings, losing
    // their content. Disk-order walk recurses into R1 (its own
    // try_emit_ifthenelse_region fires) and surfaces sibling R2 as the
    // merge continuation handled inside try_emit_ifthenelse_region.
    let defer_to_inner_sibling = region.kind == RegionKind::IfThenElse
        && find_same_entry_inner_sibling(region_id, region_tree).is_some();
    if let Some((emitted, pulled_continuation, matched)) = dispatch_region_emitters(
        region,
        region_id,
        region_tree,
        cfg,
        ctx,
        idom,
        !defer_to_inner_sibling,
    ) {
        if matches!(matched, MatchedEmitter::SequenceChain) {
            // The SequenceChain emit decodes each pin body, including
            // pin-0's after-chain fallthrough block, which SESE often
            // assigns to an ANCESTOR region rather than this one.
            // `mark_region_consumed` only walks this region's subtree, so
            // it misses that block and the ancestor's disk-order fallback
            // re-decodes it (a trailing duplicate, e.g. Seq_TwoPin's third
            // PrintString). Record every emitted statement offset into the
            // shared consumed set so no ancestor sweep re-covers a pin body
            // this emit already produced.
            for stmt in &emitted {
                consumed.extend(extra_consumed_ranges_for_stmt(stmt));
            }
        }
        stmts.extend(emitted);
        mark_region_consumed(region_tree, region_id, cfg, consumed, visited_blocks);
        if let Some(continuation_id) = pulled_continuation {
            mark_region_consumed(region_tree, continuation_id, cfg, consumed, visited_blocks);
        }
        return;
    }
    // Fallback walk for RegionKind::Linear, RegionKind::Trivial, and
    // any specialised kind whose per-kind emitter declined (e.g.
    // SequenceChain when the structure skeleton has no push-chain
    // entry for the PUSH terminator: the region keeps its SequenceChain
    // classification but `try_emit_sequencechain_region` returns None,
    // and we fall through to here).
    //
    // Disk-order interleaved walk: visit every direct-owned block and
    // every immediate-child region in disk-start order, dispatching
    // each child region through `walk_region` (which routes to its
    // per-kind emitter) and each block through `decode_region_block_if_unclaimed`.
    // This preserves on-disk position when the region owns preamble
    // blocks that precede child regions, fixing the prior emit order
    // bug where the sweep-residue tail surfaced preamble blocks AFTER
    // child loop/branch bodies.
    walk_region_disk_order(
        region_tree,
        region_id,
        walk,
        stmts,
        consumed,
        visited_blocks,
    );
}

/// One item to emit during a region's fallback walk: either a directly
/// owned block (decoded inline) or an immediate child region (recursed
/// via `walk_region`).
enum WalkItem {
    Block(BlockId),
    ChildRegion(RegionId),
}

/// Reorder the peer items by successor-BFS from `entry_block_id`. Each
/// child-region item is keyed by its entry block; reaching that entry
/// during BFS pulls the whole child region in at its execution-order
/// position. Items unreachable from the entry keep their relative
/// (disk-order) ordering at the tail.
fn reorder_items_by_successor_bfs(
    items: Vec<(usize, WalkItem)>,
    entry_block_id: BlockId,
    cfg: &ControlFlowGraph,
    region_tree: &RegionTree,
) -> Vec<(usize, WalkItem)> {
    // Index items by the block id that "owns" their execution-order
    // anchor: WalkItem::Block uses the block itself; WalkItem::ChildRegion
    // uses the child region's entry block (the only successor edge the
    // outer walk follows into the child).
    let mut item_by_anchor: BTreeMap<BlockId, (usize, WalkItem)> = BTreeMap::new();
    for (start, item) in items {
        let anchor = match item {
            WalkItem::Block(block_id) => block_id,
            WalkItem::ChildRegion(child_id) => region_tree.regions[child_id].entry,
        };
        item_by_anchor.insert(anchor, (start, item));
    }

    let mut ordered: Vec<(usize, WalkItem)> = Vec::with_capacity(item_by_anchor.len());
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    queue.push_back(entry_block_id);
    visited.insert(entry_block_id);
    while let Some(current) = queue.pop_front() {
        if let Some(item) = item_by_anchor.remove(&current) {
            ordered.push(item);
        }
        if let Some(successors) = cfg.successors.get(&current) {
            for &succ in successors {
                if visited.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
    }
    // Append any leftover items the BFS didn't reach (irreducible /
    // back-edge residue) in their original disk-sorted order.
    for (_, leftover) in item_by_anchor {
        ordered.push(leftover);
    }
    ordered
}

/// Disk-order interleaved walk of one region's direct-owned blocks and
/// immediate-child regions. Used as the fallback when no per-kind
/// emitter handled the region as a single unit.
///
/// Ordering: the region's entry block first (entry-anchored, as the
/// retired flow-BFS was), then every other directly-owned block plus every
/// immediate-child region's entry block, sorted by on-disk start address.
/// Each child region's entry appears once in the merged sequence; when
/// the iteration reaches that entry, the child is recursed via
/// `walk_region` and its blocks are skipped on subsequent iterations
/// because `walk_region` calls `mark_region_consumed`, populating
/// `visited_blocks`.
///
/// Entry-first ordering matters for cross-event-inlined events whose
/// bodies span multiple disjoint disk ranges: the entry block can sit
/// at a higher disk address than other ranges that the entry's exec-pin
/// graph eventually reaches (e.g. an event entry at a high disk offset
/// whose body chains into shared DoOnce-reset blocks at a much lower offset).
/// Pure disk order would emit the shared reset block before the entry
/// body, swapping the rendered statement order versus the linear sweep.
fn walk_region_disk_order(
    region_tree: &RegionTree,
    region_id: RegionId,
    walk: RegionWalkCtx,
    stmts: &mut Vec<Stmt>,
    consumed: &mut Vec<Range<usize>>,
    visited_blocks: &mut BTreeSet<BlockId>,
) {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    let region = &region_tree.regions[region_id];
    let mut items: Vec<(usize, WalkItem)> = Vec::new();

    // Direct-owned blocks of this region (excluding the sink and child
    // region entries, which are tracked via their region instead).
    let child_entry_blocks: BTreeSet<BlockId> = region
        .children
        .iter()
        .map(|&child_id| region_tree.regions[child_id].entry)
        .collect();
    let entry_block_id = region.entry;
    let mut entry_block_item: Option<WalkItem> = None;
    for (&block_id, &owner) in &region_tree.block_to_region {
        if owner != region_id || block_id == cfg.sink {
            continue;
        }
        if child_entry_blocks.contains(&block_id) {
            // Child-region entries are walked through their region item
            // below; do not double-queue them as plain blocks.
            continue;
        }
        if let Some(block) = cfg.blocks.get(block_id) {
            if !block.opcodes.is_empty() {
                if block_id == entry_block_id {
                    // Defer to the entry-first slot so the disk-order
                    // sort below cannot push it after a lower-address
                    // peer.
                    entry_block_item = Some(WalkItem::Block(block_id));
                } else {
                    items.push((block.start, WalkItem::Block(block_id)));
                }
            }
        }
    }

    // Child regions, anchored at their entry block's disk start. A
    // child whose entry happens to be the region's own entry is queued
    // as a child item (not as the entry-first block) so the per-kind
    // emitter still drives it.
    for &child_id in &region.children {
        let child_entry = region_tree.regions[child_id].entry;
        let Some(block) = cfg.blocks.get(child_entry) else {
            continue;
        };
        if child_entry == entry_block_id {
            entry_block_item = Some(WalkItem::ChildRegion(child_id));
        } else {
            items.push((block.start, WalkItem::ChildRegion(child_id)));
        }
    }

    items.sort_by_key(|(start, _)| *start);

    // When the entry block sits at a higher disk address than every other
    // peer (cross-event-inlined shape: entry was patched onto a higher
    // offset and chains downward into shared lower-address blocks), the
    // remaining peers have a real execution-order dependency that disk
    // order alone gets wrong. Reorder the peers by successor BFS from the
    // entry so the rendered statement order follows the linear sweep.
    // Peers unreachable from the entry keep their disk-order position at
    // the tail (covers irreducible residue blocks the BFS doesn't touch).
    if let Some(entry_start) = cfg.blocks.get(entry_block_id).map(|block| block.start) {
        let peer_starts_below_entry = items.iter().all(|(start, _)| *start < entry_start);
        if !items.is_empty() && peer_starts_below_entry {
            items = reorder_items_by_successor_bfs(items, entry_block_id, cfg, region_tree);
        }
    }

    let ordered_items = entry_block_item
        .into_iter()
        .chain(items.into_iter().map(|(_, item)| item));

    for item in ordered_items {
        match item {
            WalkItem::Block(block_id) => {
                if visited_blocks.contains(&block_id) {
                    continue;
                }
                decode_region_block_if_unclaimed(
                    cfg,
                    block_id,
                    ctx,
                    stmts,
                    consumed,
                    visited_blocks,
                );
            }
            WalkItem::ChildRegion(child_id) => {
                let child_entry = region_tree.regions[child_id].entry;
                if visited_blocks.contains(&child_entry) {
                    continue;
                }
                walk_region(region_tree, child_id, walk, stmts, consumed, visited_blocks);
            }
        }
    }
}

/// Walk region-owned blocks that lie OUTSIDE the if-body byte span
/// `[body_start_pos, body_end_pos)` after `try_decode_naked_if`
/// returns, decoding each via `decode_block_opcodes` and appending the
/// resulting `Stmt`s.
///
/// The naked-if helper closes at the matching `EX_POP_EXECUTION_FLOW`
/// inside the body. Region-owned blocks past that close hold trailing
/// content (typical: a single call statement following the latent
/// gate) that `mark_region_consumed` would silently drop in the
/// caller (a latent-gate-followed-by-call shape).
///
/// A region's byte coverage can also include EARLIER disjoint ranges,
/// typically a latent-resume target block sitting in the ubergraph
/// dispatch table well before the event body. Those blocks belong to
/// the same region (the event partition owns the resume bytes), but
/// `try_decode_naked_if` never reaches them because they're outside
/// the if-body. The resume edge follows the `POP_EXECUTION_FLOW`
/// naturally and emits the resume block as a peer of the
/// Branch; the emit pipeline then re-inlines it via the
/// `/*resume:0xHEX*/` annotation. Without this walk the alt path
/// drops it (a latent-resume-target shape).
pub(super) fn walk_extra_region_blocks(
    region_id: RegionId,
    body_start_pos: usize,
    body_end_pos: usize,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
    out: &mut Vec<Stmt>,
    pre_consumed: &Option<Range<usize>>,
) {
    let Some(region_ranges) = ctx.region_byte_ranges.and_then(|map| map.get(&region_id)) else {
        return;
    };

    // A block is in-scope when at least one byte sits inside any
    // region range. The naked-if helper has already consumed the body
    // span; anything outside that span but inside the region's coverage
    // is fair game.
    let block_in_region = |block: &BasicBlock| -> bool {
        region_ranges
            .iter()
            .any(|range| block.start < range.end && range.start < block.end)
    };
    let block_outside_body =
        |block: &BasicBlock| -> bool { block.end <= body_start_pos || block.start >= body_end_pos };

    let mut extras: Vec<&BasicBlock> = cfg
        .blocks
        .iter()
        .filter(|block| {
            !block.opcodes.is_empty()
                && block.end > block.start
                && block_outside_body(block)
                && block_in_region(block)
        })
        .collect();
    extras.sort_by_key(|block| block.start);

    let mut consumed: Vec<Range<usize>> = Vec::new();
    if let Some(range) = pre_consumed {
        consumed.push(range.clone());
    }
    for block in extras {
        // Skip a block whose entire span is already consumed (the
        // inner-else splice path moved its content into a nested
        // Branch's else_body).
        if let Some(range) = pre_consumed {
            if block.start >= range.start && block.end <= range.end {
                continue;
            }
        }
        decode_block_opcodes(cfg, block.id, ctx, out, &mut consumed, region_ranges);
    }
}

/// Mark `region_id` and all its transitive descendants in `dispatched` so
/// the root region walk skips them (they have been folded into another
/// construct's body).
pub(super) fn mark_subtree_dispatched(
    region_tree: &RegionTree,
    region_id: RegionId,
    dispatched: &mut BTreeSet<RegionId>,
) {
    dispatched.insert(region_id);
    for &child in &region_tree.regions[region_id].children {
        mark_subtree_dispatched(region_tree, child, dispatched);
    }
}

/// Mark every block transitively contained in `region_id` (the region
/// itself plus every descendant region) as visited, and merge their
/// byte extents into `consumed`. Used when the emitter handled the
/// region as a single unit so the per-opcode walk doesn't re-emit the
/// same bytes.
pub(super) fn mark_region_consumed(
    region_tree: &RegionTree,
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    consumed: &mut Vec<Range<usize>>,
    visited_blocks: &mut BTreeSet<BlockId>,
) {
    let mut stack: Vec<RegionId> = vec![region_id];
    while let Some(current) = stack.pop() {
        for (&block_id, &owner) in &region_tree.block_to_region {
            if owner != current {
                continue;
            }
            if block_id == cfg.sink {
                continue;
            }
            visited_blocks.insert(block_id);
            if let Some(block) = cfg.blocks.get(block_id) {
                if !block.opcodes.is_empty() {
                    consumed.push(block.start..block.end);
                }
            }
        }
        for &child in &region_tree.regions[current].children {
            stack.push(child);
        }
    }
}

/// Decode every opcode in `block_id` that isn't already inside a
/// `consumed` span or claim-protected. Emit one `Stmt` per decoded
/// position; advance through multi-opcode spans by trusting the
/// recogniser to update the cursor past the construct.
fn decode_region_block_if_unclaimed(
    cfg: &ControlFlowGraph,
    block_id: BlockId,
    ctx: &DecodeCtx,
    stmts: &mut Vec<Stmt>,
    consumed: &mut Vec<Range<usize>>,
    visited_blocks: &mut BTreeSet<BlockId>,
) {
    if !visited_blocks.insert(block_id) {
        return;
    }
    let block = match cfg.blocks.get(block_id) {
        Some(block) => block,
        None => return,
    };
    if block.opcodes.is_empty() {
        return; // synthetic sink or empty placeholder
    }

    let block_end = block.end;
    for &opcode_addr in &block.opcodes {
        if address_in_consumed(consumed, opcode_addr) {
            continue;
        }
        if claimed_end_for_disk_sweep(ctx, opcode_addr).is_some() {
            continue;
        }
        if opcode_addr >= ctx.bytecode.len() {
            continue;
        }
        let mut pos = opcode_addr;
        let before = pos;
        match decode_one_or_branch(&mut pos, block_end, ctx) {
            Ok(Some(stmt)) => {
                consumed.extend(extra_consumed_ranges(&stmt, before, pos));
                stmts.push(stmt);
                if pos > before {
                    consumed.push(before..pos);
                }
            }
            Ok(None) => {
                if pos > before {
                    consumed.push(before..pos);
                }
            }
            Err(unknown) => {
                stmts.push(*unknown);
                if pos > before {
                    consumed.push(before..pos);
                }
            }
        }
    }
}

/// Report the byte offsets a freshly decoded `stmt` consumed that fall
/// OUTSIDE the cursor advance `before..pos`.
///
/// A `Stmt::Sequence` can be decoded via a jump-target chain (the inline
/// `try_decode_sequence` path reached through `decode_jump`, or a
/// cross-event-inlined Sequence whose chain head lives in another event's
/// skeleton). The cursor advances only past the local opcode, but the
/// Sequence's pin bodies decode statements at arbitrary disk offsets. If
/// those offsets are not recorded as consumed, a later disk-order sweep
/// of the same block (or an ancestor block) re-decodes the same bytes as
/// siblings, e.g. a `Sequence@0x1de { ResetDoOnce }`
/// followed by a duplicate `ResetDoOnce` from the re-decoded gate-clear
/// pair.
///
/// The Sequence's own pin statements carry the disk offsets of every
/// opcode the emitter already consumed, so deriving the consumed set from
/// the emitted statements is self-contained (no cross-event skeleton
/// lookup) and reports exactly what was emitted (no over-claim). Each
/// inner offset becomes a single-byte range `[off..off+1]`; the sweep
/// gates re-decode on the opcode's start address, so a single-byte mark
/// is enough to skip it. Offsets inside `before..pos` are dropped (the
/// cursor advance already covers them). Non-Sequence statements report
/// nothing.
/// Record every disk offset a structured `stmt` and its nested
/// statements consumed as single-byte ranges `[off..off+1]`. Unlike
/// `extra_consumed_ranges`, there is no cursor window to filter against,
/// the caller already emitted the whole construct as a unit (a region
/// emit), so every offset it covered should be marked. Lets an ancestor
/// disk-order sweep skip bytes a structured emitter already produced.
fn extra_consumed_ranges_for_stmt(stmt: &Stmt) -> Vec<Range<usize>> {
    let mut offsets: Vec<usize> = Vec::new();
    collect_stmt_offsets(stmt, &mut offsets);
    offsets.into_iter().map(|off| off..off + 1).collect()
}

pub(super) fn extra_consumed_ranges(stmt: &Stmt, before: usize, pos: usize) -> Vec<Range<usize>> {
    let Stmt::Sequence { pins, .. } = stmt else {
        return Vec::new();
    };
    let mut offsets: Vec<usize> = Vec::new();
    for pin in pins {
        for inner in pin {
            collect_stmt_offsets(inner, &mut offsets);
        }
    }
    offsets
        .into_iter()
        .filter(|&off| off < before || off >= pos)
        .map(|off| off..off + 1)
        .collect()
}

/// Recursively gather the disk offset of `stmt` and every nested
/// statement (branch arms, sequence pins, loop bodies, switch cases,
/// latch init/body) into `out`.
pub(super) fn collect_stmt_offsets(stmt: &Stmt, out: &mut Vec<usize>) {
    match stmt {
        Stmt::Assignment { offset, .. }
        | Stmt::Call { offset, .. }
        | Stmt::Return { offset, .. }
        | Stmt::Break { offset }
        | Stmt::EventCall { offset, .. } => out.push(*offset),
        Stmt::Branch {
            offset,
            then_body,
            else_body,
            ..
        } => {
            out.push(*offset);
            for inner in then_body.iter().chain(else_body.iter()) {
                collect_stmt_offsets(inner, out);
            }
        }
        Stmt::Sequence { offset, pins } => {
            out.push(*offset);
            for pin in pins {
                for inner in pin {
                    collect_stmt_offsets(inner, out);
                }
            }
        }
        Stmt::Loop {
            offset,
            body,
            completion,
            ..
        } => {
            out.push(*offset);
            for inner in body {
                collect_stmt_offsets(inner, out);
            }
            if let Some(completion_body) = completion {
                for inner in completion_body {
                    collect_stmt_offsets(inner, out);
                }
            }
        }
        Stmt::Switch {
            offset,
            cases,
            default,
            ..
        } => {
            out.push(*offset);
            for case in cases {
                for inner in &case.body {
                    collect_stmt_offsets(inner, out);
                }
            }
            if let Some(default_body) = default {
                for inner in default_body {
                    collect_stmt_offsets(inner, out);
                }
            }
        }
        Stmt::Latch {
            offset, init, body, ..
        } => {
            out.push(*offset);
            for inner in init.iter().chain(body.iter()) {
                collect_stmt_offsets(inner, out);
            }
        }
        Stmt::Unknown { offset, .. } => out.push(*offset),
    }
}

pub(super) fn address_in_consumed(consumed: &[Range<usize>], addr: usize) -> bool {
    consumed
        .iter()
        .any(|span| span.start <= addr && addr < span.end)
}

#[cfg(test)]
mod cluster_a_helper_tests {
    use super::*;
    use crate::bytecode::cfg::region::{Region, RegionTree};

    /// Build a minimal RegionTree mirroring the same-entry dual-role shape:
    /// R0 = IfThenElse entry=B0 exit=B11 children=[R1, R2]
    /// R1 = IfThenElse entry=B0 exit=B2 (same-entry inner sibling of R0)
    /// R2 = IfThenElse entry=B2 exit=B10 (merge continuation of R1)
    fn grip_actor_tree() -> RegionTree {
        let regions = vec![
            Region {
                id: 0,
                entry: 0,
                exit: 11,
                parent: None,
                children: vec![1, 2],
                kind: RegionKind::IfThenElse,
            },
            Region {
                id: 1,
                entry: 0,
                exit: 2,
                parent: Some(0),
                children: vec![],
                kind: RegionKind::IfThenElse,
            },
            Region {
                id: 2,
                entry: 2,
                exit: 10,
                parent: Some(0),
                children: vec![],
                kind: RegionKind::IfThenElse,
            },
        ];
        RegionTree {
            regions,
            root: 0,
            block_to_region: std::collections::BTreeMap::new(),
        }
    }

    /// Build a flat IfThenElse tree with no dual-role pattern (the
    /// regular single-arm case where the dual-role defer should NOT fire).
    fn flat_tree() -> RegionTree {
        let regions = vec![
            Region {
                id: 0,
                entry: 0,
                exit: 4,
                parent: None,
                children: vec![1],
                kind: RegionKind::IfThenElse,
            },
            Region {
                id: 1,
                entry: 1,
                exit: 3,
                parent: Some(0),
                children: vec![],
                kind: RegionKind::IfThen,
            },
        ];
        RegionTree {
            regions,
            root: 0,
            block_to_region: std::collections::BTreeMap::new(),
        }
    }

    #[test]
    fn same_entry_inner_sibling_detects_dual_role_at_outer() {
        let tree = grip_actor_tree();
        // R0 has R1 as same-entry inner sibling (both entry == B0).
        assert_eq!(find_same_entry_inner_sibling(0, &tree), Some(1));
    }

    #[test]
    fn same_entry_inner_sibling_absent_when_child_has_distinct_entry() {
        let tree = grip_actor_tree();
        // R2 (entry=B2) is a child of R0 but entry differs from R0's
        // entry (B0). R0's same-entry inner sibling is R1, not R2.
        assert_eq!(find_same_entry_inner_sibling(2, &tree), None);
    }

    #[test]
    fn same_entry_inner_sibling_absent_on_flat_tree() {
        let tree = flat_tree();
        // R0.children = [R1] but R1.entry (B1) != R0.entry (B0).
        assert_eq!(find_same_entry_inner_sibling(0, &tree), None);
    }

    #[test]
    fn merge_continuation_finds_sibling_at_r1_exit() {
        let tree = grip_actor_tree();
        // R1.exit = B2 = R2.entry; both share parent R0.
        assert_eq!(find_merge_continuation_region(1, &tree), Some(2));
    }

    #[test]
    fn merge_continuation_absent_for_outer_region() {
        let tree = grip_actor_tree();
        // R0 has no parent so no sibling can be a continuation.
        assert_eq!(find_merge_continuation_region(0, &tree), None);
    }

    #[test]
    fn merge_continuation_absent_when_no_sibling_matches_exit() {
        let tree = flat_tree();
        // R1 has no continuation sibling (R0 is its parent, not sibling).
        assert_eq!(find_merge_continuation_region(1, &tree), None);
    }
}

#[cfg(test)]
mod own_exit_continuation_tests {
    use super::*;
    use crate::bytecode::cfg::region::{Region, RegionTree};
    use crate::bytecode::cfg::{BasicBlock, ControlFlowGraph};

    /// Build an own-exit-with-content region tree (the predicate should
    /// fire on r1 whose exit block carries content):
    /// r0 kind=Linear     entry=b5 exit=b6(sink) parent=None children=[1]
    /// r1 kind=IfThenElse entry=b1 exit=b0      parent=Some(0) children=[]
    /// block_to_region: 0:1, 1:1, 2:1, 3:1, 4:0, 5:0, 6:0
    fn fly_region_tree() -> RegionTree {
        let regions = vec![
            Region {
                id: 0,
                entry: 5,
                exit: 6,
                parent: None,
                children: vec![1],
                kind: RegionKind::Linear,
            },
            Region {
                id: 1,
                entry: 1,
                exit: 0,
                parent: Some(0),
                children: vec![],
                kind: RegionKind::IfThenElse,
            },
        ];
        let mut block_to_region = BTreeMap::new();
        for block_id in 0..4 {
            block_to_region.insert(block_id, 1);
        }
        for block_id in 4..7 {
            block_to_region.insert(block_id, 0);
        }
        RegionTree {
            regions,
            root: 0,
            block_to_region,
        }
    }

    /// Build a sink-exit region tree (predicate should decline because
    /// r1's exit is the synthetic sink, not a content block):
    /// r0 kind=Linear     entry=b4 exit=b5(sink) parent=None children=[1]
    /// r1 kind=IfThenElse entry=b1 exit=b5(sink) parent=Some(0) children=[]
    fn toggle_menu_region_tree() -> RegionTree {
        let regions = vec![
            Region {
                id: 0,
                entry: 4,
                exit: 5,
                parent: None,
                children: vec![1],
                kind: RegionKind::Linear,
            },
            Region {
                id: 1,
                entry: 1,
                exit: 5,
                parent: Some(0),
                children: vec![],
                kind: RegionKind::IfThenElse,
            },
        ];
        let mut block_to_region = BTreeMap::new();
        for block_id in 0..4 {
            block_to_region.insert(block_id, 1);
        }
        for block_id in 4..6 {
            block_to_region.insert(block_id, 0);
        }
        RegionTree {
            regions,
            root: 0,
            block_to_region,
        }
    }

    /// Build a CFG mock with `block_count` blocks. Block `sink_id` is the
    /// synthetic sink (empty opcodes). Other blocks default to one opcode
    /// at a synthetic address; override via `empty_blocks` to mark a
    /// block as having zero opcodes for the empty-content guard test.
    fn cfg_with_blocks(
        block_count: usize,
        sink_id: BlockId,
        empty_blocks: &[BlockId],
    ) -> ControlFlowGraph {
        let mut blocks = Vec::with_capacity(block_count);
        for id in 0..block_count {
            let opcodes = if id == sink_id || empty_blocks.contains(&id) {
                Vec::new()
            } else {
                vec![id * 0x10]
            };
            blocks.push(BasicBlock {
                id,
                start: id * 0x10,
                end: id * 0x10 + opcodes.len(),
                opcodes,
            });
        }
        ControlFlowGraph {
            blocks,
            successors: BTreeMap::new(),
            predecessors: BTreeMap::new(),
            entry: 0,
            sink: sink_id,
        }
    }

    #[test]
    fn fly_r1_predicate_fires() {
        let tree = fly_region_tree();
        let cfg = cfg_with_blocks(7, 6, &[]);
        // r1.exit = b0, not sink (b6). block_to_region[b0] = 1 = r1.
        // b0 has one opcode. Predicate should fire.
        assert!(is_own_exit_with_content(1, &tree, &cfg));
    }

    #[test]
    fn toggle_menu_r1_predicate_declines_sink_exit() {
        let tree = toggle_menu_region_tree();
        let cfg = cfg_with_blocks(6, 5, &[]);
        // r1.exit = b5 = the synthetic sink. Predicate should decline.
        assert!(!is_own_exit_with_content(1, &tree, &cfg));
    }

    #[test]
    fn fly_r0_predicate_declines_sink_exit() {
        let tree = fly_region_tree();
        let cfg = cfg_with_blocks(7, 6, &[]);
        // r0.exit = b6 = sink. Predicate should decline.
        assert!(!is_own_exit_with_content(0, &tree, &cfg));
    }

    #[test]
    fn predicate_declines_when_exit_owned_by_different_region() {
        // Mutated tree: r1.exit = b4, but block_to_region[b4] = 0 (not r1).
        let mut tree = fly_region_tree();
        tree.regions[1].exit = 4;
        let cfg = cfg_with_blocks(7, 6, &[]);
        assert!(!is_own_exit_with_content(1, &tree, &cfg));
    }

    #[test]
    fn predicate_declines_when_exit_block_empty() {
        let tree = fly_region_tree();
        // Mark b0 as having zero opcodes.
        let cfg = cfg_with_blocks(7, 6, &[0]);
        assert!(!is_own_exit_with_content(1, &tree, &cfg));
    }

    #[test]
    fn predicate_declines_for_missing_region() {
        let tree = fly_region_tree();
        let cfg = cfg_with_blocks(7, 6, &[]);
        assert!(!is_own_exit_with_content(99, &tree, &cfg));
    }
}
