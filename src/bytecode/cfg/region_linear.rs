//! Post-merge Linear-region synthesis.
//!
//! After the base SESE region tree is built, walks the tree in postorder
//! and synthesises a Linear sibling region for each branch-kind region
//! whose exit block carries opcodes but is innermost-owned by a strict
//! descendant.
//!
//! The rule's purpose is to surface post-merge content for the
//! `IfThenElse -> IfThenElse -> IfThenElse` chain whose merge block
//! falls inside a byte-sliced descendant, without disturbing the BP
//! IsValid-macro dual-role pattern or SequenceChain pin walks.
//!
//! Wired into production decode via the
//! `build_region_tree_with_linear_merges` entry point (`decode/mod.rs`
//! and `k2node_byte_map.rs` build their region trees through it).

use std::collections::{BTreeMap, BTreeSet};

use super::region::{Region, RegionId, RegionKind, RegionTree};
use super::{reachable_bounded, BlockId, BoundedReach, ControlFlowGraph};

/// Synthesise post-merge Linear sibling regions in `tree`.
///
/// Walks regions in postorder so that nested triggers fire from the
/// leaves up. For each region R that matches every filter, allocates a
/// new `Linear(M, R.parent.exit)` sibling positioned immediately after
/// R under R's parent, then reassigns `block_to_region[b]` for every
/// block transitively reachable from M without crossing R.parent.exit.
///
/// Returns the ids of newly-added Linear regions for divergence logging.
pub(crate) fn extract_post_merge_linears(
    tree: &mut RegionTree,
    cfg: &ControlFlowGraph,
) -> Vec<RegionId> {
    let mut added: Vec<RegionId> = Vec::new();
    let order = postorder(tree);
    for region_id in order {
        if let Some(new_id) = try_extract_linear(tree, cfg, region_id) {
            added.push(new_id);
        }
    }
    added
}

/// Apply the rule once for `region_id`. Returns the new Linear region's
/// id when synthesis fires, `None` otherwise.
fn try_extract_linear(
    tree: &mut RegionTree,
    cfg: &ControlFlowGraph,
    region_id: RegionId,
) -> Option<RegionId> {
    let region = tree.regions.get(region_id)?;
    let merge_block = region.exit;
    if merge_block == cfg.sink {
        return None;
    }
    if cfg.blocks.get(merge_block)?.opcodes.is_empty() {
        return None;
    }
    if !is_branch_kind(region.kind) {
        return None;
    }
    let parent_id = region.parent?;
    let parent_exit = tree.regions.get(parent_id)?.exit;

    // Guard 1: skip degenerate (M == R.parent.exit).
    //
    // When the merge block is already the parent's exit, it belongs to
    // R.parent's structural scope; the parent (or its ancestor) is
    // responsible for surfacing it. Synthesising a Linear sibling of R
    // would produce a degenerate entry==exit region with nothing to
    // contribute.
    if parent_exit == merge_block {
        return None;
    }

    let owner = *tree.block_to_region.get(&merge_block)?;
    if owner == region_id {
        // Within-region merges are already handled elsewhere.
        return None;
    }
    if !is_strict_descendant(tree, region_id, owner) {
        // Merge sits in ancestor / sibling scope; out-of-bounds for us.
        return None;
    }

    // Guard 2: skip cascade (owner is already RegionKind::Linear).
    //
    // Catches both pre-existing Linear owners and Linears synthesised
    // earlier in this same pass. Postorder visits descendants first, so
    // any Linear that legitimately fires for M does so on the strict
    // descendant of R that triggered it; promoting again at an ancestor
    // R would re-fire on the freshly-synthesised Linear and produce a
    // cascade of redundant siblings up the tree.
    if tree.regions.get(owner)?.kind == RegionKind::Linear {
        return None;
    }
    if find_same_entry_inner_sibling(tree, region_id).is_some() {
        // R is the outer wrap of a BP-macro dual-role; R is deferred to
        // its inner sibling. Don't double-handle.
        return None;
    }

    // Guard 3: skip when the merge block is itself a branch head whose
    // content already belongs to an existing sibling region.
    //
    // A genuine post-merge join converges and continues linearly: it has
    // a single CFG successor. When M instead has multiple successors it is
    // a nested branch's entry (a fork), not a convergence point. In one
    // observed shape, M is the entry block of an
    // existing sibling region S (`S.parent == R.parent`, `S.entry == M`):
    // a second unconditional if/else that follows R's first-if. M is
    // only innermost-owned by a deeper descendant of R because that
    // descendant's slice reaches back up to M; S, the region for which M
    // is the structural entry, owns none of its own entry block.
    //
    // Synthesising a flat Linear here steals S's arm blocks and emits its
    // bodies unconditionally. Bounding the slice would leave S with no
    // entry. The correct repair is to give M back to S so S surfaces as a
    // normal sibling after R: reassign M to S and decline flat synthesis.
    // `mark_region_consumed(R)` then no longer sweeps M (it left R's
    // subtree), and the disk-order walk emits S with M as its preamble.
    if !merge_is_true_join(cfg, merge_block) {
        if let Some(sibling_id) = sibling_region_with_entry(tree, region_id, merge_block) {
            tree.block_to_region.insert(merge_block, sibling_id);
            return None;
        }
    }

    let new_id = tree.regions.len();
    let new_region = Region {
        id: new_id,
        entry: merge_block,
        exit: parent_exit,
        parent: Some(parent_id),
        children: Vec::new(),
        kind: RegionKind::Linear,
    };
    tree.regions.push(new_region);

    insert_child_after(tree, parent_id, region_id, new_id);

    let blocks_to_move = collect_slice(cfg, merge_block, parent_exit);
    reassign_blocks(tree, &blocks_to_move, new_id, parent_exit);

    Some(new_id)
}

/// Find a sibling of `region_id` (same parent) whose entry block is
/// `merge_block`. That sibling is the structural region the merge block
/// heads; reassigning the block to it lets the disk-order walk surface it
/// after `region_id` instead of stealing it into a flat Linear.
fn sibling_region_with_entry(
    tree: &RegionTree,
    region_id: RegionId,
    merge_block: BlockId,
) -> Option<RegionId> {
    let parent_id = tree.regions.get(region_id)?.parent?;
    let parent = tree.regions.get(parent_id)?;
    parent.children.iter().copied().find(|&child_id| {
        child_id != region_id
            && tree
                .regions
                .get(child_id)
                .is_some_and(|child| child.entry == merge_block)
    })
}

/// True iff `merge_block` is a genuine convergence point (at most one CFG
/// successor) rather than the head of a nested branch.
///
/// The synthesised Linear region slices from M with the parent's exit as
/// the only boundary. That slice is correct only when M continues
/// linearly toward the exit. When M forks, the slice would cross into a
/// nested branch's arms and steal blocks owned by that branch region.
fn merge_is_true_join(cfg: &ControlFlowGraph, merge_block: BlockId) -> bool {
    cfg.successors
        .get(&merge_block)
        .map(|succs| succs.len() <= 1)
        .unwrap_or(true)
}

/// True iff `region.kind` is one of the arm-byte-slicing branch kinds.
///
/// SequenceChain, DoOnceGate, Loop, Linear, Trivial decode via pin walks
/// or full block walks and surface their children normally without
/// byte-slicing, so they don't trigger the merge-block drop the rule
/// fixes.
fn is_branch_kind(kind: RegionKind) -> bool {
    matches!(
        kind,
        RegionKind::IfThen | RegionKind::IfThenElse | RegionKind::Switch
    )
}

/// True iff `candidate` is a strict descendant of `ancestor` in the
/// region tree. Walks `candidate.parent` chain; returns true when
/// `ancestor` is reached before the root and `candidate != ancestor`.
fn is_strict_descendant(tree: &RegionTree, ancestor: RegionId, candidate: RegionId) -> bool {
    if candidate == ancestor {
        return false;
    }
    let mut cursor = tree.regions.get(candidate).and_then(|region| region.parent);
    while let Some(parent_id) = cursor {
        if parent_id == ancestor {
            return true;
        }
        cursor = tree.regions.get(parent_id).and_then(|region| region.parent);
    }
    false
}

/// Equivalent of `region_decode::find_same_entry_inner_sibling`.
///
/// Returns the child region of `region_id` that shares R's entry block,
/// signalling the BP IsValid-macro dual-role wrap pattern. Duplicated
/// here so the cfg crate doesn't depend on the decoder; the consumer
/// implementation in `region_decode.rs` retains identical semantics.
fn find_same_entry_inner_sibling(tree: &RegionTree, region_id: RegionId) -> Option<RegionId> {
    let region = tree.regions.get(region_id)?;
    let entry = region.entry;
    region.children.iter().copied().find(|&child_id| {
        tree.regions
            .get(child_id)
            .is_some_and(|child| child.entry == entry && child_id != region_id)
    })
}

/// Insert `new_id` into `parent.children` immediately after `after_id`.
fn insert_child_after(
    tree: &mut RegionTree,
    parent_id: RegionId,
    after_id: RegionId,
    new_id: RegionId,
) {
    let parent = &mut tree.regions[parent_id];
    let position = parent
        .children
        .iter()
        .position(|&child| child == after_id)
        .map(|index| index + 1)
        .unwrap_or(parent.children.len());
    parent.children.insert(position, new_id);
}

/// Postorder traversal of the region tree.
fn postorder(tree: &RegionTree) -> Vec<RegionId> {
    let mut order: Vec<RegionId> = Vec::with_capacity(tree.regions.len());
    let mut visit_stack: Vec<(RegionId, bool)> = vec![(tree.root, false)];
    while let Some((node, expanded)) = visit_stack.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        visit_stack.push((node, true));
        if let Some(region) = tree.regions.get(node) {
            for &child in &region.children {
                visit_stack.push((child, false));
            }
        }
    }
    order
}

/// All blocks reachable from `entry` in `cfg` without crossing `boundary`,
/// plus `boundary` itself when it is a successor of any visited block.
fn collect_slice(cfg: &ControlFlowGraph, entry: BlockId, boundary: BlockId) -> BTreeSet<BlockId> {
    reachable_bounded(
        cfg,
        entry,
        boundary,
        BoundedReach {
            skip_sink: false,
            include_boundary: false,
        },
    )
}

/// Reassign `tree.block_to_region` for every block in `slice` to
/// `new_owner`, except `boundary` which stays with its current owner
/// (it is the enclosing region's exit, not part of the Linear sibling).
fn reassign_blocks(
    tree: &mut RegionTree,
    slice: &BTreeSet<BlockId>,
    new_owner: RegionId,
    boundary: BlockId,
) {
    let mut updates: BTreeMap<BlockId, RegionId> = BTreeMap::new();
    for &block_id in slice {
        if block_id == boundary {
            continue;
        }
        updates.insert(block_id, new_owner);
    }
    for (block_id, owner) in updates {
        tree.block_to_region.insert(block_id, owner);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::cfg::region::Region;
    use std::collections::BTreeMap;

    fn mini_tree() -> RegionTree {
        // Build a tiny tree by hand:
        //   r0 IfThenElse(entry=0, exit=7)
        //     r1 IfThenElse(entry=0, exit=3)
        //       r2 IfThenElse(entry=1, exit=3)
        let regions = vec![
            Region {
                id: 0,
                entry: 0,
                exit: 7,
                parent: None,
                children: vec![1],
                kind: RegionKind::IfThenElse,
            },
            Region {
                id: 1,
                entry: 0,
                exit: 3,
                parent: Some(0),
                children: vec![2],
                kind: RegionKind::IfThenElse,
            },
            Region {
                id: 2,
                entry: 1,
                exit: 3,
                parent: Some(1),
                children: vec![],
                kind: RegionKind::IfThenElse,
            },
        ];
        let mut block_to_region: BTreeMap<BlockId, RegionId> = BTreeMap::new();
        block_to_region.insert(0, 1);
        block_to_region.insert(1, 2);
        block_to_region.insert(2, 2);
        block_to_region.insert(3, 2);
        block_to_region.insert(4, 1);
        block_to_region.insert(5, 2);
        block_to_region.insert(6, 0);
        block_to_region.insert(7, 0);
        RegionTree {
            regions,
            root: 0,
            block_to_region,
        }
    }

    #[test]
    fn strict_descendant_walks_parent_chain() {
        let tree = mini_tree();
        assert!(is_strict_descendant(&tree, 1, 2));
        assert!(is_strict_descendant(&tree, 0, 2));
        assert!(is_strict_descendant(&tree, 0, 1));
        assert!(!is_strict_descendant(&tree, 2, 1));
        assert!(!is_strict_descendant(&tree, 1, 1));
    }

    #[test]
    fn same_entry_inner_sibling_finds_dual_role() {
        let tree = mini_tree();
        // r0 and r1 share entry b0: r0's child r1 has the same entry.
        assert_eq!(find_same_entry_inner_sibling(&tree, 0), Some(1));
        // r1's only child r2 has entry b1, not b0.
        assert_eq!(find_same_entry_inner_sibling(&tree, 1), None);
    }

    #[test]
    fn insert_child_after_preserves_order() {
        let mut tree = mini_tree();
        tree.regions.push(Region {
            id: 3,
            entry: 3,
            exit: 7,
            parent: Some(0),
            children: vec![],
            kind: RegionKind::Linear,
        });
        insert_child_after(&mut tree, 0, 1, 3);
        // r0's children should be [1, 3] (1 was the only entry, 3 was
        // inserted after it).
        assert_eq!(tree.regions[0].children, vec![1, 3]);
    }
}
