//! T1/T2 reducibility check.
//!
//! T1 (self-loop removal): drop any edge `n -> n`.
//! T2 (single-predecessor collapse): if `n` has exactly one predecessor
//! `p`, merge `n` into `p`. `p` inherits every outgoing edge of `n`
//! except the (already-dropped) `n -> p` back-edge if it existed.
//!
//! Repeat until no transformation fires. The CFG is reducible iff a
//! single node remains. Unreachable nodes do not exist in our CFGs
//! (build_cfg restricts to forward-reachable from entry), so the
//! "single connected component" qualifier from the textbook holds
//! automatically.

use std::collections::{BTreeMap, BTreeSet};

use super::{BlockId, ControlFlowGraph};

/// True iff `cfg` is reducible under T1/T2 transformations.
///
/// An empty CFG (no blocks) is treated as reducible. A CFG with one
/// block, even with a self-loop, is reducible. A CFG with multiple
/// blocks is reducible iff repeated T1/T2 collapse all of them into one.
pub fn is_reducible(cfg: &ControlFlowGraph) -> bool {
    let mut successors: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    let mut predecessors: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();

    // Seed the working graph with every block (even those without
    // outgoing edges, so they participate in T2 collapse from their
    // predecessor side).
    for block in &cfg.blocks {
        successors.insert(block.id, BTreeSet::new());
        predecessors.insert(block.id, BTreeSet::new());
    }
    for (&source, targets) in &cfg.successors {
        for &target in targets {
            successors.entry(source).or_default().insert(target);
            predecessors.entry(target).or_default().insert(source);
        }
    }

    let mut changed = true;
    while changed {
        changed = false;

        // T1: drop every self-loop.
        let nodes: Vec<BlockId> = successors.keys().copied().collect();
        for node in nodes {
            if successors
                .get(&node)
                .map(|edges| edges.contains(&node))
                .unwrap_or(false)
            {
                if let Some(edges) = successors.get_mut(&node) {
                    edges.remove(&node);
                }
                if let Some(edges) = predecessors.get_mut(&node) {
                    edges.remove(&node);
                }
                changed = true;
            }
        }

        // T2: collapse any node with exactly one predecessor INTO that
        // predecessor. Iterate a snapshot so collapsing one node mid-loop
        // doesn't invalidate iteration order.
        let candidates: Vec<BlockId> = successors.keys().copied().collect();
        for node in candidates {
            if !successors.contains_key(&node) {
                continue;
            }
            let preds = predecessors.get(&node).cloned().unwrap_or_default();
            if preds.len() != 1 {
                continue;
            }
            let parent = *preds.iter().next().expect("exactly one predecessor");
            if parent == node {
                continue;
            }
            merge_node_into(&mut successors, &mut predecessors, node, parent);
            changed = true;
        }
    }

    successors.len() <= 1
}

/// Fold `child`'s outgoing edges into `parent` and delete `child` from
/// the working graph. Caller has already established that `child`'s only
/// predecessor is `parent`.
fn merge_node_into(
    successors: &mut BTreeMap<BlockId, BTreeSet<BlockId>>,
    predecessors: &mut BTreeMap<BlockId, BTreeSet<BlockId>>,
    child: BlockId,
    parent: BlockId,
) {
    // 1. Drop the parent -> child edge.
    if let Some(parent_succs) = successors.get_mut(&parent) {
        parent_succs.remove(&child);
    }

    // 2. Pull child's outgoing edges into parent's. Update child's
    //    successors' predecessor sets to point at parent instead.
    let child_succs = successors.remove(&child).unwrap_or_default();
    predecessors.remove(&child);
    for succ in child_succs {
        if let Some(succ_preds) = predecessors.get_mut(&succ) {
            succ_preds.remove(&child);
            // If parent already has this edge, the predecessor set
            // gains a duplicate-via-set (no-op). If not, both sides
            // gain a fresh edge.
            succ_preds.insert(parent);
        }
        successors.entry(parent).or_default().insert(succ);
        // A new self-loop on `parent` from `child -> parent` after the
        // merge is left in place; the next T1 iteration deletes it.
    }
}
