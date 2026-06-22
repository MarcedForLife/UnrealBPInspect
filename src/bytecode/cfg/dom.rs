//! Dominator and post-dominator analysis over a `ControlFlowGraph`.
//!
//! Uses the Cooper-Harvey-Kennedy iterative algorithm
//! ("A Simple, Fast Dominance Algorithm", 2001). The algorithm is O(N^2)
//! worst-case but linear in practice on reducible CFGs, and far simpler
//! to implement and audit than Lengauer-Tarjan. CFG sizes here are at
//! most a few hundred blocks per event, so quadratic behaviour is not
//! a concern.
//!
//! Public entry points:
//! - `compute_dominators` returns the immediate-dominator map.
//! - `compute_postdominators` reverses the CFG and runs the same
//!   algorithm starting from the synthetic sink (`cfg.sink`).

use std::collections::{BTreeMap, BTreeSet};

use super::{BlockId, ControlFlowGraph};

/// Borrow-only view over an immediate-dominator (or immediate-post-dominator)
/// map for walking a node's ancestor chain.
///
/// `compute_dominators` / `compute_postdominators` return the chain with the
/// root excluded (the root self-map is stripped), so [`DomChain::ancestors`]
/// terminates on the first absent key. It additionally guards against a
/// self-map (`parent == node`) and any repeated node, so a malformed map
/// cannot spin forever.
pub(crate) struct DomChain<'a>(pub &'a BTreeMap<BlockId, BlockId>);

impl DomChain<'_> {
    /// Strict ancestors of `node`, innermost first, excluding `node`.
    /// Empty when `node` is the root or absent from the map.
    pub(crate) fn ancestors(&self, node: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        let mut cursor = node;
        let mut seen = BTreeSet::from([node]);
        std::iter::from_fn(move || {
            let &parent = self.0.get(&cursor)?;
            if parent == cursor || !seen.insert(parent) {
                return None;
            }
            cursor = parent;
            Some(parent)
        })
    }
}

/// Compute the immediate-dominator map for `cfg`.
///
/// The entry block has no immediate dominator and is absent from the
/// returned map. Every other reachable block maps to its idom. Blocks
/// unreachable from the entry are also absent.
pub fn compute_dominators(cfg: &ControlFlowGraph) -> BTreeMap<BlockId, BlockId> {
    let post_order = reverse_postorder(&cfg.successors, cfg.entry, cfg.blocks.len());
    iterative_dominators(cfg.entry, &post_order, &cfg.predecessors)
}

/// Compute the immediate-post-dominator map for `cfg`.
///
/// The CFG has a synthetic sink (`cfg.sink`) wired up so every real
/// leaf has an edge to it. The reverse CFG therefore has a single
/// entry (the sink) and Cooper-Harvey-Kennedy produces a well-defined
/// ipostdom for every block. The sink itself is excluded from the
/// returned map (it is its own post-dominator root), but every other
/// block reachable from `cfg.entry` is present.
pub fn compute_postdominators(cfg: &ControlFlowGraph) -> BTreeMap<BlockId, BlockId> {
    let (rev_successors, rev_predecessors) = build_reverse_cfg(cfg);
    let post_order = reverse_postorder(&rev_successors, cfg.sink, cfg.blocks.len());
    let mut raw = iterative_dominators(cfg.sink, &post_order, &rev_predecessors);
    // Drop the sink's self-mapping; callers want real ipostdom entries.
    raw.remove(&cfg.sink);
    raw
}

/// Build the reverse CFG, simply by swapping every edge of `cfg`.
/// Every block (including the sink) gets an entry in both maps so the
/// downstream traversal does not need to special-case absent keys.
fn build_reverse_cfg(
    cfg: &ControlFlowGraph,
) -> (
    BTreeMap<BlockId, Vec<BlockId>>,
    BTreeMap<BlockId, Vec<BlockId>>,
) {
    let mut rev_successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut rev_predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();

    for block in &cfg.blocks {
        rev_successors.insert(block.id, Vec::new());
        rev_predecessors.insert(block.id, Vec::new());
    }

    for block in &cfg.blocks {
        let succs = cfg
            .successors
            .get(&block.id)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        for &succ in succs {
            rev_successors.entry(succ).or_default().push(block.id);
            rev_predecessors.entry(block.id).or_default().push(succ);
        }
    }

    (rev_successors, rev_predecessors)
}

/// Reverse-postorder DFS from `root` over `successors`. Returns nodes in
/// reverse order of DFS finish time, i.e. nodes nearer the entry come
/// first. Unreachable nodes are omitted.
///
/// `node_capacity` bounds the `visited` vector and must be greater than
/// every BlockId that can appear in `successors`. The Cooper-Harvey
/// inner loop iterates this list, skipping the root.
fn reverse_postorder(
    successors: &BTreeMap<BlockId, Vec<BlockId>>,
    root: BlockId,
    node_capacity: usize,
) -> Vec<BlockId> {
    let mut visited = vec![false; node_capacity];
    let mut finished: Vec<BlockId> = Vec::new();
    let mut stack: Vec<(BlockId, usize)> = Vec::new();

    if root >= visited.len() {
        return finished;
    }
    visited[root] = true;
    stack.push((root, 0));

    while let Some(&(node, child_index)) = stack.last() {
        let children = successors.get(&node).map(|v| v.as_slice()).unwrap_or(&[]);
        if child_index < children.len() {
            let last = stack.last_mut().expect("stack non-empty");
            *last = (node, child_index + 1);
            let child = children[child_index];
            if child < visited.len() && !visited[child] {
                visited[child] = true;
                stack.push((child, 0));
            }
        } else {
            stack.pop();
            finished.push(node);
        }
    }
    finished.reverse();
    finished
}

/// Cooper-Harvey-Kennedy iterative dominators.
///
/// `post_order` is the reverse-postorder list of reachable nodes (root
/// first). `predecessors` maps each block to its predecessor list.
/// Returns the idom map with the root excluded.
fn iterative_dominators(
    root: BlockId,
    post_order: &[BlockId],
    predecessors: &BTreeMap<BlockId, Vec<BlockId>>,
) -> BTreeMap<BlockId, BlockId> {
    let mut rpo_index: BTreeMap<BlockId, usize> = BTreeMap::new();
    for (index, &node) in post_order.iter().enumerate() {
        rpo_index.insert(node, index);
    }

    // dom[n] = idom(n); the root maps to itself by convention. We strip
    // that mapping before returning.
    let mut dom: BTreeMap<BlockId, BlockId> = BTreeMap::new();
    dom.insert(root, root);

    let mut changed = true;
    while changed {
        changed = false;
        for &node in post_order
            .iter()
            .skip_while(|&&entry| entry != root)
            .skip(1)
        {
            let preds = predecessors
                .get(&node)
                .map(|edges| edges.as_slice())
                .unwrap_or(&[]);
            let mut new_idom: Option<BlockId> = None;
            for &pred in preds {
                if !dom.contains_key(&pred) {
                    continue;
                }
                new_idom = Some(match new_idom {
                    None => pred,
                    Some(current) => intersect(&dom, &rpo_index, pred, current),
                });
            }
            if let Some(candidate) = new_idom {
                let existing = dom.get(&node).copied();
                if existing != Some(candidate) {
                    dom.insert(node, candidate);
                    changed = true;
                }
            }
        }
    }

    dom.remove(&root);
    dom
}

/// Walk up the dominator tree from each of `finger_a` and `finger_b`
/// until they meet. Per Cooper-Harvey-Kennedy: walk whichever finger is
/// FURTHER from the root in reverse-postorder (larger rpo index) one
/// step up the tree, until both fingers agree.
fn intersect(
    dom: &BTreeMap<BlockId, BlockId>,
    rpo_index: &BTreeMap<BlockId, usize>,
    mut finger_a: BlockId,
    mut finger_b: BlockId,
) -> BlockId {
    while finger_a != finger_b {
        let a_index = rpo_index.get(&finger_a).copied().unwrap_or(usize::MAX);
        let b_index = rpo_index.get(&finger_b).copied().unwrap_or(usize::MAX);
        if a_index > b_index {
            let next = dom.get(&finger_a).copied().unwrap_or(finger_a);
            if next == finger_a {
                return finger_a;
            }
            finger_a = next;
        } else {
            let next = dom.get(&finger_b).copied().unwrap_or(finger_b);
            if next == finger_b {
                return finger_b;
            }
            finger_b = next;
        }
    }
    finger_a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ancestors_yields_innermost_first_excluding_node() {
        // 3 -> 2 -> 1 -> 0(root, absent).
        let idom = BTreeMap::from([(1, 0), (2, 1), (3, 2)]);
        let chain = DomChain(&idom);
        assert_eq!(chain.ancestors(3).collect::<Vec<_>>(), vec![2, 1, 0]);
        assert_eq!(chain.ancestors(3).count(), 3);
    }

    #[test]
    fn ancestors_of_root_or_absent_node_is_empty() {
        let idom = BTreeMap::from([(1, 0)]);
        let chain = DomChain(&idom);
        assert_eq!(chain.ancestors(0).count(), 0); // root, absent from map
        assert_eq!(chain.ancestors(42).count(), 0); // unreachable, absent
    }

    #[test]
    fn ancestors_terminates_on_self_map_and_cycle() {
        // Self-map at the root yields nothing past it.
        let self_map = BTreeMap::from([(1, 1)]);
        assert_eq!(DomChain(&self_map).ancestors(1).count(), 0);
        // A malformed 2-cycle stops once the repeat is seen, never spins.
        let cycle = BTreeMap::from([(1, 2), (2, 1)]);
        assert_eq!(DomChain(&cycle).ancestors(1).collect::<Vec<_>>(), vec![2]);
    }
}
