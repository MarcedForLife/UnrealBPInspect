//! Unit tests for CFG construction, dominance, and reducibility.
//!
//! Each test constructs a hand-rolled `ControlFlowGraph` directly rather
//! than going through `build_cfg`, isolating dominance / reducibility
//! correctness from opcode-graph construction. A separate test exercises
//! `build_cfg` against a synthetic `OpcodeGraph` to confirm the leader
//! / edge wiring math.

use std::collections::{BTreeMap, BTreeSet};

use super::dom::{compute_dominators, compute_postdominators};
use super::reducibility::is_reducible;
use super::{BasicBlock, BlockId, ControlFlowGraph};

/// Build a synthetic CFG from a list of `(source, target)` edges. Block
/// ids are 0..node_count and a synthetic sink is appended at id
/// `node_count`. Every block with no outgoing edges in `edges` gains
/// an implicit edge to the sink, matching `build_cfg`'s production
/// behaviour. `start` and `end` are derived from id (one byte per
/// block); the dominance / reducibility code doesn't read those fields.
fn make_cfg(node_count: usize, edges: &[(BlockId, BlockId)]) -> ControlFlowGraph {
    let sink_id = node_count;
    let mut blocks: Vec<BasicBlock> = (0..=node_count)
        .map(|id| BasicBlock {
            id,
            start: id,
            end: id + 1,
            opcodes: if id == sink_id { Vec::new() } else { vec![id] },
        })
        .collect();
    blocks.sort_by_key(|block| block.id);

    let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for block in &blocks {
        successors.insert(block.id, Vec::new());
        predecessors.insert(block.id, Vec::new());
    }
    let mut has_outgoing: BTreeSet<BlockId> = BTreeSet::new();
    for &(source, target) in edges {
        successors.entry(source).or_default().push(target);
        predecessors.entry(target).or_default().push(source);
        has_outgoing.insert(source);
    }
    // Wire every non-sink block without outgoing edges to the sink.
    for block_id in 0..node_count {
        if !has_outgoing.contains(&block_id) {
            successors.entry(block_id).or_default().push(sink_id);
            predecessors.entry(sink_id).or_default().push(block_id);
        }
    }

    ControlFlowGraph {
        blocks,
        successors,
        predecessors,
        entry: 0,
        sink: sink_id,
    }
}

#[test]
fn dominators_diamond() {
    // 0 -> 1, 2 ; 1 -> 3 ; 2 -> 3
    let cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let dominators = compute_dominators(&cfg);
    assert_eq!(dominators.get(&1), Some(&0));
    assert_eq!(dominators.get(&2), Some(&0));
    assert_eq!(dominators.get(&3), Some(&0));
    assert!(!dominators.contains_key(&0));
}

#[test]
fn dominators_chain() {
    // 0 -> 1 -> 2 -> 3
    let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
    let dominators = compute_dominators(&cfg);
    assert_eq!(dominators.get(&1), Some(&0));
    assert_eq!(dominators.get(&2), Some(&1));
    assert_eq!(dominators.get(&3), Some(&2));
}

#[test]
fn dominators_loop() {
    // 0 -> 1 -> 2 -> 1 (back edge) ; 2 -> 3
    let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 1), (2, 3)]);
    let dominators = compute_dominators(&cfg);
    assert_eq!(dominators.get(&1), Some(&0));
    assert_eq!(dominators.get(&2), Some(&1));
    assert_eq!(dominators.get(&3), Some(&2));
}

#[test]
fn dominators_nested_if() {
    // 0 -> 1, 2 ; 1 -> 4 ; 2 -> 3, 4 ; 3 -> 4
    let cfg = make_cfg(5, &[(0, 1), (0, 2), (1, 4), (2, 3), (2, 4), (3, 4)]);
    let dominators = compute_dominators(&cfg);
    assert_eq!(dominators.get(&1), Some(&0));
    assert_eq!(dominators.get(&2), Some(&0));
    assert_eq!(dominators.get(&3), Some(&2));
    assert_eq!(dominators.get(&4), Some(&0));
}

#[test]
fn postdominators_diamond() {
    // 0 -> 1, 2 ; 1 -> 3 ; 2 -> 3 ; 3 is the join, then implicit
    // edge to the synthetic sink.
    let cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let postdominators = compute_postdominators(&cfg);
    assert_eq!(postdominators.get(&0), Some(&3));
    assert_eq!(postdominators.get(&1), Some(&3));
    assert_eq!(postdominators.get(&2), Some(&3));
    // Block 3 post-dominates 0, 1, 2 but its own ipostdom is the
    // synthetic sink.
    assert_eq!(postdominators.get(&3), Some(&cfg.sink));
    assert!(!postdominators.contains_key(&cfg.sink));
}

#[test]
fn postdominators_two_returns() {
    // 0 -> 1, 2 ; 1 and 2 are real leaves. With the synthetic sink
    // wired up, both 1 and 2 reach the sink directly, and ipostdom(0)
    // = sink. The sink itself is excluded from the returned map (it
    // is its own post-dominator root); blocks 1 and 2 each map to it.
    let cfg = make_cfg(3, &[(0, 1), (0, 2)]);
    let postdominators = compute_postdominators(&cfg);
    assert_eq!(postdominators.get(&0), Some(&cfg.sink));
    assert_eq!(postdominators.get(&1), Some(&cfg.sink));
    assert_eq!(postdominators.get(&2), Some(&cfg.sink));
    assert!(!postdominators.contains_key(&cfg.sink));
}

#[test]
fn reducible_diamond_is_reducible() {
    let cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
    assert!(is_reducible(&cfg));
}

#[test]
fn reducible_natural_loop_is_reducible() {
    // 0 -> 1 -> 2 -> 1 (back edge) ; 2 -> 3
    let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 1), (2, 3)]);
    assert!(is_reducible(&cfg));
}

#[test]
fn irreducible_two_entry_loop() {
    // Classic irreducible (multi-entry loop):
    //   0 -> 1, 2
    //   1 -> 2
    //   2 -> 1
    // Both 1 and 2 are loop entries; neither dominates the other.
    let cfg = make_cfg(3, &[(0, 1), (0, 2), (1, 2), (2, 1)]);
    assert!(!is_reducible(&cfg));
}

#[test]
fn build_cfg_simple_diamond() {
    use crate::bytecode::opcodes::{EX_JUMP, EX_JUMP_IF_NOT, EX_NOTHING};
    use crate::bytecode::partition::OpcodeGraph;

    // Synthetic opcode graph: addresses 0, 10, 20, 30, 40 are opcode
    // boundaries with opcodes NOTHING, JUMP_IF_NOT, NOTHING, JUMP,
    // NOTHING (the join). JUMP_IF_NOT branches to 30 with fallthrough
    // 20; JUMP at 20 jumps to 40.
    let mut boundaries: BTreeSet<usize> = BTreeSet::new();
    let mut successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut opcodes: BTreeMap<usize, u8> = BTreeMap::new();
    for &addr in &[0usize, 10, 20, 30, 40] {
        boundaries.insert(addr);
    }
    opcodes.insert(0, EX_NOTHING);
    opcodes.insert(10, EX_JUMP_IF_NOT);
    opcodes.insert(20, EX_NOTHING);
    opcodes.insert(30, EX_JUMP);
    opcodes.insert(40, EX_NOTHING);

    successors.insert(0, vec![10]);
    successors.insert(10, vec![30, 20]);
    successors.insert(20, vec![40]);
    successors.insert(30, vec![40]);
    successors.insert(40, vec![]);

    let graph = OpcodeGraph {
        boundaries,
        successors,
        opcodes,
        flow_frames: Vec::new(),
    };
    #[allow(clippy::single_range_in_vec_init)]
    let owned: Vec<std::ops::Range<usize>> = vec![0..50];

    let cfg = super::build::build_cfg(&graph, 0, &owned);
    // 4 real blocks plus the synthetic sink.
    assert_eq!(cfg.blocks.len(), 5);
    assert_eq!(cfg.sink, 4);
    let real_starts: Vec<usize> = cfg
        .blocks
        .iter()
        .filter(|block| block.id != cfg.sink)
        .map(|block| block.start)
        .collect();
    assert_eq!(real_starts, vec![0, 20, 30, 40]);
    // Entry block contains the conditional jump opcode at the end.
    assert_eq!(cfg.blocks[0].opcodes, vec![0, 10]);
    // The sink has no opcodes and is the only block past the real ids.
    assert!(cfg.blocks[cfg.sink].opcodes.is_empty());

    // Confirm dominance / reducibility on the built CFG. The sink is
    // dominated by the only real leaf (block 40 = id 3), so the
    // dominator map has one entry per real non-entry block plus the
    // sink: 4 entries.
    let dominators = compute_dominators(&cfg);
    assert_eq!(dominators.len(), 4);
    assert!(is_reducible(&cfg));
}
