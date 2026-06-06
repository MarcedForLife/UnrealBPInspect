//! Unit tests for SESE region decomposition.
//!
//! Each test constructs a synthetic CFG (and a synthetic `OpcodeGraph`
//! when the kind classifier needs opcode bytes) and asserts the shape
//! of the resulting `RegionTree`. Decomposition correctness is verified
//! through three lenses: per-region entry/exit values, region-kind
//! classification, and block-to-innermost-region assignment.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::opcodes::{EX_JUMP, EX_JUMP_IF_NOT, EX_NOTHING, EX_RETURN, EX_SWITCH_VALUE};
use crate::bytecode::partition::OpcodeGraph;

use super::dom::{compute_dominators, compute_postdominators};
use super::region::{build_region_tree, RegionKind};
use super::{BasicBlock, BlockId, ControlFlowGraph};

/// Build a synthetic CFG from edge list plus optional per-block
/// terminator opcode bytes. Block `i` occupies addresses `i*10..(i+1)*10`
/// with one opcode at `i*10`. A synthetic sink is appended at id
/// `node_count`, with implicit edges from every real leaf, mirroring
/// the contract `build_cfg` produces.
fn make_cfg_with_opcodes(
    node_count: usize,
    edges: &[(BlockId, BlockId)],
    terminator_opcodes: &BTreeMap<BlockId, u8>,
) -> (ControlFlowGraph, OpcodeGraph) {
    let sink_id = node_count;
    let sink_addr = node_count * 10;
    let mut blocks: Vec<BasicBlock> = (0..node_count)
        .map(|id| BasicBlock {
            id,
            start: id * 10,
            end: id * 10 + 10,
            opcodes: vec![id * 10],
        })
        .collect();
    blocks.push(BasicBlock {
        id: sink_id,
        start: sink_addr,
        end: sink_addr,
        opcodes: Vec::new(),
    });

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
    for block_id in 0..node_count {
        if !has_outgoing.contains(&block_id) {
            successors.entry(block_id).or_default().push(sink_id);
            predecessors.entry(sink_id).or_default().push(block_id);
        }
    }

    let cfg = ControlFlowGraph {
        blocks,
        successors,
        predecessors,
        entry: 0,
        sink: sink_id,
    };

    let mut boundaries: BTreeSet<usize> = BTreeSet::new();
    let mut opcodes: BTreeMap<usize, u8> = BTreeMap::new();
    let mut graph_successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for block_id in 0..node_count {
        let addr = block_id * 10;
        boundaries.insert(addr);
        // Real successors only -- the synthetic sink isn't part of
        // the opcode graph. A leaf-block default opcode reads as
        // EX_RETURN regardless of whether its only successor is the
        // sink.
        let real_succs: Vec<BlockId> = cfg
            .successors
            .get(&block_id)
            .map(|edges| {
                edges
                    .iter()
                    .copied()
                    .filter(|target| *target != cfg.sink)
                    .collect()
            })
            .unwrap_or_default();
        let default_op = if real_succs.len() >= 2 {
            EX_JUMP_IF_NOT
        } else if real_succs.is_empty() {
            EX_RETURN
        } else {
            EX_NOTHING
        };
        let op = terminator_opcodes
            .get(&block_id)
            .copied()
            .unwrap_or(default_op);
        opcodes.insert(addr, op);
        let succs: Vec<usize> = real_succs.iter().map(|target| target * 10).collect();
        graph_successors.insert(addr, succs);
    }
    let graph = OpcodeGraph {
        boundaries,
        successors: graph_successors,
        opcodes,
        flow_frames: Vec::new(),
    };
    (cfg, graph)
}

fn make_cfg(node_count: usize, edges: &[(BlockId, BlockId)]) -> (ControlFlowGraph, OpcodeGraph) {
    make_cfg_with_opcodes(node_count, edges, &BTreeMap::new())
}

#[test]
fn diamond_yields_ifthenelse_root() {
    // 0 -> 1, 2 ; 1 -> 3 ; 2 -> 3
    let (cfg, graph) = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let root = &tree.regions[tree.root];
    assert_eq!(root.entry, 0);
    // Root spans entry to the synthetic sink; block 3 is the inner
    // join and shows up as its own region.
    assert_eq!(root.exit, cfg.sink);
    assert_eq!(root.kind, RegionKind::IfThenElse);
    let inner = tree
        .regions
        .iter()
        .find(|region| region.entry == 0 && region.exit == 3);
    // The branching block always pairs with its real ipostdom too.
    assert!(
        inner.is_some() || root.exit == 3,
        "expected an (0, 3) region as a child of the root"
    );
}

#[test]
fn chain_yields_linear_root() {
    // 0 -> 1 -> 2 -> 3
    let mut terminators: BTreeMap<BlockId, u8> = BTreeMap::new();
    terminators.insert(0, EX_NOTHING);
    terminators.insert(1, EX_NOTHING);
    terminators.insert(2, EX_NOTHING);
    terminators.insert(3, EX_RETURN);
    let (cfg, graph) = make_cfg_with_opcodes(4, &[(0, 1), (1, 2), (2, 3)], &terminators);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let root = &tree.regions[tree.root];
    assert_eq!(root.kind, RegionKind::Linear);
    // Every block is assigned to the only existing region (the root).
    for block_id in 0..4 {
        assert_eq!(tree.block_to_region.get(&block_id), Some(&tree.root));
    }
}

#[test]
fn natural_loop_yields_loop_kind() {
    // 0 -> 1 ; 1 -> 2, 3 ; 2 -> 1 (back-edge) ; 3 = exit
    let (cfg, graph) = make_cfg(4, &[(0, 1), (1, 2), (1, 3), (2, 1)]);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let loop_region = tree
        .regions
        .iter()
        .find(|region| region.kind == RegionKind::Loop)
        .expect("at least one Loop region");
    assert_eq!(loop_region.entry, 1);
}

#[test]
fn nested_diamond_inside_diamond() {
    // Outer diamond 0 -> {1, 2} -> 5
    //   Inner diamond on the 1-arm: 1 -> {3, 4} -> 5
    //   2 -> 5 directly.
    //
    // Blocks: 0 (branch), 1 (branch), 2, 3, 4, 5 (join).
    let (cfg, graph) = make_cfg(6, &[(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let root = &tree.regions[tree.root];
    assert_eq!(root.entry, 0);
    // Root spans entry to the synthetic sink and classifies by the
    // entry's branching shape.
    assert_eq!(root.kind, RegionKind::IfThenElse);

    let inner = tree
        .regions
        .iter()
        .find(|region| region.entry == 1)
        .expect("inner region rooted at block 1");
    assert_eq!(inner.kind, RegionKind::IfThenElse);
    // The inner region descends from the root through the
    // entry-block branching candidate (0, 5). Walk the parent chain
    // and make sure the root is on it.
    let mut cursor = inner.parent;
    let mut reached_root = false;
    while let Some(parent_id) = cursor {
        if parent_id == tree.root {
            reached_root = true;
            break;
        }
        cursor = tree.regions[parent_id].parent;
    }
    assert!(
        reached_root,
        "inner region must descend from the root, parent chain didn't reach it"
    );
}

#[test]
fn switch_three_cases() {
    // 0 -> 1, 2, 3 ; all converge at 4.
    let mut terminators: BTreeMap<BlockId, u8> = BTreeMap::new();
    terminators.insert(0, EX_SWITCH_VALUE);
    let (cfg, graph) = make_cfg_with_opcodes(
        5,
        &[(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)],
        &terminators,
    );
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let root = &tree.regions[tree.root];
    // Root spans entry to the synthetic sink and is classified by
    // the entry terminator (EX_SWITCH_VALUE).
    assert_eq!(root.kind, RegionKind::Switch);
    assert_eq!(root.entry, 0);
    assert_eq!(root.exit, cfg.sink);
    // The branching-block candidate (0, 4) is captured as an inner
    // region nested inside the root.
    let inner = tree
        .regions
        .iter()
        .find(|region| region.entry == 0 && region.exit == 4)
        .expect("inner switch-body region present");
    assert_eq!(inner.parent, Some(tree.root));
}

#[test]
fn if_then_one_arm_skips_to_exit() {
    // 0 -> 1, 2 ; 1 -> 2 (then-body); 2 = post-dom (fall-through arm).
    let (cfg, graph) = make_cfg(3, &[(0, 1), (0, 2), (1, 2)]);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    // The if-then pairing lives on the inner (branching, ipostdom)
    // candidate: (0, 2). The root pair is (0, sink) and reads as
    // IfThenElse because neither immediate successor of 0 is the
    // sink.
    let inner = tree
        .regions
        .iter()
        .find(|region| region.entry == 0 && region.exit == 2)
        .expect("inner if-then region present");
    assert_eq!(inner.kind, RegionKind::IfThen);
    let root = &tree.regions[tree.root];
    assert_eq!(root.entry, 0);
    assert_eq!(root.exit, cfg.sink);
}

#[test]
fn block_to_region_innermost_assignment() {
    // Outer 0 -> {1, 2} -> 5; inner 1 -> {3, 4} -> 5.
    // Block 3 and 4 should belong to the inner region rooted at 1.
    let (cfg, graph) = make_cfg(6, &[(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let inner_id = tree
        .regions
        .iter()
        .find(|region| region.entry == 1)
        .map(|region| region.id)
        .expect("inner region present");
    assert_eq!(tree.block_to_region.get(&3), Some(&inner_id));
    assert_eq!(tree.block_to_region.get(&4), Some(&inner_id));
    // Block 2 lives on the outer-diamond 2-arm. With the synthetic
    // sink, the outer diamond shows up as an intermediate region
    // (0, 5) nested under the (0, sink) root. Block 2 must belong
    // to that intermediate region, not the root.
    let outer_id = tree
        .regions
        .iter()
        .find(|region| region.entry == 0 && region.exit == 5)
        .map(|region| region.id)
        .expect("outer (0, 5) region present");
    assert_eq!(tree.block_to_region.get(&2), Some(&outer_id));
}

#[test]
fn unused_opcodes_dont_change_classification() {
    // Sanity: JUMP and RETURN don't accidentally classify as branch.
    let mut terminators: BTreeMap<BlockId, u8> = BTreeMap::new();
    terminators.insert(0, EX_JUMP);
    terminators.insert(1, EX_RETURN);
    let (cfg, graph) = make_cfg_with_opcodes(2, &[(0, 1)], &terminators);
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);

    let tree = build_region_tree(&cfg, &idom, &ipostdom, &graph);
    let root = &tree.regions[tree.root];
    assert_eq!(root.kind, RegionKind::Linear);
}
