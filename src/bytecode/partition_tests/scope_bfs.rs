//! Tests for `bfs_reachable_with_scope` (scope-aware BFS that admits
//! back-edges only when the seed sits inside the loop scope).

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::{
    back_edges_in_range, bfs_reachable_with_scope, build_opcode_graph, LoopScopes, PartitionCtx,
};
use std::collections::BTreeMap;

/// Sanity-check `nested_loop_stream` boundaries match the docstring.
#[test]
fn scope_bfs_nested_loop_stream_layout() {
    let bytecode = nested_loop_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    for &addr in &[0x00, 0x01, 0x02, 0x08, 0x0D, 0x13, 0x18, 0x19, 0x1E] {
        assert!(
            graph.boundaries.contains(&addr),
            "expected boundary at 0x{:02x}; boundaries = {:?}",
            addr,
            graph.boundaries
        );
    }
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(scopes.get(&0x01).copied(), Some(0x0D), "inner scope");
    assert_eq!(scopes.get(&0x00).copied(), Some(0x18), "outer scope");
}

/// Behavior 2: a seed inside the loop scope traverses the back-edge
/// to the loop head and revisits body addresses (no rejection).
#[test]
fn scope_bfs_seed_inside_admits_back_edge() {
    let bytecode = nested_loop_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());

    // Seed at the inner head: inside both scopes.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0x01, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    // Inner head + inner body + inner JUMP (back-edge instr).
    assert!(reached.contains(&0x01), "inner head reached");
    assert!(reached.contains(&0x02), "inner body reached");
    assert!(reached.contains(&0x08), "inner JUMP reached");
    // Outer head reached via the outer back-edge from 0x13.
    assert!(reached.contains(&0x00), "outer head reached via back-edge");
}

/// Behavior 3: a seed outside the loop scope can reach the back-edge
/// instruction via a forward path, but the back-edge edge itself is
/// rejected, so the loop head stays out of the reachable set.
#[test]
fn scope_bfs_seed_outside_rejects_back_edge() {
    let bytecode = nested_loop_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());

    // Sibling seed at 0x18 (post-outer, outside both scopes). The
    // contrived JUMP at 0x19 forwards into 0x08 (the inner back-edge
    // JUMP); without scope-awareness the BFS would walk 0x08 -> 0x01
    // and pull in the entire inner loop body. Scope-aware BFS rejects.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0x18, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    assert!(reached.contains(&0x18), "sibling seed reached itself");
    assert!(reached.contains(&0x19), "sibling forward JUMP instruction");
    assert!(
        reached.contains(&0x08),
        "back-edge JUMP instr is reachable forward from sibling seed"
    );
    assert!(
        !reached.contains(&0x01),
        "inner head must NOT be reached via the back-edge from outside the scope"
    );
    assert!(
        !reached.contains(&0x02),
        "inner body must NOT be reached via the back-edge from outside the scope"
    );
}

/// Behavior 4: seed inside both nested scopes admits both back-edges
/// when reachable.
#[test]
fn scope_bfs_seed_inside_nested_admits_both_back_edges() {
    let bytecode = nested_loop_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());

    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0x01, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    // Inner back-edge admitted -> head 0x01 stays in result.
    assert!(
        reached.contains(&0x01),
        "inner head reachable via back-edge"
    );
    // Outer back-edge admitted -> head 0x00 reached.
    assert!(
        reached.contains(&0x00),
        "outer head reachable via back-edge"
    );
}

/// Behavior 5: seed outside both nested scopes can't reach either
/// loop head via back-edges.
#[test]
fn scope_bfs_seed_outside_nested_blocks_both_back_edges() {
    let bytecode = nested_loop_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());

    // Same sibling seed as behavior 3; it can reach the inner JUMP
    // forward but not the inner head, and it has no path to the
    // outer JUMP at 0x13 either, so the outer head also stays out.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0x18, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    assert!(!reached.contains(&0x01), "inner head blocked");
    assert!(!reached.contains(&0x00), "outer head blocked");
}

/// Behavior 6: a forward break-out edge (an `EX_JUMP` from inside
/// the loop to past `loop_exit`) propagates regardless of seed
/// position. This exercises the "forward edge always admits" rule.
#[test]
fn scope_bfs_break_out_forward_edge_propagates() {
    // Layout:
    //   0x00: EX_NOTHING                              (loop head)
    //   0x01: EX_JUMP_IF_NOT 0x0C [cond=EX_NOTHING]   (6 bytes -> 0x07; break)
    //   0x07: EX_JUMP 0x00                            (5 bytes -> 0x0C; back-edge)
    //   0x0C: EX_NOTHING                              (post-loop, break target)
    //   0x0D: EX_END_OF_SCRIPT
    let mut bytecode = Vec::new();
    bytecode.push(EX_NOTHING); // 0x00
    bytecode.push(EX_JUMP_IF_NOT); // 0x01
    bytecode.extend_from_slice(&u32_le(0x0C));
    bytecode.push(EX_NOTHING); // cond at 0x06
    bytecode.push(EX_JUMP); // 0x07
    bytecode.extend_from_slice(&u32_le(0x00));
    bytecode.push(EX_NOTHING); // 0x0C
    bytecode.push(EX_END_OF_SCRIPT); // 0x0D
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    // Sanity: scope is [0x00, 0x0C); 0x0C is the break target.
    assert_eq!(scopes.get(&0x00).copied(), Some(0x0C));

    // Seed at 0x00 (inside the scope): reaches both the back-edge
    // (admitted because seed is inside) and the break target 0x0C.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached_inside =
        bfs_reachable_with_scope(0x00, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    assert!(reached_inside.contains(&0x0C), "break target reachable");
    assert!(
        reached_inside.contains(&0x00),
        "head reachable (back-edge admitted)"
    );

    // Seed at 0x0C (outside the scope): legacy BFS at 0x0C just walks
    // forward to EOS; the break-out edge isn't reachable from this
    // seed, but a forward jump that DID land at the break target
    // would be admitted. Sanity-check: forward propagation works.
    let reached_outside =
        bfs_reachable_with_scope(0x0C, vec![], 0, &ctx, 0..bytecode.len(), &scopes, None);
    assert!(reached_outside.contains(&0x0C));
    assert!(reached_outside.contains(&0x0D));
    assert!(
        !reached_outside.contains(&0x00),
        "outside seed must not reach the loop head"
    );
}

/// Behavior 7: addresses outside `boundary` are not added to the
/// reachable set, regardless of scope. The boundary filter the
/// existing partition pipeline applies post-BFS is folded into
/// the scope-aware BFS itself.
#[test]
fn scope_bfs_boundary_clips_reach() {
    // Stream: EX_NOTHING; EX_NOTHING; EX_END_OF_SCRIPT (3 bytes).
    let bytecode = vec![EX_NOTHING, EX_NOTHING, EX_END_OF_SCRIPT];
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let empty: LoopScopes = BTreeMap::new();

    // Boundary [0, 2): excludes EOS at 0x02. BFS from 0 fallthroughs
    // to 1, would normally fallthrough to 2, but boundary clips.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0x00, vec![], 0, &ctx, 0..2, &empty, None);
    assert!(reached.contains(&0x00));
    assert!(reached.contains(&0x01));
    assert!(
        !reached.contains(&0x02),
        "addr outside boundary must not appear; got {:?}",
        reached
    );
}

/// Behavior 8: PUSH/POP stack rules with empty scopes. A focused
/// PUSH/POP stream verifies that BFS pushes the operand on PUSH and
/// resumes at the popped continuation on POP, terminating when the
/// stack would drop below `baseline_depth`.
#[test]
fn scope_bfs_stack_rules_push_pop() {
    use std::collections::BTreeSet;
    // Layout:
    //   0x00: EX_PUSH_EXECUTION_FLOW (5 bytes)  target=0x06
    //   0x05: EX_POP_EXECUTION_FLOW  (1 byte)
    //   0x06: EX_END_OF_SCRIPT        (1 byte; push target)
    let mut bytecode = vec![EX_PUSH_EXECUTION_FLOW];
    bytecode.extend_from_slice(&u32_le(6));
    bytecode.push(EX_POP_EXECUTION_FLOW);
    bytecode.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());
    let empty: LoopScopes = BTreeMap::new();

    // Seed at 0x00 with empty stack: BFS pushes 0x06, falls through
    // to 0x05, pops, resumes at 0x06.
    let ctx = PartitionCtx {
        graph: &graph,
        arm_boundaries: &[],
    };
    let reached = bfs_reachable_with_scope(0, vec![], 0, &ctx, 0..bytecode.len(), &empty, None);
    let expected: BTreeSet<usize> = [0x00, 0x05, 0x06].into_iter().collect();
    assert_eq!(reached, expected, "PUSH/POP fallthrough+pop reachability");

    // With an initial stack and matching baseline_depth, the POP at
    // 0x05 lands on the supplied continuation (also 0x06) and the
    // depth drops back to baseline rather than below it.
    let initial_stack = vec![0x06usize];
    let reached_stacked = bfs_reachable_with_scope(
        0,
        initial_stack.clone(),
        initial_stack.len(),
        &ctx,
        0..bytecode.len(),
        &empty,
        None,
    );
    assert_eq!(
        reached_stacked, expected,
        "PUSH/POP with initial_stack reaches the same set"
    );
}
