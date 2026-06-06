//! POP-resume edges in the opcode graph.
//!
//! `EX_POP_EXECUTION_FLOW` terminates linear flow without an explicit
//! operand-derived target: at runtime it pops the most recently pushed
//! continuation off the flow stack and resumes there. `build_opcode_graph`
//! resolves the pairing statically by walking each `EX_PUSH_EXECUTION_FLOW`
//! site, tracking a simulated stack depth from the pushed target, and
//! adding a successor edge from each paired POP to the push's fallthrough.
//!
//! Without these edges, POP-terminated basic blocks become CFG leaves
//! whose only successor is the synthetic sink, which collapses SESE
//! region exit endpoints onto the sink and breaks arm-extent semantics
//! for branches whose body terminates with a POP (DoOnce, IsValid, the
//! displaced-body shape the compiler emits for if/else with `push X`
//! in the then-arm).
//!
//! These tests synthesise minimal `EX_PUSH_EXECUTION_FLOW -> body ->
//! EX_POP_EXECUTION_FLOW` shapes and verify (a) the paired POP records
//! a successor edge to the push's fallthrough, (b) BFS over the graph
//! reaches the fallthrough through the body's POP, (c) nested PUSH
//! sites pair the inner POP only with the inner PUSH.

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::{bfs_reachable, build_opcode_graph, FlowFrame};
use std::collections::BTreeMap;

/// Build:
/// ```text
///   0x00: EX_PUSH_EXECUTION_FLOW target=0x0A
///   0x05: EX_NOTHING                              (fallthrough)
///   0x06: EX_NOTHING
///   0x07: EX_NOTHING
///   0x08: EX_NOTHING
///   0x09: EX_END_OF_SCRIPT
///   0x0A: EX_NOTHING                              (push target / body head)
///   0x0B: EX_POP_EXECUTION_FLOW
/// ```
///
/// Runtime: push 0x05 onto the stack, jump to 0x0A, run the body, POP
/// at 0x0B resumes at 0x05. Without the resume edge, BFS from 0x00 via
/// `graph.successors` reaches 0x0A and 0x0B but the body-side POP has
/// no edges, so the fallthrough chain past 0x05 is unreachable through
/// the body path.
fn push_pop_body_stream() -> Vec<u8> {
    let mut bytecode = Vec::new();
    bytecode.push(EX_PUSH_EXECUTION_FLOW); // 0x00
    bytecode.extend_from_slice(&u32_le(0x0A)); // pushed target
    bytecode.push(EX_NOTHING); // 0x05 — fallthrough head
    bytecode.push(EX_NOTHING); // 0x06
    bytecode.push(EX_NOTHING); // 0x07
    bytecode.push(EX_NOTHING); // 0x08
    bytecode.push(EX_END_OF_SCRIPT); // 0x09
    bytecode.push(EX_NOTHING); // 0x0A — body head
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x0B
    bytecode
}

#[test]
fn pop_resume_adds_successor_edge() {
    let stream = push_pop_body_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0x0B)
        .expect("EX_POP_EXECUTION_FLOW at 0x0B must have a successor entry");
    assert!(
        succs.contains(&0x05),
        "POP at 0x0B must record resume target 0x05 (push fallthrough); got {:?}",
        succs
    );
}

#[test]
fn pop_resume_extends_bfs_reach_through_body() {
    let stream = push_pop_body_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    let reachable = bfs_reachable(0, &graph);
    for addr in [0x00, 0x05, 0x0A, 0x0B] {
        assert!(
            reachable.contains(&addr),
            "BFS must reach 0x{:x}; got {:?}",
            addr,
            reachable
        );
    }
}

/// Build a nested push/pop where the body itself contains a push/pop:
/// ```text
///   0x00: EX_PUSH_EXECUTION_FLOW target=0x0A         (outer)
///   0x05: EX_NOTHING                                  (outer fallthrough)
///   0x06: EX_END_OF_SCRIPT
///   0x07: EX_NOTHING                                  (inner fallthrough)
///   0x08: EX_POP_EXECUTION_FLOW                       (outer POP)
///   0x09: EX_NOTHING                                  (filler)
///   0x0A: EX_PUSH_EXECUTION_FLOW target=0x10         (inner)
///   0x0F: EX_POP_EXECUTION_FLOW                       (inner POP)
///   0x10: EX_NOTHING                                  (inner body)
///   0x11: EX_POP_EXECUTION_FLOW                       (inner body POP)
/// ```
///
/// Wait, this is getting hairy. Simpler: just verify the depth gate by
/// using TWO push sites in sequence and confirming each POP only pairs
/// with its own PUSH's fallthrough.
fn two_push_two_pop_stream() -> Vec<u8> {
    let mut bytecode = Vec::new();
    // PUSH A at 0x00 -> target=0x14, fallthrough=0x05
    bytecode.push(EX_PUSH_EXECUTION_FLOW); // 0x00
    bytecode.extend_from_slice(&u32_le(0x14));
    // 0x05: PUSH B target=0x18, fallthrough=0x0A
    bytecode.push(EX_PUSH_EXECUTION_FLOW); // 0x05
    bytecode.extend_from_slice(&u32_le(0x18));
    bytecode.push(EX_NOTHING); // 0x0A
    bytecode.push(EX_END_OF_SCRIPT); // 0x0B
    while bytecode.len() < 0x14 {
        bytecode.push(EX_NOTHING); // filler
    }
    bytecode.push(EX_NOTHING); // 0x14 — A's body head
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x15 — A's POP (pairs with A)
    bytecode.push(EX_NOTHING); // 0x16
    bytecode.push(EX_NOTHING); // 0x17
    bytecode.push(EX_NOTHING); // 0x18 — B's body head
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x19 — B's POP (pairs with B)
    bytecode
}

#[test]
fn pop_resume_pairs_each_pop_with_own_push() {
    let stream = two_push_two_pop_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    let succs_a = graph
        .successors
        .get(&0x15)
        .expect("POP at 0x15 must have successors");
    assert!(
        succs_a.contains(&0x05),
        "POP at 0x15 must resume at A's fallthrough 0x05; got {:?}",
        succs_a
    );

    let succs_b = graph
        .successors
        .get(&0x19)
        .expect("POP at 0x19 must have successors");
    assert!(
        succs_b.contains(&0x0A),
        "POP at 0x19 must resume at B's fallthrough 0x0A; got {:?}",
        succs_b
    );
}

/// FlowFrame persistence on the single push/pop body stream. The frame
/// records the push at 0x00, its body head 0x0A, the matching POP at
/// 0x0B, and the resumed fallthrough 0x05.
#[test]
fn flow_frame_single_push_pop() {
    let stream = push_pop_body_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    assert_eq!(
        graph.flow_frames,
        vec![FlowFrame {
            push_addr: 0x00,
            pop_addr: 0x0B,
            pushed_target: 0x0A,
            fallthrough: 0x05,
        }],
        "single push/pop must yield exactly one frame"
    );
}

/// FlowFrame persistence on the sequential two-push/two-pop stream. Each
/// push pairs with its own depth-1 POP; the frames are ordered by push
/// address (the producer iterates pushes in ascending order).
#[test]
fn flow_frame_sequential_pushes() {
    let stream = two_push_two_pop_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    assert_eq!(
        graph.flow_frames,
        vec![
            FlowFrame {
                push_addr: 0x00,
                pop_addr: 0x15,
                pushed_target: 0x14,
                fallthrough: 0x05,
            },
            FlowFrame {
                push_addr: 0x05,
                pop_addr: 0x19,
                pushed_target: 0x18,
                fallthrough: 0x0A,
            },
        ],
        "two sequential pushes must yield two frames, one per push"
    );
}

/// FlowFrame persistence on a nested push/pop. The outer push body
/// forks on a `EX_JUMP_IF_NOT`: the fall-through arm reaches the outer
/// POP at depth 1, the taken arm contains a fully self-contained inner
/// push/pop. The depth gate must pair the inner POP with the inner PUSH
/// and the outer POP with the outer PUSH, never cross them. Crossing the
/// inner PUSH would bump the simulated depth to 2, which is exactly why
/// the inner push lives on the arm that does NOT lead to the outer POP.
///
/// ```text
///   0x00: EX_PUSH_EXECUTION_FLOW target=0x0A    (outer; fallthrough 0x05)
///   0x05: EX_NOTHING                             (outer fallthrough head)
///   0x06: EX_END_OF_SCRIPT
///   ...filler to 0x0A...
///   0x0A: EX_JUMP_IF_NOT target=0x16 cond=TRUE   (body head; 6 bytes -> 0x10)
///   0x10: EX_POP_EXECUTION_FLOW                   (outer POP; depth 1)
///   0x11: EX_END_OF_SCRIPT
///   ...filler to 0x16...
///   0x16: EX_PUSH_EXECUTION_FLOW target=0x1C     (inner; fallthrough 0x1B)
///   0x1B: EX_END_OF_SCRIPT                        (inner fallthrough dead end)
///   0x1C: EX_NOTHING                              (inner body head)
///   0x1D: EX_POP_EXECUTION_FLOW                   (inner POP; depth 1 for inner)
/// ```
fn nested_push_pop_stream() -> Vec<u8> {
    let mut bytecode = Vec::new();
    bytecode.push(EX_PUSH_EXECUTION_FLOW); // 0x00 — outer
    bytecode.extend_from_slice(&u32_le(0x0A)); // outer target
    bytecode.push(EX_NOTHING); // 0x05 — outer fallthrough head
    bytecode.push(EX_END_OF_SCRIPT); // 0x06
    while bytecode.len() < 0x0A {
        bytecode.push(EX_NOTHING); // filler 0x07..0x0A
    }
    bytecode.push(EX_JUMP_IF_NOT); // 0x0A — body fork
    bytecode.extend_from_slice(&u32_le(0x16)); // taken arm -> inner region
    bytecode.push(EX_TRUE); // condition (1 byte) -> next opcode at 0x10
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x10 — outer POP
    bytecode.push(EX_END_OF_SCRIPT); // 0x11
    while bytecode.len() < 0x16 {
        bytecode.push(EX_NOTHING); // filler 0x12..0x16
    }
    bytecode.push(EX_PUSH_EXECUTION_FLOW); // 0x16 — inner
    bytecode.extend_from_slice(&u32_le(0x1C)); // inner target
    bytecode.push(EX_END_OF_SCRIPT); // 0x1B — inner fallthrough dead end
    bytecode.push(EX_NOTHING); // 0x1C — inner body head
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x1D — inner POP
    bytecode
}

#[test]
fn flow_frame_nested_pushes() {
    let stream = nested_push_pop_stream();
    let names = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &names, &BTreeMap::new());

    let mut frames = graph.flow_frames.clone();
    frames.sort_by_key(|frame| frame.push_addr);
    assert_eq!(
        frames,
        vec![
            FlowFrame {
                push_addr: 0x00,
                pop_addr: 0x10,
                pushed_target: 0x0A,
                fallthrough: 0x05,
            },
            FlowFrame {
                push_addr: 0x16,
                pop_addr: 0x1D,
                pushed_target: 0x1C,
                fallthrough: 0x1B,
            },
        ],
        "nested pushes must pair each POP with its own depth-1 PUSH"
    );
}

/// A stream with no PUSH sites: POP (if present) should remain edgeless.
/// Confirms the post-pass is a no-op when there's nothing to pair.
#[test]
fn pop_without_push_keeps_no_resume_edge() {
    let bytecode = vec![
        EX_POP_EXECUTION_FLOW, // 0x00
        EX_END_OF_SCRIPT,      // 0x01
    ];

    let names = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &names, &BTreeMap::new());

    let succs = graph.successors.get(&0x00).cloned().unwrap_or_default();
    assert!(
        succs.is_empty(),
        "POP at 0x00 with no paired PUSH must have no successors; got {:?}",
        succs
    );
}
