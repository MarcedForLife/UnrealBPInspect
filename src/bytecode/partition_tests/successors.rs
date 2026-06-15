//! Successor-edge tests for `build_opcode_graph` plus high-level BFS
//! reachability and partitioner tie-breaking. These exercise the graph
//! construction layer that BFS later rides over.

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::{bfs_reachable, build_opcode_graph, PartitionError};
use std::collections::BTreeMap;

// EX_JUMP successor edges.
#[test]
fn successors_jump() {
    let stream = jump_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    let succs = graph.successors.get(&0).expect("EX_JUMP at offset 0");
    assert_eq!(succs, &[5usize], "EX_JUMP must have one target");
}

// EX_JUMP_IF_NOT successor edges (target + fallthrough).
#[test]
fn successors_jump_if_not() {
    let stream = cond_jump_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0)
        .expect("EX_JUMP_IF_NOT at offset 0");
    assert!(succs.contains(&7), "must include explicit target 7");
    assert!(succs.contains(&6), "must include linear fallthrough 6");
    assert_eq!(succs.len(), 2);
}

// EX_PUSH_EXECUTION_FLOW successor edges.
#[test]
fn successors_push_execution_flow() {
    let stream = push_flow_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0)
        .expect("EX_PUSH_EXECUTION_FLOW at offset 0");
    assert!(succs.contains(&6), "push target 6");
    assert!(succs.contains(&5), "linear fallthrough 5");
}

// EX_RETURN is a terminator.
#[test]
fn successors_return_is_terminator() {
    let stream = two_returns_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    let succs = graph.successors.get(&0).expect("EX_RETURN at offset 0");
    assert!(
        succs.is_empty(),
        "EX_RETURN must be a terminator; got {:?}",
        succs
    );
}

// EX_END_OF_SCRIPT is a terminator.
#[test]
fn successors_end_of_script_is_terminator() {
    let bytecode_stream = stream(&[EX_END_OF_SCRIPT]);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode_stream, 0, &nt, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0)
        .expect("EX_END_OF_SCRIPT at offset 0");
    assert!(succs.is_empty(), "EX_END_OF_SCRIPT must be a terminator");
}

// EX_POP_EXECUTION_FLOW is a terminator.
#[test]
fn successors_pop_execution_flow_is_terminator() {
    let bytecode_stream = stream(&[EX_POP_EXECUTION_FLOW]);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode_stream, 0, &nt, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0)
        .expect("EX_POP_EXECUTION_FLOW at offset 0");
    assert!(
        succs.is_empty(),
        "EX_POP_EXECUTION_FLOW must be a terminator"
    );
}

// BFS visits all addresses reachable from each event entry.
#[test]
fn bfs_two_event_reachability() {
    let stream = two_event_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    let reachable_a = bfs_reachable(0, &graph);
    assert!(reachable_a.contains(&0), "A must reach its own entry");
    assert!(reachable_a.contains(&6), "A must reach its jump target");
    assert!(
        !reachable_a.contains(&5),
        "A must not reach B-only offset 5"
    );

    let reachable_b = bfs_reachable(5, &graph);
    assert!(reachable_b.contains(&5), "B must reach its own entry");
    assert!(reachable_b.contains(&6), "B must reach shared tail");
}

// Lowest-offset event wins the tie on shared opcodes.
#[test]
fn tie_break_lowest_offset_event_wins() {
    let stream = two_event_stream();
    let entries = make_entries(&[("EventA", 0), ("EventB", 5)]);
    let nt = empty_name_table();

    let result = partition_ubergraph(&stream, &entries, &nt, 0).unwrap();

    let ranges_a = result.get("EventA").expect("EventA in output");
    assert!(
        ranges_a.iter().any(|r| r.contains(&6)),
        "shared offset 6 must be owned by EventA"
    );

    let ranges_b = result.get("EventB").expect("EventB in output");
    assert!(
        !ranges_b.iter().any(|r| r.contains(&6)),
        "EventB must not own shared offset 6"
    );
}

// Mid-instruction jump target produces JumpToMidInstruction.
#[test]
fn mid_instruction_jump_errors() {
    // EX_JUMP occupies offsets 0..5; offset 2 is mid-instruction.
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(2)); // target = offset 2 (not a boundary)
    stream.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let entries = make_entries(&[("Evt", 0)]);

    let result = partition_ubergraph(&stream, &entries, &nt, 0);
    assert!(
        matches!(result, Err(PartitionError::JumpToMidInstruction { .. })),
        "expected JumpToMidInstruction, got {:?}",
        result.map(|_| ())
    );
}

// Empty event_entries returns NoEventEntries.
#[test]
fn empty_event_entries_errors() {
    let bytecode_stream = stream(&[EX_END_OF_SCRIPT]);
    let nt = empty_name_table();
    let result = partition_ubergraph(&bytecode_stream, &[], &nt, 0);
    assert!(
        matches!(result, Err(PartitionError::NoEventEntries)),
        "expected NoEventEntries"
    );
}

// Entry not on opcode boundary returns EntryNotOpcodeBoundary.
#[test]
fn entry_not_on_boundary_errors() {
    // EX_JUMP is 5 bytes; offset 2 is inside it.
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(5));
    stream.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let entries = make_entries(&[("Evt", 2)]);

    let result = partition_ubergraph(&stream, &entries, &nt, 0);
    assert!(
        matches!(result, Err(PartitionError::EntryNotOpcodeBoundary { .. })),
        "expected EntryNotOpcodeBoundary"
    );
}

// Property test: every byte position is owned by at most one event.
#[test]
fn no_opcode_in_two_events_ranges() {
    let stream = two_event_stream();
    let entries = make_entries(&[("EventA", 0), ("EventB", 5)]);
    let nt = empty_name_table();

    let result = partition_ubergraph(&stream, &entries, &nt, 0).unwrap();

    let mut covered: BTreeMap<usize, String> = BTreeMap::new();
    for (name, ranges) in &result {
        for range in ranges {
            for byte_pos in range.clone() {
                let prev = covered.insert(byte_pos, name.clone());
                assert!(
                    prev.is_none(),
                    "byte {} covered by both '{}' and '{}'",
                    byte_pos,
                    name,
                    prev.unwrap()
                );
            }
        }
    }
}

// Push/pop propagation: BFS from offset 0 reaches both the linear body
// AND the push target (across the execution-flow edge). EX_POP_EXECUTION_FLOW
// is a terminator, so the pop opcode itself is reachable but produces no
// successors of its own.
//
// Stream layout:
//   offset 0: EX_PUSH_EXECUTION_FLOW → target=6  (5 bytes: 1 opcode + 4 target)
//   offset 5: EX_NOTHING (1 byte, linear body after push)
//   offset 6: EX_POP_EXECUTION_FLOW (1 byte, push target — terminator)
#[test]
fn push_pop_flow_propagation() {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
    stream.extend_from_slice(&u32_le(6)); // push target at offset 6
    stream.push(EX_NOTHING); // linear body at offset 5
    stream.push(EX_POP_EXECUTION_FLOW); // push target at offset 6

    let nt = empty_name_table();
    let entries = make_entries(&[("Evt", 0)]);

    let result = partition_ubergraph(&stream, &entries, &nt, 0).unwrap();
    let ranges = result.get("Evt").expect("Evt must appear in output");

    // The event must own offset 0 (entry), 5 (linear body), and 6 (push target).
    assert!(
        ranges.iter().any(|r| r.contains(&0)),
        "must own entry offset 0"
    );
    assert!(
        ranges.iter().any(|r| r.contains(&5)),
        "must own linear body at offset 5"
    );
    assert!(
        ranges.iter().any(|r| r.contains(&6)),
        "must own push target at offset 6 (propagation across push edge)"
    );
}
