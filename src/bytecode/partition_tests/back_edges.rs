//! Tests for `back_edges_in_range` (loop-scope detection from the
//! opcode graph).

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::{back_edges_in_range, build_opcode_graph};
use std::collections::BTreeMap;

/// No back-edges in a forward-only stream returns an empty map.
#[test]
fn back_edges_no_back_edges_returns_empty() {
    // EX_JUMP at 0 forward to 5; EX_END_OF_SCRIPT at 5.
    let mut bytecode = vec![EX_JUMP];
    bytecode.extend_from_slice(&u32_le(5));
    bytecode.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert!(
        scopes.is_empty(),
        "forward-only jump must not be recorded; got {:?}",
        scopes
    );
}

/// Single EX_JUMP back-edge produces one scope keyed by target.
#[test]
fn back_edges_single_jump_back_edge() {
    // Layout:
    //   0x00: EX_NOTHING (loop head)
    //   0x01: EX_JUMP -> 0x00 (5 bytes; back-edge)
    //   0x06: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_NOTHING];
    bytecode.push(EX_JUMP);
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(scopes.len(), 1, "expected one scope, got {:?}", scopes);
    let exit = scopes.get(&0).copied().expect("loop head 0");
    // back_edge_pos=1, jump_size=5, so exit = 6.
    assert_eq!(exit, 6, "exit must be back_edge_pos + jump_size = 6");
}

/// EX_JUMP_IF_NOT back-edge produces the same shape as EX_JUMP.
#[test]
fn back_edges_jump_if_not_back_edge() {
    // Layout:
    //   0x00: EX_NOTHING (loop head)
    //   0x01: EX_JUMP_IF_NOT -> 0x00 [cond=EX_NOTHING] (6 bytes; back-edge)
    //   0x07: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_NOTHING];
    bytecode.push(EX_JUMP_IF_NOT);
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_NOTHING); // condition expression
    bytecode.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(scopes.len(), 1, "expected one scope, got {:?}", scopes);
    let exit = scopes.get(&0).copied().expect("loop head 0");
    // back_edge_pos=1, JIN total size=6, so exit = 7.
    assert_eq!(
        exit, 7,
        "exit must be back_edge_pos + JIN_size = 7; got {exit}"
    );
}

/// Forward jump is not recorded even when other back-edges exist.
#[test]
fn back_edges_forward_jump_not_recorded() {
    // Layout:
    //   0x00: EX_JUMP -> 0x06 (5 bytes; forward, NOT recorded)
    //   0x05: EX_NOTHING
    //   0x06: EX_JUMP -> 0x05 (5 bytes; back-edge, recorded)
    //   0x0B: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_JUMP];
    bytecode.extend_from_slice(&u32_le(6));
    bytecode.push(EX_NOTHING); // 0x05
    bytecode.push(EX_JUMP); // 0x06
    bytecode.extend_from_slice(&u32_le(5));
    bytecode.push(EX_END_OF_SCRIPT);
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    // Only the back-edge at 0x06 (target 0x05) appears; the forward
    // jump at 0x00 is filtered out.
    assert_eq!(
        scopes.len(),
        1,
        "expected only the back-edge, got {:?}",
        scopes
    );
    assert!(scopes.contains_key(&5), "loop head at 0x05 must be present");
    assert!(
        !scopes.contains_key(&6),
        "forward-jump target must not be a loop head"
    );
}

/// Two back-edges to the same head collapse to one scope; exit is
/// the max of `back_edge_pos + jump_size` over all back-edges.
#[test]
fn back_edges_multiple_to_same_head_max_exit() {
    // Layout:
    //   0x00: EX_NOTHING (loop head)
    //   0x01: EX_JUMP -> 0x00 (5 bytes; back-edge #1, exit = 6)
    //   0x06: EX_NOTHING
    //   0x07: EX_JUMP -> 0x00 (5 bytes; back-edge #2, exit = 12)
    //   0x0C: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_NOTHING]; // 0x00
    bytecode.push(EX_JUMP); // 0x01
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_NOTHING); // 0x06
    bytecode.push(EX_JUMP); // 0x07
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_END_OF_SCRIPT); // 0x0C
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(
        scopes.len(),
        1,
        "two back-edges to one head must collapse to one scope; got {:?}",
        scopes
    );
    let exit = scopes.get(&0).copied().expect("loop head 0");
    assert_eq!(exit, 12, "exit must be max(6, 12) = 12; got {exit}");
}

/// Two distinct loops produce two scopes with non-overlapping spans.
#[test]
fn back_edges_two_distinct_loops() {
    // Layout (two adjacent self-loops):
    //   0x00: EX_NOTHING (head A)
    //   0x01: EX_JUMP -> 0x00 (back-edge A, exit = 6)
    //   0x06: EX_NOTHING (head B)
    //   0x07: EX_JUMP -> 0x06 (back-edge B, exit = 12)
    //   0x0C: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_NOTHING]; // 0x00
    bytecode.push(EX_JUMP); // 0x01
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_NOTHING); // 0x06
    bytecode.push(EX_JUMP); // 0x07
    bytecode.extend_from_slice(&u32_le(6));
    bytecode.push(EX_END_OF_SCRIPT); // 0x0C
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(scopes.len(), 2, "expected two scopes, got {:?}", scopes);
    assert_eq!(scopes.get(&0).copied(), Some(6));
    assert_eq!(scopes.get(&6).copied(), Some(12));
    // Scopes don't overlap: A is [0, 6), B is [6, 12).
}

/// Nested loops: inner scope is contained within outer.
#[test]
fn back_edges_nested_loops() {
    // Layout:
    //   0x00: EX_NOTHING (outer head)
    //   0x01: EX_NOTHING (inner head)
    //   0x02: EX_JUMP -> 0x01 (inner back-edge, exit = 7)
    //   0x07: EX_JUMP -> 0x00 (outer back-edge, exit = 12)
    //   0x0C: EX_END_OF_SCRIPT
    let mut bytecode = vec![EX_NOTHING]; // 0x00
    bytecode.push(EX_NOTHING); // 0x01
    bytecode.push(EX_JUMP); // 0x02
    bytecode.extend_from_slice(&u32_le(1));
    bytecode.push(EX_JUMP); // 0x07
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_END_OF_SCRIPT); // 0x0C
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    let scopes = back_edges_in_range(&graph, 0..bytecode.len());
    assert_eq!(scopes.len(), 2, "expected two scopes, got {:?}", scopes);
    let outer_exit = scopes.get(&0).copied().expect("outer head 0");
    let inner_exit = scopes.get(&1).copied().expect("inner head 1");
    assert_eq!(outer_exit, 12);
    assert_eq!(inner_exit, 7);
    // Inner [1, 7) is contained within outer [0, 12).
    assert!(1 >= 0 && inner_exit <= outer_exit);
}

/// Range filter: back-edge whose `instr_pos` lies outside `owner_range`
/// is not recorded.
#[test]
fn back_edges_filter_instr_pos_outside_range() {
    // Same layout as `back_edges_single_jump_back_edge`, but the
    // owner range starts after the JUMP instruction, so the JUMP
    // at 0x01 is excluded.
    let mut bytecode = vec![EX_NOTHING]; // 0x00
    bytecode.push(EX_JUMP); // 0x01
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_END_OF_SCRIPT); // 0x06
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    // Range starting after the JUMP excludes its instr_pos (0x01).
    let scopes = back_edges_in_range(&graph, 6..bytecode.len());
    assert!(
        scopes.is_empty(),
        "back-edge instr_pos outside range must be skipped; got {:?}",
        scopes
    );
}

/// Range filter: back-edge whose target lies outside `owner_range`
/// is not recorded.
#[test]
fn back_edges_filter_target_outside_range() {
    // Same layout, but the owner range starts after the target,
    // so target=0 is excluded even though instr_pos=1 is inside.
    let mut bytecode = vec![EX_NOTHING]; // 0x00
    bytecode.push(EX_JUMP); // 0x01
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_END_OF_SCRIPT); // 0x06
    let nt = empty_name_table();
    let graph = build_opcode_graph(&bytecode, 0, &nt, &BTreeMap::new());

    // Range starts at 1, so target=0 is outside.
    let scopes = back_edges_in_range(&graph, 1..bytecode.len());
    assert!(
        scopes.is_empty(),
        "back-edge target outside range must be skipped; got {:?}",
        scopes
    );
}
