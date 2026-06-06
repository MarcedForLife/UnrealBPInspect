//! Opcode boundary scanning tests (instruction-aware boundary detection
//! over a known stream).

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::build_opcode_graph;
use std::collections::BTreeMap;

#[test]
fn opcode_boundaries_known_stream() {
    let stream = two_returns_stream();
    let nt = empty_name_table();
    let graph = build_opcode_graph(&stream, 0, &nt, &BTreeMap::new());

    // EX_RETURN at 0 consumes EX_NOTHING at 1 as its sub-expression.
    // So boundaries are: 0 (EX_RETURN instruction), 2 (EX_END_OF_SCRIPT).
    assert!(graph.boundaries.contains(&0));
    assert!(graph.boundaries.contains(&2));
    assert!(
        !graph.boundaries.contains(&1),
        "offset 1 is mid-instruction"
    );
}
