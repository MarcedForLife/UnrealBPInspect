//! Tests for `addresses_to_ranges` plus a small encoding-helper sanity check.

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::addresses_to_ranges;

// Contiguous addresses merge into one span.
#[test]
fn addresses_to_ranges_contiguous() {
    // Three EX_NOTHING (1 byte each) followed by EX_END_OF_SCRIPT.
    let stream = vec![EX_NOTHING, EX_NOTHING, EX_NOTHING, EX_END_OF_SCRIPT];
    let nt = empty_name_table();
    let owned = vec![0usize, 1, 2];
    let ranges = addresses_to_ranges(&owned, &stream, 0, &nt);
    assert_eq!(ranges.len(), 1, "contiguous must merge");
    assert_eq!(ranges[0], 0..3);
}

// Disjoint addresses produce separate spans.
#[test]
fn addresses_to_ranges_disjoint() {
    let stream = vec![EX_NOTHING, EX_NOTHING, EX_NOTHING, EX_END_OF_SCRIPT];
    let nt = empty_name_table();
    let owned = vec![0usize, 2]; // skip offset 1
    let ranges = addresses_to_ranges(&owned, &stream, 0, &nt);
    assert_eq!(ranges.len(), 2, "disjoint must produce two spans");
    assert_eq!(ranges[0], 0..1);
    assert_eq!(ranges[1], 2..3);
}

// Sanity check for encoding helpers used in stream construction.
#[test]
fn u16_le_encoding() {
    assert_eq!(u16::from_le_bytes(u16_le(42)), 42);
}
