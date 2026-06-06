//! Tests for `partition`. Extracted from the production module so the
//! BFS partitioner stays focused on the pipeline; synthetic opcode-stream
//! fixtures live here.
//!
//! Sub-modules group tests by the function or behavior under test.
//! Common stream/entry builders live here at `pub(super)` visibility so
//! each sub-module can pull them in via `use super::*`.

mod addresses_to_ranges;
mod back_edges;
mod latent_resume;
// Local-only tests that load uncommitted fixtures; kept out of default builds.
#[cfg(feature = "private-fixtures")]
mod local_tests;
mod opcode_boundaries;
mod pop_resume;
mod scope_bfs;
mod successors;

use std::collections::BTreeMap;
use std::ops::Range;

use super::partition::{
    build_opcode_graph_with_resume, partition_ubergraph_with_translation, EventEntry,
    PartitionError,
};
use crate::binary::NameTable;
use crate::bytecode::decode::test_fixtures::u32_le;
use crate::bytecode::opcodes::*;

/// Test convenience wrapper around `partition_ubergraph_with_translation`
/// using an empty memory-to-disk map (synthetic streams have no drift).
/// Returns only the per-event ranges, the latent-resume map sub-test
/// uses [`partition_ubergraph_full`] when it needs the resume side.
pub(super) fn partition_ubergraph(
    bytecode: &[u8],
    event_entries: &[EventEntry],
    name_table: &NameTable,
    ue5: i32,
) -> Result<BTreeMap<String, Vec<Range<usize>>>, PartitionError> {
    let empty_translation = BTreeMap::new();
    let (graph, latent_resumes) =
        build_opcode_graph_with_resume(bytecode, ue5, name_table, &empty_translation);
    partition_ubergraph_with_translation(
        bytecode,
        event_entries,
        name_table,
        ue5,
        &graph,
        &latent_resumes,
        None,
    )
    .map(|output| output.event_ranges)
}

/// Test convenience wrapper that returns the full [`PartitionOutput`]
/// so latent-resume tests can inspect the per-call resume chunks.
#[allow(dead_code)]
pub(super) fn partition_ubergraph_full(
    bytecode: &[u8],
    event_entries: &[EventEntry],
    name_table: &NameTable,
    ue5: i32,
) -> Result<super::partition::PartitionOutput, PartitionError> {
    let empty_translation = BTreeMap::new();
    let (graph, latent_resumes) =
        build_opcode_graph_with_resume(bytecode, ue5, name_table, &empty_translation);
    partition_ubergraph_with_translation(
        bytecode,
        event_entries,
        name_table,
        ue5,
        &graph,
        &latent_resumes,
        None,
    )
}

/// Build a minimal opcode stream from a slice of bytes.
pub(super) fn stream(bytes: &[u8]) -> Vec<u8> {
    bytes.to_vec()
}

pub(super) fn u16_le(value: u16) -> [u8; 2] {
    value.to_le_bytes()
}

/// Build: [EX_RETURN][EX_NOTHING][EX_END_OF_SCRIPT]
/// EX_RETURN reads one sub-expression; EX_NOTHING is the cheapest (0 bytes).
pub(super) fn two_returns_stream() -> Vec<u8> {
    vec![EX_RETURN, EX_NOTHING, EX_END_OF_SCRIPT]
}

/// Build: [EX_JUMP→5][EX_NOTHING@5][EX_END_OF_SCRIPT@6]
/// Offsets: 0=EX_JUMP (5 bytes), 5=EX_NOTHING, 6=EX_END_OF_SCRIPT.
pub(super) fn jump_stream() -> Vec<u8> {
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(5));
    stream.push(EX_NOTHING);
    stream.push(EX_END_OF_SCRIPT);
    stream
}

/// Build: [EX_JUMP_IF_NOT→7][EX_NOTHING(cond)@5][EX_NOTHING@6][EX_END_OF_SCRIPT@7]
pub(super) fn cond_jump_stream() -> Vec<u8> {
    let mut stream = vec![EX_JUMP_IF_NOT];
    stream.extend_from_slice(&u32_le(7));
    stream.push(EX_NOTHING); // condition at offset 5
    stream.push(EX_NOTHING); // fallthrough body at offset 6
    stream.push(EX_END_OF_SCRIPT); // explicit target at offset 7
    stream
}

/// Build: [EX_PUSH_EXECUTION_FLOW→6][EX_NOTHING@5][EX_END_OF_SCRIPT@6]
pub(super) fn push_flow_stream() -> Vec<u8> {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
    stream.extend_from_slice(&u32_le(6));
    stream.push(EX_NOTHING); // linear body at offset 5
    stream.push(EX_END_OF_SCRIPT); // push target at offset 6
    stream
}

/// Two-event stream with a shared tail:
///   offset 0: EventA — [EX_JUMP→6] (5 bytes)
///   offset 5: EventB — [EX_NOTHING]
///   offset 6: shared — [EX_END_OF_SCRIPT]
pub(super) fn two_event_stream() -> Vec<u8> {
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(6));
    stream.push(EX_NOTHING); // EventB at offset 5
    stream.push(EX_END_OF_SCRIPT); // shared at offset 6
    stream
}

pub(super) fn make_entries(pairs: &[(&str, usize)]) -> Vec<EventEntry> {
    pairs
        .iter()
        .map(|&(name, offset)| EventEntry {
            name: name.to_string(),
            mem_offset: offset,
        })
        .collect()
}

/// Helper for the scope-aware BFS tests: build a one-pass loop with
/// an inner exit, an inner back-edge, an outer exit, and an outer
/// back-edge. Layout:
///
/// ```text
///   0x00: EX_NOTHING                                        (outer head)
///   0x01: EX_NOTHING                                        (inner head)
///   0x02: EX_JUMP_IF_NOT 0x0D [cond=EX_NOTHING]   (6 bytes  -> 0x08)
///   0x08: EX_JUMP 0x01                            (5 bytes  -> 0x0D; inner back-edge)
///   0x0D: EX_JUMP_IF_NOT 0x18 [cond=EX_NOTHING]   (6 bytes  -> 0x13)
///   0x13: EX_JUMP 0x00                            (5 bytes  -> 0x18; outer back-edge)
///   0x18: EX_NOTHING                                        (post-outer-loop)
///   0x19: EX_JUMP 0x08                            (5 bytes  -> 0x1E; sibling -> inner JUMP)
///   0x1E: EX_END_OF_SCRIPT
/// ```
///
/// Inner scope `[0x01, 0x0D)`, outer scope `[0x00, 0x18)`.
pub(super) fn nested_loop_stream() -> Vec<u8> {
    let mut bytecode = Vec::new();
    bytecode.push(EX_NOTHING); // 0x00
    bytecode.push(EX_NOTHING); // 0x01
    bytecode.push(EX_JUMP_IF_NOT); // 0x02
    bytecode.extend_from_slice(&u32_le(0x0D));
    bytecode.push(EX_NOTHING); // cond at 0x07
    bytecode.push(EX_JUMP); // 0x08
    bytecode.extend_from_slice(&u32_le(0x01));
    bytecode.push(EX_JUMP_IF_NOT); // 0x0D
    bytecode.extend_from_slice(&u32_le(0x18));
    bytecode.push(EX_NOTHING); // cond at 0x12
    bytecode.push(EX_JUMP); // 0x13
    bytecode.extend_from_slice(&u32_le(0x00));
    bytecode.push(EX_NOTHING); // 0x18
    bytecode.push(EX_JUMP); // 0x19
    bytecode.extend_from_slice(&u32_le(0x08));
    bytecode.push(EX_END_OF_SCRIPT); // 0x1E
    bytecode
}
