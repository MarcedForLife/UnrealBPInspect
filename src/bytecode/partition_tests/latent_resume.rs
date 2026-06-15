//! Latent-call resume targets harvested from the opcode stream.
//!
//! `EX_SKIP_OFFSET_CONST` carries the `Linkage` field of a
//! `LatentActionInfo` argument to a latent UFUNCTION call (Delay,
//! SetTimerByEvent, etc.). When the operand is a valid bytecode address
//! it identifies the resume continuation, the bytecode the VM jumps
//! to after the latent action completes asynchronously.
//!
//! The decoder treats these as orphan continuations, NOT synchronous
//! successor edges. The opcode graph does not include them in its
//! per-call successor lists, BFS leaves the resume bytes unowned, and
//! the partition emits a separate `resume_blocks` map keyed by the
//! call's disk offset for the decoder + emitter to interleave the
//! resume body after the latent call line.
//!
//! These tests verify:
//! - the resume target is NOT wired into the graph's successor edges
//!   (so the synchronous BFS does not claim it for the seed event);
//! - the partition's `resume_blocks` map carries the (call_offset ->
//!   resume range) entry;
//! - the `-1` sentinel (`0xFFFFFFFF`, "no continuation wired") is
//!   filtered cleanly.

use super::*;
use crate::bytecode::decode::test_fixtures::empty_name_table;
use crate::bytecode::partition::{bfs_reachable, build_opcode_graph_with_resume};
use std::collections::BTreeMap;

/// Build:
/// ```text
///   0x00: EX_FINAL_FUNCTION callee=0
///   0x05:   EX_SKIP_OFFSET_CONST resume=0x14
///   0x0A:   EX_END_FUNCTION_PARMS
///   0x0B: EX_POP_EXECUTION_FLOW                     (call ends a flow)
///   0x0C: EX_NOTHING                                (filler)
///   0x0D: EX_NOTHING                                (filler) ...
///   0x14: EX_NOTHING                                (resume target)
///   0x15: EX_END_OF_SCRIPT
/// ```
///
/// The post-resume bytes at `0x14..0x16` are unreachable through the
/// linear/control-flow graph alone, so without the latent-resume edge
/// they get no owner and disappear from event A's partition output.
fn latent_call_stream() -> Vec<u8> {
    let mut bytecode = Vec::new();
    bytecode.push(EX_FINAL_FUNCTION); // 0x00
    bytecode.extend_from_slice(&u32_le(0)); // callee obj idx
    bytecode.push(EX_SKIP_OFFSET_CONST); // 0x05 — Linkage operand
    bytecode.extend_from_slice(&u32_le(0x14)); // resume target
    bytecode.push(EX_END_FUNCTION_PARMS); // 0x0A
    bytecode.push(EX_POP_EXECUTION_FLOW); // 0x0B (ends linear flow)
    while bytecode.len() < 0x14 {
        bytecode.push(EX_NOTHING); // filler 0x0C..0x13
    }
    bytecode.push(EX_NOTHING); // 0x14 — resume target
    bytecode.push(EX_END_OF_SCRIPT); // 0x15
    bytecode
}

#[test]
fn latent_resume_not_in_successor_edges() {
    let stream = latent_call_stream();
    let names = empty_name_table();
    let (graph, latent_resumes) =
        build_opcode_graph_with_resume(&stream, 0, &names, &BTreeMap::new());

    let succs = graph
        .successors
        .get(&0)
        .expect("EX_FINAL_FUNCTION at offset 0 must have successors");
    assert!(
        !succs.contains(&0x14),
        "call at 0x00 must NOT carry latent resume target 0x14 as a graph edge; got {:?}",
        succs
    );
    assert_eq!(
        latent_resumes.get(&0).copied(),
        Some(0x14),
        "latent resume map must record (call_offset 0 -> resume 0x14); got {:?}",
        latent_resumes
    );
}

#[test]
fn latent_resume_not_reached_by_bfs() {
    let stream = latent_call_stream();
    let names = empty_name_table();
    let (graph, _resumes) = build_opcode_graph_with_resume(&stream, 0, &names, &BTreeMap::new());

    let reachable = bfs_reachable(0, &graph);
    assert!(
        !reachable.contains(&0x14),
        "BFS from event seed at 0x00 must NOT reach the latent resume target 0x14; got {:?}",
        reachable
    );
}

#[test]
fn latent_resume_emits_separate_chunk() {
    let stream = latent_call_stream();
    let names = empty_name_table();
    let entries = make_entries(&[("EventA", 0x00)]);

    let output =
        partition_ubergraph_full(&stream, &entries, &names, 0).expect("partition must succeed");

    // The seed event owns the synchronous reach (everything before the
    // resume target) but the resume body lives in `resume_blocks`.
    let owned = output
        .event_ranges
        .get("EventA")
        .expect("EventA must be present in the partition output");
    let max_end = owned.iter().map(|range| range.end).max().unwrap_or(0);
    assert!(
        max_end <= 0x14,
        "EventA must NOT claim bytes past the latent resume target 0x14; got {:?}",
        owned
    );
    let resume = output
        .resume_blocks
        .get(&0)
        .expect("resume_blocks must carry an entry for the call at 0x00");
    assert_eq!(resume.start, 0x14, "resume chunk must start at 0x14");
    assert!(
        resume.end >= 0x16,
        "resume chunk must cover bytes through 0x14..0x16; got {:?}",
        resume
    );
}

/// Linkage of `-1` (encoded as `0xFFFFFFFF`) means "no continuation
/// wired"; the partitioner must skip it rather than emit a bogus edge
/// that would fail jump validation.
#[test]
fn latent_resume_skips_minus_one_sentinel() {
    let mut bytecode = Vec::new();
    bytecode.push(EX_FINAL_FUNCTION); // 0x00
    bytecode.extend_from_slice(&u32_le(0));
    bytecode.push(EX_SKIP_OFFSET_CONST); // 0x05
    bytecode.extend_from_slice(&u32_le(u32::MAX)); // Linkage == -1
    bytecode.push(EX_END_FUNCTION_PARMS); // 0x0A
    bytecode.push(EX_END_OF_SCRIPT); // 0x0B

    let names = empty_name_table();
    let entries = make_entries(&[("EventA", 0x00)]);

    // Should not panic with JumpToMidInstruction; the sentinel is
    // filtered before reaching the validator.
    partition_ubergraph(&bytecode, &entries, &names, 0)
        .expect("Linkage=-1 must be filtered, not surfaced as an edge");
}
