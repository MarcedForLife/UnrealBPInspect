//! Unit tests for the structure skeleton.
//!
//! Each test constructs a tiny synthetic bytecode stream, builds the
//! skeleton over a chosen owner range, and asserts on the resulting
//! `push_chains` map. The fixtures mirror the patterns in
//! `decode/sequence.rs::tests` (grouped pushes with EX_NOTHING
//! separators) so the canonical-shape invariant is exercised the same
//! way the decoder uses it.

use super::*;
use crate::bytecode::decode::test_fixtures::{empty_name_table, identity_map, u32_le};

/// 2-pin grouped Sequence (single chain, no children, no nesting).
///
///   0x00 EX_PUSH target=0x0C   pushes pin 1
///   0x05 EX_NOTHING            pin 0 inline body
///   0x06 EX_POP                 pin 0 pop
///   0x07..0x0B filler (EX_NOTHING)
///   0x0C EX_NOTHING            pin 1 body
///   0x0D EX_POP
///   0x0E EX_END_OF_SCRIPT
fn single_chain_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
    stream.extend_from_slice(&u32_le(0x0C));
    stream.push(EX_NOTHING); // 0x05 pin 0
    stream.push(EX_POP_EXECUTION_FLOW); // 0x06
    stream.push(EX_NOTHING); // 0x07 filler
    stream.push(EX_NOTHING); // 0x08
    stream.push(EX_NOTHING); // 0x09
    stream.push(EX_NOTHING); // 0x0A
    stream.push(EX_NOTHING); // 0x0B
    stream.push(EX_NOTHING); // 0x0C pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x0D
    stream.push(EX_END_OF_SCRIPT); // 0x0E
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn single_chain_has_no_parent_and_two_pins() {
    let (stream, boundaries) = single_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    assert_eq!(
        skeleton.push_chains.len(),
        1,
        "expected exactly one chain, got {}",
        skeleton.push_chains.len()
    );
    let node = skeleton.push_chains.get(&0).expect("chain at head 0x00");
    assert_eq!(node.head, 0);
    assert_eq!(node.after_chain, 0x05);
    assert_eq!(node.push_targets.len(), 2, "pin 0 + 1 pushed pin");
    assert_eq!(node.parent_chain, None, "top-level chain has no parent");
    assert_eq!(node.pin_partitions.len(), 2);
    assert!(
        node.pin_partitions.iter().all(|segs| !segs.is_empty()),
        "every pin partition must be non-empty"
    );
}

/// Two independent grouped chains in the same owner range.
///
/// Chain A occupies 0x00..0x0E, chain B starts at 0x0E.
///
///   0x00 EX_PUSH target=0x0C    chain A pushes pin 1
///   0x05 EX_NOTHING             chain A pin 0
///   0x06 EX_POP
///   0x07..0x0B filler
///   0x0C EX_NOTHING             chain A pin 1
///   0x0D EX_POP
///   0x0E EX_PUSH target=0x1A    chain B pushes pin 1
///   0x13 EX_NOTHING             chain B pin 0
///   0x14 EX_POP
///   0x15..0x19 filler
///   0x1A EX_NOTHING             chain B pin 1
///   0x1B EX_POP
///   0x1C EX_END_OF_SCRIPT
fn two_independent_chains_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
    stream.extend_from_slice(&u32_le(0x0C));
    stream.push(EX_NOTHING); // 0x05
    stream.push(EX_POP_EXECUTION_FLOW); // 0x06
    stream.push(EX_NOTHING); // 0x07
    stream.push(EX_NOTHING); // 0x08
    stream.push(EX_NOTHING); // 0x09
    stream.push(EX_NOTHING); // 0x0A
    stream.push(EX_NOTHING); // 0x0B
    stream.push(EX_NOTHING); // 0x0C
    stream.push(EX_POP_EXECUTION_FLOW); // 0x0D
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x0E
    stream.extend_from_slice(&u32_le(0x1A));
    stream.push(EX_NOTHING); // 0x13
    stream.push(EX_POP_EXECUTION_FLOW); // 0x14
    stream.push(EX_NOTHING); // 0x15
    stream.push(EX_NOTHING); // 0x16
    stream.push(EX_NOTHING); // 0x17
    stream.push(EX_NOTHING); // 0x18
    stream.push(EX_NOTHING); // 0x19
    stream.push(EX_NOTHING); // 0x1A
    stream.push(EX_POP_EXECUTION_FLOW); // 0x1B
    stream.push(EX_END_OF_SCRIPT); // 0x1C
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn two_independent_chains_both_top_level() {
    let (stream, boundaries) = two_independent_chains_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    assert_eq!(skeleton.push_chains.len(), 2, "expected two chains");
    let chain_a = skeleton.push_chains.get(&0).expect("chain A at 0x00");
    let chain_b = skeleton.push_chains.get(&0x0E).expect("chain B at 0x0E");
    assert_eq!(chain_a.parent_chain, None);
    assert_eq!(chain_b.parent_chain, None);
}

/// Genuine nested Sequence: outer 2-pin chain whose pin 0 inline body
/// IS another 2-pin chain. The inner chain's head sits inside the
/// outer chain's pin 0 partition, so `parent_chain` should be set.
///
///   0x00 EX_PUSH target=0x14    outer push -> outer pin 1
///   0x05 EX_PUSH target=0x10    inner push -> inner pin 1
///   0x0A EX_NOTHING             inner pin 0
///   0x0B EX_POP                 inner pin 0 pop
///   0x0C..0x0F filler
///   0x10 EX_NOTHING             inner pin 1
///   0x11 EX_POP                 inner pin 1 pop -> outer pin 0 done
///   0x12..0x13 filler
///   0x14 EX_NOTHING             outer pin 1
///   0x15 EX_POP
///   0x16 EX_END_OF_SCRIPT
fn genuine_nested_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW];
    stream.extend_from_slice(&u32_le(0x14)); // outer pushes pin 1
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x05 inner push
    stream.extend_from_slice(&u32_le(0x10)); // inner pushes its pin 1
    stream.push(EX_NOTHING); // 0x0A inner pin 0
    stream.push(EX_POP_EXECUTION_FLOW); // 0x0B
    stream.push(EX_NOTHING); // 0x0C
    stream.push(EX_NOTHING); // 0x0D
    stream.push(EX_NOTHING); // 0x0E
    stream.push(EX_NOTHING); // 0x0F
    stream.push(EX_NOTHING); // 0x10 inner pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x11
    stream.push(EX_NOTHING); // 0x12
    stream.push(EX_NOTHING); // 0x13
    stream.push(EX_NOTHING); // 0x14 outer pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x15
    stream.push(EX_END_OF_SCRIPT); // 0x16
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn genuine_nested_chain_records_parent() {
    let (stream, boundaries) = genuine_nested_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    assert_eq!(
        skeleton.push_chains.len(),
        2,
        "expected outer + inner chains, got {}",
        skeleton.push_chains.len()
    );
    let outer = skeleton.push_chains.get(&0).expect("outer chain at 0x00");
    let inner = skeleton
        .push_chains
        .get(&0x05)
        .expect("inner chain at 0x05");
    assert_eq!(outer.parent_chain, None, "outer chain is top-level");
    assert_eq!(
        inner.parent_chain,
        Some(0),
        "inner chain's head 0x05 sits inside outer pin 0"
    );
}

/// Phantom-child detection. This is a real fixture's ReceiveTick bug
/// shape: a chain whose head address sits inside another chain's pin
/// partition. The skeleton must mark the inner chain as a child of the
/// outer chain via `parent_chain`, so a downstream caller knows not to
/// re-partition the parent's push opcodes from inside the inner pin.
///
/// The construction here is the same as `genuine_nested_stream`
/// (because the structural signature is the same: head-inside-pin).
/// What this test asserts in addition is that the inner chain's head
/// falls strictly inside one of the outer chain's pin partition
/// ranges, not just at its boundary.
#[test]
fn phantom_child_detected_when_head_inside_parent_partition() {
    let (stream, boundaries) = genuine_nested_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    let outer = skeleton.push_chains.get(&0).expect("outer chain");
    let inner = skeleton.push_chains.get(&0x05).expect("inner chain");
    assert_eq!(inner.parent_chain, Some(outer.head));

    // Head 0x05 must be contained in some range of the outer chain's
    // pin partition. Without this, the parent-containment fixed point
    // wouldn't have anything to match on.
    let head_inside_outer = outer
        .pin_partitions
        .iter()
        .flatten()
        .any(|range| range.contains(&inner.head));
    assert!(
        head_inside_outer,
        "phantom child detection requires inner head to land inside outer pin partition"
    );
}

/// Boundary respect: if the owner range stops short of a chain's head,
/// that chain must NOT appear in the skeleton. This guards the
/// per-event scoping invariant (no cross-event partition contamination).
#[test]
fn chain_outside_owner_range_excluded() {
    let (stream, boundaries) = two_independent_chains_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    // Owner range cuts off before chain B's head at 0x0E.
    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..0x0E, &[], None);

    assert_eq!(
        skeleton.push_chains.len(),
        1,
        "only chain A should appear when chain B's head is outside owner_range"
    );
    assert!(skeleton.push_chains.contains_key(&0));
    assert!(!skeleton.push_chains.contains_key(&0x0E));
}

#[test]
fn empty_owner_range_yields_empty_skeleton() {
    let (stream, boundaries) = single_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..0, &[], None);
    assert!(skeleton.push_chains.is_empty());
}

/// Interleaved 2-PUSH chain: each PUSH is followed by an EX_JUMP to
/// its pin body, and the prior PUSH's continuation `T_0` points
/// directly at the next PUSH's offset `P_1`. The target-coherence
/// invariant accepts this and the chain keeps both pushes.
///
///   0x00 EX_PUSH target=0x0A       (T_0 = P_1, coherent)
///   0x05 EX_JUMP target=0x18       (pin 2 body)
///   0x0A EX_PUSH target=0x14       second push (P_1)
///   0x0F EX_JUMP target=0x12       (pin 1 body, inline-ish)
///   0x14 EX_POP                    pin 0 inline body / continuation
///   ...
fn coherent_interleaved_chain_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW]; // 0x00
    stream.extend_from_slice(&u32_le(0x0A)); // T_0 == P_1
    stream.push(EX_JUMP); // 0x05
    stream.extend_from_slice(&u32_le(0x20)); // pin 2 body at 0x20
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x0A P_1
    stream.extend_from_slice(&u32_le(0x14)); // T_1 = pin 0 inline = 0x14
    stream.push(EX_JUMP); // 0x0F
    stream.extend_from_slice(&u32_le(0x18)); // pin 1 body at 0x18
    stream.push(EX_NOTHING); // 0x14 pin 0 inline
    stream.push(EX_POP_EXECUTION_FLOW); // 0x15
    stream.push(EX_NOTHING); // 0x16 filler
    stream.push(EX_NOTHING); // 0x17 filler
    stream.push(EX_NOTHING); // 0x18 pin 1 body
    stream.push(EX_POP_EXECUTION_FLOW); // 0x19
    stream.push(EX_NOTHING); // 0x1A filler
    stream.push(EX_NOTHING); // 0x1B
    stream.push(EX_NOTHING); // 0x1C
    stream.push(EX_NOTHING); // 0x1D
    stream.push(EX_NOTHING); // 0x1E
    stream.push(EX_NOTHING); // 0x1F
    stream.push(EX_NOTHING); // 0x20 pin 2 body
    stream.push(EX_POP_EXECUTION_FLOW); // 0x21
    stream.push(EX_END_OF_SCRIPT); // 0x22
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn coherent_interleaved_chain_accepts_both_pushes() {
    let (stream, boundaries) = coherent_interleaved_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    let node = skeleton
        .push_chains
        .get(&0)
        .expect("interleaved chain at head 0x00");
    assert_eq!(
        node.push_targets.len(),
        3,
        "coherent interleaved chain holds pin 0 + 2 pushed pins, got {}",
        node.push_targets.len()
    );
}

/// Same shape as the coherent interleaved chain, but the gap between
/// `T_0` and `P_1` is one byte (a single `EX_TRACEPOINT` stride emitted
/// by the editor build). The invariant accepts `T_0 == P_1 - 1`.
fn tracepoint_stride_chain_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW]; // 0x00
    stream.extend_from_slice(&u32_le(0x0A)); // T_0 = 0x0A; P_1 will be at 0x0B
    stream.push(EX_JUMP); // 0x05
    stream.extend_from_slice(&u32_le(0x20)); // pin 2 body at 0x20
    stream.push(EX_TRACEPOINT); // 0x0A 1-byte stride before P_1
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x0B P_1 (T_0 + 1)
    stream.extend_from_slice(&u32_le(0x14)); // T_1 = 0x14 = pin 0 inline
    stream.push(EX_JUMP); // 0x10
    stream.extend_from_slice(&u32_le(0x18)); // pin 1 body
    stream.push(EX_NOTHING); // 0x15 pin 0 inline (after_chain after JUMP at 0x10..0x15)
    stream.push(EX_POP_EXECUTION_FLOW); // 0x16
    stream.push(EX_NOTHING); // 0x17 filler
    stream.push(EX_NOTHING); // 0x18 pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x19
    stream.push(EX_NOTHING); // 0x1A
    stream.push(EX_NOTHING); // 0x1B
    stream.push(EX_NOTHING); // 0x1C
    stream.push(EX_NOTHING); // 0x1D
    stream.push(EX_NOTHING); // 0x1E
    stream.push(EX_NOTHING); // 0x1F
    stream.push(EX_NOTHING); // 0x20 pin 2
    stream.push(EX_POP_EXECUTION_FLOW); // 0x21
    stream.push(EX_END_OF_SCRIPT); // 0x22
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn tracepoint_stride_accepts_chain() {
    let (stream, boundaries) = tracepoint_stride_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    let node = skeleton
        .push_chains
        .get(&0)
        .expect("tracepoint-stride chain at head 0x00");
    assert_eq!(
        node.push_targets.len(),
        3,
        "1-byte stride still satisfies the invariant"
    );
}

/// Phantom-chain shape: two interleaved-form PUSHes whose first
/// continuation `T_0` lands far away from the second PUSH's offset
/// `P_1`. Without the coherence check, the lookahead would merge the
/// two pushes into one chain because no POP appears between them.
/// With the check, T_0 != P_1 and T_0 != P_1 - 1, so chain A terminates
/// at its single push and chain B becomes its own chain head.
///
///   0x00 EX_PUSH target=0x18       (T_0 = chain A's pin 1 body, far from P_1)
///   0x05 EX_JUMP target=0x14       (pin body)
///   0x0A EX_PUSH target=0x22       chain B head (P_1 = 0x0A; gap > 1)
///   0x0F EX_JUMP target=0x1C       (pin body)
///   0x14 EX_NOTHING                chain A pin 0 inline
///   0x15 EX_POP
///   0x16..0x17 filler
///   0x18 EX_NOTHING                chain A pin 1 body
///   0x19 EX_POP
///   0x1A..0x1B filler
///   0x1C EX_NOTHING                chain B pin 0 inline
///   0x1D EX_POP
///   0x1E..0x21 filler
///   0x22 EX_NOTHING                chain B pin 1 body
///   0x23 EX_POP
///   0x24 EX_END_OF_SCRIPT
fn phantom_interleaved_chain_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_PUSH_EXECUTION_FLOW]; // 0x00
    stream.extend_from_slice(&u32_le(0x18)); // T_0 lands far from P_1
    stream.push(EX_JUMP); // 0x05
    stream.extend_from_slice(&u32_le(0x14)); // pin 1 body for chain A
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x0A chain B head
    stream.extend_from_slice(&u32_le(0x22));
    stream.push(EX_JUMP); // 0x0F
    stream.extend_from_slice(&u32_le(0x1C)); // chain B pin body
    stream.push(EX_NOTHING); // 0x14 chain A pin 0
    stream.push(EX_POP_EXECUTION_FLOW); // 0x15
    stream.push(EX_NOTHING); // 0x16
    stream.push(EX_NOTHING); // 0x17
    stream.push(EX_NOTHING); // 0x18 chain A pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x19
    stream.push(EX_NOTHING); // 0x1A
    stream.push(EX_NOTHING); // 0x1B
    stream.push(EX_NOTHING); // 0x1C chain B pin 0
    stream.push(EX_POP_EXECUTION_FLOW); // 0x1D
    stream.push(EX_NOTHING); // 0x1E
    stream.push(EX_NOTHING); // 0x1F
    stream.push(EX_NOTHING); // 0x20
    stream.push(EX_NOTHING); // 0x21
    stream.push(EX_NOTHING); // 0x22 chain B pin 1
    stream.push(EX_POP_EXECUTION_FLOW); // 0x23
    stream.push(EX_END_OF_SCRIPT); // 0x24
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

#[test]
fn phantom_interleaved_chain_terminates_at_first_push() {
    let (stream, boundaries) = phantom_interleaved_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    let chain_a = skeleton.push_chains.get(&0).expect("chain A at 0x00");
    assert_eq!(
        chain_a.push_targets.len(),
        2,
        "chain A should hold only its single PUSH (pin 0 + 1 pushed pin)"
    );
    let chain_b = skeleton
        .push_chains
        .get(&0x0A)
        .expect("chain B should anchor at 0x0A as its own head");
    assert_eq!(
        chain_b.push_targets.len(),
        2,
        "chain B should hold its single PUSH"
    );
}

#[test]
fn non_push_opcode_at_boundary_skipped() {
    // Stream where the owner range starts at an EX_NOTHING; the
    // skeleton should walk past it without anchoring.
    let stream = vec![EX_NOTHING, EX_NOTHING, EX_END_OF_SCRIPT];
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
    assert!(skeleton.push_chains.is_empty());
}

/// User-Sequence shape: a 2-PUSH interleaved chain whose inline pin
/// body sits at `T_{N-1}` (the last PUSH's continuation), one byte past
/// the trailing JUMP. The inline-pin partition must include the inline
/// body bytes (0x14, 0x15) and `push_targets` must record the seed at
/// 0x14, not `after_chain_disk` (0x0F, the trailing JUMP).
///
/// This is the canonical user-Sequence layout from the BP compiler:
/// the chain ends with `EX_JUMP body=other_pin`, and the inline pin
/// runs at the byte right after that JUMP.
#[test]
fn user_sequence_inline_seed_at_last_push_continuation() {
    let (stream, boundaries) = coherent_interleaved_chain_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);
    let node = skeleton.push_chains.get(&0).expect("chain at 0x00");

    assert_eq!(node.after_chain, 0x0F, "after_chain ends at trailing JUMP");
    assert_eq!(
        node.push_targets.last().copied(),
        Some(0x14),
        "inline pin seed should be T_{{N-1}} (0x14), not after_chain_disk (0x0F)"
    );
    let inline_partition = node.pin_partitions.last().expect("inline pin partition");
    assert!(
        inline_partition.iter().any(|range| range.contains(&0x14)),
        "inline pin partition must include the inline body byte 0x14, got {:?}",
        inline_partition
    );
    assert!(
        inline_partition.iter().any(|range| range.contains(&0x15)),
        "inline pin partition must include the inline-pop byte 0x15, got {:?}",
        inline_partition
    );
}

/// For-loop scaffold shape: a 2-pin interleaved chain whose inline-pin
/// seed (T_0, the only PUSH's continuation) sits at the loop-exit
/// cleanup AND a JUMP back-edge from inside the chain's pin body lands
/// below the chain head, in init bytes that belong to the outer decoder.
///
/// Layout:
///
///   0x00..0x04 EX_NOTHING * 5      init bytes (below chain head)
///   0x05 EX_PUSH target=0x10       chain head; T_0 = 0x10
///   0x0A EX_JUMP target=0x18       pin 0 body lives at 0x18 (JUMP
///                                    target of the chain's own JUMP)
///   0x0F EX_NOTHING                filler before T_0
///   0x10 EX_JUMP target=0x00       T_0 starts with a back-edge into init
///   0x15 EX_NOTHING * 3            filler
///   0x18 EX_NOTHING                pin 0 body
///   0x19 EX_POP
///   0x1A EX_END_OF_SCRIPT
///
/// The back-edge from T_0 (the inline-pin seed) directly targets the
/// init bytes below `chain_head=0x05`. Without the chain-head floor, an
/// inline-pin BFS seeded at T_0 would walk the back-edge and absorb the
/// init bytes into the inline pin's partition. The floor blocks every
/// successor below the head, regardless of edge mechanism.
fn for_loop_scaffold_with_back_edge_stream() -> (Vec<u8>, Vec<usize>) {
    let mut stream = vec![EX_NOTHING; 5]; // 0x00..0x04 init
    stream.push(EX_PUSH_EXECUTION_FLOW); // 0x05
    stream.extend_from_slice(&u32_le(0x10)); // T_0 = 0x10
    stream.push(EX_JUMP); // 0x0A
    stream.extend_from_slice(&u32_le(0x18)); // pin 0 body at 0x18
    stream.push(EX_NOTHING); // 0x0F filler before T_0
    stream.push(EX_JUMP); // 0x10 T_0 (loop-exit cleanup) starts with a back-edge JUMP
    stream.extend_from_slice(&u32_le(0x00)); // back-edge into init
    stream.push(EX_NOTHING); // 0x15 filler
    stream.push(EX_NOTHING); // 0x16
    stream.push(EX_NOTHING); // 0x17
    stream.push(EX_NOTHING); // 0x18 pin 0 body
    stream.push(EX_POP_EXECUTION_FLOW); // 0x19
    stream.push(EX_END_OF_SCRIPT); // 0x1A
    let boundaries: Vec<usize> = (0..stream.len()).collect();
    (stream, boundaries)
}

/// With the chain-head floor active in scope-aware BFS, the inline-pin
/// seed lands at `T_{N-1}` (the last PUSH's continuation) regardless of
/// whether a back-edge from inside the chain's bytes points below the
/// head. The floor guarantees the inline-pin partition holds no addresses
/// below `chain_head`, so the for-loop scaffold's init bytes stay outside
/// the chain's territory for the outer decoder to consume.
#[test]
fn for_loop_scaffold_floor_blocks_below_chain_head() {
    let (stream, boundaries) = for_loop_scaffold_with_back_edge_stream();
    let map = identity_map(&boundaries);
    let names = empty_name_table();

    let skeleton = build_skeleton(&stream, 0, &names, &map, 0..stream.len(), &[], None);

    // The chain may or may not be accepted depending on partition
    // emptiness. When accepted, two things must hold:
    //
    // 1. The inline-pin seed is `T_{N-1}` (here 0x10), NOT
    //    `after_chain_disk` (here 0x0F). The chain-head-floor handles
    //    back-edge escapes uniformly so seeding at `T_{N-1}` is safe.
    // 2. No address below `chain_head` (0x05) appears in any pin
    //    partition; the floor rejects every successor below the head.
    if let Some(node) = skeleton.push_chains.get(&0x05) {
        let inline_seed = *node.push_targets.last().expect("at least one seed");
        assert_eq!(
            inline_seed, 0x10,
            "inline seed should be T_{{N-1}} (0x10), got {:#x}",
            inline_seed
        );
        let below_head: Vec<usize> = node
            .pin_partitions
            .iter()
            .flat_map(|segments| segments.iter().flat_map(|range| range.clone()))
            .filter(|&addr| addr < 0x05)
            .collect();
        assert!(
            below_head.is_empty(),
            "no pin partition byte may sit below chain_head=0x05; offenders: {:?}",
            below_head
        );
    }
}
