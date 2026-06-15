//! Structural-reduction skeleton for the decoder.
//!
//! Pre-computes Sequence push-chain skeletons for an event's owned
//! bytecode range. Each chain records its push targets, per-pin
//! reachability partitions, and an optional `parent_chain` link.
//!
//! The parent-containment fixed point distinguishes a genuine nested
//! Sequence (whose head sits inside a parent's pin partition) from a
//! peer chain that happens to live in the same event. This eliminates
//! the phantom-nested-Sequence class of bug, where the previous
//! per-call partitioner recursively re-partitioned a parent chain's
//! own push opcodes from inside an inner pin's body.
//!
//! `try_decode_sequence` looks up its pin partition here keyed by the
//! chain head's disk offset; the skeleton is the single source of truth
//! for sequence shape.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::{
    build_opcode_graph, opcode_length_at, partition_seeds_with_stack, OpcodeGraph, PartitionCtx,
    StackSeed,
};
use crate::bytecode::readers::read_bc_u32;

/// Operand width for `EX_PUSH_EXECUTION_FLOW` targets.
const PUSH_TARGET_BYTES: usize = 4;
/// Total byte length of a single `EX_PUSH_EXECUTION_FLOW` instruction
/// (opcode byte + target operand).
pub(crate) const PUSH_INSTR_BYTES: usize = 1 + PUSH_TARGET_BYTES;
/// Operand width for `EX_JUMP` targets reached via push-stub follow.
const JUMP_OPERAND_BYTES: usize = 4;
/// Total byte length of a single `EX_JUMP` instruction.
const JUMP_INSTR_BYTES: usize = 1 + JUMP_OPERAND_BYTES;

/// One Sequence push chain plus its per-pin partition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PushChainNode {
    /// Disk offset of the first `EX_PUSH_EXECUTION_FLOW` in the chain.
    pub head: usize,
    /// Disk offset just past the last push opcode (where pin 0 begins).
    pub after_chain: usize,
    /// Disk offsets of pin body starts in canonical scan order: pin 0
    /// is `after_chain`, then pins 1..N in execution order (reverse of
    /// push order).
    pub push_targets: Vec<usize>,
    /// Per-pin owned ranges, parallel to `push_targets`.
    pub pin_partitions: Vec<Vec<Range<usize>>>,
    /// Head offset of the enclosing chain when this chain's head sits
    /// inside another chain's pin partition. `None` for top-level
    /// chains within `owner_range`.
    pub parent_chain: Option<usize>,
}

/// Per-event skeleton: every push chain reachable in the event's owned
/// range, keyed by chain head disk offset.
#[derive(Debug, Default, Clone)]
pub struct StructureSkeleton {
    pub push_chains: BTreeMap<usize, PushChainNode>,
}

/// Build the structural skeleton for one event's owned bytecode range.
///
/// 1. Obtain the opcode graph (the shared `prebuilt_graph` when supplied,
///    else build one over the full bytecode stream).
/// 2. Find every push-chain head inside `owner_range` (a contiguous run
///    of `EX_PUSH_EXECUTION_FLOW` opcodes, possibly separated by
///    side-effect opcodes whose interleaved-form lookahead matches the
///    canonical sequence shape).
/// 3. For each chain, partition seeds (pin 0 inline body + each pushed
///    body in execution order) over `owner_range` to recover per-pin
///    owned ranges.
/// 4. Iterate parent-containment to a fixed point, marking chains whose
///    head sits inside another chain's pin partition as children.
///
/// `arm_boundaries` lists tail-JIN displaced-arm ranges within the
/// event. Pin partitioning treats each arm as a hard wall: a chain
/// whose head sits inside arm A may only own bytes within A; a chain
/// outside every arm may not partition into any arm. Pass `&[]` for
/// events with no tail-JIN arms (the common case).
///
/// `prebuilt_graph` lets the ubergraph decode path share one opcode graph
/// across every event, resume block, and inline body instead of rebuilding
/// it per call. The graph is a pure function of
/// `(bytecode, ue5, name_table, mem_to_disk)` and independent of
/// `owner_range`, so any caller passing the same full-stream inputs may
/// share it. Pass `None` for callers with a different bytecode slice
/// (standalone function bodies, synthetic test streams), which build their
/// own graph internally.
pub fn build_skeleton(
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
    owner_range: Range<usize>,
    arm_boundaries: &[Range<usize>],
    prebuilt_graph: Option<&OpcodeGraph>,
) -> StructureSkeleton {
    if owner_range.start >= owner_range.end || owner_range.end > bytecode.len() {
        return StructureSkeleton::default();
    }

    let owned_graph;
    let graph = match prebuilt_graph {
        Some(graph) => graph,
        None => {
            owned_graph = build_opcode_graph(bytecode, ue5, name_table, mem_to_disk);
            &owned_graph
        }
    };
    let ctx = PartitionCtx {
        graph,
        arm_boundaries,
    };

    let mut push_chains: BTreeMap<usize, PushChainNode> = BTreeMap::new();
    let mut consumed_by_run: BTreeSet<usize> = BTreeSet::new();

    for &offset in graph.boundaries.iter() {
        if !owner_range.contains(&offset) {
            continue;
        }
        if consumed_by_run.contains(&offset) {
            continue;
        }
        if bytecode.get(offset) != Some(&EX_PUSH_EXECUTION_FLOW) {
            continue;
        }
        if let Some(node) = build_chain_node(
            offset,
            bytecode,
            ue5,
            name_table,
            mem_to_disk,
            &ctx,
            &owner_range,
        ) {
            // Mark every push-opcode boundary consumed by this chain's
            // own push run so we don't re-anchor on the second push of
            // a grouped chain. We re-walk the chain head-to-after_chain
            // via `opcode_length_at` to find each push offset; pin
            // bodies live past `after_chain` and remain available for
            // nested-chain detection.
            mark_chain_run_consumed(&node, bytecode, ue5, name_table, &mut consumed_by_run);
            push_chains.insert(offset, node);
        }
    }

    assign_parent_containment(&mut push_chains);

    StructureSkeleton { push_chains }
}

/// Mark every `EX_PUSH_EXECUTION_FLOW` opcode within the chain's
/// `[head, after_chain)` extent as consumed so the outer scanner won't
/// anchor on the same chain twice. Non-push separator opcodes inside an
/// interleaved chain are NOT consumed; they're decode-only material and
/// can't be a push chain head themselves.
fn mark_chain_run_consumed(
    node: &PushChainNode,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    consumed: &mut BTreeSet<usize>,
) {
    let mut cursor = node.head;
    while cursor < node.after_chain {
        if bytecode.get(cursor) == Some(&EX_PUSH_EXECUTION_FLOW) {
            consumed.insert(cursor);
        }
        let length = opcode_length_at(cursor, bytecode, ue5, name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }
}

/// Build a `PushChainNode` for the chain anchored at `head`, or return
/// `None` if `head` doesn't actually start a push chain or the chain
/// can't be partitioned cleanly.
fn build_chain_node(
    head: usize,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
    ctx: &PartitionCtx<'_>,
    owner_range: &Range<usize>,
) -> Option<PushChainNode> {
    let graph = ctx.graph;
    if bytecode.get(head) != Some(&EX_PUSH_EXECUTION_FLOW) {
        return None;
    }

    let chain = scan_push_chain_shape(
        head,
        owner_range.end,
        bytecode,
        ue5,
        name_table,
        mem_to_disk,
    )?;
    if chain.push_targets_mem.is_empty() {
        return None;
    }

    // Translate chain operands into disk coords. `chain_pushes_disk[i]`
    // is the continuation pushed by the i-th PUSH; in the canonical
    // grouped form (no JUMP after each PUSH) the continuation is also
    // the body head, while the interleaved-with-JUMP form decouples
    // them and we recover the body head from the JUMP operand.
    let chain_pushes_disk: Vec<usize> = chain
        .push_targets_mem
        .iter()
        .map(|&mem| mem_to_disk.get(&mem).copied().unwrap_or(mem))
        .collect();
    if chain_pushes_disk.iter().any(|&disk| disk >= bytecode.len()) {
        return None;
    }
    let interleaved = chain.body_targets_mem.iter().all(|body| body.is_some());

    // Partition boundary clamps each pin's BFS to the event's owned
    // range, extended past the end of the push chain when the chain's
    // `after_chain_disk` lands beyond `owner_range.end`.
    let upper = owner_range.end.max(chain.after_chain_disk);
    let boundary = owner_range.start..upper;

    // Pin numbering follows BP execution order. Both forms place the
    // inline pin (pin 0) ahead of the pushed pins; the two seeding
    // helpers differ only in how the flow stack is reconstructed per pin.
    let seeds = if interleaved {
        seed_interleaved_pins(&chain, &chain_pushes_disk, bytecode, mem_to_disk, graph)?
    } else {
        seed_grouped_pins(
            &chain,
            &chain_pushes_disk,
            owner_range.end,
            bytecode,
            mem_to_disk,
        )?
    };

    // `push_targets` mirrors each seed's address in seeding order.
    let seed_addrs: Vec<usize> = seeds.iter().map(|seed| seed.seed).collect();

    if !seed_addrs
        .iter()
        .all(|seed| graph.boundaries.contains(seed))
    {
        return None;
    }

    let pin_partitions =
        partition_seeds_with_stack(bytecode, &seeds, ctx, boundary, ue5, name_table, head);

    if pin_partitions.iter().any(|segments| segments.is_empty()) {
        return None;
    }

    Some(PushChainNode {
        head,
        after_chain: chain.after_chain_disk,
        push_targets: seed_addrs,
        pin_partitions,
        parent_chain: None,
    })
}

/// Seed the pins of an interleaved-with-JUMP chain. Each pushed pin enters
/// via JUMP with its own continuation on the flow stack; the inline trailer
/// runs with an empty stack after every continuation has popped. Returns
/// `None` when a body operand falls outside the bytecode stream.
fn seed_interleaved_pins(
    chain: &ChainShape,
    chain_pushes_disk: &[usize],
    bytecode: &[u8],
    mem_to_disk: &BTreeMap<usize, usize>,
    graph: &OpcodeGraph,
) -> Option<Vec<StackSeed>> {
    let mut seeds: Vec<StackSeed> = Vec::with_capacity(chain_pushes_disk.len() + 1);
    for (push_index, &cont_disk) in chain_pushes_disk.iter().enumerate() {
        let body_mem =
            chain.body_targets_mem[push_index].expect("interleaved => every push has a JUMP body");
        let body_disk = *mem_to_disk.get(&body_mem)?;
        if body_disk >= bytecode.len() {
            return None;
        }
        seeds.push(StackSeed {
            seed: body_disk,
            initial_stack: vec![cont_disk],
            is_inline_pin: false,
        });
    }
    // The inline pin runs after every PUSH operand has been popped. In the
    // canonical interleaved emit its body lives at T_{N-1} (the last PUSH's
    // continuation). Seeding at T_{N-1} is safe because scope-aware BFS with
    // a `chain_head_floor` rejects ANY successor below `head` regardless of
    // edge mechanism (back-edge, forward jump, POP, switch case offset), so
    // a BP-emitted for-loop scaffold cannot escape below the chain head into
    // the outer event's init bytes via the loop back-edge.
    let inline_body = pick_interleaved_inline_seed(
        chain_pushes_disk.last().copied(),
        chain.after_chain_disk,
        graph,
    );
    if !seeds.iter().any(|seed| seed.seed == inline_body) {
        seeds.push(StackSeed {
            seed: inline_body,
            initial_stack: Vec::new(),
            is_inline_pin: true,
        });
    }
    Some(seeds)
}

/// Seed the pins of a canonical grouped chain. Every continuation is pushed
/// before pin 0 runs, so pin 0 starts with the full chain stack and each
/// subsequent pin has one fewer item. Pop order is LIFO: the last-pushed
/// continuation fires first, so pin 1 is the last PUSH operand, pin 2 the
/// second-to-last, and so on. Returns `None` when a body operand falls
/// outside the bytecode stream.
fn seed_grouped_pins(
    chain: &ChainShape,
    chain_pushes_disk: &[usize],
    range_end: usize,
    bytecode: &[u8],
    mem_to_disk: &BTreeMap<usize, usize>,
) -> Option<Vec<StackSeed>> {
    let mut seeds: Vec<StackSeed> = Vec::with_capacity(chain_pushes_disk.len() + 1);
    seeds.push(StackSeed {
        seed: chain.after_chain_disk,
        initial_stack: chain_pushes_disk.to_vec(),
        is_inline_pin: true,
    });
    for popped_index in (0..chain_pushes_disk.len()).rev() {
        let body_disk = match chain.body_targets_mem[popped_index] {
            Some(body_mem) => *mem_to_disk.get(&body_mem)?,
            None => follow_push_stub(
                chain_pushes_disk[popped_index],
                range_end,
                bytecode,
                mem_to_disk,
            ),
        };
        if body_disk >= bytecode.len() {
            return None;
        }
        // Stack after popping the i-th continuation: everything pushed
        // before it remains on the stack (cont_0..cont_{i-1}).
        let initial_stack = chain_pushes_disk[..popped_index].to_vec();
        seeds.push(StackSeed {
            seed: body_disk,
            initial_stack,
            is_inline_pin: false,
        });
    }
    Some(seeds)
}

/// Pick the BFS seed for an interleaved-form chain's inline (last) pin.
///
/// For a user-authored N-pin Sequence the inline pin's body lives at
/// `T_{N-1}`, the last PUSH's continuation. Seeding at `after_chain_disk`
/// instead would give the inline pin only the few bytes of chain plumbing
/// immediately past the last PUSH, dropping the real pin content.
///
/// `T_{N-1}` is uniformly safe under scope-aware BFS with a chain-head
/// floor: an inline-pin seed cannot reach pre-chain bytes regardless of
/// edge mechanism (back-edge, forward jump, POP, switch case offset),
/// so for-loop scaffolds cannot leak loop-init bytes into the inline
/// pin's partition. The fallback to `after_chain_disk` triggers only
/// when the candidate is missing, equal to the fallback already, or
/// not a graph boundary.
fn pick_interleaved_inline_seed(
    candidate: Option<usize>,
    fallback: usize,
    graph: &OpcodeGraph,
) -> usize {
    let candidate = match candidate {
        Some(addr) => addr,
        None => return fallback,
    };
    if candidate == fallback {
        return fallback;
    }
    if !graph.boundaries.contains(&candidate) {
        return fallback;
    }
    candidate
}

/// Outcome of a push-chain shape scan. Mirrors
/// `decode/sequence.rs::PushChain` minus the interleaved side-effect
/// statements (the skeleton doesn't decode them, it only needs the
/// chain extent and target list to seed partitioning).
///
/// `push_targets_mem` collects the operands of each `EX_PUSH_EXECUTION_FLOW`
/// in encounter order. Those operands are the pin's continuation
/// addresses (where the VM resumes after the pin pops).
///
/// `body_targets_mem` collects each pin's body head. For each PUSH the
/// scanner looks for a follow-up `EX_JUMP` (skipping separators) whose
/// target is the actual pin body. If no JUMP is found before the next
/// PUSH or end-of-chain, the body coincides with the PUSH operand
/// (canonical grouped form), and the scanner records `None` so the
/// caller can fall back to the cont as the body seed.
struct ChainShape {
    push_targets_mem: Vec<usize>,
    body_targets_mem: Vec<Option<usize>>,
    after_chain_disk: usize,
}

/// Scan a push chain's shape. Recognises the same grouped + interleaved
/// forms as `decode/sequence.rs::scan_push_chain` but without invoking
/// the recursive statement decoder: every non-push opcode advances by
/// `opcode_length_at`.
///
/// Two consecutive pushes (no separator opcode) signal a nested chain;
/// the second push terminates the outer scan so the nested chain gets
/// its own entry in the skeleton.
///
/// Each subsequent PUSH must satisfy a target-coherence invariant: the
/// previous PUSH's operand `T_i`, resolved through `mem_to_disk`, equals
/// the next PUSH's disk position `P_{i+1}` or `P_{i+1} - 1` (allowing
/// for a single `EX_TRACEPOINT` stride between adjacent pushes). When the
/// invariant fails, the chain terminates at the last coherent PUSH so
/// the next PUSH starts its own chain in a later iteration of the outer
/// scan, eliminating phantom multi-PUSH chains the greedy lookahead
/// would otherwise stitch together from two adjacent single-PUSH
/// Sequences.
fn scan_push_chain_shape(
    start: usize,
    range_end: usize,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> Option<ChainShape> {
    let mut push_targets_mem: Vec<usize> = Vec::new();
    let mut body_targets_mem: Vec<Option<usize>> = Vec::new();
    let mut cursor = start;
    let mut last_was_push = false;
    // Disk offset just past the last accepted PUSH instruction. When we
    // terminate the chain due to a coherence-check failure, we rewind
    // `cursor` here so the next PUSH (which we just rejected) is left
    // for the outer scan to anchor on as a fresh chain head.
    let mut last_push_end = start;

    while cursor < range_end {
        let opcode = *bytecode.get(cursor)?;
        if opcode == EX_PUSH_EXECUTION_FLOW {
            if last_was_push {
                break;
            }
            if cursor + PUSH_INSTR_BYTES > range_end {
                return None;
            }
            // Target-coherence check on the PREVIOUS push (interleaved
            // form only): when the prior PUSH was paired with a JUMP to
            // its pin body, its operand is the pin's CONTINUATION and
            // must land at this push's offset (canonical) or one byte
            // before (single tracepoint stride). Anything else means
            // this push belongs to a different Sequence; terminate the
            // chain at the previous push by rewinding the cursor so
            // this push reads as the chain's after_chain boundary. The
            // grouped form (no per-PUSH JUMP body) is exempt because
            // its PUSH operands point at pin bodies, not continuations.
            if let (Some(&prev_target_mem), Some(Some(_))) =
                (push_targets_mem.last(), body_targets_mem.last())
            {
                let prev_target_disk = mem_to_disk
                    .get(&prev_target_mem)
                    .copied()
                    .unwrap_or(prev_target_mem);
                let coherent = prev_target_disk == cursor || prev_target_disk + 1 == cursor;
                if !coherent {
                    cursor = last_push_end;
                    break;
                }
            }
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(bytecode, &mut peek) as usize;
            push_targets_mem.push(target_mem);
            // Look ahead from the byte after this PUSH for an EX_JUMP
            // (skipping tracepoint-style separators) before another
            // PUSH appears. The interleaved chain emitted by the BP
            // compiler always pairs each PUSH with a JUMP that
            // immediately enters the pin body; the JUMP target is the
            // body head.
            let body_mem = lookahead_jump_body(peek, range_end, bytecode, ue5, name_table);
            body_targets_mem.push(body_mem);
            cursor = peek;
            last_push_end = cursor;
            last_was_push = true;
            continue;
        }

        if !is_followed_by_more_push(cursor, range_end, bytecode, ue5, name_table) {
            break;
        }

        let length = opcode_length_at(cursor, bytecode, ue5, name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
        last_was_push = false;
    }

    Some(ChainShape {
        push_targets_mem,
        body_targets_mem,
        after_chain_disk: cursor,
    })
}

/// Walk forward from the byte just past an `EX_PUSH_EXECUTION_FLOW`
/// looking for the matching `EX_JUMP` body target. Skips short
/// separator opcodes (`EX_TRACEPOINT`, `EX_WIRE_TRACEPOINT`) along the
/// way. Returns the JUMP operand (memory coords) when found, or `None`
/// when another PUSH or any other control-flow opcode appears first
/// (the canonical grouped form puts the pin body inline with no JUMP).
fn lookahead_jump_body(
    start: usize,
    range_end: usize,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> Option<usize> {
    let mut cursor = start;
    while cursor < range_end {
        let opcode = *bytecode.get(cursor)?;
        if opcode == EX_JUMP {
            if cursor + JUMP_INSTR_BYTES > range_end {
                return None;
            }
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(bytecode, &mut peek) as usize;
            return Some(target_mem);
        }
        if opcode == EX_PUSH_EXECUTION_FLOW
            || opcode == EX_POP_EXECUTION_FLOW
            || opcode == EX_JUMP_IF_NOT
            || opcode == EX_RETURN
            || opcode == EX_END_OF_SCRIPT
            || opcode == EX_POP_FLOW_IF_NOT
        {
            return None;
        }
        let length = opcode_length_at(cursor, bytecode, ue5, name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// Look ahead from `cursor` (a non-push opcode) to determine whether
/// another push appears before the first pop or the end of range.
/// Mirrors `decode/sequence.rs::is_followed_by_more_push`.
fn is_followed_by_more_push(
    cursor: usize,
    range_end: usize,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> bool {
    let mut scan = cursor;
    while scan < range_end {
        let opcode = match bytecode.get(scan) {
            Some(&op) => op,
            None => return false,
        };
        if opcode == EX_PUSH_EXECUTION_FLOW {
            return true;
        }
        if opcode == EX_POP_EXECUTION_FLOW {
            return false;
        }
        let length = opcode_length_at(scan, bytecode, ue5, name_table);
        if length == 0 {
            return false;
        }
        scan += length;
    }
    false
}

/// If `target_disk` points at a one-instruction `EX_JUMP` stub, return
/// the jump destination resolved through `mem_to_disk`. Otherwise
/// return `target_disk` unchanged. Mirrors
/// `decode/sequence.rs::follow_push_stub` for the skeleton's own seed
/// derivation.
fn follow_push_stub(
    target_disk: usize,
    range_end: usize,
    bytecode: &[u8],
    mem_to_disk: &BTreeMap<usize, usize>,
) -> usize {
    if target_disk + JUMP_INSTR_BYTES > range_end {
        return target_disk;
    }
    if bytecode.get(target_disk) != Some(&EX_JUMP) {
        return target_disk;
    }
    let mut cursor = target_disk + 1;
    let jump_target_mem = read_bc_u32(bytecode, &mut cursor) as usize;
    match mem_to_disk.get(&jump_target_mem) {
        Some(&disk) if disk >= target_disk && disk < range_end => disk,
        _ => target_disk,
    }
}

/// Iterate parent assignment until stable. A chain whose head address
/// falls inside another chain's pin partition becomes that chain's
/// child. Multiple containment levels are resolved by repeated passes,
/// each chain settling on the innermost containing parent.
fn assign_parent_containment(chains: &mut BTreeMap<usize, PushChainNode>) {
    if chains.len() < 2 {
        return;
    }

    let snapshot: Vec<(usize, Vec<Vec<Range<usize>>>)> = chains
        .iter()
        .map(|(&head, node)| (head, node.pin_partitions.clone()))
        .collect();

    let mut changed = true;
    while changed {
        changed = false;
        let chain_heads: Vec<usize> = chains.keys().copied().collect();
        for child_head in chain_heads {
            let new_parent = innermost_containing_parent(child_head, &snapshot);
            let entry = chains.get_mut(&child_head).expect("entry must exist");
            if entry.parent_chain != new_parent {
                entry.parent_chain = new_parent;
                changed = true;
            }
        }
    }
}

/// Find the head of the chain whose pin partition contains `child_head`,
/// preferring the innermost (largest start offset) containing chain when
/// multiple chains contain the address. Returns `None` if no chain
/// contains `child_head`, or if the only candidate is `child_head`
/// itself.
fn innermost_containing_parent(
    child_head: usize,
    snapshot: &[(usize, Vec<Vec<Range<usize>>>)],
) -> Option<usize> {
    let mut best: Option<usize> = None;
    for (parent_head, pin_partitions) in snapshot {
        if *parent_head == child_head {
            continue;
        }
        if !pin_partitions
            .iter()
            .flatten()
            .any(|range| range.contains(&child_head))
        {
            continue;
        }
        // Prefer the parent with the highest head offset (innermost).
        match best {
            Some(current) if current > *parent_head => {}
            _ => best = Some(*parent_head),
        }
    }
    best
}

#[cfg(test)]
mod tests;
