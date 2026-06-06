//! Basic-block CFG construction over `OpcodeGraph`.
//!
//! `build_cfg` consumes the global opcode graph, an event entry address,
//! and the byte ranges that event owns, and produces a basic-block CFG
//! whose nodes / edges are restricted to addresses inside `owned`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Range;

use crate::bytecode::opcodes::{
    EX_JUMP, EX_POP_EXECUTION_FLOW, EX_POP_FLOW_IF_NOT, EX_PUSH_EXECUTION_FLOW,
};
use crate::bytecode::partition::OpcodeGraph;

use super::{BasicBlock, BlockId, ControlFlowGraph};

/// Which reachability discipline `build_cfg_with` uses to bound the CFG's
/// address set from the event entry.
#[derive(Clone, Copy)]
enum Reachability {
    /// Flow-unaware forward reach over `graph.successors`. Complete coverage
    /// of every owned address forward-reachable from the entry.
    ForwardOwned,
    /// Flow-stack-aware reach matching the decoder's push/pop discipline.
    FlowStack,
}

/// Build a basic-block CFG for one event.
///
/// `entry` is the disk offset of the event's first opcode and MUST be in
/// `graph.boundaries` and inside one of the `owned` ranges. `owned` is the
/// set of byte ranges this event owns (per partition's per-event range
/// map); only opcode addresses landing in those ranges become nodes, and
/// only edges between owned addresses become edges in the resulting CFG.
///
/// Returns an empty-block CFG (single empty block, no edges) if the entry
/// is unreachable; this preserves caller invariants while still giving the
/// downstream probe something to inspect.
pub fn build_cfg(graph: &OpcodeGraph, entry: usize, owned: &[Range<usize>]) -> ControlFlowGraph {
    build_cfg_with(graph, entry, owned, Reachability::ForwardOwned)
}

/// Build a CFG whose blocks are bounded to the flow-stack-reachable address
/// set from `entry`, matching the decoder's flow-stack coverage. The cross-event
/// inline body decode uses this instead of the default `build_cfg` so the
/// inlined body does not absorb non-flow-reachable scaffold from a sibling
/// arm. Full-event consumers keep using `build_cfg` (flow-unaware forward
/// reach), where complete coverage is correct.
pub fn build_cfg_flow_reachable(
    graph: &OpcodeGraph,
    entry: usize,
    owned: &[Range<usize>],
) -> ControlFlowGraph {
    build_cfg_with(graph, entry, owned, Reachability::FlowStack)
}

/// Shared CFG construction. The only difference between the two public
/// entry points is the reachability discipline used to bound the address
/// set; everything downstream (leaders, blocks, edge wiring, synthetic
/// sink) is identical.
fn build_cfg_with(
    graph: &OpcodeGraph,
    entry: usize,
    owned: &[Range<usize>],
    reachability: Reachability,
) -> ControlFlowGraph {
    let owned_addrs = collect_owned_addresses(graph, owned);
    let reachable = match reachability {
        Reachability::ForwardOwned => bfs_reachable_owned(graph, entry, &owned_addrs),
        Reachability::FlowStack => bfs_reachable_flow_stack(graph, entry, &owned_addrs),
    };

    if reachable.is_empty() {
        return empty_cfg(entry);
    }

    let leaders = compute_leaders(graph, entry, &reachable);
    let mut blocks = build_blocks(graph, &leaders, &reachable);
    let (mut successors, mut predecessors) = wire_edges(graph, &blocks, &reachable);

    // `build_blocks` sorts leaders by address, so the entry block's
    // id is whichever block starts at the entry disk offset (NOT
    // necessarily id 0; events that loop back to a lower address get
    // a smaller-address block as id 0). Fall back to 0 only if the
    // entry address didn't survive leader detection.
    let entry_block_id = blocks
        .iter()
        .find(|block| block.start == entry)
        .map(|block| block.id)
        .unwrap_or(0);

    let sink = attach_synthetic_sink(&mut blocks, &mut successors, &mut predecessors);

    ControlFlowGraph {
        blocks,
        successors,
        predecessors,
        entry: entry_block_id,
        sink,
    }
}

/// Append a synthetic sink block (no opcodes, no successors) and wire
/// every existing leaf block (no successors) to it. The synthetic sink
/// is always assigned id `blocks.len()` before insertion, so it sits
/// past every real block id.
///
/// Returns the synthetic sink's `BlockId`. The block's `start` and
/// `end` are both the max real-block `end` (sentinel addresses past
/// the bytecode buffer), so the sink doesn't collide with any real
/// opcode address.
fn attach_synthetic_sink(
    blocks: &mut Vec<BasicBlock>,
    successors: &mut BTreeMap<BlockId, Vec<BlockId>>,
    predecessors: &mut BTreeMap<BlockId, Vec<BlockId>>,
) -> BlockId {
    let sink_id = blocks.len();
    let sink_addr = blocks.iter().map(|block| block.end).max().unwrap_or(0);
    let sink_block = BasicBlock {
        id: sink_id,
        start: sink_addr,
        end: sink_addr,
        opcodes: Vec::new(),
    };

    let leaf_ids: Vec<BlockId> = blocks
        .iter()
        .filter(|block| {
            successors
                .get(&block.id)
                .map(|edges| edges.is_empty())
                .unwrap_or(true)
        })
        .map(|block| block.id)
        .collect();

    blocks.push(sink_block);
    successors.insert(sink_id, Vec::new());
    predecessors.insert(sink_id, Vec::new());

    for leaf_id in leaf_ids {
        successors.entry(leaf_id).or_default().push(sink_id);
        predecessors.entry(sink_id).or_default().push(leaf_id);
    }

    sink_id
}

/// Owned opcode addresses, derived from the address-range list. Only the
/// `boundaries` set is consulted; ranges that include non-boundary bytes
/// (the operand body of multi-byte opcodes) contribute nothing extra.
fn collect_owned_addresses(graph: &OpcodeGraph, owned: &[Range<usize>]) -> BTreeSet<usize> {
    let mut addresses = BTreeSet::new();
    for range in owned {
        for &boundary in graph.boundaries.range(range.start..range.end) {
            addresses.insert(boundary);
        }
    }
    addresses
}

/// Flow-stack-aware reachability matching the decoder's push/pop
/// discipline. Unlike `bfs_reachable_owned` (which follows every successor
/// of `EX_PUSH_EXECUTION_FLOW` eagerly), this simulates the execution-flow
/// stack: at PUSH, defer the pushed target onto the stack and follow only
/// the fallthrough; at `EX_POP_EXECUTION_FLOW`, resume the stack top; at
/// `EX_POP_FLOW_IF_NOT`, follow the fallthrough plus the pop branch when the
/// stack is non-empty. The visited key includes the stack top and depth so a
/// re-visit through a different push/pop path can still be enqueued.
///
/// Used only by `build_cfg_flow_reachable` for the cross-event inline body
/// decode, where a flow-unaware reach would admit non-flow-reachable
/// scaffold bytes that belong to a sibling arm (the source event's DoOnce
/// gate set), corrupting the inlined body.
fn bfs_reachable_flow_stack(
    graph: &OpcodeGraph,
    entry: usize,
    owned: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    let mut reached = BTreeSet::new();
    if !owned.contains(&entry) {
        return reached;
    }
    let mut visited: BTreeSet<(usize, usize, Option<usize>)> = BTreeSet::new();
    let mut queue: VecDeque<(usize, Vec<usize>)> = VecDeque::new();
    queue.push_back((entry, Vec::new()));
    while let Some((addr, stack)) = queue.pop_front() {
        if !visited.insert((addr, stack.len(), stack.last().copied())) {
            continue;
        }
        if !owned.contains(&addr) {
            continue;
        }
        reached.insert(addr);
        let opcode = graph.opcodes.get(&addr).copied();
        let Some(succs) = graph.successors.get(&addr) else {
            continue;
        };
        match opcode {
            Some(EX_PUSH_EXECUTION_FLOW) => {
                // Successors of PUSH are [pushed_target, fallthrough].
                // Defer the pushed target on the simulated stack and follow
                // only the fallthrough.
                if let Some(&pushed_target) = succs.first() {
                    let mut new_stack = stack.clone();
                    new_stack.push(pushed_target);
                    for &succ in succs.iter().skip(1) {
                        queue.push_back((succ, new_stack.clone()));
                    }
                }
            }
            Some(EX_POP_EXECUTION_FLOW) => {
                let mut new_stack = stack.clone();
                if let Some(resume) = new_stack.pop() {
                    queue.push_back((resume, new_stack));
                }
            }
            Some(EX_POP_FLOW_IF_NOT) => {
                for &succ in succs {
                    queue.push_back((succ, stack.clone()));
                }
                if let Some(&top) = stack.last() {
                    let mut new_stack = stack.clone();
                    new_stack.pop();
                    queue.push_back((top, new_stack));
                }
            }
            _ => {
                for &succ in succs {
                    queue.push_back((succ, stack.clone()));
                }
            }
        }
    }
    reached
}

/// BFS over `graph.successors`, restricted to `owned` addresses.
///
/// This is the CFG-build sibling of partition's `bfs_reachable_with_scope`
/// minus the flow-stack tracking; partition already chopped the bytecode
/// into per-event ranges, so the CFG just needs to discover which owned
/// addresses are forward-reachable from the event entry.
fn bfs_reachable_owned(
    graph: &OpcodeGraph,
    entry: usize,
    owned: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    let mut reached = BTreeSet::new();
    if !owned.contains(&entry) {
        return reached;
    }
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(entry);
    while let Some(addr) = queue.pop_front() {
        if !reached.insert(addr) {
            continue;
        }
        let Some(succs) = graph.successors.get(&addr) else {
            continue;
        };
        for &succ in succs {
            if owned.contains(&succ) && !reached.contains(&succ) {
                queue.push_back(succ);
            }
        }
    }
    reached
}

/// An address `addr` is a basic-block leader (block start) iff
/// (a) `addr == entry`, (b) `addr` has 2+ predecessors among reachable
/// addresses, or (c) `addr`'s unique predecessor branches to more than one
/// reachable address OR is an explicit terminator opcode (the predecessor
/// terminates the previous block).
///
/// The successor-count test catches multi-way opcodes (jump, conditional
/// jump, switch, push, return) because they have 0 or 2+ successors.
/// `EX_POP_EXECUTION_FLOW` is special: `wire_pop_resume_edges` gives it a
/// single resume successor, so it would otherwise be chained as a
/// fallthrough; the explicit terminator check below ends the block at
/// POP and promotes the resume target to a leader.
fn compute_leaders(
    graph: &OpcodeGraph,
    entry: usize,
    reachable: &BTreeSet<usize>,
) -> BTreeSet<usize> {
    let mut in_degree: BTreeMap<usize, usize> = BTreeMap::new();
    let mut unique_pred: BTreeMap<usize, usize> = BTreeMap::new();

    for &addr in reachable {
        let Some(succs) = graph.successors.get(&addr) else {
            continue;
        };
        for &succ in succs {
            if !reachable.contains(&succ) {
                continue;
            }
            let count = in_degree.entry(succ).or_insert(0);
            *count += 1;
            if *count == 1 {
                unique_pred.insert(succ, addr);
            } else {
                unique_pred.remove(&succ);
            }
        }
    }

    let mut leaders = BTreeSet::new();
    leaders.insert(entry);

    for &addr in reachable {
        if addr == entry {
            continue;
        }
        let degree = in_degree.get(&addr).copied().unwrap_or(0);
        if degree >= 2 {
            leaders.insert(addr);
            continue;
        }
        if degree == 1 {
            if let Some(&pred) = unique_pred.get(&addr) {
                let pred_succs_in_owned = graph
                    .successors
                    .get(&pred)
                    .map(|succs| succs.iter().filter(|succ| reachable.contains(succ)).count())
                    .unwrap_or(0);
                if pred_succs_in_owned >= 2 || is_explicit_terminator(graph, pred) {
                    leaders.insert(addr);
                }
            }
        }
    }

    // EX_JUMP targets are leaders: an unconditional jump ends a basic block
    // and its target starts a new one, even when in-degree is 1.
    for &addr in reachable {
        if graph.opcodes.get(&addr).copied() == Some(EX_JUMP) {
            if let Some(succs) = graph.successors.get(&addr) {
                for &target in succs {
                    if reachable.contains(&target) {
                        leaders.insert(target);
                    }
                }
            }
        }
    }

    leaders
}

/// Group reachable opcodes into blocks by walking forward from each
/// leader through fallthrough successors until hitting (a) another
/// leader, (b) a multi-successor opcode (terminator), or (c) an opcode
/// with no owned successors.
fn build_blocks(
    graph: &OpcodeGraph,
    leaders: &BTreeSet<usize>,
    reachable: &BTreeSet<usize>,
) -> Vec<BasicBlock> {
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut leader_list: Vec<usize> = leaders.iter().copied().collect();
    leader_list.sort();

    for (block_index, &leader) in leader_list.iter().enumerate() {
        let mut opcodes: Vec<usize> = vec![leader];
        let mut cursor = leader;

        loop {
            let succs_in_owned: Vec<usize> = graph
                .successors
                .get(&cursor)
                .map(|succs| {
                    succs
                        .iter()
                        .copied()
                        .filter(|succ| reachable.contains(succ))
                        .collect()
                })
                .unwrap_or_default();

            if succs_in_owned.len() != 1 {
                break;
            }
            if is_explicit_terminator(graph, cursor) {
                break;
            }
            // Exactly one owned successor here (len checked above); end the
            // straight-line chain rather than indexing if that ever breaks.
            let Some(&next) = succs_in_owned.first() else {
                break;
            };
            if leaders.contains(&next) {
                break;
            }
            opcodes.push(next);
            cursor = next;
        }

        let last_addr = *opcodes.last().expect("block has at least the leader");
        let end = block_end_address(graph, last_addr, reachable, leaders);

        blocks.push(BasicBlock {
            id: block_index,
            start: leader,
            end,
            opcodes,
        });
    }

    blocks
}

/// True if the opcode at `addr` ends a basic block regardless of its
/// successor count.
///
/// `EX_JUMP` (unconditional jump) has one successor but transfers control
/// to a non-contiguous target; per basic-block definition, the block ends
/// at the jump and a new block begins at the target.
///
/// `EX_POP_EXECUTION_FLOW` has a single resume successor wired by
/// `wire_pop_resume_edges`; chaining across that edge would extend the
/// block from a displaced body into the event prologue.
fn is_explicit_terminator(graph: &OpcodeGraph, addr: usize) -> bool {
    matches!(
        graph.opcodes.get(&addr).copied(),
        Some(EX_JUMP) | Some(EX_POP_EXECUTION_FLOW)
    )
}

/// Compute the byte-coordinate `end` of the block whose last opcode
/// starts at `last_addr`. For an internal block, this is the address of
/// the next opcode (the next leader or the next reachable address in
/// linear order); for a terminator that consumes the rest of the stream,
/// this falls back to the next boundary in `graph.boundaries`.
///
/// The CFG only needs `end` for diagnostic / probe purposes; the
/// opcode-level structuring downstream uses the explicit `opcodes` list.
fn block_end_address(
    graph: &OpcodeGraph,
    last_addr: usize,
    reachable: &BTreeSet<usize>,
    leaders: &BTreeSet<usize>,
) -> usize {
    if let Some(&next_boundary) = graph.boundaries.range(last_addr + 1..).next() {
        return next_boundary;
    }
    // Past the last opcode in the stream; use a sentinel past `last_addr`
    // by deriving from the highest reachable address. Cannot happen for a
    // valid input unless the event ends at the literal end of the buffer.
    let highest = reachable
        .iter()
        .chain(leaders.iter())
        .copied()
        .max()
        .unwrap_or(last_addr);
    highest + 1
}

/// Build successors / predecessors keyed by `BlockId` from the per-opcode
/// edges in `graph`. Only edges whose source is the last opcode of a
/// block and whose target is the start of another block in this CFG
/// produce an edge.
fn wire_edges(
    graph: &OpcodeGraph,
    blocks: &[BasicBlock],
    reachable: &BTreeSet<usize>,
) -> (
    BTreeMap<BlockId, Vec<BlockId>>,
    BTreeMap<BlockId, Vec<BlockId>>,
) {
    let start_to_block: BTreeMap<usize, BlockId> =
        blocks.iter().map(|block| (block.start, block.id)).collect();

    let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for block in blocks {
        successors.insert(block.id, Vec::new());
        predecessors.insert(block.id, Vec::new());
    }

    for block in blocks {
        let terminator = *block.opcodes.last().expect("block non-empty");
        let raw_succs = match graph.successors.get(&terminator) {
            Some(succs) => succs,
            None => continue,
        };
        // Preserve the on-disk ordering of successor edges (consistent
        // with `OpcodeGraph::successors`) so downstream consumers can
        // distinguish "branch taken" from "fallthrough" by index.
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        let mut succ_blocks: Vec<BlockId> = Vec::new();
        for &target_addr in raw_succs {
            if !reachable.contains(&target_addr) {
                continue;
            }
            let Some(&target_block) = start_to_block.get(&target_addr) else {
                // Edge into the middle of a block — should not happen
                // because `compute_leaders` promotes every multi-way
                // target to a leader. Skip defensively.
                continue;
            };
            if seen.insert(target_block) {
                succ_blocks.push(target_block);
            }
        }
        for &succ_block in &succ_blocks {
            predecessors.entry(succ_block).or_default().push(block.id);
        }
        successors.insert(block.id, succ_blocks);
    }

    (successors, predecessors)
}

/// Empty placeholder CFG: a single empty entry block, a synthetic sink
/// after it with an entry -> sink edge. Used when the entry address is
/// not owned, so the caller still receives a well-formed structure for
/// diagnostic reporting.
fn empty_cfg(entry: usize) -> ControlFlowGraph {
    let entry_block = BasicBlock {
        id: 0,
        start: entry,
        end: entry,
        opcodes: Vec::new(),
    };
    let sink_block = BasicBlock {
        id: 1,
        start: entry,
        end: entry,
        opcodes: Vec::new(),
    };
    let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    successors.insert(0, vec![1]);
    successors.insert(1, Vec::new());
    predecessors.insert(0, Vec::new());
    predecessors.insert(1, vec![0]);
    ControlFlowGraph {
        blocks: vec![entry_block, sink_block],
        successors,
        predecessors,
        entry: 0,
        sink: 1,
    }
}
