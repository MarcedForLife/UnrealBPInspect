//! Control-flow graph (CFG) for bytecode decode.
//!
//! Builds basic-block CFGs over the existing opcode-level graph
//! (`bytecode::partition::OpcodeGraph`), computes dominators /
//! post-dominators (Cooper-Harvey-Kennedy iterative algorithm), and
//! probes reducibility via T1/T2 reductions.
//!
//! CFG construction faithfully mirrors the partition's BFS reachability;
//! the reducibility probes confirm BP bytecode is reducible enough for
//! the structuring passes.

use std::collections::{BTreeMap, BTreeSet};

pub mod build;
pub mod dom;
pub mod macro_region;
pub mod reducibility;
pub mod region;
pub mod region_linear;

#[cfg(test)]
mod probe_tests;
#[cfg(test)]
mod region_tests;
#[cfg(test)]
mod tests;

/// Identifier for a basic block within one `ControlFlowGraph`. Indexes
/// into `ControlFlowGraph::blocks`.
pub type BlockId = usize;

/// A maximal straight-line run of opcodes within one event scope.
///
/// `start` is the disk offset of the first opcode. `end` is the disk
/// offset just past the last opcode (i.e. `end == last_opcode_start +
/// last_opcode_length`). `opcodes` lists every opcode start address in
/// the block, in execution order. The terminator (branch / jump / pop /
/// return / latent call) is the last entry in `opcodes`.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct BasicBlock {
    pub id: BlockId,
    pub start: usize,
    pub end: usize,
    pub opcodes: Vec<usize>,
}

/// Single-event control-flow graph.
///
/// Nodes are basic blocks; edges are control-flow successors filtered to
/// blocks within the event's owned address set. `entry` is always block 0
/// and corresponds to the event entry point. `successors` and
/// `predecessors` use `BTreeMap` for deterministic iteration; both are
/// dense (every block id has an entry, possibly empty).
///
/// `sink` is a synthetic block (no opcodes, no successors) appended
/// after all real blocks. Every real block whose successor list would
/// otherwise be empty (event-exit leaves: returns, end-of-script,
/// PoPs that leave the event scope) gets an edge to the sink. This
/// gives the reverse CFG a single entry, which lets
/// Cooper-Harvey-Kennedy compute a well-defined post-dominator for
/// every block. Downstream consumers that walk opcodes (probes,
/// classifier) should skip the sink because its `opcodes` is empty.
#[derive(Clone, Debug)]
pub struct ControlFlowGraph {
    pub blocks: Vec<BasicBlock>,
    pub successors: BTreeMap<BlockId, Vec<BlockId>>,
    pub predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    pub entry: BlockId,
    pub sink: BlockId,
}

impl ControlFlowGraph {
    /// Total opcode count across every block. Convenience for probes.
    #[allow(dead_code)]
    pub fn opcode_count(&self) -> usize {
        self.blocks.iter().map(|block| block.opcodes.len()).sum()
    }

    /// Return the BlockId whose `start` equals `addr`, if any.
    #[allow(dead_code)]
    pub fn block_at_start(&self, addr: usize) -> Option<BlockId> {
        self.blocks
            .iter()
            .find(|block| block.start == addr)
            .map(|block| block.id)
    }
}

/// Knobs for [`reachable_bounded`] that capture the small semantic
/// differences between the region-slice walks that back onto it.
#[derive(Clone, Copy)]
pub(crate) struct BoundedReach {
    /// Skip edges into `cfg.sink` (the synthetic event-exit junction)
    /// so the walk never enters it. Macro-region growth needs this; the
    /// region-slice walks leave the sink out of their address space
    /// already and never request it.
    pub skip_sink: bool,
    /// Always include `boundary` in the result, even when no visited
    /// block has it as a successor. When false, `boundary` appears only
    /// if it is genuinely reachable as a successor.
    pub include_boundary: bool,
}

/// Blocks reachable from `start` over `cfg` successors, stopping at
/// `boundary` (its successors are never expanded). `boundary` is a
/// member when reached as a successor; [`BoundedReach::include_boundary`]
/// additionally forces it in. With [`BoundedReach::skip_sink`] set,
/// edges into `cfg.sink` are ignored.
///
/// Shared by the three region-slice walks (`reachable_in_slice`,
/// `collect_slice`, macro-region `reachable_bounded`); their differing
/// sink and boundary handling is expressed entirely through `opts`.
pub(crate) fn reachable_bounded(
    cfg: &ControlFlowGraph,
    start: BlockId,
    boundary: BlockId,
    opts: BoundedReach,
) -> BTreeSet<BlockId> {
    let mut reached: BTreeSet<BlockId> = BTreeSet::new();
    reached.insert(start);
    let mut frontier: Vec<BlockId> = vec![start];
    while let Some(node) = frontier.pop() {
        if node == boundary {
            continue;
        }
        let succs = cfg
            .successors
            .get(&node)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        for &succ in succs {
            if opts.skip_sink && succ == cfg.sink {
                continue;
            }
            if reached.insert(succ) && succ != boundary {
                frontier.push(succ);
            }
        }
    }
    if opts.include_boundary {
        reached.insert(boundary);
    }
    reached
}
