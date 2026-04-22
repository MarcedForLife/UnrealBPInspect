//! Block-CFG data types and build-config knobs.

use std::collections::HashMap;
use std::ops::Range;

use crate::bytecode::{JUMP_OFFSET_TOLERANCE, STRUCTURE_OFFSET_TOLERANCE};

pub(crate) type BlockId = usize;

/// Varies between the linearization build (tight tolerance, sequence
/// super-blocks collapsed) and the structurer build (relaxed tolerance
/// after mem_adj drift, raw uncollapsed layout so the `if !(cond) jump`
/// guard exit isn't buried inside a super-block).
#[derive(Debug, Clone, Copy)]
pub(super) struct BlockCfgConfig {
    pub jump_tolerance: usize,
    pub collapse_sequence_super_blocks: bool,
}

impl BlockCfgConfig {
    pub(super) fn linearization() -> Self {
        Self {
            jump_tolerance: JUMP_OFFSET_TOLERANCE,
            collapse_sequence_super_blocks: true,
        }
    }

    pub(super) fn structurer() -> Self {
        Self {
            jump_tolerance: STRUCTURE_OFFSET_TOLERANCE,
            collapse_sequence_super_blocks: false,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) enum BlockMetadata {
    #[default]
    Normal,
    /// `DoOnce(name) {` / `FlipFlop(name) {` header to `}` body-end (emitted
    /// by `transform_latch_patterns`). Name captured so later passes don't
    /// re-parse the header line.
    LatchBody { latch_name: String },
    /// Stands in for an entire Sequence dispatch (chain + inline body + pin
    /// bodies). Linearization emits `stmt_range` verbatim so
    /// `reorder_flow_patterns` can re-detect the pattern. All three ranges
    /// are statement indices; `stmt_range` is
    /// `chain.start .. max(inline_body.end, pins[*].end)`.
    SequenceSuperBlock {
        chain: Range<usize>,
        inline_body: Range<usize>,
        pins: Vec<Range<usize>>,
    },
}

/// Which terminator closed a `ReturnTerminal` block. Recorded during CFG
/// construction so downstream passes can distinguish `pop_flow` (scope close)
/// from `return nop` / `return` (function exit) from `jump_computed` (switch
/// dispatch) without re-inspecting statement text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReturnKind {
    PopFlow,
    Return,
    JumpComputed,
}

#[derive(Debug, Clone)]
pub(crate) struct Block {
    pub stmt_range: Range<usize>,
    pub exit: BlockExit,
    /// Only consumed by tests today; populated in real CFGs so later passes
    /// can consume it without a rebuild.
    #[allow(dead_code)]
    pub metadata: BlockMetadata,
    pub emitted: bool,
    /// Count of `push_flow` statements in this block's range, so the
    /// structurer can match push/pop pairs without re-scanning text.
    pub push_flow_count: u32,
    pub return_kind: Option<ReturnKind>,
}

#[derive(Debug, Clone)]
pub(crate) enum BlockExit {
    FallThrough,
    Jump(BlockId),
    /// `fall_through` is the true-body, `target` is the false-body.
    CondJump {
        fall_through: BlockId,
        target: BlockId,
    },
    /// Function-exit (return, pop_flow, jump_computed). No local convergence.
    ReturnTerminal,
    /// Latch body-close `}`. Block ends with no fall-through edge, but
    /// shared post-latch code can still be a sibling branch's convergence.
    LatchTerminal,
}

impl BlockExit {
    /// True for any non-fall-through, non-jump exit. Both variants contribute
    /// no outgoing edges to the CFG.
    #[allow(dead_code)]
    pub(super) fn is_terminal(&self) -> bool {
        matches!(self, BlockExit::ReturnTerminal | BlockExit::LatchTerminal)
    }

    /// True only for function-exit terminals; `find_convergence_target`
    /// uses this to distinguish them from latch body-ends (which still
    /// admit sibling convergence).
    pub(super) fn is_return(&self) -> bool {
        matches!(self, BlockExit::ReturnTerminal)
    }
}

pub(crate) struct BlockCfg {
    pub blocks: Vec<Block>,
    pub stmt_to_block: HashMap<usize, BlockId>,
}
