//! Block-CFG construction: basic-block splitting and edge wiring.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::bytecode::decode::BcStatement;
use crate::bytecode::flow::{parse_if_jump, parse_jump, parse_jump_computed, parse_push_flow};
use crate::bytecode::{OffsetMap, BARE_RETURN, BLOCK_CLOSE, POP_FLOW, RETURN_NOP};

use super::collapse::{annotate_latch_bodies, collapse_sequence_super_blocks, parse_latch_header};
use super::types::{
    Block, BlockCfg, BlockCfgConfig, BlockExit, BlockId, BlockMetadata, ReturnKind,
};

impl BlockCfg {
    /// Tight jump tolerance, Sequence dispatches collapsed into super-blocks.
    pub fn build(stmts: &[BcStatement], offset_map: &OffsetMap) -> Self {
        Self::build_with_config(stmts, offset_map, BlockCfgConfig::linearization())
    }

    /// Relaxed jump tolerance (mem_adj drift accumulates by the time the
    /// structurer runs) and uncollapsed layout so the `if !(cond) jump`
    /// guard exit stays visible to `detect_else_branch_via_cfg`.
    pub fn build_for_structurer(stmts: &[BcStatement], offset_map: &OffsetMap) -> Self {
        Self::build_with_config(stmts, offset_map, BlockCfgConfig::structurer())
    }

    fn build_with_config(
        stmts: &[BcStatement],
        offset_map: &OffsetMap,
        config: BlockCfgConfig,
    ) -> Self {
        let (blocks, stmt_to_block) = build_basic_blocks(stmts, offset_map, config.jump_tolerance);
        let mut cfg = BlockCfg {
            blocks,
            stmt_to_block,
        };
        wire_block_edges(
            &mut cfg.blocks,
            stmts,
            offset_map,
            &cfg.stmt_to_block,
            config.jump_tolerance,
        );
        annotate_latch_bodies(&mut cfg.blocks, stmts);
        if config.collapse_sequence_super_blocks {
            collapse_sequence_super_blocks(&mut cfg, stmts, offset_map);
        }
        cfg
    }

    /// Block whose `stmt_range` contains `stmt_idx`, or `None` when the index
    /// falls outside every block's range.
    pub fn block_of(&self, stmt_idx: usize) -> Option<BlockId> {
        if let Some(&bid) = self.stmt_to_block.get(&stmt_idx) {
            return Some(bid);
        }
        // Blocks are built in physical order, so starts are non-decreasing.
        let pos = self
            .blocks
            .partition_point(|b| b.stmt_range.start <= stmt_idx);
        if pos == 0 {
            return None;
        }
        let bid = pos - 1;
        let range = &self.blocks[bid].stmt_range;
        if stmt_idx < range.end {
            Some(bid)
        } else {
            None
        }
    }

    pub fn compute_in_degree(&self) -> Vec<usize> {
        super::analysis::compute_in_degree(&self.blocks)
    }

    pub fn compute_predecessors(&self) -> Vec<Vec<BlockId>> {
        super::analysis::compute_predecessors(&self.blocks)
    }
}

/// Inclusive `[open, close]` ranges of latch-body atoms (`DoOnce(X) {` through
/// matching `}`). Nested latch bodies would double-match, so interior openers
/// are ignored while scanning to the outermost close.
pub(super) fn compute_latch_body_ranges(stmts: &[BcStatement]) -> Vec<(usize, usize)> {
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if parse_latch_header(&stmts[i].text).is_some() {
            // Find the matching close-brace, allowing nested blocks.
            let mut depth = 1;
            let mut j = i + 1;
            while j < stmts.len() {
                let t = stmts[j].text.trim();
                if t.ends_with('{')
                    && (t == "A|B: {" || parse_latch_header(&stmts[j].text).is_some())
                {
                    depth += 1;
                } else if t == "}" {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                j += 1;
            }
            if j < stmts.len() {
                ranges.push((i, j));
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    ranges
}

/// Boundary after every jump/cond-jump/terminal/jump_computed, before every
/// jump target. Latch bodies (`DoOnce(X) { ... }` / `FlipFlop(X) { A|B: { ... } }`)
/// are atomic: interior boundaries are suppressed so the DFS emits the latch
/// as one block ending in `}`.
pub(super) fn build_basic_blocks(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
    jump_tolerance: usize,
) -> (Vec<Block>, HashMap<usize, BlockId>) {
    let mut target_indices: HashSet<usize> = HashSet::new();
    for stmt in stmts {
        if let Some((_, target)) = parse_if_jump(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
        if let Some(target) = parse_jump(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
        if let Some(target) = parse_push_flow(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
    }

    // Suppress block boundaries strictly inside latch bodies. The opener still
    // starts a block, the `}` close still ends it.
    let latch_ranges = compute_latch_body_ranges(stmts);
    let inside_latch = |idx: usize| -> bool {
        latch_ranges
            .iter()
            .any(|&(open, close)| idx > open && idx < close)
    };

    let mut blocks: Vec<Block> = Vec::new();
    let mut current_start = 0;
    // Flushed into each Block at close so the structurer can match nested
    // push_flow / pop_flow pairs without re-scanning statement text.
    let mut push_flow_count: u32 = 0;

    let is_block_end = |stmt: &BcStatement| -> bool {
        stmt.text == RETURN_NOP
            || stmt.text == BARE_RETURN
            || stmt.text == POP_FLOW
            || stmt.text.trim() == BLOCK_CLOSE
            || parse_jump(&stmt.text).is_some()
            || parse_if_jump(&stmt.text).is_some()
            || parse_jump_computed(&stmt.text)
    };

    let new_block = |range: Range<usize>, push_flow_count: u32| Block {
        stmt_range: range,
        exit: BlockExit::FallThrough, // patched in wire_block_edges
        metadata: BlockMetadata::Normal,
        emitted: false,
        push_flow_count,
        return_kind: None,
    };

    for (i, stmt) in stmts.iter().enumerate() {
        if target_indices.contains(&i) && i > current_start && !inside_latch(i) {
            blocks.push(new_block(current_start..i, push_flow_count));
            push_flow_count = 0;
            current_start = i;
        }

        if parse_push_flow(&stmt.text).is_some() {
            push_flow_count += 1;
        }

        if is_block_end(stmt) && !inside_latch(i) {
            blocks.push(new_block(current_start..i + 1, push_flow_count));
            push_flow_count = 0;
            current_start = i + 1;
        }
    }
    if current_start < stmts.len() {
        blocks.push(new_block(current_start..stmts.len(), push_flow_count));
    }

    let mut stmt_to_block: HashMap<usize, BlockId> = HashMap::new();
    for (bid, block) in blocks.iter().enumerate() {
        stmt_to_block.insert(block.stmt_range.start, bid);
    }

    (blocks, stmt_to_block)
}

pub(super) fn wire_block_edges(
    blocks: &mut [Block],
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
    stmt_to_block: &HashMap<usize, BlockId>,
    jump_tolerance: usize,
) {
    let resolve_target = |target_offset: usize| -> Option<BlockId> {
        let stmt_idx = offset_map.find_fuzzy(target_offset, jump_tolerance)?;
        stmt_to_block.get(&stmt_idx).copied()
    };

    for bid in 0..blocks.len() {
        let range = &blocks[bid].stmt_range;
        if range.is_empty() {
            continue;
        }
        let last_idx = range.end - 1;
        let last_text = &stmts[last_idx].text;
        let next_block = bid + 1;

        if last_text == POP_FLOW {
            blocks[bid].exit = BlockExit::ReturnTerminal;
            blocks[bid].return_kind = Some(ReturnKind::PopFlow);
        } else if last_text == RETURN_NOP || last_text == BARE_RETURN {
            blocks[bid].exit = BlockExit::ReturnTerminal;
            blocks[bid].return_kind = Some(ReturnKind::Return);
        } else if last_text.trim() == BLOCK_CLOSE {
            blocks[bid].exit = BlockExit::LatchTerminal;
        } else if let Some((_, target)) = parse_if_jump(last_text) {
            let ft = if next_block < blocks.len() {
                next_block
            } else {
                bid
            };
            blocks[bid].exit = match resolve_target(target) {
                Some(tbid) => BlockExit::CondJump {
                    fall_through: ft,
                    target: tbid,
                },
                None => BlockExit::FallThrough,
            };
        } else if let Some(target) = parse_jump(last_text) {
            blocks[bid].exit = match resolve_target(target) {
                Some(tbid) => BlockExit::Jump(tbid),
                None => BlockExit::FallThrough,
            };
        } else if parse_jump_computed(last_text) {
            blocks[bid].exit = BlockExit::ReturnTerminal;
            blocks[bid].return_kind = Some(ReturnKind::JumpComputed);
        }
        // else: FallThrough (default)
    }
}
