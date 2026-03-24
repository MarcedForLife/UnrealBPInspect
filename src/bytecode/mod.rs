//! Kismet bytecode decoding and structuring pipeline.
//!
//! 1. [`decode`]: expression decoding into flat statements
//! 2. [`flow`]: pattern detection (sequences, loops, convergence reorder)
//! 3. [`structure`]: if/else reconstruction from jump patterns
//! 4. [`inline`]: temp inlining, cleanup, summary pattern folding

pub mod decode;
pub mod flow;
mod format;
pub mod inline;
pub mod names;
pub mod opcodes;
pub mod readers;
pub mod resolve;
pub mod structure;

use std::collections::HashMap;

/// Fuzzy offset tolerance for jump target resolution. FName operands are 8 bytes
/// on disk but 12 in memory, so each FName read shifts targets by +4 bytes. This
/// single-step granularity covers the common case of one missed adjustment.
pub const JUMP_OFFSET_TOLERANCE: usize = 4;

pub use decode::{decode_bytecode, BcStatement};
pub use flow::{
    parse_if_jump, parse_jump, parse_push_flow, reorder_convergence, reorder_flow_patterns,
};
pub use inline::{
    cleanup_structured_output, discard_unused_assignments, fold_summary_patterns,
    inline_constant_temps, inline_single_use_temps, strip_orphaned_blocks, strip_unmatched_braces,
};
pub use structure::structure_bytecode;

/// Maps bytecode memory offsets to statement indices with fuzzy matching.
/// Jump targets can land on filtered opcodes (wire_trace, tracepoint), so the
/// nearest statement may be a few bytes away from the target address.
pub struct OffsetMap {
    exact: HashMap<usize, usize>,
    sorted: Vec<(usize, usize)>, // (offset, index), sorted by offset
}

impl OffsetMap {
    /// Build from statements, filtering out entries with mem_offset == 0.
    pub fn build(stmts: &[BcStatement]) -> Self {
        let exact: HashMap<usize, usize> = stmts
            .iter()
            .enumerate()
            .filter(|(_, s)| s.mem_offset > 0)
            .map(|(i, s)| (s.mem_offset, i))
            .collect();
        let mut sorted: Vec<(usize, usize)> = exact.iter().map(|(&off, &idx)| (off, idx)).collect();
        sorted.sort_by_key(|&(off, _)| off);
        OffsetMap { exact, sorted }
    }

    /// Exact offset lookup.
    pub fn find(&self, target: usize) -> Option<usize> {
        self.exact.get(&target).copied()
    }

    /// Fuzzy lookup: exact match first, then closest within `tolerance` bytes.
    pub fn find_fuzzy(&self, target: usize, tolerance: usize) -> Option<usize> {
        if let Some(&idx) = self.exact.get(&target) {
            return Some(idx);
        }
        let pos = self.sorted.partition_point(|&(off, _)| off <= target);
        let below = if pos > 0 {
            Some(self.sorted[pos - 1])
        } else {
            None
        };
        let above = if pos < self.sorted.len() {
            Some(self.sorted[pos])
        } else {
            None
        };
        let best = match (below, above) {
            (Some((below_off, below_idx)), Some((above_off, above_idx))) => {
                let below_dist = target.saturating_sub(below_off);
                let above_dist = above_off.saturating_sub(target);
                if below_dist <= above_dist {
                    Some((below_dist, below_idx))
                } else {
                    Some((above_dist, above_idx))
                }
            }
            (Some((below_off, below_idx)), None) => {
                Some((target.saturating_sub(below_off), below_idx))
            }
            (None, Some((above_off, above_idx))) => {
                Some((above_off.saturating_sub(target), above_idx))
            }
            (None, None) => None,
        };
        match best {
            Some((dist, idx)) if dist <= tolerance => Some(idx),
            _ => None,
        }
    }

    /// Fuzzy lookup that also resolves targets past the last statement to `stmts.len()`.
    pub fn find_fuzzy_or_end(
        &self,
        target: usize,
        tolerance: usize,
        stmts_len: usize,
    ) -> Option<usize> {
        self.find_fuzzy(target, tolerance).or_else(|| {
            if !self.sorted.is_empty() && target > self.sorted.last().unwrap().0 {
                Some(stmts_len)
            } else {
                None
            }
        })
    }
}
