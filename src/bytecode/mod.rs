//! Kismet bytecode decoding and structuring pipeline.
//!
//! 1. [`decode`]: expression decoding into flat statements
//! 2. [`flow`]: pattern detection (sequences, loops, convergence reorder)
//! 3. [`structure`]: if/else reconstruction from jump patterns
//! 4. [`inline`]: temp inlining, cleanup, summary pattern folding

pub mod decode;
pub mod flow;
pub mod inline;
pub mod names;
pub mod opcodes;
pub mod readers;
pub mod resolve;
pub mod structure;

use std::collections::HashMap;

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
            (Some((bo, bi)), Some((ao, ai))) => {
                let bd = target.saturating_sub(bo);
                let ad = ao.saturating_sub(target);
                if bd <= ad {
                    Some((bd, bi))
                } else {
                    Some((ad, ai))
                }
            }
            (Some((bo, bi)), None) => Some((target.saturating_sub(bo), bi)),
            (None, Some((ao, ai))) => Some((ao.saturating_sub(target), ai)),
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
