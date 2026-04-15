//! Kismet bytecode decoding and structuring pipeline.
//!
//! - [`decode`] - expression decoding into flat statements
//! - [`flow`] - pattern detection (sequences, loops, convergence reorder)
//! - [`structure`] - if/else reconstruction from jump patterns
//! - [`transforms`] - temp inlining, cleanup, summary pattern folding
//! - [`pipeline`] - orchestration (wires the above stages together)

pub mod decode;
pub mod flow;
mod format;
pub mod names;
pub mod opcodes;
pub mod pipeline;
pub mod readers;
pub mod resolve;
pub mod structure;
pub mod transforms;

use std::collections::HashMap;

/// Fuzzy offset tolerance for jump target resolution. FName operands are 8 bytes
/// on disk but 12 in memory, so each FName read shifts targets by +4 bytes. This
/// single-step granularity covers the common case of one missed adjustment.
pub const JUMP_OFFSET_TOLERANCE: usize = 4;

// Bytecode statement text constants used across flow, structure, and transform passes.
pub const RETURN_NOP: &str = "return nop";
pub const POP_FLOW: &str = "pop_flow";
pub const SEQUENCE_MARKER_PREFIX: &str = "// sequence [";

/// Target line width for pseudocode readability. Used by temp inlining (skip
/// substitutions that would exceed this), line folding, and ternary hoisting.
pub const MAX_LINE_WIDTH: usize = 120;

pub use decode::{decode_bytecode, BcStatement};

/// Split BcStatements at `// sequence [N]:` markers.
/// Returns a list of (optional marker text, body statements).
/// When there are no sequence markers, returns a single entry.
pub fn split_by_sequence_markers(stmts: &[BcStatement]) -> Vec<(Option<String>, Vec<BcStatement>)> {
    let marker_indices: Vec<usize> = stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| s.text.starts_with(SEQUENCE_MARKER_PREFIX))
        .map(|(i, _)| i)
        .collect();

    if marker_indices.is_empty() {
        return vec![(None, stmts.to_vec())];
    }

    let mut result = Vec::new();

    // Statements before the first marker (prefix)
    if marker_indices[0] > 0 {
        result.push((None, stmts[..marker_indices[0]].to_vec()));
    }

    for (i, &start) in marker_indices.iter().enumerate() {
        let marker_text = stmts[start].text.clone();
        let body_start = start + 1;
        let body_end = if i + 1 < marker_indices.len() {
            marker_indices[i + 1]
        } else {
            stmts.len()
        };
        let body: Vec<BcStatement> = if body_start < body_end {
            stmts[body_start..body_end].to_vec()
        } else {
            Vec::new()
        };
        result.push((Some(marker_text), body));
    }

    result
}

/// Maps bytecode memory offsets to statement indices with fuzzy matching.
/// Jump targets can land on filtered opcodes (wire_trace, tracepoint), so the
/// nearest statement may be a few bytes away from the target address.
pub struct OffsetMap {
    exact: HashMap<usize, usize>,
    sorted: Vec<(usize, usize)>, // (offset, index), sorted by offset
}

impl OffsetMap {
    /// Build from statements, including offset aliases from inlined temps.
    pub fn build(stmts: &[BcStatement]) -> Self {
        let mut exact: HashMap<usize, usize> = HashMap::new();
        for (i, stmt) in stmts.iter().enumerate() {
            if stmt.mem_offset > 0 {
                exact.insert(stmt.mem_offset, i);
            }
            for &alias in &stmt.offset_aliases {
                if alias > 0 {
                    exact.entry(alias).or_insert(i);
                }
            }
        }
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
                if below_dist < above_dist {
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
