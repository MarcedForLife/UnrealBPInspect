//! Kismet bytecode decoding and structuring pipeline.
//!
//! - [`decode`] - expression decoding into flat statements
//! - [`flow`] - pattern detection (sequences, loops, convergence reorder)
//! - [`structure`] - if/else reconstruction from jump patterns
//! - [`transforms`] - temp inlining, cleanup, summary pattern folding
//! - [`pipeline`] - orchestration (wires the above stages together)

pub mod block_graph;
pub mod cfg;
pub mod decode;
pub mod flow;
mod format;
pub mod latch;
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
///
/// Used by [`flow::BlockCfg::build`] and [`flow::reorder_convergence`], which
/// run directly on freshly-decoded statements where only one mem_adj step has
/// been applied.
pub const JUMP_OFFSET_TOLERANCE: usize = 4;

/// Fuzzy offset tolerance for post-linearization statement lookups. Twice the
/// base [`JUMP_OFFSET_TOLERANCE`] because these lookups run after flow
/// reordering, latch transforms, or cross-event partitioning, where two
/// adjacent FName adjustments can compound and push targets up to 8 bytes
/// away from any surviving statement.
///
/// Used by [`cfg::partition_by_reachability`] (event-partition BFS),
/// [`latch::transform_latch_patterns`] (latch body walks),
/// [`structure`] (if/else structurer), and the ubergraph-layer passes in
/// `output_summary::ubergraph` (entry-block lookup, jump normalization,
/// jump-chain collapse, renumber).
pub const STRUCTURE_OFFSET_TOLERANCE: usize = 8;

// Bytecode statement text constants used across flow, structure, and transform passes.
// These form a producer/consumer protocol: the producer emits one of these tokens,
// downstream passes pattern-match on them to make structural decisions. Centralizing
// the strings here means a rename shows up as compile errors at every call site.

/// Pseudo-return inserted as a sentinel so exit jumps within flow bodies can resolve.
/// Emitted by flow reorder passes and latch transforms, consumed by the structurer,
/// cleanup passes, and ubergraph post-processing.
pub const RETURN_NOP: &str = "return nop";

/// Decoded form of `EX_POP_EXECUTION_FLOW`. Marks the end of a pushed-flow body
/// (latch body, ForEach iteration, sequence pin body). Consumed by BlockCfg,
/// latch transforms, flow reorder, and the structurer.
pub const POP_FLOW: &str = "pop_flow";

/// Bare `return` without the `nop` suffix. Treated as a terminal by BlockCfg and
/// the structurer, and as an unconditional-dead-code trigger by cleanup passes.
pub const BARE_RETURN: &str = "return";

/// Standalone closing brace. Emitted by `emit_single_loop`, latch transforms, and
/// the structurer to close a block. BlockCfg treats it as a block terminator,
/// cleanup passes use it for brace balance.
pub const BLOCK_CLOSE: &str = "}";

/// Sequence pin marker prefix emitted by `flow::SequenceEmitter::emit` as
/// `// sequence [N]:`. Consumed by `split_by_sequence_markers`, the `has_sequences`
/// gate in `reorder_convergence`, `post_structure_cleanup`, and cleanup passes.
pub const SEQUENCE_MARKER_PREFIX: &str = "// sequence [";

/// Child-sequence marker prefix emitted by `flow::SequenceEmitter::emit` when
/// `depth > 0`. Distinct from `SEQUENCE_MARKER_PREFIX` so that
/// `split_by_sequence_markers` doesn't tear a parent pin body apart at nested
/// sequences. Consumed by cleanup passes and comment placement in `output_summary`.
pub const SUB_SEQUENCE_MARKER_PREFIX: &str = "// sub-sequence [";

/// Weaker prefix that matches both `// sequence [` and `// sub-sequence [`.
/// Used by consumers that treat both marker families uniformly (e.g. comment
/// anchor resolution in `output_summary::comments`).
pub const ANY_SEQUENCE_MARKER_PREFIX: &str = "// sequence";

/// Weaker prefix form of `SUB_SEQUENCE_MARKER_PREFIX` matching `// sub-sequence`
/// without the opening bracket. Used alongside `ANY_SEQUENCE_MARKER_PREFIX` at
/// consumers that check both `[N]:` variants and potential future suffix changes.
pub const ANY_SUB_SEQUENCE_MARKER_PREFIX: &str = "// sub-sequence";

/// Loop-completion marker emitted by `emit_single_loop` after a ForEach/while body.
/// `dedup_completion_paths` in `transforms::pipeline` walks forward from this line
/// to find the completion block. `post_structure_cleanup` strips bare occurrences
/// after structuring, keeping annotated variants like
/// `LOOP_COMPLETE_SAME_AS_PRELOOP` / `LOOP_COMPLETE_REPEATS_PRELOOP`.
pub const LOOP_COMPLETE_MARKER: &str = "// on loop complete:";

/// Annotated loop-completion marker emitted when the completion block duplicates
/// the pre-loop setup entirely.
pub const LOOP_COMPLETE_SAME_AS_PRELOOP: &str = "// on loop complete: (same as pre-loop setup)";

/// Annotated loop-completion marker emitted when the completion block repeats
/// the pre-loop setup with additional unique lines.
pub const LOOP_COMPLETE_REPEATS_PRELOOP: &str = "// on loop complete: (repeats pre-loop setup)";

/// Build the sequence pin marker for index `idx` (top-level sequences).
pub fn sequence_marker(idx: usize) -> String {
    format!("{SEQUENCE_MARKER_PREFIX}{idx}]:")
}

/// Build the sub-sequence pin marker for index `idx` (nested child sequences).
pub fn sub_sequence_marker(idx: usize) -> String {
    format!("{SUB_SEQUENCE_MARKER_PREFIX}{idx}]:")
}

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

    /// Fuzzy lookup preferring the first statement at or after `target`.
    ///
    /// Event entry labels land on the start of an instruction that may have been
    /// filtered (wire_trace, tracepoint), so the first decoded statement is always
    /// forward. Falls back to the nearest below-target statement if no forward
    /// match exists within `tolerance`.
    pub fn find_fuzzy_forward(&self, target: usize, tolerance: usize) -> Option<usize> {
        if let Some(&idx) = self.exact.get(&target) {
            return Some(idx);
        }
        let pos = self.sorted.partition_point(|&(off, _)| off <= target);
        let above = if pos < self.sorted.len() {
            let (off, idx) = self.sorted[pos];
            let dist = off.saturating_sub(target);
            if dist <= tolerance {
                Some(idx)
            } else {
                None
            }
        } else {
            None
        };
        if above.is_some() {
            return above;
        }
        if pos > 0 {
            let (off, idx) = self.sorted[pos - 1];
            let dist = target.saturating_sub(off);
            if dist <= tolerance {
                return Some(idx);
            }
        }
        None
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
