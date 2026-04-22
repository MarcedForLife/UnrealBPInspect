//! Sequence-span detection entry, combining grouped + interleaved detectors
//! into a sorted list `cfg/block` uses to collapse each Sequence into a
//! super-block before linearization.

use super::super::decode::BcStatement;
use super::super::OffsetMap;
use super::loops::{detect_grouped_sequences, detect_interleaved_sequences};

pub(super) struct SequencePin {
    pub body_start_idx: usize,
    pub body_end_idx: usize,
}

pub(super) struct SequenceNode {
    pub chain_start: usize,
    pub chain_end: usize,
    pub inline_end: usize,
    pub pins: Vec<SequencePin>,
}

/// Detected Sequence statement span. Indices refer to the source stream
/// passed to the detector. Collapsed into a super-block before linearization.
#[derive(Debug, Clone)]
pub(crate) struct SequenceSpan {
    pub chain: std::ops::Range<usize>,
    pub inline_body: std::ops::Range<usize>,
    pub pins: Vec<std::ops::Range<usize>>,
}

impl SequenceSpan {
    /// Smallest range covering the dispatch chain, inline body, and every pin body.
    pub fn full_range(&self) -> std::ops::Range<usize> {
        let mut end = self.inline_body.end;
        for pin in &self.pins {
            if pin.end > end {
                end = pin.end;
            }
        }
        self.chain.start..end
    }
}

/// Detect every Sequence super-block (grouped + interleaved dispatch chains),
/// sorted by `chain.start`. Parent Sequences that dispatch to children are
/// kept in the result; collapsing callers should skip any span whose
/// `full_range` lies inside an already-consumed range.
pub(crate) fn detect_sequence_spans(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) -> Vec<SequenceSpan> {
    let mut sequences = detect_grouped_sequences(stmts, offset_map);
    // Mark consumed so interleaved detection doesn't re-match the same pairs.
    let mut used = vec![false; stmts.len()];
    for seq in &sequences {
        let chain_end = seq.inline_end.min(stmts.len().saturating_sub(1));
        used[seq.chain_start..=chain_end].fill(true);
        for pin in &seq.pins {
            let end = pin.body_end_idx.min(stmts.len().saturating_sub(1));
            used[pin.body_start_idx..=end].fill(true);
        }
    }
    detect_interleaved_sequences(stmts, &used, offset_map, &mut sequences);
    // SequenceNode inline_end and pin body_end_idx point AT the pop_flow terminator;
    // convert to half-open ranges that include it.
    let mut spans: Vec<SequenceSpan> = sequences
        .into_iter()
        .map(|seq| SequenceSpan {
            chain: seq.chain_start..seq.chain_end,
            inline_body: seq.chain_end..(seq.inline_end + 1),
            pins: seq
                .pins
                .into_iter()
                .map(|pin| pin.body_start_idx..(pin.body_end_idx + 1))
                .collect(),
        })
        .collect();
    spans.sort_by_key(|span| span.chain.start);
    spans
}
