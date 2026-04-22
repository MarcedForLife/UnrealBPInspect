//! Emits a reordered statement stream from detected SequenceNode/ForLoop lists,
//! with marker lines downstream passes use to recover pin boundaries and bodies.

use std::collections::HashSet;

use super::super::decode::BcStatement;
use super::super::{
    sequence_marker, sub_sequence_marker, OffsetMap, BLOCK_CLOSE, JUMP_OFFSET_TOLERANCE,
    LOOP_COMPLETE_MARKER, POP_FLOW, RETURN_NOP,
};
use super::loops::{find_child_sequence_starts, find_displaced_blocks, ForLoop};
use super::parsers::{parse_jump, parse_pop_flow_if_not, parse_push_flow};
use super::sequence::SequenceNode;

/// Shared state for Sequence emission. Tracks emitted chains so child
/// Sequences aren't re-emitted when the main loop reaches their position.
struct SequenceEmitter<'a> {
    stmts: &'a [BcStatement],
    sequences: &'a [SequenceNode],
    child_starts: &'a HashSet<usize>,
    offset_map: &'a OffsetMap,
    emitted: HashSet<usize>,
}

impl<'a> SequenceEmitter<'a> {
    fn emit(&mut self, seq: &SequenceNode, depth: usize, output: &mut Vec<BcStatement>) {
        let seq_offset = self.stmts[seq.chain_start].mem_offset;
        // Child markers use the sub- prefix so `split_by_sequence_markers`
        // doesn't tear the parent pin body apart.
        let build_marker = |idx: usize| -> String {
            if depth > 0 {
                sub_sequence_marker(idx)
            } else {
                sequence_marker(idx)
            }
        };
        let marker = |text: String| BcStatement::new(seq_offset, text);
        let sentinel =
            |idx: usize| BcStatement::new(self.stmts[idx].mem_offset, RETURN_NOP.to_string());

        for (pi, pin) in seq.pins.iter().enumerate() {
            output.push(marker(build_marker(pi)));
            output.extend_from_slice(&self.stmts[pin.body_start_idx..pin.body_end_idx]);
            self.emit_child_sequences(pin.body_start_idx, pin.body_end_idx, depth, output);
            // Sentinel so intra-body if-else exit jumps resolve.
            output.push(sentinel(pin.body_end_idx));
        }

        output.push(marker(build_marker(seq.pins.len())));
        output.extend_from_slice(&self.stmts[seq.chain_end..seq.inline_end]);
        self.emit_child_sequences(seq.chain_end, seq.inline_end, depth, output);
        output.push(sentinel(seq.inline_end));

        for &(ds, de) in
            &find_displaced_blocks(self.stmts, seq.chain_end, seq.inline_end, self.offset_map)
        {
            output.extend_from_slice(&self.stmts[ds..de]);
            output.push(sentinel(de));
        }
    }

    /// Find unconditional jumps to child Sequences, emit them inline, and
    /// remove the triggering jump (the child content now follows directly).
    fn emit_child_sequences(
        &mut self,
        scan_start: usize,
        scan_end: usize,
        depth: usize,
        output: &mut Vec<BcStatement>,
    ) {
        for idx in scan_start..scan_end.min(self.stmts.len()) {
            let Some(target) = parse_jump(&self.stmts[idx].text) else {
                continue;
            };
            let Some(target_idx) = self.offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) else {
                continue;
            };
            let child_chain = self.sequences.iter().find_map(|seq| {
                if self.child_starts.contains(&seq.chain_start)
                    && target_idx >= seq.chain_start
                    && target_idx <= seq.inline_end
                    && !self.emitted.contains(&seq.chain_start)
                {
                    Some(seq.chain_start)
                } else {
                    None
                }
            });
            if let Some(chain_start) = child_chain {
                let jump_stmt = &self.stmts[idx];
                if let Some(pos) = output
                    .iter()
                    .rposition(|s| s.mem_offset == jump_stmt.mem_offset && s.text == jump_stmt.text)
                {
                    output.remove(pos);
                }
                self.emitted.insert(chain_start);
                if let Some(child) = self.sequences.iter().find(|s| s.chain_start == chain_start) {
                    self.emit(child, depth + 1, output);
                }
            }
        }
    }
}

/// Emit a single loop: header, extra, body (recursive), increment, close,
/// completion. `nested` suppresses the trailing return nop (which belongs to
/// the function, not the inner loop).
fn emit_single_loop(
    stmts: &[BcStatement],
    lp: &ForLoop,
    loops: &[ForLoop],
    emitted: &mut HashSet<usize>,
    nested: bool,
    output: &mut Vec<BcStatement>,
) {
    emitted.insert(lp.if_idx);
    let lp_offset = stmts[lp.if_idx].mem_offset;
    let marker = |text: &str| BcStatement::new(lp_offset, text.to_string());
    let body_end = if stmts[lp.body_end_idx].text == RETURN_NOP {
        lp.body_end_idx
    } else {
        lp.body_end_idx + 1
    };
    // Confirmed ForEach drops the increment; unconfirmed keeps it as `while`.
    let keyword = if lp.foreach.is_some() {
        "foreach"
    } else {
        "while"
    };
    output.push(marker(&format!("{} ({}) {{", keyword, lp.cond_text)));
    if lp.extra_start < lp.extra_end {
        output.extend_from_slice(&stmts[lp.extra_start..lp.extra_end]);
    }
    let body_output_start = output.len();
    emit_body_range(stmts, lp.body_start_idx, body_end, loops, emitted, output);
    // In confirmed ForEach, pop_flow_if_not means "continue", not "break";
    // rewrite to a marker the structurer handles differently.
    if lp.foreach.is_some() {
        for stmt in &mut output[body_output_start..] {
            if let Some(cond) = parse_pop_flow_if_not(&stmt.text) {
                stmt.text = format!("continue_if_not({})", cond);
            }
        }
    }
    if lp.foreach.is_none() {
        output.extend_from_slice(&stmts[lp.incr_start..lp.back_jump_idx]);
    }
    output.push(marker(BLOCK_CLOSE));
    // ForEach completion path: convert pop_flow to unconditional jumps to the
    // function return so the structurer detects if/else boundaries (skip-else
    // pattern). Emit a no-op anchor at the next statement's offset after each
    // converted jump so inline passes can't remove the OffsetMap entry the
    // structurer needs. Strip push_flow and plain jumps (loop control artifacts).
    if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
        output.push(marker(LOOP_COMPLETE_MARKER));
        let end_offset = stmts[lp.body_end_idx].mem_offset;
        let completion = &stmts[cs..=ce];
        for (rel, stmt) in completion.iter().enumerate() {
            if parse_push_flow(&stmt.text).is_some() || parse_jump(&stmt.text).is_some() {
                continue;
            }
            if stmt.text == POP_FLOW {
                output.push(BcStatement::new(
                    stmt.mem_offset,
                    format!("jump 0x{:x}", end_offset),
                ));
                // Anchor: next stmt's offset must survive in OffsetMap even
                // if inline passes remove its original statement.
                if let Some(next) = completion.get(rel + 1) {
                    if next.mem_offset > 0 {
                        output.push(BcStatement::new(next.mem_offset, String::new()));
                    }
                }
                continue;
            }
            output.push(stmt.clone());
        }
    }
    // Only top-level loops emit the trailing return nop. Nested loops share
    // the same body_end_idx (inflated to stmts.len()-1); emitting it inside
    // the parent would let dead-code elimination strip the parent's completion.
    if !nested && stmts[lp.body_end_idx].text == RETURN_NOP {
        output.push(stmts[lp.body_end_idx].clone());
    }
}

/// Emit statements in a range, recursively formatting nested loops. The
/// `emitted` set prevents double-formatting when sibling loops share inflated
/// body_end ranges; `consumed` tracks indices already emitted by a nested loop.
fn emit_body_range(
    stmts: &[BcStatement],
    start: usize,
    end: usize,
    loops: &[ForLoop],
    emitted: &mut HashSet<usize>,
    output: &mut Vec<BcStatement>,
) {
    let mut consumed = HashSet::new();
    let mut i = start;
    while i < end {
        if let Some(inner) = loops
            .iter()
            .find(|l| l.if_idx == i && !emitted.contains(&l.if_idx))
        {
            // Mark the inner body range consumed so it isn't re-emitted flat.
            let inner_body_end = if inner.body_end_idx < end {
                inner.body_end_idx + 1
            } else {
                end
            };
            for idx in inner.body_start_idx..inner_body_end {
                consumed.insert(idx);
            }
            emit_single_loop(stmts, inner, loops, emitted, true, output);
            i = inner.loop_ctrl_end + 1;
        } else if consumed.contains(&i) {
            i += 1;
        } else {
            output.push(stmts[i].clone());
            i += 1;
        }
    }
}

/// Emit reordered statements with sequence pins and loop bodies inlined.
pub(super) fn emit_reordered(
    stmts: &[BcStatement],
    sequences: &[SequenceNode],
    loops: &[ForLoop],
    used: &mut [bool],
    offset_map: &OffsetMap,
) -> Vec<BcStatement> {
    let child_starts = find_child_sequence_starts(stmts, sequences, offset_map);

    for seq in sequences {
        used[seq.chain_start..=seq.inline_end].fill(true);
        for pin in &seq.pins {
            used[pin.body_start_idx..=pin.body_end_idx].fill(true);
        }
        for &(ds, de) in &find_displaced_blocks(stmts, seq.chain_end, seq.inline_end, offset_map) {
            if de < used.len() {
                used[ds..=de].fill(true);
            }
        }
    }
    for lp in loops {
        used[lp.if_idx..=lp.loop_ctrl_end].fill(true);
        used[lp.body_start_idx..=lp.body_end_idx].fill(true);
        if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
            used[cs..=ce].fill(true);
        }
        if let Some(ref info) = lp.foreach {
            for &idx in &info.init_indices {
                if idx < used.len() {
                    used[idx] = true;
                }
            }
        }
    }

    let mut output: Vec<BcStatement> = Vec::new();
    let mut emitter = SequenceEmitter {
        stmts,
        sequences,
        child_starts: &child_starts,
        offset_map,
        emitted: HashSet::new(),
    };
    let mut emitted_loops: HashSet<usize> = HashSet::new();

    let mut i = 0;
    while i < stmts.len() {
        if let Some(seq) = sequences.iter().find(|s| s.chain_start == i) {
            let is_child = child_starts.contains(&seq.chain_start);
            if !is_child && !emitter.emitted.contains(&seq.chain_start) {
                emitter.emitted.insert(seq.chain_start);
                emitter.emit(seq, 0, &mut output);
            }
            i = seq.inline_end + 1;
            continue;
        }

        if let Some(lp) = loops
            .iter()
            .find(|l| l.if_idx == i && !emitted_loops.contains(&l.if_idx))
        {
            emit_single_loop(stmts, lp, loops, &mut emitted_loops, false, &mut output);
            i = lp.loop_ctrl_end + 1;
            continue;
        }

        if !used[i] {
            output.push(stmts[i].clone());
        }
        i += 1;
    }

    output
}
