//! ForLoop, ForEach, and Sequence dispatch-chain detection. Handles init
//! suppression, counter variables, displaced ForEach bodies, and child
//! sequence starts inside loop bodies.

use std::collections::HashSet;

use super::super::decode::{BcStatement, StmtKind};
use super::super::{OffsetMap, JUMP_OFFSET_TOLERANCE};
use super::sequence::{SequenceNode, SequencePin};
use super::{FORLOOP_OFFSET_TOLERANCE, FORLOOP_PUSHFLOW_WINDOW};

/// Set `BP_INSPECT_TRACE_SEQUENCES=1` to print per-candidate accept/reject
/// decisions for Sequence detection. Useful when a parser change drops a
/// Sequence and the structurer's downstream output looks scrambled.
const SEQ_TRACE_ENV: &str = "BP_INSPECT_TRACE_SEQUENCES";

fn seq_trace_enabled() -> bool {
    std::env::var(SEQ_TRACE_ENV).is_ok()
}

fn format_pin_ranges(pins: &[SequencePin]) -> String {
    pins.iter()
        .map(|p| format!("{}..{}", p.body_start_idx, p.body_end_idx))
        .collect::<Vec<_>>()
        .join(",")
}

pub(super) struct ForLoop {
    pub(super) cond_text: String,
    pub(super) if_idx: usize,
    pub(super) extra_start: usize,
    pub(super) extra_end: usize,
    pub(super) incr_start: usize,
    pub(super) back_jump_idx: usize,
    pub(super) loop_ctrl_end: usize,
    pub(super) body_start_idx: usize,
    pub(super) body_end_idx: usize,
    pub(super) completion_start: Option<usize>,
    pub(super) completion_end: Option<usize>,
    /// Set when this loop is a confirmed ForEach. Flow emits `foreach {` and
    /// suppresses init/increment boilerplate so the pattern layer only
    /// extracts ITEM/ARRAY from the body.
    pub(super) foreach: Option<ForeachInfo>,
}

pub(super) struct ForeachInfo {
    /// `Temp_int_* = 0` init statements to suppress from output.
    pub(super) init_indices: Vec<usize>,
}

/// Expand a Sequence pin's body boundary by following if/jump targets beyond
/// the current end. Rescans after each expansion (new code may contain further jumps).
fn expand_body_end(
    stmts: &[BcStatement],
    body_start: usize,
    initial_end: usize,
    existing_pins: &[(usize, usize)],
    offset_map: &OffsetMap,
) -> usize {
    let mut be = initial_end;
    let mut scan_from = body_start;
    loop {
        let mut expanded = false;
        let mut idx = scan_from;
        while idx <= be {
            if let Some((_, jump_target)) = stmts[idx].if_jump() {
                if let Some(target_idx) = offset_map.find_fuzzy(jump_target, JUMP_OFFSET_TOLERANCE)
                {
                    let in_other_pin = existing_pins
                        .iter()
                        .any(|&(ps, pe)| target_idx >= ps && target_idx <= pe);
                    if target_idx > be && !in_other_pin {
                        if let Some(displaced_end) = stmts[target_idx..]
                            .iter()
                            .position(|s| s.kind == StmtKind::PopFlow)
                            .map(|p| p + target_idx)
                        {
                            if displaced_end > be {
                                scan_from = be + 1;
                                be = displaced_end;
                                expanded = true;
                            }
                        }
                    }
                }
            }
            idx += 1;
        }
        if !expanded {
            break;
        }
    }
    be
}

/// Enumerate displaced blocks reachable from the inline body's if/jump targets.
/// Returns `(start_idx, pop_flow_idx)` pairs.
pub(super) fn find_displaced_blocks(
    stmts: &[BcStatement],
    body_start: usize,
    body_end: usize,
    offset_map: &OffsetMap,
) -> Vec<(usize, usize)> {
    let mut blocks = Vec::new();
    for idx in body_start..body_end {
        let Some((_, jump_target)) = stmts[idx].if_jump() else {
            continue;
        };
        let Some(target_idx) = offset_map.find_fuzzy(jump_target, JUMP_OFFSET_TOLERANCE) else {
            continue;
        };
        if target_idx <= body_end {
            continue;
        }
        let Some(displaced_end) = stmts[target_idx..]
            .iter()
            .position(|s| s.kind == StmtKind::PopFlow)
            .map(|p| p + target_idx)
        else {
            continue;
        };
        blocks.push((target_idx, displaced_end));
    }
    blocks
}

/// Detect grouped push_flow chains: regular functions emit
/// `push_flow E; push_flow C; jump body0; push_flow D; jump body1; ... inline; pop_flow`.
pub(super) fn detect_grouped_sequences(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) -> Vec<SequenceNode> {
    let mut sequences: Vec<SequenceNode> = Vec::new();

    let mut i = 0;
    while i < stmts.len() {
        let Some(_end_offset) = stmts[i].push_flow_target() else {
            i += 1;
            continue;
        };

        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut scan_idx = i + 1;
        while scan_idx + 1 < stmts.len() {
            let Some(_cont) = stmts[scan_idx].push_flow_target() else {
                break;
            };
            let Some(body) = stmts[scan_idx + 1].jump_target() else {
                break;
            };
            pairs.push((_cont, body));
            scan_idx += 2;
        }

        if pairs.len() < 2 {
            i += 1;
            continue;
        }

        let inline_start = scan_idx;
        let inline_end = stmts[inline_start..]
            .iter()
            .position(|s| s.kind == StmtKind::PopFlow)
            .map(|p| p + inline_start);
        let Some(inline_end) = inline_end else {
            i += 1;
            continue;
        };

        let mut pins: Vec<SequencePin> = Vec::new();
        let mut body_scan = inline_end + 1;
        for _ in 0..pairs.len() {
            if body_scan >= stmts.len() {
                break;
            }
            let body_start = body_scan;
            let Some(initial_end) = stmts[body_start..]
                .iter()
                .position(|s| s.kind == StmtKind::PopFlow)
                .map(|p| p + body_start)
            else {
                break;
            };
            let pin_ranges: Vec<(usize, usize)> = pins
                .iter()
                .map(|p| (p.body_start_idx, p.body_end_idx))
                .collect();
            let body_end = expand_body_end(stmts, body_start, initial_end, &pin_ranges, offset_map);
            pins.push(SequencePin {
                body_start_idx: body_start,
                body_end_idx: body_end,
            });
            body_scan = body_end + 1;
        }
        if pins.len() != pairs.len() {
            i += 1;
            continue;
        }

        if seq_trace_enabled() {
            eprintln!(
                "[seq:grouped] chain={}..{} pairs={} inline_end={} pins=[{}]",
                i,
                scan_idx,
                pairs.len(),
                inline_end,
                format_pin_ranges(&pins),
            );
        }

        sequences.push(SequenceNode {
            chain_start: i,
            chain_end: inline_start,
            inline_end,
            pins,
        });

        i = inline_end + 1;
    }

    sequences
}

/// Detect alternating push_flow/jump chains (UberGraph pattern):
/// `push_flow A; jump body0; push_flow B; jump body1; ... inline_code; pop_flow`.
pub(super) fn detect_interleaved_sequences(
    stmts: &[BcStatement],
    used: &[bool],
    offset_map: &OffsetMap,
    sequences: &mut Vec<SequenceNode>,
) {
    let mut i = 0;
    while i + 1 < stmts.len() {
        if used[i] {
            i += 1;
            continue;
        }
        let Some(_resume) = stmts[i].push_flow_target() else {
            i += 1;
            continue;
        };
        let Some(_body_off) = stmts[i + 1].jump_target() else {
            i += 1;
            continue;
        };

        // Skip for-loop body dispatch: a for-loop has `if !(cond) jump` BEFORE
        // the push_flow AND a back-edge jump AFTER it. Checking both directions
        // avoids false skips on if-guarded Sequences (preceding if-jump, no back-edge).
        const BACK_JUMP_SEARCH_WINDOW: usize = 10;
        let is_forloop_dispatch = (1..=FORLOOP_PUSHFLOW_WINDOW).any(|offset| {
            if i < offset {
                return false;
            }
            let cond_idx = i - offset;
            if stmts[cond_idx].if_jump().is_none() {
                return false;
            }
            let incr_start = i + 2;
            let search_end = stmts.len().min(incr_start + BACK_JUMP_SEARCH_WINDOW);
            (incr_start..search_end).any(|scan_idx| {
                stmts[scan_idx]
                    .jump_target()
                    .is_some_and(|back_target| back_target <= stmts[cond_idx].mem_offset)
            })
        });
        if is_forloop_dispatch {
            i += 2;
            continue;
        }

        let chain_start = i;
        let mut jump_targets: Vec<usize> = Vec::new(); // body offsets
        let mut scan_idx = i;
        while scan_idx + 1 < stmts.len() && !used[scan_idx] {
            let Some(_resume) = stmts[scan_idx].push_flow_target() else {
                break;
            };
            let Some(body_off) = stmts[scan_idx + 1].jump_target() else {
                break;
            };
            jump_targets.push(body_off);
            scan_idx += 2;
        }
        if jump_targets.is_empty() {
            i += 1;
            continue;
        }

        // Inline body ends at exact pop_flow (pop_flow_if_not is a conditional
        // branch within the body, not the terminator).
        let inline_start = scan_idx;
        let inline_end = stmts[inline_start..]
            .iter()
            .position(|s| s.kind == StmtKind::PopFlow)
            .map(|p| p + inline_start);
        let Some(inline_end) = inline_end else {
            i += 1;
            continue;
        };

        let mut pins: Vec<SequencePin> = Vec::new();
        let mut all_found = true;
        for &target in &jump_targets {
            let Some(body_start) = offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) else {
                all_found = false;
                break;
            };
            // Body ends at first pop_flow, expanded to include displaced blocks
            // (switch case bodies, etc.).
            let Some(initial_end) = stmts[body_start..]
                .iter()
                .position(|s| s.kind == StmtKind::PopFlow)
                .map(|p| p + body_start)
            else {
                all_found = false;
                break;
            };
            let pin_ranges: Vec<(usize, usize)> = pins
                .iter()
                .map(|p| (p.body_start_idx, p.body_end_idx))
                .collect();
            let body_end = expand_body_end(stmts, body_start, initial_end, &pin_ranges, offset_map);
            pins.push(SequencePin {
                body_start_idx: body_start,
                body_end_idx: body_end,
            });
        }
        if !all_found || pins.len() != jump_targets.len() {
            i += 1;
            continue;
        }

        // Reject pins whose RANGE overlaps our own chain or inline body
        // (degenerate post-latch layout with scaffolding removed -- treating
        // it as a Sequence duplicates pin markers). Pins lying entirely
        // before `chain_start` are legal: the bytecode emitter places pin
        // bodies wherever they fall in the stream, and a small content edit
        // upstream can shift a pin from after-chain to before-chain. The
        // detector must be stable across that shift.
        let pin_overlaps_chain = pins
            .iter()
            .any(|p| !(p.body_end_idx < chain_start || p.body_start_idx > inline_end));
        if pin_overlaps_chain {
            if seq_trace_enabled() {
                eprintln!(
                    "[seq:reject] chain={}..{} pairs={} inline_end={} reason=pin-overlaps-chain pins=[{}]",
                    chain_start,
                    scan_idx,
                    jump_targets.len(),
                    inline_end,
                    format_pin_ranges(&pins),
                );
            }
            i += 1;
            continue;
        }

        // Single-pair: require 2+ meaningful statements in the inline body to
        // avoid false positives on trivial UberGraph stubs.
        if jump_targets.len() == 1 {
            let meaningful = stmts[inline_start..inline_end]
                .iter()
                .filter(|s| {
                    s.kind != StmtKind::PopFlow
                        && !s.text.starts_with("push_flow ")
                        && !s.text.starts_with("pop_flow_if_not(")
                })
                .count();
            if meaningful < 2 {
                i += 1;
                continue;
            }
        }

        if seq_trace_enabled() {
            eprintln!(
                "[seq:accept] chain={}..{} pairs={} inline_end={} pins=[{}]",
                chain_start,
                scan_idx,
                jump_targets.len(),
                inline_end,
                format_pin_ranges(&pins),
            );
        }

        sequences.push(SequenceNode {
            chain_start,
            chain_end: inline_start,
            inline_end,
            pins,
        });
        i = inline_end + 1;
    }
}

/// Resolve ForEach body layout (may be displaced after the completion path).
/// Returns `(body_start, loop_ctrl_end, completion_start, completion_end)`;
/// `None` completion means no displaced body.
fn resolve_foreach_body(
    stmts: &[BcStatement],
    body_jump_target: usize,
    back_jump_idx: usize,
    pop_idx: Option<usize>,
) -> Option<(usize, usize, Option<usize>, Option<usize>)> {
    if let Some(pop_idx) = pop_idx {
        let body_at_jump = stmts.iter().position(|s| {
            s.mem_offset > 0 && s.mem_offset.abs_diff(body_jump_target) < FORLOOP_OFFSET_TOLERANCE
        });
        let (body_start, completion) = match body_at_jump {
            Some(actual_body) if actual_body > pop_idx + 1 => {
                (actual_body, (Some(pop_idx + 1), Some(actual_body - 1)))
            }
            _ => (pop_idx + 1, (None, None)),
        };
        Some((body_start, pop_idx, completion.0, completion.1))
    } else {
        // Closest match, not first-match: completion-path statements can land
        // inside the tolerance window of the body target.
        let mut body_idx = stmts
            .iter()
            .enumerate()
            .filter(|(_, s)| {
                s.mem_offset > 0
                    && s.mem_offset.abs_diff(body_jump_target) < FORLOOP_OFFSET_TOLERANCE
            })
            .min_by_key(|(_, s)| s.mem_offset.abs_diff(body_jump_target))
            .map(|(idx, _)| idx)?;
        // Fuzzy matching can land on a preceding terminator; skip to real content.
        while body_idx < stmts.len()
            && matches!(
                stmts[body_idx].kind,
                StmtKind::PopFlow | StmtKind::ReturnNop
            )
        {
            body_idx += 1;
        }
        // If body is displaced past back_jump, the gap is the completion path.
        let (cs, ce) = if body_idx > back_jump_idx + 1 {
            (Some(back_jump_idx + 1), Some(body_idx - 1))
        } else {
            (None, None)
        };
        Some((body_idx, back_jump_idx, cs, ce))
    }
}

/// Detect ForEach pattern: `INDEX = COUNTER` in the extra range or body start,
/// and `COUNTER = ...` in the increment region. Returns init-line indices to suppress.
fn detect_foreach_info(stmts: &[BcStatement], lp: &ForLoop) -> Option<ForeachInfo> {
    let counter = find_increment_counter(stmts, lp.incr_start, lp.back_jump_idx)?;

    let body_candidate = (lp.body_start_idx < lp.body_end_idx).then_some(lp.body_start_idx);
    let has_index_assign = (lp.extra_start..lp.extra_end)
        .chain(body_candidate)
        .any(|idx| {
            stmts[idx]
                .text
                .split_once(" = ")
                .is_some_and(|(lhs, rhs)| lhs.starts_with("Temp_int_") && rhs == counter)
        });
    if !has_index_assign {
        return None;
    }

    let init_indices = find_foreach_init_stmts(stmts, lp.if_idx);
    Some(ForeachInfo { init_indices })
}

/// Scan backward from `if_idx` for ForEach init boilerplate: `Temp_int_* = 0`
/// and `Temp_bool_* = false` break-hit init. Skips `$`-prefixed condition temps
/// (cleaned up later by `discard_unused_assignments` / `fold_section_temps`).
fn find_foreach_init_stmts(stmts: &[BcStatement], if_idx: usize) -> Vec<usize> {
    let mut result = Vec::new();
    for j in (0..if_idx).rev() {
        let text = stmts[j].text.as_str();
        if text.is_empty() {
            continue;
        }
        if text
            .strip_suffix(" = 0")
            .is_some_and(|v| v.starts_with("Temp_int_"))
        {
            result.push(j);
            continue;
        }
        if text.starts_with("Temp_bool_") && text.ends_with(" = false") {
            result.push(j);
            continue;
        }
        if text.starts_with('$') {
            continue; // skip, don't collect
        }
        break;
    }
    result
}

/// Extract the counter variable name from the increment region (assignment
/// writing back to a `Temp_int_*` variable).
fn find_increment_counter(
    stmts: &[BcStatement],
    incr_start: usize,
    back_jump_idx: usize,
) -> Option<&str> {
    stmts[incr_start..back_jump_idx].iter().find_map(|stmt| {
        let (lhs, _) = stmt.text.split_once(" = ")?;
        lhs.starts_with("Temp_int_").then_some(lhs)
    })
}

/// Detect for-loops (including ForEach with displaced body and completion path).
pub(super) fn detect_for_loops(
    stmts: &[BcStatement],
    sequences: &[SequenceNode],
    _offset_map: &OffsetMap,
) -> Vec<ForLoop> {
    let mut loops: Vec<ForLoop> = Vec::new();

    for i in 0..stmts.len() {
        let Some((_, _end_offset)) = stmts[i].if_jump() else {
            continue;
        };

        let mut pf_idx = None;
        for window_offset in 1..=FORLOOP_PUSHFLOW_WINDOW.min(stmts.len().saturating_sub(i + 1)) {
            if i + window_offset + 1 >= stmts.len() {
                break;
            }
            if stmts[i + window_offset].push_flow_target().is_some()
                && stmts[i + window_offset + 1].jump_target().is_some()
            {
                pf_idx = Some(i + window_offset);
                break;
            }
        }
        let Some(pf_idx) = pf_idx else { continue };

        let Some(body_jump_target) = stmts[pf_idx + 1].jump_target() else {
            continue;
        };

        let extra_start = i + 1;
        let extra_end = pf_idx;

        let incr_start = pf_idx + 2;

        let mut back_jump_idx = None;
        for scan_idx in incr_start..stmts.len() {
            if let Some(back_target) = stmts[scan_idx].jump_target() {
                if back_target <= stmts[i].mem_offset {
                    back_jump_idx = Some(scan_idx);
                    break;
                }
            }
        }
        let Some(back_jump_idx) = back_jump_idx else {
            continue;
        };

        let pop_idx = stmts[(back_jump_idx + 1)..stmts.len().min(back_jump_idx + 3)]
            .iter()
            .position(|s| s.kind == StmtKind::PopFlow)
            .map(|p| p + back_jump_idx + 1);

        // ForEach bodies are displaced AFTER the completion path; detected by
        // checking if body_jump_target lands past the control block end.
        let Some((body_start, loop_ctrl_end, completion_start, completion_end)) =
            resolve_foreach_body(stmts, body_jump_target, back_jump_idx, pop_idx)
        else {
            continue;
        };

        if body_start >= stmts.len() {
            continue;
        }

        let mut body_end = stmts.len() - 1;
        for seq in sequences {
            for pin in &seq.pins {
                if pin.body_start_idx > loop_ctrl_end && pin.body_start_idx <= body_end {
                    body_end = pin.body_start_idx - 1;
                }
            }
        }

        let Some(jump_pos) = stmts[i].text.rfind(") jump 0x") else {
            continue;
        };
        let cond = stmts[i].text[5..jump_pos].to_string();

        let overlaps_sequence = sequences.iter().any(|seq| {
            let loop_end = loop_ctrl_end.max(body_end);
            i <= seq.inline_end && loop_end >= seq.chain_start
        });
        if overlaps_sequence {
            continue;
        }

        let mut lp = ForLoop {
            cond_text: cond,
            if_idx: i,
            extra_start,
            extra_end,
            incr_start,
            back_jump_idx,
            loop_ctrl_end,
            body_start_idx: body_start,
            body_end_idx: body_end,
            completion_start,
            completion_end,
            foreach: None,
        };
        lp.foreach = detect_foreach_info(stmts, &lp);
        loops.push(lp);
    }

    loops
}

/// Collect `chain_start`s of Sequences that are children of another
/// Sequence's pin/inline body (push_flow entry point is the target of an
/// unconditional jump). The push_flow target check distinguishes real
/// sub-Sequence dispatch from coincidental jumps landing in another range.
pub(super) fn find_child_sequence_starts(
    stmts: &[BcStatement],
    sequences: &[SequenceNode],
    offset_map: &OffsetMap,
) -> HashSet<usize> {
    let mut child_starts: HashSet<usize> = HashSet::new();

    for seq in sequences {
        let ranges = seq
            .pins
            .iter()
            .map(|pin| (pin.body_start_idx, pin.body_end_idx))
            .chain(std::iter::once((seq.chain_end, seq.inline_end)));

        for (scan_start, scan_end) in ranges {
            for idx in scan_start..scan_end.min(stmts.len()) {
                let Some(target) = stmts[idx].jump_target() else {
                    continue;
                };
                let Some(target_idx) = offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) else {
                    continue;
                };
                if target_idx >= stmts.len() || stmts[target_idx].push_flow_target().is_none() {
                    continue;
                }
                for other in sequences {
                    if other.chain_start != seq.chain_start
                        && target_idx >= other.chain_start
                        && target_idx <= other.inline_end
                    {
                        child_starts.insert(other.chain_start);
                    }
                }
            }
        }
    }

    child_starts
}
