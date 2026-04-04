//! Flow pattern detection and bytecode reordering.
//!
//! Detects Sequence nodes, ForLoop, ForEach, and convergence patterns in flat bytecode,
//! then reorders so downstream structuring sees natural control flow.

use std::collections::HashSet;

use super::decode::BcStatement;
use super::{OffsetMap, JUMP_OFFSET_TOLERANCE};

/// Offset tolerance for ForEach loop body detection. Jump targets use in-memory offsets
/// but we index by on-disk offsets + cumulative mem_adj. The drift accumulates from
/// FFieldPath (variable length on disk, 8-byte pointer in memory) and obj-ref (+4 each).
const FORLOOP_OFFSET_TOLERANCE: usize = 64;

/// Max gap (in statements) between an if_jump and its push_flow/jump pair.
/// Filtered opcodes (wire_trace, tracepoint) can appear between them.
const FORLOOP_PUSHFLOW_WINDOW: usize = 4;

/// Parse "push_flow 0xHEX" -> target offset.
pub fn parse_push_flow(text: &str) -> Option<usize> {
    text.strip_prefix("push_flow 0x")
        .and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "jump 0xHEX" -> target offset.
pub fn parse_jump(text: &str) -> Option<usize> {
    text.strip_prefix("jump 0x")
        .and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "if !(COND) jump 0xHEX" -> (condition, target offset).
pub fn parse_if_jump(text: &str) -> Option<(&str, usize)> {
    if !text.starts_with("if !(") {
        return None;
    }
    let jump_pos = text.rfind(") jump 0x")?;
    let cond = &text[5..jump_pos];
    let target = usize::from_str_radix(&text[jump_pos + 9..], 16).ok()?;
    Some((cond, target))
}

/// Parse "pop_flow_if_not(COND)" -> condition string.
pub fn parse_pop_flow_if_not(text: &str) -> Option<&str> {
    let inner = text.strip_prefix("pop_flow_if_not(")?;
    let cond = inner.strip_suffix(')')?;
    Some(cond)
}

/// Parse "continue_if_not(COND)" -> condition string.
/// This is a synthetic marker emitted for pop_flow_if_not inside ForEach bodies,
/// where the pop means "skip to next iteration" rather than "break".
pub fn parse_continue_if_not(text: &str) -> Option<&str> {
    let inner = text.strip_prefix("continue_if_not(")?;
    let cond = inner.strip_suffix(')')?;
    Some(cond)
}

/// Parse "jump_computed(EXPR)" -> true if it's a computed jump.
pub fn parse_jump_computed(text: &str) -> bool {
    text.starts_with("jump_computed(")
}

struct SequencePin {
    body_start_idx: usize,
    body_end_idx: usize,
}

struct SequenceNode {
    chain_start: usize,
    chain_end: usize,
    inline_end: usize,
    pins: Vec<SequencePin>,
}

struct ForLoop {
    cond_text: String,
    if_idx: usize,
    extra_start: usize,
    extra_end: usize,
    incr_start: usize,
    back_jump_idx: usize,
    loop_ctrl_end: usize,
    body_start_idx: usize,
    body_end_idx: usize,
    completion_start: Option<usize>,
    completion_end: Option<usize>,
    /// When set, this loop is a confirmed ForEach. The flow layer emits
    /// `foreach {` and suppresses init/increment boilerplate, so the pattern
    /// layer only needs to extract ITEM/ARRAY from the body.
    foreach: Option<ForeachInfo>,
}

/// ForEach-specific details detected by the flow layer.
struct ForeachInfo {
    /// Indices of `Temp_int_* = 0` init statements to suppress from output.
    init_indices: Vec<usize>,
}

/// Expand a Sequence pin's body boundary by following if/jump targets beyond the
/// current end. Rescans after each expansion since new code may contain further jumps.
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
            if let Some((_, jump_target)) = parse_if_jump(&stmts[idx].text) {
                if let Some(target_idx) = offset_map.find_fuzzy(jump_target, JUMP_OFFSET_TOLERANCE)
                {
                    let in_other_pin = existing_pins
                        .iter()
                        .any(|&(ps, pe)| target_idx >= ps && target_idx <= pe);
                    if target_idx > be && !in_other_pin {
                        if let Some(displaced_end) = stmts[target_idx..]
                            .iter()
                            .position(|s| s.text == "pop_flow")
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
fn find_displaced_blocks(
    stmts: &[BcStatement],
    body_start: usize,
    body_end: usize,
    offset_map: &OffsetMap,
) -> Vec<(usize, usize)> {
    let mut blocks = Vec::new();
    for idx in body_start..body_end {
        let Some((_, jump_target)) = parse_if_jump(&stmts[idx].text) else {
            continue;
        };
        let Some(target_idx) = offset_map.find_fuzzy(jump_target, JUMP_OFFSET_TOLERANCE) else {
            continue;
        };
        if target_idx <= body_end {
            continue;
        }
        // Find the pop_flow that ends this displaced block
        let Some(displaced_end) = stmts[target_idx..]
            .iter()
            .position(|s| s.text == "pop_flow")
            .map(|p| p + target_idx)
        else {
            continue;
        };
        blocks.push((target_idx, displaced_end));
    }
    blocks
}

/// Detect grouped push_flow chains (regular function Sequence pattern).
///
/// Regular functions emit grouped push_flows followed by jump/body pairs:
///   push_flow E; push_flow C; jump body0; push_flow D; jump body1; ... inline; pop_flow
fn detect_grouped_sequences(stmts: &[BcStatement], offset_map: &OffsetMap) -> Vec<SequenceNode> {
    let mut sequences: Vec<SequenceNode> = Vec::new();

    let mut i = 0;
    while i < stmts.len() {
        let Some(_end_offset) = parse_push_flow(&stmts[i].text) else {
            i += 1;
            continue;
        };

        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut scan_idx = i + 1;
        while scan_idx + 1 < stmts.len() {
            let Some(_cont) = parse_push_flow(&stmts[scan_idx].text) else {
                break;
            };
            let Some(body) = parse_jump(&stmts[scan_idx + 1].text) else {
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
            .position(|s| s.text == "pop_flow")
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
                .position(|s| s.text == "pop_flow")
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

/// Detect alternating push_flow/jump sequence chains (UberGraph pattern).
///
/// UberGraph interleaves push_flow/jump pairs instead of grouping push_flows:
///   push_flow A; jump body0; push_flow B; jump body1; ... inline_code; pop_flow
fn detect_interleaved_sequences(
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
        // Look for push_flow immediately followed by jump
        let Some(_resume) = parse_push_flow(&stmts[i].text) else {
            i += 1;
            continue;
        };
        let Some(_body_off) = parse_jump(&stmts[i + 1].text) else {
            i += 1;
            continue;
        };

        // Skip push_flow/jump pairs that are part of a for-loop body dispatch.
        // A for-loop has if !(cond) jump BEFORE the push_flow AND a backward jump
        // (back-edge) AFTER it. if-guards before Sequences also have preceding
        // if-jumps but no back-edge, so checking both directions avoids false skips.
        const BACK_JUMP_SEARCH_WINDOW: usize = 10;
        let is_forloop_dispatch = (1..=FORLOOP_PUSHFLOW_WINDOW).any(|offset| {
            if i < offset {
                return false;
            }
            let cond_idx = i - offset;
            if parse_if_jump(&stmts[cond_idx].text).is_none() {
                return false;
            }
            let incr_start = i + 2;
            let search_end = stmts.len().min(incr_start + BACK_JUMP_SEARCH_WINDOW);
            (incr_start..search_end).any(|scan_idx| {
                parse_jump(&stmts[scan_idx].text)
                    .is_some_and(|back_target| back_target <= stmts[cond_idx].mem_offset)
            })
        });
        if is_forloop_dispatch {
            i += 2;
            continue;
        }

        // Collect alternating push_flow/jump pairs
        let chain_start = i;
        let mut jump_targets: Vec<usize> = Vec::new(); // body offsets
        let mut scan_idx = i;
        while scan_idx + 1 < stmts.len() && !used[scan_idx] {
            let Some(_resume) = parse_push_flow(&stmts[scan_idx].text) else {
                break;
            };
            let Some(body_off) = parse_jump(&stmts[scan_idx + 1].text) else {
                break;
            };
            jump_targets.push(body_off);
            scan_idx += 2;
        }
        if jump_targets.is_empty() {
            i += 1;
            continue;
        }

        // After the chain: inline body until pop_flow (exact).
        // pop_flow_if_not is a conditional branch WITHIN the body, not the terminator.
        let inline_start = scan_idx;
        let inline_end = stmts[inline_start..]
            .iter()
            .position(|s| s.text == "pop_flow")
            .map(|p| p + inline_start);
        let Some(inline_end) = inline_end else {
            i += 1;
            continue;
        };

        // Locate body blocks by jump target offset
        let mut pins: Vec<SequencePin> = Vec::new();
        let mut all_found = true;
        for &target in &jump_targets {
            let Some(body_start) = offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) else {
                all_found = false;
                break;
            };
            // Find body end: first pop_flow from body_start, then expand
            // to include displaced blocks (switch case bodies, etc.)
            let Some(initial_end) = stmts[body_start..]
                .iter()
                .position(|s| s.text == "pop_flow")
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

        // For single-pair sequences, require the inline body to have at least
        // 2 meaningful statements (not just pop_flow/push_flow). This prevents
        // false positives on trivial UberGraph stubs.
        if jump_targets.len() == 1 {
            let meaningful = stmts[inline_start..inline_end]
                .iter()
                .filter(|s| {
                    s.text != "pop_flow"
                        && !s.text.starts_with("push_flow ")
                        && !s.text.starts_with("pop_flow_if_not(")
                })
                .count();
            if meaningful < 2 {
                i += 1;
                continue;
            }
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

/// Resolve ForEach body layout: body may be displaced after the completion path.
///
/// Returns `(body_start, loop_ctrl_end, completion_start, completion_end)`.
/// `None` for the completion range means no displaced body was detected.
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
        // Find the CLOSEST matching statement, not first-match. Completion path statements
        // can land within the tolerance window of the body target, so we need the nearest
        // offset to avoid picking the wrong statement.
        let mut body_idx = stmts
            .iter()
            .enumerate()
            .filter(|(_, s)| {
                s.mem_offset > 0
                    && s.mem_offset.abs_diff(body_jump_target) < FORLOOP_OFFSET_TOLERANCE
            })
            .min_by_key(|(_, s)| s.mem_offset.abs_diff(body_jump_target))
            .map(|(idx, _)| idx)?;
        // Fuzzy matching can land on a preceding terminator; skip to real content
        while body_idx < stmts.len()
            && (stmts[body_idx].text == "pop_flow" || stmts[body_idx].text == "return nop")
        {
            body_idx += 1;
        }
        // If body is displaced past the back_jump, the gap is the completion path
        let (cs, ce) = if body_idx > back_jump_idx + 1 {
            (Some(back_jump_idx + 1), Some(body_idx - 1))
        } else {
            (None, None)
        };
        Some((body_idx, back_jump_idx, cs, ce))
    }
}

/// Detect whether this loop is a ForEach pattern. Checks for `INDEX = COUNTER`
/// in the extra range or body start, and `COUNTER = ...` in the increment region.
/// Returns `Some(ForeachInfo)` with init line indices to suppress.
fn detect_foreach_info(stmts: &[BcStatement], lp: &ForLoop) -> Option<ForeachInfo> {
    let counter = find_increment_counter(stmts, lp.incr_start, lp.back_jump_idx)?;

    // Check for INDEX = COUNTER in the extra range or body start
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

/// Scan backward from `if_idx` collecting ForEach init boilerplate to suppress:
/// `Temp_int_* = 0` init lines and `Temp_bool_* = false` break-hit init.
/// Skips `$`-prefixed condition computation temps (these are cleaned up later
/// by `discard_unused_assignments` or `fold_section_temps`).
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

/// Extract the counter variable name from the increment region.
///
/// The increment region (between push_flow+jump and back_jump) contains statements like:
///   `$Add_IntInt = COUNTER + 1`
///   `COUNTER = $Add_IntInt`
/// We look for the assignment that writes back to a Temp_int variable.
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
fn detect_for_loops(
    stmts: &[BcStatement],
    sequences: &[SequenceNode],
    _offset_map: &OffsetMap,
) -> Vec<ForLoop> {
    let mut loops: Vec<ForLoop> = Vec::new();

    for i in 0..stmts.len() {
        let Some((_, _end_offset)) = parse_if_jump(&stmts[i].text) else {
            continue;
        };

        let mut pf_idx = None;
        for window_offset in 1..=FORLOOP_PUSHFLOW_WINDOW.min(stmts.len().saturating_sub(i + 1)) {
            if i + window_offset + 1 >= stmts.len() {
                break;
            }
            if parse_push_flow(&stmts[i + window_offset].text).is_some()
                && parse_jump(&stmts[i + window_offset + 1].text).is_some()
            {
                pf_idx = Some(i + window_offset);
                break;
            }
        }
        let Some(pf_idx) = pf_idx else { continue };

        let Some(body_jump_target) = parse_jump(&stmts[pf_idx + 1].text) else {
            continue;
        };

        let extra_start = i + 1;
        let extra_end = pf_idx;

        let incr_start = pf_idx + 2;

        let mut back_jump_idx = None;
        for scan_idx in incr_start..stmts.len() {
            if let Some(back_target) = parse_jump(&stmts[scan_idx].text) {
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
            .position(|s| s.text == "pop_flow")
            .map(|p| p + back_jump_idx + 1);

        // For ForEach loops, the body is displaced AFTER the completion path.
        // Detect by checking if the body_jump_target lands past the control block end.
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
            // Check if any of the loop's ranges overlap the sequence's range
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

/// Collect chain_starts of Sequences that are children of another Sequence's
/// pin body. A child Sequence is one whose push_flow entry point is the target
/// of an unconditional jump from a parent's pin body or inline body.
///
/// The push_flow target check distinguishes real sub-Sequence dispatch from
/// coincidental control-flow jumps that land within another Sequence's range.
fn find_child_sequence_starts(
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
                let Some(target) = parse_jump(&stmts[idx].text) else {
                    continue;
                };
                let Some(target_idx) = offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) else {
                    continue;
                };
                if target_idx >= stmts.len() || parse_push_flow(&stmts[target_idx].text).is_none() {
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

/// Bundles shared state for Sequence emission so individual methods don't
/// need 5+ parameters. Tracks which Sequences have been emitted to support
/// child inlining (a child is emitted once within its parent, then skipped
/// when the main loop reaches its standalone position).
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
        // Child sequences use "sub-sequence" markers so that
        // split_by_sequence_markers (which splits on "// sequence [")
        // doesn't tear the parent pin body apart.
        let prefix = if depth > 0 {
            "sub-sequence"
        } else {
            "sequence"
        };
        let marker = |text: &str| BcStatement {
            mem_offset: seq_offset,
            text: text.to_string(),
        };
        let sentinel = |idx: usize| BcStatement {
            mem_offset: self.stmts[idx].mem_offset,
            text: "return nop".to_string(),
        };

        // Emit each pin body, following unconditional jumps to child Sequences
        for (pi, pin) in seq.pins.iter().enumerate() {
            output.push(marker(&format!("// {} [{}]:", prefix, pi)));
            output.extend_from_slice(&self.stmts[pin.body_start_idx..pin.body_end_idx]);
            self.emit_child_sequences(pin.body_start_idx, pin.body_end_idx, depth, output);
            // Sentinel so if-else exit jumps within the body can resolve
            output.push(sentinel(pin.body_end_idx));
        }

        // Inline body (after all pin dispatch pairs)
        output.push(marker(&format!("// {} [{}]:", prefix, seq.pins.len())));
        output.extend_from_slice(&self.stmts[seq.chain_end..seq.inline_end]);
        self.emit_child_sequences(seq.chain_end, seq.inline_end, depth, output);
        output.push(sentinel(seq.inline_end));

        // Displaced blocks reachable from the inline body's conditional jumps
        for &(ds, de) in
            &find_displaced_blocks(self.stmts, seq.chain_end, seq.inline_end, self.offset_map)
        {
            output.extend_from_slice(&self.stmts[ds..de]);
            output.push(sentinel(de));
        }
    }

    /// Scan for unconditional jumps targeting child Sequences and emit them inline.
    /// Removes the triggering jump from output since the child content follows inline.
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
            // Find the child Sequence this jump dispatches to
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
                // Remove the triggering jump from output. The child content
                // is emitted inline so the jump is now a no-op skip.
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

/// Emit a single loop: while header, extra, body (recursive), increment, close, completion.
/// `nested` is true when called from within another loop's body, suppressing the
/// trailing return nop (which belongs to the function, not the inner loop).
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
    let marker = |text: &str| BcStatement {
        mem_offset: lp_offset,
        text: text.to_string(),
    };
    let body_end = if stmts[lp.body_end_idx].text == "return nop" {
        lp.body_end_idx
    } else {
        lp.body_end_idx + 1
    };
    // Confirmed ForEach: emit `foreach (COND)` and drop the increment.
    // Unconfirmed: emit `while (COND)` with increment preserved.
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
    // In confirmed ForEach bodies, pop_flow_if_not is "continue to next item",
    // not "break". Rewrite to a marker the structurer handles differently.
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
    output.push(marker("}"));
    // Emit ForEach completion path after the loop.
    // Convert pop_flow to unconditional jumps targeting the function return
    // so the structurer can detect if/else boundaries (skip-else pattern).
    // After each converted jump, emit a no-op anchor at the next statement's
    // offset so inline passes can't remove the OffsetMap entry the structurer
    // needs for else-branch resolution.
    // Strip push_flow and plain jumps which are loop control artifacts.
    if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
        output.push(marker("// on loop complete:"));
        let end_offset = stmts[lp.body_end_idx].mem_offset;
        let completion = &stmts[cs..=ce];
        for (rel, stmt) in completion.iter().enumerate() {
            if parse_push_flow(&stmt.text).is_some() || parse_jump(&stmt.text).is_some() {
                continue;
            }
            if stmt.text == "pop_flow" {
                output.push(BcStatement {
                    mem_offset: stmt.mem_offset,
                    text: format!("jump 0x{:x}", end_offset),
                });
                // Anchor: the next statement's offset must survive in the
                // OffsetMap even if inline passes remove its original statement.
                if let Some(next) = completion.get(rel + 1) {
                    if next.mem_offset > 0 {
                        output.push(BcStatement {
                            mem_offset: next.mem_offset,
                            text: String::new(),
                        });
                    }
                }
                continue;
            }
            output.push(stmt.clone());
        }
    }
    // Only emit the trailing return nop for top-level loops. Nested loops
    // share the same body_end_idx (inflated to stmts.len()-1), and emitting
    // it inside the parent body would cause dead code elimination to strip
    // the parent's completion path.
    if !nested && stmts[lp.body_end_idx].text == "return nop" {
        output.push(stmts[lp.body_end_idx].clone());
    }
}

/// Emit statements from a range, recursively formatting any nested loops.
/// Uses an `emitted` set to prevent the same loop from being formatted twice
/// (sibling loops in the same function share inflated body_end ranges).
/// Tracks indices consumed by nested loop bodies to avoid duplication.
fn emit_body_range(
    stmts: &[BcStatement],
    start: usize,
    end: usize,
    loops: &[ForLoop],
    emitted: &mut HashSet<usize>,
    output: &mut Vec<BcStatement>,
) {
    // Collect index ranges consumed by nested loops within this range,
    // so we can skip them after the nested loop is emitted.
    let mut consumed = HashSet::new();
    let mut i = start;
    while i < end {
        if let Some(inner) = loops
            .iter()
            .find(|l| l.if_idx == i && !emitted.contains(&l.if_idx))
        {
            // Mark the inner loop's body range as consumed so statements
            // aren't emitted twice (once inside the while, once flat).
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
fn emit_reordered(
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
        // Mark displaced blocks reachable from the inline body
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
        // Suppress init lines for confirmed ForEach loops
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

/// Reorder bytecode statements to place sequence/loop bodies in logical execution order.
pub fn reorder_flow_patterns(stmts: &[BcStatement]) -> Vec<BcStatement> {
    if stmts.is_empty() {
        return Vec::new();
    }

    let offset_map = OffsetMap::build(stmts);
    let mut used = vec![false; stmts.len()];

    let mut sequences = detect_grouped_sequences(stmts, &offset_map);
    detect_interleaved_sequences(stmts, &used, &offset_map, &mut sequences);
    let loops = detect_for_loops(stmts, &sequences, &offset_map);

    if sequences.is_empty() && loops.is_empty() {
        return stmts.to_vec();
    }

    emit_reordered(stmts, &sequences, &loops, &mut used, &offset_map)
}

/// Reorder displaced if/else branches caused by convergence inlining.
///
/// The compiler sometimes inlines shared convergence code after one branch, then uses
/// backward jumps from others. We reorder so all jumps become forward and
/// structure_bytecode can detect if/else correctly. Loops until no groups remain.
pub fn reorder_convergence(stmts: &mut Vec<BcStatement>) {
    // Loop because each reorder shifts indices; process one convergence group per iteration.
    loop {
        if stmts.len() < 4 {
            return;
        }
        if !reorder_one_convergence(stmts) {
            return;
        }
    }
}

struct ConvergenceGroup {
    target_idx: usize,
    jump_indices: Vec<usize>,
    conv_end: usize,
}

/// Find the earliest convergence group: 2+ backward unconditional jumps sharing a target.
/// Scans for the convergence extent with if-nesting depth tracking.
fn find_convergence_group(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) -> Option<ConvergenceGroup> {
    use std::collections::HashMap;

    let find_idx =
        |target: usize| -> Option<usize> { offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) };

    // Find backward unconditional jumps (target resolves to earlier index)
    let mut backward_jumps: Vec<(usize, usize)> = Vec::new(); // (jump_idx, target_idx)
    for (i, stmt) in stmts.iter().enumerate() {
        if let Some(target) = parse_jump(&stmt.text) {
            if let Some(target_idx) = find_idx(target) {
                if target_idx < i {
                    backward_jumps.push((i, target_idx));
                }
            }
        }
    }

    // Group by target; need 2+ backward jumps to same target
    let mut target_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(jump_idx, target_idx) in &backward_jumps {
        target_groups.entry(target_idx).or_default().push(jump_idx);
    }

    // Process the earliest convergence group first (by target index) so that
    // index shifts from reordering don't invalidate later groups
    let mut conv = None;
    for (&target_idx, jump_indices) in &target_groups {
        if jump_indices.len() < 2 {
            continue;
        }
        if conv
            .as_ref()
            .is_none_or(|(ti, _): &(usize, Vec<usize>)| target_idx < *ti)
        {
            conv = Some((target_idx, jump_indices.clone()));
        }
    }
    let (conv_target_idx, mut jump_indices) = conv?;
    jump_indices.sort();

    // Find convergence code extent: from target_idx to the exit jump that leaves the
    // convergence block. Track if-nesting depth so that jumps inside nested if/else
    // blocks within the convergence code don't prematurely terminate the scan.
    // Each if-jump increments depth, and its exit jump decrements it. Only a jump at
    // depth 0 marks the true convergence exit.
    let mut conv_end = conv_target_idx;
    let mut if_depth = 0usize;
    for (j, stmt) in stmts.iter().enumerate().skip(conv_target_idx) {
        conv_end = j;
        if parse_if_jump(&stmt.text).is_some() {
            if_depth += 1;
            continue;
        }
        if let Some(jt) = parse_jump(&stmt.text) {
            if if_depth > 0 {
                if_depth -= 1;
                continue;
            }
            if let Some(jt_idx) = find_idx(jt) {
                if jt_idx > j {
                    break;
                }
            }
            if jt > stmts.last().map(|s| s.mem_offset).unwrap_or(0) {
                break;
            }
        }
    }

    Some(ConvergenceGroup {
        target_idx: conv_target_idx,
        jump_indices,
        conv_end,
    })
}

/// Match each backward jump to its if-statement and build the reordered output
/// with displaced blocks placed before convergence code.
fn build_convergence_reorder(
    stmts: &[BcStatement],
    group: &ConvergenceGroup,
    offset_map: &OffsetMap,
) -> Option<Vec<BcStatement>> {
    use std::collections::HashSet;

    let find_idx =
        |target: usize| -> Option<usize> { offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) };

    // Build a set of all displaced block ranges (between conv_end and the backward jumps).
    let all_displaced_start = group.conv_end + 1;
    let &all_displaced_end = group.jump_indices.last()?;

    if all_displaced_start > all_displaced_end || all_displaced_end >= stmts.len() {
        return None;
    }

    // Each backward jump terminates a displaced block. Find which if-statement's false
    // target matches the start of each block.
    struct DisplacedBlock {
        if_idx: usize,
        block_start: usize,
        block_end: usize, // inclusive (the backward jump itself)
    }
    let mut displaced: Vec<DisplacedBlock> = Vec::new();

    // Determine block boundaries: blocks are separated by the backward jumps.
    // First block starts at all_displaced_start, subsequent blocks start after prev jump.
    let mut block_starts: Vec<usize> = vec![all_displaced_start];
    for &ji in &group.jump_indices[..group.jump_indices.len() - 1] {
        block_starts.push(ji + 1);
    }

    for (bi, &jump_idx) in group.jump_indices.iter().enumerate() {
        let block_start = block_starts[bi];
        let mut found = false;
        for (i, stmt) in stmts.iter().enumerate().take(group.target_idx) {
            if let Some((_, target)) = parse_if_jump(&stmt.text) {
                if let Some(target_idx) = find_idx(target) {
                    if target_idx == block_start {
                        displaced.push(DisplacedBlock {
                            if_idx: i,
                            block_start,
                            block_end: jump_idx,
                        });
                        found = true;
                        break;
                    }
                }
            }
        }
        if !found {
            return None;
        }
    }

    // Sort displaced blocks by if_idx descending (deeper nested first)
    displaced.sort_by(|a, b| b.if_idx.cmp(&a.if_idx));

    // Build the reordered output:
    // [before convergence] [synthetic jump] [displaced blocks deepest-first] [convergence] [after]
    let mut output: Vec<BcStatement> = Vec::new();

    output.extend_from_slice(&stmts[..group.target_idx]);

    // Insert synthetic jump to convergence (so structure.rs sees a forward jump)
    let conv_offset = stmts[group.target_idx].mem_offset;
    output.push(BcStatement {
        mem_offset: 0,
        text: format!("jump 0x{:x}", conv_offset),
    });

    // Emit displaced blocks (deepest if_idx first = inner-false before outer-false)
    for db in &displaced {
        for stmt in &stmts[db.block_start..db.block_end] {
            output.push(stmt.clone());
        }
        // Replace backward jump with forward jump to convergence
        output.push(BcStatement {
            mem_offset: stmts[db.block_end].mem_offset,
            text: format!("jump 0x{:x}", conv_offset),
        });
    }

    // Emit convergence code
    output.extend_from_slice(&stmts[group.target_idx..=group.conv_end]);

    // Emit anything after convergence that isn't a displaced block
    let displaced_range: HashSet<usize> = displaced
        .iter()
        .flat_map(|db| db.block_start..=db.block_end)
        .collect();
    for (j, stmt) in stmts.iter().enumerate().skip(group.conv_end + 1) {
        if !displaced_range.contains(&j) {
            output.push(stmt.clone());
        }
    }

    Some(output)
}

/// Duplicate inline convergence code into sibling branches.
///
/// The compiler sometimes places shared post-branch code inside the first
/// if-branch and uses a backward jump from a sibling branch to reach it.
/// Instead of extracting and reordering, we duplicate the convergence code
/// at the backward jump site so each branch is self-contained.
///
/// Pattern detected:
/// ```text
/// if !(COND) jump ELSE
///   specific_code
///   convergence_code          // [conv_start..exit_jump)
///   jump END                  // exit_jump
/// ELSE:
///   ...
///   jump conv_start           // backward jump, replaced with duplicated code
/// ```
fn duplicate_inline_convergence(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) -> Option<Vec<BcStatement>> {
    let find_idx =
        |target: usize| -> Option<usize> { offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) };
    let last_offset = stmts.last()?.mem_offset;

    for (bj_idx, stmt) in stmts.iter().enumerate() {
        let Some(target) = parse_jump(&stmt.text) else {
            continue;
        };
        let Some(conv_start) = find_idx(target) else {
            continue;
        };
        if conv_start >= bj_idx {
            continue; // not backward
        }

        // Skip dead-code backward jumps (preceded by a forward exit)
        if bj_idx > 0 {
            if let Some(prev_target) = parse_jump(&stmts[bj_idx - 1].text) {
                if let Some(prev_idx) = find_idx(prev_target) {
                    if prev_idx > bj_idx {
                        continue;
                    }
                }
                if prev_target > last_offset {
                    continue;
                }
            }
        }

        // Target must be inside a branch (an if-jump's true body)
        let mut if_idx_found = false;
        for if_stmt in stmts.iter().take(conv_start) {
            if let Some((_, false_target)) = parse_if_jump(&if_stmt.text) {
                if let Some(false_idx) = find_idx(false_target) {
                    if false_idx > conv_start && false_idx <= bj_idx {
                        if_idx_found = true;
                    }
                }
            }
        }
        if !if_idx_found {
            continue;
        }

        // Find the exit jump (forward jump to end) after conv_start
        let mut exit_jump_idx = None;
        for (j, exit_stmt) in stmts.iter().enumerate().take(bj_idx).skip(conv_start) {
            if let Some(exit_target) = parse_jump(&exit_stmt.text) {
                if let Some(exit_idx) = find_idx(exit_target) {
                    if exit_idx > bj_idx {
                        exit_jump_idx = Some(j);
                        break;
                    }
                }
                if exit_target > last_offset {
                    exit_jump_idx = Some(j);
                    break;
                }
            }
        }
        let Some(exit_jump_idx) = exit_jump_idx else {
            continue;
        };

        // Convergence must be 4+ statements. Shorter sequences tend to be
        // loop back-edges or internal control flow rather than shared
        // post-branch code.
        let conv_range = &stmts[conv_start..exit_jump_idx];
        if conv_range.len() < 4 {
            continue;
        }
        // Allow control flow in convergence code only if all jumps target
        // outside the range (safe to duplicate without breaking references)
        let has_internal_jumps = conv_range.iter().any(|s| {
            if let Some((_, jt)) = parse_if_jump(&s.text) {
                find_idx(jt).is_some_and(|ti| ti >= conv_start && ti < exit_jump_idx)
            } else if let Some(jt) = parse_jump(&s.text) {
                find_idx(jt).is_some_and(|ti| ti >= conv_start && ti < exit_jump_idx)
            } else {
                false
            }
        });
        if has_internal_jumps {
            continue;
        }

        // Block duplication if there are forward references to the convergence
        // start (they'd break if the code is relocated). Other backward jumps
        // are fine: they'll be duplicated in subsequent iterations.
        let forward_refs = stmts
            .iter()
            .enumerate()
            .filter(|(i, s)| {
                *i != bj_idx
                    && *i <= conv_start
                    && parse_jump(&s.text)
                        .and_then(&find_idx)
                        .is_some_and(|ti| ti == conv_start)
            })
            .count();
        if forward_refs > 0 {
            continue;
        }

        // Duplicate: replace the backward jump with a copy of convergence + exit
        let mut output: Vec<BcStatement> = Vec::new();
        output.extend_from_slice(&stmts[..bj_idx]);
        // Convergence code (duplicated)
        for orig in conv_range {
            output.push(BcStatement {
                mem_offset: 0,
                text: orig.text.clone(),
            });
        }
        // Exit jump (duplicated, keeps the same forward target)
        output.push(BcStatement {
            mem_offset: stmts[bj_idx].mem_offset,
            text: stmts[exit_jump_idx].text.clone(),
        });
        // Everything after the backward jump
        output.extend_from_slice(&stmts[bj_idx + 1..]);

        return Some(output);
    }

    None
}

/// Process a single convergence group. Returns true if a reorder was performed.
fn reorder_one_convergence(stmts: &mut Vec<BcStatement>) -> bool {
    let offset_map = OffsetMap::build(stmts);
    if let Some(group) = find_convergence_group(stmts, &offset_map) {
        if let Some(reordered) = build_convergence_reorder(stmts, &group, &offset_map) {
            *stmts = reordered;
            return true;
        }
    }
    // Fallback: duplicate inline convergence (single backward jump into a branch body)
    if let Some(reordered) = duplicate_inline_convergence(stmts, &offset_map) {
        *stmts = reordered;
        return true;
    }
    false
}

// Inline tests: these test private flow pattern parsers (parse_push_flow, parse_jump, etc.)
// that aren't accessible from tests/.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_flow_valid() {
        assert_eq!(parse_push_flow("push_flow 0x1A2B"), Some(0x1A2B));
    }

    #[test]
    fn push_flow_invalid() {
        assert_eq!(parse_push_flow("something else"), None);
    }

    #[test]
    fn jump_valid() {
        assert_eq!(parse_jump("jump 0xFF"), Some(0xFF));
    }

    #[test]
    fn jump_invalid() {
        assert_eq!(parse_jump("not a jump"), None);
    }

    #[test]
    fn if_jump_valid() {
        assert_eq!(
            parse_if_jump("if !(cond) jump 0x100"),
            Some(("cond", 0x100))
        );
    }

    #[test]
    fn if_jump_invalid() {
        assert_eq!(parse_if_jump("if (cond) jump 0x100"), None);
    }

    #[test]
    fn pop_flow_if_not_valid() {
        assert_eq!(parse_pop_flow_if_not("pop_flow_if_not(cond)"), Some("cond"));
    }

    #[test]
    fn pop_flow_if_not_invalid() {
        assert_eq!(parse_pop_flow_if_not("something else"), None);
    }

    #[test]
    fn jump_computed_true() {
        assert!(parse_jump_computed("jump_computed(expr)"));
    }

    #[test]
    fn jump_computed_false() {
        assert!(!parse_jump_computed("jump 0x100"));
    }
}
