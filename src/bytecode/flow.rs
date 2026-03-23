//! Flow pattern detection and bytecode reordering.
//!
//! Detects Sequence nodes, ForLoop, ForEach, and convergence patterns in flat bytecode,
//! then reorders so downstream structuring sees natural control flow.

use super::decode::BcStatement;

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

/// Parse "jump_computed(EXPR)" -> true if it's a computed jump.
pub fn parse_jump_computed(text: &str) -> bool {
    text.starts_with("jump_computed(")
}

/// Expand a Sequence pin's body boundary by following if/jump targets beyond the
/// current end. Rescans after each expansion since new code may contain further jumps.
fn expand_body_end(
    stmts: &[BcStatement],
    body_start: usize,
    initial_end: usize,
    existing_pins: &[(usize, usize)],
    resolve_offset: &dyn Fn(usize) -> Option<usize>,
) -> usize {
    let mut be = initial_end;
    let mut scan_from = body_start;
    loop {
        let mut expanded = false;
        let mut idx = scan_from;
        while idx <= be {
            if let Some((_, jump_target)) = parse_if_jump(&stmts[idx].text) {
                if let Some(target_idx) = resolve_offset(jump_target) {
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
    resolve_offset: &dyn Fn(usize) -> Option<usize>,
) -> Vec<(usize, usize)> {
    let mut blocks = Vec::new();
    for idx in body_start..body_end {
        let Some((_, jump_target)) = parse_if_jump(&stmts[idx].text) else {
            continue;
        };
        let Some(target_idx) = resolve_offset(jump_target) else {
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

/// Reorder bytecode statements to place sequence/loop bodies in logical execution order.
pub fn reorder_flow_patterns(stmts: &[BcStatement]) -> Vec<BcStatement> {
    if stmts.is_empty() {
        return Vec::new();
    }

    let mut used = vec![false; stmts.len()];

    // Offset-to-index map for resolving jump targets across both patterns
    let offset_to_idx: std::collections::HashMap<usize, usize> = stmts
        .iter()
        .enumerate()
        .map(|(idx, s)| (s.mem_offset, idx))
        .collect();
    let resolve_offset = |target: usize| -> Option<usize> {
        offset_to_idx.get(&target).copied().or_else(|| {
            (1..=4).find_map(|d| {
                offset_to_idx
                    .get(&(target + d))
                    .or_else(|| offset_to_idx.get(&(target.wrapping_sub(d))))
                    .copied()
            })
        })
    };

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

    let mut sequences: Vec<SequenceNode> = Vec::new();

    let mut i = 0;
    while i < stmts.len() {
        let Some(_end_offset) = parse_push_flow(&stmts[i].text) else {
            i += 1;
            continue;
        };

        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut j = i + 1;
        while j + 1 < stmts.len() {
            let Some(_cont) = parse_push_flow(&stmts[j].text) else {
                break;
            };
            let Some(body) = parse_jump(&stmts[j + 1].text) else {
                break;
            };
            pairs.push((_cont, body));
            j += 2;
        }

        if pairs.len() < 2 {
            i += 1;
            continue;
        }

        let inline_start = j;
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
            let body_end =
                expand_body_end(stmts, body_start, initial_end, &pin_ranges, &resolve_offset);
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

    // Detect alternating push_flow/jump sequence chains (UberGraph pattern).
    // Regular functions use grouped push_flows, but UberGraph interleaves them:
    //   push_flow A; jump body0; push_flow B; jump body1; ... inline_code; pop_flow
    // Each body ends with pop_flow. We locate bodies by their jump target offset.
    {
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

            // Collect alternating push_flow/jump pairs
            let chain_start = i;
            let mut jump_targets: Vec<usize> = Vec::new(); // body offsets
            let mut j = i;
            while j + 1 < stmts.len() && !used[j] {
                let Some(_resume) = parse_push_flow(&stmts[j].text) else {
                    break;
                };
                let Some(body_off) = parse_jump(&stmts[j + 1].text) else {
                    break;
                };
                jump_targets.push(body_off);
                j += 2;
            }
            if jump_targets.is_empty() {
                i += 1;
                continue;
            }

            // After the chain: inline body until pop_flow (exact).
            // pop_flow_if_not is a conditional branch WITHIN the body, not the terminator.
            let inline_start = j;
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
                let Some(body_start) = resolve_offset(target) else {
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
                let body_end =
                    expand_body_end(stmts, body_start, initial_end, &pin_ranges, &resolve_offset);
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

    // Detect for-loops (including ForEach)
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
        // ForEach detection: completion path between loop exit and displaced body
        completion_start: Option<usize>,
        completion_end: Option<usize>,
    }

    let mut loops: Vec<ForLoop> = Vec::new();

    for i in 0..stmts.len() {
        let Some((_, _end_offset)) = parse_if_jump(&stmts[i].text) else {
            continue;
        };

        let mut pf_idx = None;
        for k in 1..=4usize.min(stmts.len().saturating_sub(i + 1)) {
            if i + k + 1 >= stmts.len() {
                break;
            }
            if parse_push_flow(&stmts[i + k].text).is_some()
                && parse_jump(&stmts[i + k + 1].text).is_some()
            {
                pf_idx = Some(i + k);
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
        for j in incr_start..stmts.len() {
            if let Some(back_target) = parse_jump(&stmts[j].text) {
                if back_target <= stmts[i].mem_offset {
                    back_jump_idx = Some(j);
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
        //
        // Offset tolerance: jump targets use in-memory offsets but we index by on-disk
        // offsets + cumulative mem_adj. The drift accumulates from FFieldPath (variable
        // length on disk, 8-byte pointer in memory) and obj-ref (+4 each) differences.
        const OFFSET_TOLERANCE: usize = 64;

        let (body_start, loop_ctrl_end, completion_start, completion_end) = if let Some(pop_idx) =
            pop_idx
        {
            let body_at_jump = stmts.iter().position(|s| {
                s.mem_offset > 0 && s.mem_offset.abs_diff(body_jump_target) < OFFSET_TOLERANCE
            });
            if let Some(actual_body) = body_at_jump {
                if actual_body > pop_idx + 1 {
                    (
                        actual_body,
                        pop_idx,
                        Some(pop_idx + 1),
                        Some(actual_body - 1),
                    )
                } else {
                    (pop_idx + 1, pop_idx, None, None)
                }
            } else {
                (pop_idx + 1, pop_idx, None, None)
            }
        } else {
            // Find the CLOSEST matching statement, not first-match. Completion path statements
            // can land within the tolerance window of the body target, so we need the nearest
            // offset to avoid picking the wrong statement.
            let body_idx = stmts
                .iter()
                .enumerate()
                .filter(|(_, s)| {
                    s.mem_offset > 0 && s.mem_offset.abs_diff(body_jump_target) < OFFSET_TOLERANCE
                })
                .min_by_key(|(_, s)| s.mem_offset.abs_diff(body_jump_target))
                .map(|(idx, _)| idx);
            let Some(body_idx) = body_idx else { continue };
            // If body is displaced past the back_jump, the gap is the completion path
            let (cs, ce) = if body_idx > back_jump_idx + 1 {
                (Some(back_jump_idx + 1), Some(body_idx - 1))
            } else {
                (None, None)
            };
            (body_idx, back_jump_idx, cs, ce)
        };

        if body_start >= stmts.len() {
            continue;
        }

        let mut body_end = stmts.len() - 1;
        for seq in &sequences {
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

        loops.push(ForLoop {
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
        });
    }

    if sequences.is_empty() && loops.is_empty() {
        return stmts.to_vec();
    }

    for seq in &sequences {
        used[seq.chain_start..=seq.inline_end].fill(true);
        for pin in &seq.pins {
            used[pin.body_start_idx..=pin.body_end_idx].fill(true);
        }
        // Mark displaced blocks reachable from the inline body
        for &(ds, de) in
            &find_displaced_blocks(stmts, seq.chain_end, seq.inline_end, &resolve_offset)
        {
            if de < used.len() {
                used[ds..=de].fill(true);
            }
        }
    }
    for lp in &loops {
        used[lp.if_idx..=lp.loop_ctrl_end].fill(true);
        used[lp.body_start_idx..=lp.body_end_idx].fill(true);
        // Mark ForEach completion range as used (we'll emit it after the loop)
        if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
            used[cs..=ce].fill(true);
        }
    }

    let mut output: Vec<BcStatement> = Vec::new();
    let marker = |offset: usize, text: &str| BcStatement {
        mem_offset: offset,
        text: text.to_string(),
    };

    let mut i = 0;
    while i < stmts.len() {
        if let Some(seq) = sequences.iter().find(|s| s.chain_start == i) {
            let seq_offset = stmts[seq.chain_start].mem_offset;
            for (pi, pin) in seq.pins.iter().enumerate() {
                output.push(marker(seq_offset, &format!("// sequence [{}]:", pi)));
                output.extend_from_slice(&stmts[pin.body_start_idx..pin.body_end_idx]);
                // Sentinel at pop_flow offset so if-else exit jumps within
                // the body can resolve (the pop_flow itself is excluded).
                output.push(BcStatement {
                    mem_offset: stmts[pin.body_end_idx].mem_offset,
                    text: "return nop".to_string(),
                });
            }
            output.push(marker(
                seq_offset,
                &format!("// sequence [{}]:", seq.pins.len()),
            ));
            output.extend_from_slice(&stmts[seq.chain_end..seq.inline_end]);
            // Sentinel for inline body's pop_flow. This must appear before
            // displaced blocks so the structurer can detect if/else patterns
            // where the true branch returns via pop_flow.
            output.push(BcStatement {
                mem_offset: stmts[seq.inline_end].mem_offset,
                text: "return nop".to_string(),
            });
            // Append displaced blocks reachable from the inline body's
            // if/jump targets (e.g. else branches at distant offsets).
            let displaced =
                find_displaced_blocks(stmts, seq.chain_end, seq.inline_end, &resolve_offset);
            for &(ds, de) in &displaced {
                output.extend_from_slice(&stmts[ds..de]);
                output.push(BcStatement {
                    mem_offset: stmts[de].mem_offset,
                    text: "return nop".to_string(),
                });
            }

            i = seq.inline_end + 1;
            continue;
        }

        if let Some(lp) = loops.iter().find(|l| l.if_idx == i) {
            let lp_offset = stmts[lp.if_idx].mem_offset;
            output.push(marker(lp_offset, &format!("while ({}) {{", lp.cond_text)));
            if lp.extra_start < lp.extra_end {
                output.extend_from_slice(&stmts[lp.extra_start..lp.extra_end]);
            }
            let body_end = if stmts[lp.body_end_idx].text == "return nop" {
                lp.body_end_idx
            } else {
                lp.body_end_idx + 1
            };
            output.extend_from_slice(&stmts[lp.body_start_idx..body_end]);
            output.extend_from_slice(&stmts[lp.incr_start..lp.back_jump_idx]);
            output.push(marker(lp_offset, "}"));
            // Emit ForEach completion path after the loop
            if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
                output.push(marker(lp_offset, "// on loop complete:"));
                for stmt in &stmts[cs..=ce] {
                    // Skip push_flow/pop_flow/jump that are loop control artifacts
                    if parse_push_flow(&stmt.text).is_some()
                        || stmt.text == "pop_flow"
                        || parse_jump(&stmt.text).is_some()
                    {
                        continue;
                    }
                    output.push(stmt.clone());
                }
            }
            if stmts[lp.body_end_idx].text == "return nop" {
                output.push(stmts[lp.body_end_idx].clone());
            }
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

/// Process a single convergence group. Returns true if a reorder was performed.
fn reorder_one_convergence(stmts: &mut Vec<BcStatement>) -> bool {
    use std::collections::{HashMap, HashSet};

    let offset_map = super::OffsetMap::build(stmts);
    let find_idx = |target: usize| -> Option<usize> { offset_map.find_fuzzy(target, 4) };

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
    let Some((conv_target_idx, mut jump_indices)) = conv else {
        return false;
    };
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
        // Track if-nesting within convergence code
        if parse_if_jump(&stmt.text).is_some() {
            if_depth += 1;
            continue;
        }
        if let Some(jt) = parse_jump(&stmt.text) {
            if if_depth > 0 {
                // This jump is an if-block's exit jump, reduces nesting
                if_depth -= 1;
                continue;
            }
            // Top-level forward jump or jump past end = convergence exit
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

    // Build a set of all displaced block ranges (between conv_end and the backward jumps).
    // Each backward jump terminates a block; blocks are contiguous between conv_end+1
    // and the last backward jump.
    let all_displaced_start = conv_end + 1;
    let Some(&all_displaced_end) = jump_indices.last() else {
        return false;
    };

    if all_displaced_start > all_displaced_end || all_displaced_end >= stmts.len() {
        return false;
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
    let mut block_starts: Vec<usize> = Vec::new();
    block_starts.push(all_displaced_start);
    for &ji in &jump_indices[..jump_indices.len() - 1] {
        block_starts.push(ji + 1);
    }

    for (bi, &jump_idx) in jump_indices.iter().enumerate() {
        let block_start = block_starts[bi];
        // Find the if-statement whose false target points to this block's start
        let mut found = false;
        for (i, stmt) in stmts.iter().enumerate().take(conv_target_idx) {
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
            // Can't match this block to an if-statement; bail out
            return false;
        }
    }

    // Sort displaced blocks by if_idx descending (deeper nested first)
    displaced.sort_by(|a, b| b.if_idx.cmp(&a.if_idx));

    // Build the reordered output:
    // [before convergence] [synthetic jump] [displaced blocks deepest-first] [convergence] [after]
    let mut output: Vec<BcStatement> = Vec::new();

    // Emit everything before convergence
    output.extend_from_slice(&stmts[..conv_target_idx]);

    // Insert synthetic jump to convergence (so structure.rs sees a forward jump)
    let conv_offset = stmts[conv_target_idx].mem_offset;
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
    output.extend_from_slice(&stmts[conv_target_idx..=conv_end]);

    // Emit anything after convergence that isn't a displaced block
    let displaced_range: HashSet<usize> = displaced
        .iter()
        .flat_map(|db| db.block_start..=db.block_end)
        .collect();
    for (j, stmt) in stmts.iter().enumerate().skip(conv_end + 1) {
        if !displaced_range.contains(&j) {
            output.push(stmt.clone());
        }
    }

    *stmts = output;
    true
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
