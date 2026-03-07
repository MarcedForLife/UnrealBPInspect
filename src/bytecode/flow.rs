use super::decode::BcStatement;

/// Parse "push_flow 0xHEX" → target offset.
pub fn parse_push_flow(text: &str) -> Option<usize> {
    text.strip_prefix("push_flow 0x").and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "jump 0xHEX" → target offset.
pub fn parse_jump(text: &str) -> Option<usize> {
    text.strip_prefix("jump 0x").and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "if !(COND) jump 0xHEX" → (condition, target offset).
pub fn parse_if_jump(text: &str) -> Option<(&str, usize)> {
    if !text.starts_with("if !(") { return None; }
    let jump_pos = text.rfind(") jump 0x")?;
    let cond = &text[5..jump_pos];
    let target = usize::from_str_radix(&text[jump_pos + 9..], 16).ok()?;
    Some((cond, target))
}

/// Parse "pop_flow_if_not(COND)" → condition string.
pub fn parse_pop_flow_if_not(text: &str) -> Option<&str> {
    let inner = text.strip_prefix("pop_flow_if_not(")?;
    let cond = inner.strip_suffix(')')?;
    Some(cond)
}

/// Parse "jump_computed(EXPR)" → true if it's a computed jump.
pub fn parse_jump_computed(text: &str) -> bool {
    text.starts_with("jump_computed(")
}

/// Reorder bytecode stmts to place sequence/loop bodies in logical execution order.
pub fn reorder_flow_patterns(stmts: &[BcStatement]) -> Vec<BcStatement> {
    if stmts.is_empty() { return Vec::new(); }

    let mut used = vec![false; stmts.len()];

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
        let Some(_end_offset) = parse_push_flow(&stmts[i].text) else { i += 1; continue };

        let mut pairs: Vec<(usize, usize)> = Vec::new();
        let mut j = i + 1;
        while j + 1 < stmts.len() {
            let Some(_cont) = parse_push_flow(&stmts[j].text) else { break };
            let Some(body) = parse_jump(&stmts[j + 1].text) else { break };
            pairs.push((_cont, body));
            j += 2;
        }

        if pairs.len() < 2 {
            i += 1;
            continue;
        }

        let inline_start = j;
        let inline_end = stmts[inline_start..].iter().position(|s| s.text == "pop_flow")
            .map(|p| p + inline_start);
        let Some(inline_end) = inline_end else { i += 1; continue };

        let mut pins: Vec<SequencePin> = Vec::new();
        let mut body_scan = inline_end + 1;
        for _ in 0..pairs.len() {
            if body_scan >= stmts.len() { break; }
            let body_start = body_scan;
            let body_end = stmts[body_start..].iter().position(|s| s.text == "pop_flow")
                .map(|p| p + body_start);
            let Some(body_end) = body_end else { break };
            pins.push(SequencePin { body_start_idx: body_start, body_end_idx: body_end });
            body_scan = body_end + 1;
        }
        if pins.len() != pairs.len() { i += 1; continue; }

        sequences.push(SequenceNode {
            chain_start: i,
            chain_end: inline_start,
            inline_end,
            pins,
        });

        i = inline_end + 1;
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
        let Some((_, _end_offset)) = parse_if_jump(&stmts[i].text) else { continue };

        let mut pf_idx = None;
        for k in 1..=4usize.min(stmts.len().saturating_sub(i + 1)) {
            if i + k + 1 >= stmts.len() { break; }
            if parse_push_flow(&stmts[i + k].text).is_some()
                && parse_jump(&stmts[i + k + 1].text).is_some()
            {
                pf_idx = Some(i + k);
                break;
            }
        }
        let Some(pf_idx) = pf_idx else { continue };

        let Some(body_jump_target) = parse_jump(&stmts[pf_idx + 1].text) else { continue };

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
        let Some(back_jump_idx) = back_jump_idx else { continue };

        let pop_idx = stmts[(back_jump_idx + 1)..stmts.len().min(back_jump_idx + 3)]
            .iter().position(|s| s.text == "pop_flow")
            .map(|p| p + back_jump_idx + 1);

        // For ForEach loops, the body is displaced AFTER the completion path.
        // Detect by checking if the body_jump_target lands past the control block end.
        let (body_start, loop_ctrl_end, completion_start, completion_end) = if let Some(pop_idx) = pop_idx {
            // Check if the actual body is displaced further (ForEach pattern)
            let body_at_jump = stmts.iter().position(|s| {
                s.mem_offset > 0 && s.mem_offset.abs_diff(body_jump_target) < 64
            });
            if let Some(actual_body) = body_at_jump {
                if actual_body > pop_idx + 1 {
                    (actual_body, pop_idx, Some(pop_idx + 1), Some(actual_body - 1))
                } else {
                    (pop_idx + 1, pop_idx, None, None)
                }
            } else {
                (pop_idx + 1, pop_idx, None, None)
            }
        } else {
            // Find the CLOSEST matching statement (not just the first within tolerance)
            let body_idx = stmts.iter().enumerate()
                .filter(|(_, s)| s.mem_offset > 0 && s.mem_offset.abs_diff(body_jump_target) < 64)
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

        if body_start >= stmts.len() { continue; }

        let mut body_end = stmts.len() - 1;
        for seq in &sequences {
            for pin in &seq.pins {
                if pin.body_start_idx > loop_ctrl_end && pin.body_start_idx <= body_end {
                    body_end = pin.body_start_idx - 1;
                }
            }
        }

        let cond = stmts[i].text[5..stmts[i].text.rfind(") jump 0x").unwrap()].to_string();

        let overlaps_sequence = sequences.iter().any(|seq| {
            i >= seq.chain_start && i <= seq.inline_end
        });
        if overlaps_sequence { continue; }

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
    let marker = |text: &str| BcStatement { mem_offset: 0, text: text.to_string() };

    let mut i = 0;
    while i < stmts.len() {
        if let Some(seq) = sequences.iter().find(|s| s.chain_start == i) {
            for (pi, pin) in seq.pins.iter().enumerate() {
                output.push(marker(&format!("// sequence [{}]:", pi)));
                output.extend_from_slice(&stmts[pin.body_start_idx..pin.body_end_idx]);
            }
            output.push(marker(&format!("// sequence [{}]:", seq.pins.len())));
            output.extend_from_slice(&stmts[seq.chain_end..seq.inline_end]);

            i = seq.inline_end + 1;
            continue;
        }

        if let Some(lp) = loops.iter().find(|l| l.if_idx == i) {
            output.push(marker(&format!("while ({}) {{", lp.cond_text)));
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
            output.push(marker("}"));
            // Emit ForEach completion path after the loop
            if let (Some(cs), Some(ce)) = (lp.completion_start, lp.completion_end) {
                output.push(marker("// on loop complete:"));
                for j in cs..=ce {
                    // Skip push_flow/pop_flow/jump that are loop control artifacts
                    if parse_push_flow(&stmts[j].text).is_some()
                        || stmts[j].text == "pop_flow"
                        || parse_jump(&stmts[j].text).is_some() { continue; }
                    output.push(stmts[j].clone());
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
/// The UE4 compiler sometimes inlines shared "convergence" code after one branch,
/// then uses backward jumps from other branches to reach it. This produces:
///   [inner-true] [convergence] [outer-false → backward jump] [inner-false → backward jump]
/// We reorder to:
///   [inner-true] [synthetic jump] [inner-false] [outer-false] [convergence]
/// so all jumps become forward and structure_bytecode can detect if/else correctly.
///
/// Loops until no more convergence groups are found, handling multiple independent
/// nested-if patterns in the same function.
pub fn reorder_convergence(stmts: &mut Vec<BcStatement>) {
    // Loop because each reorder shifts indices; process one convergence group per iteration.
    loop {
        if stmts.len() < 4 { return; }
        if !reorder_one_convergence(stmts) { return; }
    }
}

/// Process a single convergence group. Returns true if a reorder was performed.
fn reorder_one_convergence(stmts: &mut Vec<BcStatement>) -> bool {
    use std::collections::{HashMap, HashSet};

    // Build offset → index map with 4-byte tolerance
    let exact_map: HashMap<usize, usize> = stmts.iter().enumerate()
        .filter(|(_, s)| s.mem_offset > 0)
        .map(|(i, s)| (s.mem_offset, i))
        .collect();
    let mut sorted_offsets: Vec<(usize, usize)> = exact_map.iter()
        .map(|(&off, &idx)| (off, idx))
        .collect();
    sorted_offsets.sort_by_key(|&(off, _)| off);

    let find_idx = |target: usize| -> Option<usize> {
        if let Some(&idx) = exact_map.get(&target) { return Some(idx); }
        let pos = sorted_offsets.partition_point(|&(off, _)| off <= target);
        let below = if pos > 0 { Some(sorted_offsets[pos - 1]) } else { None };
        let above = if pos < sorted_offsets.len() { Some(sorted_offsets[pos]) } else { None };
        let best = match (below, above) {
            (Some((bo, bi)), Some((ao, ai))) => {
                let bd = target.saturating_sub(bo);
                let ad = ao.saturating_sub(target);
                if bd <= ad { Some((bd, bi)) } else { Some((ad, ai)) }
            }
            (Some((bo, bi)), None) => Some((target.saturating_sub(bo), bi)),
            (None, Some((ao, ai))) => Some((ao.saturating_sub(target), ai)),
            (None, None) => None,
        };
        match best {
            Some((dist, idx)) if dist <= 4 => Some(idx),
            _ => None,
        }
    };

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

    // Group by target — need 2+ backward jumps to same target
    let mut target_groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(jump_idx, target_idx) in &backward_jumps {
        target_groups.entry(target_idx).or_default().push(jump_idx);
    }

    // Find the earliest convergence group (by target index) for stable ordering
    let mut conv = None;
    for (&target_idx, jump_indices) in &target_groups {
        if jump_indices.len() < 2 { continue; }
        if conv.as_ref().map_or(true, |(ti, _): &(usize, Vec<usize>)| target_idx < *ti) {
            conv = Some((target_idx, jump_indices.clone()));
        }
    }
    let Some((conv_target_idx, mut jump_indices)) = conv else { return false };
    jump_indices.sort();

    // Find convergence code extent: from target_idx to the exit jump that leaves the
    // convergence block. Only count top-level forward jumps (not jumps inside nested ifs
    // within the convergence code). Track nesting by counting if-jump/end pairs.
    let mut conv_end = conv_target_idx;
    let mut if_depth = 0usize;
    for j in conv_target_idx..stmts.len() {
        conv_end = j;
        // Track if-nesting within convergence code
        if parse_if_jump(&stmts[j].text).is_some() {
            if_depth += 1;
            continue;
        }
        if let Some(jt) = parse_jump(&stmts[j].text) {
            if if_depth > 0 {
                // This jump is an if-block's exit jump — reduces nesting
                if_depth -= 1;
                continue;
            }
            // Top-level forward jump or jump past end = convergence exit
            if let Some(jt_idx) = find_idx(jt) {
                if jt_idx > j { break; }
            }
            if jt > stmts.last().map(|s| s.mem_offset).unwrap_or(0) { break; }
        }
    }

    // Build a set of all displaced block ranges (between conv_end and the backward jumps).
    // Each backward jump terminates a block; blocks are contiguous between conv_end+1
    // and the last backward jump.
    let all_displaced_start = conv_end + 1;
    let all_displaced_end = *jump_indices.last().unwrap(); // inclusive

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
        for i in 0..conv_target_idx {
            if let Some((_, target)) = parse_if_jump(&stmts[i].text) {
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
            // Can't match this block to an if-statement — bail out
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
        for j in db.block_start..db.block_end {
            output.push(stmts[j].clone());
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
    let displaced_range: HashSet<usize> = displaced.iter()
        .flat_map(|db| db.block_start..=db.block_end)
        .collect();
    for j in (conv_end + 1)..stmts.len() {
        if !displaced_range.contains(&j) {
            output.push(stmts[j].clone());
        }
    }

    *stmts = output;
    true
}

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
        assert_eq!(parse_if_jump("if !(cond) jump 0x100"), Some(("cond", 0x100)));
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
