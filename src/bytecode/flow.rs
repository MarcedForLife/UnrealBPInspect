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
