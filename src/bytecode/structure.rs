use std::collections::{HashMap, HashSet};
use super::decode::BcStatement;
use super::flow::{parse_if_jump, parse_jump, parse_push_flow, parse_pop_flow_if_not, parse_jump_computed};

/// Convert flat bytecode statements into structured pseudo-code with if/else blocks.
pub fn structure_bytecode(stmts: &[BcStatement], labels: &HashMap<usize, String>) -> Vec<String> {
    if stmts.is_empty() { return Vec::new(); }

    let exact_map: HashMap<usize, usize> = stmts.iter().enumerate()
        .filter(|(_, s)| s.mem_offset > 0)
        .map(|(i, s)| (s.mem_offset, i))
        .collect();
    let mut sorted_offsets: Vec<(usize, usize)> = exact_map.iter()
        .map(|(&off, &idx)| (off, idx))
        .collect();
    sorted_offsets.sort_by_key(|&(off, _)| off);

    let find_target_idx = |target: usize| -> Option<usize> {
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

    let find_target_idx_or_end = |target: usize| -> Option<usize> {
        find_target_idx(target).or_else(|| {
            if !sorted_offsets.is_empty() && target > sorted_offsets.last().unwrap().0 {
                Some(stmts.len())
            } else {
                None
            }
        })
    };

    let label_at: HashMap<usize, &String> = labels.iter().filter_map(|(offset, name)| {
        stmts.iter().position(|s| s.mem_offset >= *offset).map(|idx| (idx, name))
    }).collect();

    #[derive(Clone)]
    #[allow(clippy::enum_variant_names)]
    enum BlockEvent { CloseIf, CloseIfOpenElse, CloseIfOpenElseIf(String), CloseElse }

    let mut events: HashMap<usize, Vec<BlockEvent>> = HashMap::new();
    let mut skip: HashSet<usize> = HashSet::new();
    let mut replacements: HashMap<usize, String> = HashMap::new();

    // Pass 1: collect if-blocks
    struct IfBlock {
        if_idx: usize,
        cond: String,
        target_idx: usize,
        jump_idx: Option<usize>,
        end_idx: Option<usize>,
    }
    let mut if_blocks: Vec<IfBlock> = Vec::new();

    for (i, stmt) in stmts.iter().enumerate() {
        let Some((cond, target)) = parse_if_jump(&stmt.text) else { continue };
        let Some(target_idx) = find_target_idx_or_end(target) else { continue };

        let mut jump_idx = None;
        let mut end_idx = None;
        if target_idx > 0 && target_idx <= stmts.len() {
            let check_idx = if target_idx == stmts.len() { target_idx - 1 } else { target_idx - 1 };
            let prev = &stmts[check_idx];
            if let Some(end_target) = parse_jump(&prev.text) {
                if let Some(eidx) = find_target_idx_or_end(end_target) {
                    // Only valid if/else when else-end is at or after else-start
                    if eidx >= target_idx {
                        jump_idx = Some(check_idx);
                        end_idx = Some(eidx);
                    }
                }
            }
        }
        if_blocks.push(IfBlock { if_idx: i, cond: cond.to_string(), target_idx, jump_idx, end_idx });
    }

    // Pass 2: detect chains — B is chained to A when B starts at A's else
    // and both converge to the same end point
    let chained: HashSet<usize> = {
        let mut set = HashSet::new();
        for a in &if_blocks {
            let Some(a_end) = a.end_idx else { continue };
            if set.contains(&a.if_idx) { continue; }
            let mut cur_target = a.target_idx;
            loop {
                let next = if_blocks.iter().find(|b| {
                    b.if_idx == cur_target && !set.contains(&b.if_idx)
                    && (b.end_idx == Some(a_end) || b.target_idx == a_end)
                });
                let Some(b) = next else { break };
                set.insert(b.if_idx);
                cur_target = b.target_idx;
            }
        }
        set
    };

    let is_next_chained = |target_idx: usize| -> bool {
        if_blocks.iter().any(|b| b.if_idx == target_idx && chained.contains(&b.if_idx))
    };

    for blk in &if_blocks {
        if chained.contains(&blk.if_idx) {
            // Chained else-if: emit } else if (cond) { at our if_idx
            events.entry(blk.if_idx).or_default().push(
                BlockEvent::CloseIfOpenElseIf(blk.cond.clone())
            );
            skip.insert(blk.if_idx);
            if let Some(ji) = blk.jump_idx { skip.insert(ji); }

            if !is_next_chained(blk.target_idx) {
                // Last in chain — close the block
                if blk.jump_idx.is_some() {
                    // Has unconditional jump → else body follows
                    events.entry(blk.target_idx).or_default().push(BlockEvent::CloseIfOpenElse);
                    if let Some(end_idx) = blk.end_idx {
                        events.entry(end_idx).or_default().push(BlockEvent::CloseElse);
                    }
                } else {
                    // No else body
                    events.entry(blk.target_idx).or_default().push(BlockEvent::CloseIf);
                }
            }
        } else {
            // Non-chained: either standalone or head of a chain
            replacements.insert(blk.if_idx, format!("if ({}) {{", blk.cond));
            if let Some(ji) = blk.jump_idx { skip.insert(ji); }

            if is_next_chained(blk.target_idx) {
                // Head of chain — chained block handles the transition
            } else if blk.end_idx.is_some() {
                events.entry(blk.target_idx).or_default().push(BlockEvent::CloseIfOpenElse);
                events.entry(blk.end_idx.unwrap()).or_default().push(BlockEvent::CloseElse);
            } else {
                events.entry(blk.target_idx).or_default().push(BlockEvent::CloseIf);
            }
        }
    }

    // Ubergraph cleanup: suppress preamble, rewrite pop_flow
    let is_ubergraph = !labels.is_empty();
    if is_ubergraph {
        // Suppress push_flow and jump_computed before the first label
        let first_label_idx = label_at.keys().copied().min();
        if let Some(first_label) = first_label_idx {
            for i in 0..first_label {
                if parse_push_flow(&stmts[i].text).is_some() || parse_jump_computed(&stmts[i].text) {
                    skip.insert(i);
                }
            }
        }
    }

    let mut output = Vec::new();
    let mut indent: usize = 0;

    for (i, stmt) in stmts.iter().enumerate() {
        if let Some(evts) = events.get(&i) {
            for evt in evts.iter().rev() {
                match evt {
                    BlockEvent::CloseIf => {
                        indent = indent.saturating_sub(1);
                        output.push(format!("{}}}", "    ".repeat(indent)));
                    }
                    BlockEvent::CloseIfOpenElse => {
                        indent = indent.saturating_sub(1);
                        output.push(format!("{}}} else {{", "    ".repeat(indent)));
                        indent += 1;
                    }
                    BlockEvent::CloseIfOpenElseIf(cond) => {
                        indent = indent.saturating_sub(1);
                        output.push(format!("{}}} else if ({}) {{", "    ".repeat(indent), cond));
                        indent += 1;
                    }
                    BlockEvent::CloseElse => {
                        indent = indent.saturating_sub(1);
                        output.push(format!("{}}}", "    ".repeat(indent)));
                    }
                }
            }
        }

        if let Some(label) = label_at.get(&i) {
            // Label orphan code before the first event label as latent resumes
            if is_ubergraph && !output.is_empty() && !output.iter().any(|l| l.starts_with("---")) {
                // Check there's actual content (not just returns)
                let has_content = output.iter().any(|l| {
                    let t = l.trim();
                    !t.is_empty() && t != "return"
                });
                if has_content {
                    output.insert(0, "--- (latent resume) ---".to_string());
                }
            }
            output.push(format!("--- {} ---", label));
        }

        if skip.contains(&i) { continue; }

        if let Some(replacement) = replacements.get(&i) {
            output.push(format!("{}{}", "    ".repeat(indent), replacement));
            indent += 1;
        } else if stmt.text == "}" {
            indent = indent.saturating_sub(1);
            output.push(format!("{}}}", "    ".repeat(indent)));
        } else if stmt.text.ends_with(" {") {
            output.push(format!("{}{}", "    ".repeat(indent), stmt.text));
            indent += 1;
        } else if is_ubergraph && stmt.text == "pop_flow" {
            output.push(format!("{}return", "    ".repeat(indent)));
        } else if is_ubergraph {
            if let Some(cond) = parse_pop_flow_if_not(&stmt.text) {
                output.push(format!("{}if (!{}) return", "    ".repeat(indent), cond));
            } else {
                let text = if stmt.text == "return nop" { "return" } else { &stmt.text };
                output.push(format!("{}{}", "    ".repeat(indent), text));
            }
        } else {
            let text = if stmt.text == "return nop" { "return" } else { &stmt.text };
            output.push(format!("{}{}", "    ".repeat(indent), text));
        }
    }

    if let Some(evts) = events.get(&stmts.len()) {
        for evt in evts.iter().rev() {
            match evt {
                BlockEvent::CloseIf | BlockEvent::CloseElse => {
                    indent = indent.saturating_sub(1);
                    output.push(format!("{}}}", "    ".repeat(indent)));
                }
                BlockEvent::CloseIfOpenElse => {
                    indent = indent.saturating_sub(1);
                    output.push(format!("{}}} else {{", "    ".repeat(indent)));
                    indent += 1;
                }
                BlockEvent::CloseIfOpenElseIf(cond) => {
                    indent = indent.saturating_sub(1);
                    output.push(format!("{}}} else if ({}) {{", "    ".repeat(indent), cond));
                    indent += 1;
                }
            }
        }
    }

    while indent > 0 {
        indent -= 1;
        output.push(format!("{}}}", "    ".repeat(indent)));
    }

    output
}
