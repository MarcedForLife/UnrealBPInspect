use std::collections::{HashMap, HashSet};
use super::decode::BcStatement;
use super::flow::{parse_if_jump, parse_jump};

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
    enum BlockEvent { CloseIf, CloseIfOpenElse, CloseElse }

    let mut events: HashMap<usize, Vec<BlockEvent>> = HashMap::new();
    let mut skip: HashSet<usize> = HashSet::new();
    let mut replacements: HashMap<usize, String> = HashMap::new();

    for (i, stmt) in stmts.iter().enumerate() {
        let Some((cond, target)) = parse_if_jump(&stmt.text) else { continue };
        let Some(target_idx) = find_target_idx_or_end(target) else { continue };

        if target_idx > 0 && target_idx <= stmts.len() {
            let check_idx = if target_idx == stmts.len() { target_idx - 1 } else { target_idx - 1 };
            let prev = &stmts[check_idx];
            if let Some(end_target) = parse_jump(&prev.text) {
                if let Some(end_idx) = find_target_idx_or_end(end_target) {
                    replacements.insert(i, format!("if ({}) {{", cond));
                    skip.insert(check_idx);
                    events.entry(target_idx).or_default().push(BlockEvent::CloseIfOpenElse);
                    events.entry(end_idx).or_default().push(BlockEvent::CloseElse);
                    continue;
                }
            }
        }

        replacements.insert(i, format!("if ({}) {{", cond));
        events.entry(target_idx).or_default().push(BlockEvent::CloseIf);
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
                    BlockEvent::CloseElse => {
                        indent = indent.saturating_sub(1);
                        output.push(format!("{}}}", "    ".repeat(indent)));
                    }
                }
            }
        }

        if let Some(label) = label_at.get(&i) {
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
            }
        }
    }

    while indent > 0 {
        indent -= 1;
        output.push(format!("{}}}", "    ".repeat(indent)));
    }

    output
}
