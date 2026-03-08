use super::decode::BcStatement;
use super::flow::{
    parse_if_jump, parse_jump, parse_jump_computed, parse_pop_flow_if_not, parse_push_flow,
};
use std::collections::{HashMap, HashSet};

/// Negate a condition string for if/else inversion.
/// Rules: `!X` → `X`, `!(expr)` → `expr` (if balanced), otherwise `!(cond)`.
/// Wraps in parens when infix operators are present to preserve precedence
/// (`!A && B` means `(!A) && B`, not `!(A && B)`) — depth tracking avoids
/// wrapping operators inside nested parentheses.
fn negate_cond(cond: &str) -> String {
    // Already negated simple expr: !X → X
    if cond.starts_with('!') && !cond.starts_with("!(") {
        let rest = &cond[1..];
        // Only strip if rest has no top-level operators (it's a simple !ident)
        if !rest.contains(' ') {
            return rest.to_string();
        }
    }
    // Already negated parenthesized expr: !(X) → X
    if cond.starts_with("!(") {
        if let Some(inner) = cond.strip_prefix("!(").and_then(|s| s.strip_suffix(')')) {
            // Verify parens are balanced (the stripped ')' is the matching one)
            let mut depth = 0i32;
            let balanced = inner.chars().all(|ch| {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                depth >= 0
            }) && depth == 0;
            if balanced {
                return inner.to_string();
            }
        }
    }
    // Check if condition has infix operators at paren depth 0 (needs wrapping)
    let mut depth = 0i32;
    let bytes = cond.as_bytes();
    let mut has_infix = false;
    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' if depth == 0 && i > 0 && i + 1 < bytes.len() => {
                has_infix = true;
                break;
            }
            _ => {}
        }
    }
    if has_infix {
        format!("!({})", cond)
    } else {
        format!("!{}", cond)
    }
}

/// Convert flat bytecode statements into structured pseudo-code with if/else blocks.
///
/// **Condition fidelity:** `&&` and `||` in decoded bytecode are ALWAYS faithful to the
/// original Blueprint. They come from `BooleanAND`/`BooleanOR` Kismet function calls
/// inlined by `try_inline_operator()` in `decode.rs`. The structuring pass NEVER merges
/// separate Branch nodes into compound conditions — it only detects if/else blocks from
/// `JumpIfNot` opcodes and chains them into else-if when they share the same end target.
pub fn structure_bytecode(stmts: &[BcStatement], labels: &HashMap<usize, String>) -> Vec<String> {
    if stmts.is_empty() {
        return Vec::new();
    }

    let exact_map: HashMap<usize, usize> = stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| s.mem_offset > 0)
        .map(|(i, s)| (s.mem_offset, i))
        .collect();
    let mut sorted_offsets: Vec<(usize, usize)> =
        exact_map.iter().map(|(&off, &idx)| (off, idx)).collect();
    sorted_offsets.sort_by_key(|&(off, _)| off);

    let find_target_idx = |target: usize| -> Option<usize> {
        if let Some(&idx) = exact_map.get(&target) {
            return Some(idx);
        }
        let pos = sorted_offsets.partition_point(|&(off, _)| off <= target);
        let below = if pos > 0 {
            Some(sorted_offsets[pos - 1])
        } else {
            None
        };
        let above = if pos < sorted_offsets.len() {
            Some(sorted_offsets[pos])
        } else {
            None
        };
        let best = match (below, above) {
            (Some((bo, bi)), Some((ao, ai))) => {
                let bd = target.saturating_sub(bo);
                let ad = ao.saturating_sub(target);
                if bd <= ad {
                    Some((bd, bi))
                } else {
                    Some((ad, ai))
                }
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

    let label_at: HashMap<usize, &String> = labels
        .iter()
        .filter_map(|(offset, name)| {
            stmts
                .iter()
                .position(|s| s.mem_offset >= *offset)
                .map(|idx| (idx, name))
        })
        .collect();

    #[derive(Clone)]
    #[allow(clippy::enum_variant_names)]
    enum BlockEvent {
        CloseIf,
        CloseIfOpenElse,
        CloseIfOpenElseIf(String),
        CloseElse,
    }

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
        else_close_idx: Option<usize>,
    }
    let mut if_blocks: Vec<IfBlock> = Vec::new();

    for (i, stmt) in stmts.iter().enumerate() {
        let Some((cond, target)) = parse_if_jump(&stmt.text) else {
            continue;
        };
        let Some(target_idx) = find_target_idx_or_end(target) else {
            continue;
        };

        let mut jump_idx = None;
        let mut end_idx = None;
        if target_idx > 0 && target_idx <= stmts.len() {
            let check_idx = target_idx - 1;
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
        if_blocks.push(IfBlock {
            if_idx: i,
            cond: cond.to_string(),
            target_idx,
            jump_idx,
            end_idx,
            else_close_idx: None,
        });
    }

    // Pass 1.5: false-block truncation — when the false block contains an
    // unconditional jump to end_idx, the else body ends at that jump, not at end_idx.
    // This prevents inner else blocks from engulfing outer false blocks.
    for blk in &mut if_blocks {
        let Some(end_idx) = blk.end_idx else {
            continue;
        };
        let target_idx = blk.target_idx;
        if target_idx >= end_idx {
            continue;
        }
        for j in target_idx..end_idx {
            if j >= stmts.len() {
                break;
            }
            if let Some(jt) = parse_jump(&stmts[j].text) {
                if let Some(jt_idx) = find_target_idx_or_end(jt) {
                    if jt_idx == end_idx {
                        blk.else_close_idx = Some(j + 1);
                        break;
                    }
                }
            }
        }
    }

    // Pass 2: detect chains — B is chained to A when B starts at A's else
    // and both converge to the same end point
    let chained: HashSet<usize> = {
        let mut set = HashSet::new();
        for a in &if_blocks {
            let Some(a_end) = a.end_idx else { continue };
            if set.contains(&a.if_idx) {
                continue;
            }
            let mut cur_target = a.target_idx;
            loop {
                let next = if_blocks.iter().find(|b| {
                    b.if_idx == cur_target
                        && !set.contains(&b.if_idx)
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
        if_blocks
            .iter()
            .any(|b| b.if_idx == target_idx && chained.contains(&b.if_idx))
    };

    for blk in &if_blocks {
        let else_end = blk.else_close_idx.unwrap_or(blk.end_idx.unwrap_or(0));

        if chained.contains(&blk.if_idx) {
            // Chained else-if: emit } else if (cond) { at our if_idx
            events
                .entry(blk.if_idx)
                .or_default()
                .push(BlockEvent::CloseIfOpenElseIf(blk.cond.clone()));
            skip.insert(blk.if_idx);
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }

            if !is_next_chained(blk.target_idx) {
                // Last in chain — close the block
                if blk.jump_idx.is_some() {
                    // Has unconditional jump → else body follows
                    events
                        .entry(blk.target_idx)
                        .or_default()
                        .push(BlockEvent::CloseIfOpenElse);
                    if blk.end_idx.is_some() {
                        events
                            .entry(else_end)
                            .or_default()
                            .push(BlockEvent::CloseElse);
                    }
                } else {
                    // No else body
                    events
                        .entry(blk.target_idx)
                        .or_default()
                        .push(BlockEvent::CloseIf);
                }
            }
        } else {
            // Non-chained: either standalone or head of a chain
            replacements.insert(blk.if_idx, format!("if ({}) {{", blk.cond));
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }

            if is_next_chained(blk.target_idx) {
                // Head of chain — chained block handles the transition
            } else if blk.end_idx.is_some() {
                events
                    .entry(blk.target_idx)
                    .or_default()
                    .push(BlockEvent::CloseIfOpenElse);
                events
                    .entry(else_end)
                    .or_default()
                    .push(BlockEvent::CloseElse);
            } else {
                events
                    .entry(blk.target_idx)
                    .or_default()
                    .push(BlockEvent::CloseIf);
            }
        }
    }

    // Suppress push_flow and jump_computed everywhere (their semantic meaning
    // has already been consumed by reorder_flow_patterns for sequences/loops)
    let is_ubergraph = !labels.is_empty();
    for (i, stmt) in stmts.iter().enumerate() {
        if parse_push_flow(&stmt.text).is_some() || parse_jump_computed(&stmt.text) {
            skip.insert(i);
        }
    }

    // Track block types for pop_flow → break/return disambiguation
    #[derive(Clone, Copy, PartialEq)]
    enum BlockType {
        If,
        Loop,
    }
    let mut block_stack: Vec<BlockType> = Vec::new();

    let in_loop =
        |stack: &[BlockType]| -> bool { stack.iter().rev().any(|b| *b == BlockType::Loop) };

    // Pre-collect jump targets for label injection
    let mut label_targets: HashMap<usize, String> = HashMap::new();
    let mut pending_labels: HashMap<usize, String> = HashMap::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if skip.contains(&i) || replacements.contains_key(&i) {
            continue;
        }
        if let Some(target) = parse_jump(&stmt.text) {
            if let Some(target_idx) = find_target_idx_or_end(target) {
                let is_jump_to_end_label = target_idx >= stmts.len()
                    || (target_idx == stmts.len() - 1 && stmts[target_idx].text == "return nop");
                if is_jump_to_end_label {
                    // Jump to end — will be break or omitted
                } else if let Some(lbl) = label_at.get(&target_idx) {
                    label_targets.insert(i, format!("goto {}", lbl));
                } else {
                    // Generate a label for the target
                    let label_name = format!("L_{:04x}", target);
                    pending_labels
                        .entry(target_idx)
                        .or_insert_with(|| label_name.clone());
                    label_targets.insert(i, format!("goto {}", label_name));
                }
            }
        }
    }

    let mut output = Vec::new();
    let mut indent: usize = 0;

    let emit_block_events = |evts: &[BlockEvent],
                             indent: &mut usize,
                             output: &mut Vec<String>,
                             block_stack: &mut Vec<BlockType>| {
        for evt in evts.iter().rev() {
            match evt {
                BlockEvent::CloseIf => {
                    *indent = indent.saturating_sub(1);
                    output.push(format!("{}}}", "    ".repeat(*indent)));
                    block_stack.pop();
                }
                BlockEvent::CloseIfOpenElse => {
                    *indent = indent.saturating_sub(1);
                    output.push(format!("{}}} else {{", "    ".repeat(*indent)));
                    // Pop If, push If (same level)
                    *indent += 1;
                }
                BlockEvent::CloseIfOpenElseIf(cond) => {
                    *indent = indent.saturating_sub(1);
                    output.push(format!(
                        "{}}} else if ({}) {{",
                        "    ".repeat(*indent),
                        cond
                    ));
                    // Pop If, push If (same level)
                    *indent += 1;
                }
                BlockEvent::CloseElse => {
                    *indent = indent.saturating_sub(1);
                    output.push(format!("{}}}", "    ".repeat(*indent)));
                    block_stack.pop();
                }
            }
        }
    };

    for (i, stmt) in stmts.iter().enumerate() {
        if let Some(evts) = events.get(&i) {
            emit_block_events(evts, &mut indent, &mut output, &mut block_stack);
        }

        // Inject pending labels
        if let Some(lbl) = pending_labels.get(&i) {
            output.push(format!("{}:", lbl));
        }

        if let Some(label) = label_at.get(&i) {
            // Label orphan code before the first event label as latent resumes
            if is_ubergraph && !output.is_empty() && !output.iter().any(|l| l.starts_with("---")) {
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

        if skip.contains(&i) {
            continue;
        }

        if let Some(replacement) = replacements.get(&i) {
            output.push(format!("{}{}", "    ".repeat(indent), replacement));
            indent += 1;
            block_stack.push(BlockType::If);
        } else if stmt.text == "}" {
            indent = indent.saturating_sub(1);
            output.push(format!("{}}}", "    ".repeat(indent)));
            block_stack.pop();
        } else if stmt.text.ends_with(" {") {
            let is_loop = stmt.text.starts_with("while ") || stmt.text.starts_with("for ");
            output.push(format!("{}{}", "    ".repeat(indent), stmt.text));
            indent += 1;
            block_stack.push(if is_loop {
                BlockType::Loop
            } else {
                BlockType::If
            });
        } else if stmt.text == "pop_flow" {
            let keyword = if in_loop(&block_stack) {
                "break"
            } else {
                "return"
            };
            output.push(format!("{}{}", "    ".repeat(indent), keyword));
        } else if let Some(cond) = parse_pop_flow_if_not(&stmt.text) {
            let keyword = if in_loop(&block_stack) {
                "break"
            } else {
                "return"
            };
            let negated = negate_cond(cond);
            output.push(format!(
                "{}if ({}) {}",
                "    ".repeat(indent),
                negated,
                keyword
            ));
        } else if let Some(target) = parse_jump(&stmt.text) {
            // Resolve raw jumps
            if let Some(target_idx) = find_target_idx_or_end(target) {
                let is_jump_to_end = target_idx >= stmts.len()
                    || (target_idx == stmts.len() - 1 && stmts[target_idx].text == "return nop");
                if is_jump_to_end {
                    // Jump to end — break or omit
                    if in_loop(&block_stack) {
                        output.push(format!("{}break", "    ".repeat(indent)));
                    }
                    // Outside loops, jump-to-end is implicit return — omit
                } else if let Some(goto_text) = label_targets.get(&i) {
                    output.push(format!("{}{}", "    ".repeat(indent), goto_text));
                } else {
                    // Fallback: keep raw jump
                    output.push(format!("{}{}", "    ".repeat(indent), stmt.text));
                }
            } else {
                output.push(format!("{}{}", "    ".repeat(indent), stmt.text));
            }
        } else {
            let text = if stmt.text == "return nop" {
                "return"
            } else {
                &stmt.text
            };
            output.push(format!("{}{}", "    ".repeat(indent), text));
        }
    }

    if let Some(evts) = events.get(&stmts.len()) {
        emit_block_events(evts, &mut indent, &mut output, &mut block_stack);
    }

    while indent > 0 {
        indent -= 1;
        output.push(format!("{}}}", "    ".repeat(indent)));
    }

    // Post-process: convert "goto L_XXXX" to "break" (in loop) or remove (outside loop)
    // when the label appears right after a closing "}"
    let break_labels: HashSet<String> = {
        let mut set = HashSet::new();
        for i in 0..output.len() {
            let trimmed = output[i].trim();
            if trimmed.ends_with(':') && !trimmed.starts_with("---") && !trimmed.starts_with("//") {
                let label = &trimmed[..trimmed.len() - 1];
                // Check if the previous non-empty line is a closing brace
                if let Some(prev) = output[..i].iter().rev().find(|l| !l.trim().is_empty()) {
                    if prev.trim() == "}" {
                        set.insert(label.to_string());
                    }
                }
            }
        }
        set
    };
    if !break_labels.is_empty() {
        for i in 0..output.len() {
            let trimmed = output[i].trim().to_string();
            if let Some(label) = trimmed.strip_prefix("goto ") {
                if break_labels.contains(label) {
                    let indent_str = " ".repeat(output[i].len() - trimmed.len());
                    let line_indent = indent_str.len() / 4; // 4 spaces per indent level
                                                            // Check if we're inside a loop by scanning previous lines
                    let in_loop = output[..i].iter().rev().any(|l| {
                        let lt = l.trim();
                        let li = (l.len() - l.trim_start().len()) / 4;
                        li < line_indent && (lt.starts_with("while ") || lt.starts_with("for "))
                    });
                    if in_loop {
                        output[i] = format!("{}break", indent_str);
                    } else {
                        // Outside loop: redundant fall-through, mark for removal
                        output[i] = String::new();
                    }
                }
            }
        }
        // Remove empty lines from cleared gotos and unused labels
        output.retain(|line| !line.is_empty());
        let remaining_gotos: HashSet<String> = output
            .iter()
            .filter_map(|l| l.trim().strip_prefix("goto ").map(|s| s.to_string()))
            .collect();
        output.retain(|line| {
            let trimmed = line.trim();
            if trimmed.ends_with(':') && !trimmed.starts_with("---") && !trimmed.starts_with("//") {
                let label = &trimmed[..trimmed.len() - 1];
                if break_labels.contains(label) {
                    return remaining_gotos.contains(label);
                }
            }
            true
        });
    }

    // Post-process: extract convergence code from inside blocks.
    // When a label inside a block is targeted by 2+ gotos, the code from
    // the label to the block boundary is shared convergence code that
    // should appear after the enclosing block, not inside one branch.
    extract_convergence(&mut output);

    output
}

fn extract_convergence(output: &mut Vec<String>) {
    // Process one convergence label per iteration (indices shift after each)
    loop {
        // Collect goto targets and their line indices
        let mut goto_map: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, line) in output.iter().enumerate() {
            if let Some(label) = line.trim().strip_prefix("goto ") {
                goto_map.entry(label.to_string()).or_default().push(i);
            }
        }

        // Find first convergence label (2+ gotos)
        let conv = goto_map
            .iter()
            .find(|(_, gotos)| gotos.len() >= 2)
            .map(|(label, gotos)| (label.clone(), gotos.clone()));
        let Some((label_name, goto_indices)) = conv else {
            break;
        };

        // Find the label line
        let label_text = format!("{}:", label_name);
        let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
            break;
        };

        // Determine convergence code extent: from label+1 until a structural
        // boundary (closing brace / else) at shallower indent
        let code_start = label_idx + 1;
        if code_start >= output.len() {
            break;
        }

        let first_indent = output[code_start].len() - output[code_start].trim_start().len();
        let mut code_end = code_start;
        for (j, line) in output[code_start..].iter().enumerate() {
            let j = j + code_start;
            let trimmed = line.trim();
            if trimmed.is_empty() {
                code_end = j + 1;
                continue;
            }
            let line_indent = line.len() - line.trim_start().len();
            if line_indent < first_indent
                && (trimmed.starts_with('}') || trimmed.starts_with("} else"))
            {
                break;
            }
            if j > code_start
                && trimmed.ends_with(':')
                && !trimmed.starts_with("//")
                && !trimmed.starts_with("---")
            {
                break;
            }
            code_end = j + 1;
        }
        if code_end <= code_start {
            break;
        }

        // Extract convergence content (trimmed)
        let conv_content: Vec<String> = output[code_start..code_end]
            .iter()
            .map(|l| l.trim().to_string())
            .collect();

        // Find insert point: first `}` after all gotos at indent < shallowest goto indent
        let min_goto_indent = goto_indices
            .iter()
            .map(|&i| output[i].len() - output[i].trim_start().len())
            .min()
            .unwrap_or(0);
        let max_goto = goto_indices.iter().copied().max().unwrap_or(0);

        let mut insert_after = None;
        for (j, line) in output[(max_goto + 1)..].iter().enumerate() {
            let j = j + max_goto + 1;
            let trimmed = line.trim();
            let line_indent = line.len() - line.trim_start().len();
            if trimmed == "}" && line_indent < min_goto_indent {
                insert_after = Some(j);
                break;
            }
        }
        // Fallback: append at end
        let insert_pos = insert_after.unwrap_or(output.len());
        let target_indent = if insert_pos < output.len() {
            output[insert_pos].len() - output[insert_pos].trim_start().len()
        } else {
            0
        };

        // Collect all lines to remove
        let mut to_remove: Vec<usize> = Vec::new();
        to_remove.push(label_idx);
        to_remove.extend(code_start..code_end);
        to_remove.extend(&goto_indices);
        to_remove.sort();
        to_remove.dedup();

        // Remove in reverse order
        for &idx in to_remove.iter().rev() {
            if idx < output.len() {
                output.remove(idx);
            }
        }

        // Adjust insert position for removed lines
        let removed_before = to_remove.iter().filter(|&&idx| idx < insert_pos).count();
        let adjusted_pos = insert_pos.saturating_sub(removed_before);

        // Insert convergence code at target indent
        let indent_str = "    ".repeat(target_indent / 4);
        for (i, content) in conv_content.iter().enumerate() {
            let line = if content.is_empty() {
                String::new()
            } else {
                format!("{}{}", indent_str, content)
            };
            let pos = (adjusted_pos + 1 + i).min(output.len());
            output.insert(pos, line);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negate_simple_not() {
        assert_eq!(negate_cond("!X"), "X");
    }

    #[test]
    fn negate_parenthesized_not() {
        assert_eq!(negate_cond("!(A && B)"), "A && B");
    }

    #[test]
    fn negate_simple_var() {
        assert_eq!(negate_cond("X"), "!X");
    }

    #[test]
    fn negate_compound() {
        assert_eq!(negate_cond("A && B"), "!(A && B)");
    }

    #[test]
    fn negate_self_member() {
        assert_eq!(negate_cond("!self.GrippingActor"), "self.GrippingActor");
    }
}
