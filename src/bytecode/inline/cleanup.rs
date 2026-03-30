//! Expression cleanup and structural artifact removal.

use super::{
    expr_is_compound, find_at_depth_zero, find_matching_paren, is_ident_char, strip_outer_parens,
};
use std::collections::{HashMap, HashSet};

/// Find the closing brace that matches a block-opening line at `open_idx`.
/// Tracks brace depth so nested blocks are correctly skipped.
/// `} else {` is treated as a close at the current depth (stops the search
/// if depth reaches 0) rather than a net-zero open+close.
fn find_block_close(lines: &[String], open_idx: usize) -> usize {
    let mut depth = 1i32;
    let mut idx = open_idx + 1;
    while idx < lines.len() && depth > 0 {
        let inner = lines[idx].trim();
        if inner == "}" || inner.starts_with("} ") {
            depth -= 1;
        } else if inner.ends_with(" {") || inner == "{" {
            depth += 1;
        }
        if depth > 0 {
            idx += 1;
        }
    }
    idx
}

/// Try to simplify `!(!X)` to `X`. Returns `Some(simplified)` on success.
///
/// Only safe when the inner `!` covers the entire expression (no bare `&&`/`||` at
/// paren depth 0). For example, `!(!A && B)` is NOT a double negation because the
/// inner `!` only negates `A`.
fn try_strip_double_negation(s: &str) -> Option<String> {
    let pos = s.find("!(")?;
    // Check the char before `!` is a prefix context (start, space, `(`, `!`)
    if pos > 0 {
        let prev = s.as_bytes()[pos - 1];
        if prev != b'(' && prev != b' ' && prev != b'!' {
            return None;
        }
    }
    let inner_start = pos + 2;
    let inner = find_matching_paren(&s[pos + 1..])?;
    let inner_text = &s[inner_start..pos + 1 + inner];
    let after_neg = inner_text.strip_prefix('!')?;
    if has_toplevel_logical_op(after_neg) {
        return None;
    }
    Some(format!(
        "{}{}{}",
        &s[..pos],
        after_neg,
        &s[pos + 2 + inner..]
    ))
}

/// Clean up structured output: double negation, extra parens, trailing returns.
pub fn cleanup_structured_output(lines: &mut Vec<String>) {
    // Pass 0: eliminate constant-condition gates (DoOnce/FlipFlop artifacts).
    // `if (!true) ...` / `if (false) ...` = dead branch, remove entirely.
    // `if (!false) ...` / `if (true) ...` = always-taken, inline body.
    eliminate_constant_condition_branches(lines);

    // Pass 1: clean each line in place
    for line in lines.iter_mut() {
        let trimmed = line.trim();
        let cleaned = clean_line(trimmed);
        if cleaned != trimmed {
            *line = cleaned;
        }
    }

    // Pass 2: strip trailing returns
    // Remove "return" as the very last line (it's implicit)
    while lines.last().map(|l| l.trim()) == Some("return") {
        lines.pop();
    }
    // Remove duplicate "return\nreturn" sequences (common at ubergraph section boundaries)
    let mut i = 0;
    while i + 1 < lines.len() {
        if lines[i].trim() == "return" && lines[i + 1].trim() == "return" {
            lines.remove(i + 1);
        } else {
            i += 1;
        }
    }
    // Remove "return" immediately before "// sequence [N]:" markers.
    // These are sentinel leaks from Sequence body boundaries (return nop).
    let mut i = 0;
    while i + 1 < lines.len() {
        let next = lines[i + 1].trim();
        if lines[i].trim() == "return"
            && (next.starts_with("// sequence [")
                || next.starts_with("// sub-sequence [")
                || next.starts_with("case ")
                || next.starts_with("switch ("))
        {
            lines.remove(i);
            continue;
        }
        i += 1;
    }

    // Pass 3: suppress dead code after unconditional return at brace depth 0
    // Only in non-ubergraph functions (no "---" labels)
    let has_labels = lines.iter().any(|l| l.starts_with("---"));
    if !has_labels {
        let mut dead = false;
        let mut depth = 0i32;
        lines.retain(|line| {
            let trimmed = line.trim();
            // Track brace depth
            if trimmed.starts_with('}') {
                depth -= 1;
            }
            let at_top = depth <= 0;
            if trimmed.ends_with(" {") || trimmed == "{" {
                depth += 1;
            }
            if dead {
                // Switch/case markers restart live code (case fall-through)
                if trimmed.starts_with("case ") || trimmed.starts_with("switch (") {
                    dead = false;
                    return true;
                }
                // Closing braces are structural, keep them
                trimmed == "}" || trimmed.is_empty()
            } else {
                if at_top && trimmed == "return" {
                    dead = true;
                }
                true
            }
        });
    }

    // Pass 4: rewrite negated guards with compound conditions
    rewrite_negated_guards(lines);

    // Pass 5: strip trailing unmatched closing braces.
    // Per-pin structuring can leave orphaned `}` when flow patterns consume
    // the block-opening statement but not its close. Count braces and strip excess.
    let opens: usize = lines.iter().filter(|l| l.trim().ends_with('{')).count();
    let closes: usize = lines.iter().filter(|l| l.trim().starts_with('}')).count();
    let excess = closes.saturating_sub(opens);
    for _ in 0..excess {
        if lines.last().is_some_and(|l| l.trim() == "}") {
            lines.pop();
        } else {
            break;
        }
    }
}

/// Classify a constant condition: returns `Some(true)` for always-taken branches
/// (`true`, `!false`), `Some(false)` for dead branches (`false`, `!true`),
/// or `None` if the condition isn't a constant.
fn classify_constant_condition(if_line: &str) -> Option<bool> {
    let trimmed = if_line.trim();
    // Match "if (COND) STMT" or "if (COND) {"
    let after_if = trimmed.strip_prefix("if ")?;
    if !after_if.starts_with('(') {
        return None;
    }
    let close = find_matching_paren(after_if)?;
    let mut cond = after_if[1..close].trim();
    // Strip redundant outer parens: !(true) -> !true, (true) -> true
    if let Some(inner) = cond.strip_prefix("!(") {
        if let Some(val) = inner.strip_suffix(')') {
            let negated = format!("!{}", val);
            return match negated.as_str() {
                "!true" => Some(false),
                "!false" => Some(true),
                _ => None,
            };
        }
    }
    if cond.starts_with('(') {
        if let Some(close_inner) = find_matching_paren(cond) {
            if close_inner == cond.len() - 1 {
                cond = cond[1..close_inner].trim();
            }
        }
    }
    match cond {
        "true" | "!false" => Some(true),
        "false" | "!true" => Some(false),
        _ => None,
    }
}

/// Remove constant-condition branches from structured output.
///
/// Handles both single-line (`if (!true) return`) and block forms (`if (!true) {`).
/// Dead branches are removed entirely; always-taken branches have the if wrapper
/// stripped and body inlined.
pub fn eliminate_constant_condition_branches(lines: &mut Vec<String>) {
    let mut idx = 0;
    while idx < lines.len() {
        let Some(always_taken) = classify_constant_condition(&lines[idx]) else {
            idx += 1;
            continue;
        };

        let trimmed = lines[idx].trim().to_string();
        let is_block = trimmed.ends_with(" {") || trimmed == "{";

        if is_block {
            let close_idx = find_block_close(lines, idx);

            if always_taken {
                // Inline the body: remove if-line and closing brace (or else block)
                if close_idx < lines.len() && lines[close_idx].trim().starts_with("} else {") {
                    let else_end = find_block_close(lines, close_idx);
                    if else_end < lines.len() {
                        lines.drain(close_idx..=else_end);
                    }
                } else if close_idx < lines.len() {
                    lines.remove(close_idx);
                }
                lines.remove(idx);
            } else {
                // Dead branch: remove the entire block
                if close_idx < lines.len() && lines[close_idx].trim().starts_with("} else {") {
                    // Remove if-line through "} else {", keep else body, remove else close
                    lines.drain(idx..=close_idx);
                    let else_close = find_block_close(lines, idx.saturating_sub(1));
                    if else_close < lines.len() {
                        lines.remove(else_close);
                    }
                } else {
                    let end = if close_idx < lines.len() {
                        close_idx + 1
                    } else {
                        close_idx
                    };
                    lines.drain(idx..end);
                }
            }
        } else {
            // Single-line form: "if (COND) STMT"
            if always_taken {
                let after_if = trimmed.strip_prefix("if ").unwrap();
                let close = find_matching_paren(after_if).unwrap();
                let stmt = after_if[close + 1..].trim();
                if stmt.is_empty() {
                    lines.remove(idx);
                } else {
                    lines[idx] = stmt.to_string();
                    idx += 1;
                }
            } else {
                lines.remove(idx);
            }
        }
    }
}

pub(super) fn clean_line(text: &str) -> String {
    let mut s = text.to_string();

    // Strip bool(expr) -> expr (Kismet cast-to-bool is redundant in pseudocode)
    let mut bool_scan_pos = 0;
    while bool_scan_pos < s.len() {
        let Some(rel_pos) = s[bool_scan_pos..].find("bool(") else {
            break;
        };
        let pos = bool_scan_pos + rel_pos;
        if pos > 0 && is_ident_char(s.as_bytes()[pos - 1]) {
            bool_scan_pos = pos + 5;
            continue;
        }
        let paren_start = pos + 4;
        if let Some(close) = find_matching_paren(&s[paren_start..]) {
            let inner = s[paren_start + 1..paren_start + close].to_string();
            s = format!("{}{}{}", &s[..pos], inner, &s[paren_start + close + 1..]);
            bool_scan_pos = 0; // restart, string changed
        } else {
            break;
        }
    }

    // Double negation elimination: !(!X) -> X
    while let Some(simplified) = try_strip_double_negation(&s) {
        s = simplified;
    }

    // Outer extra parens in if-conditions: "if ((EXPR)) {" -> "if (EXPR) {"
    // Also handles "if ((EXPR)) return"
    for prefix in &["if (", "} else if ("] {
        if !s.starts_with(prefix) {
            continue;
        }
        let after_prefix = prefix.len();
        // Find the matching ')' for the '(' at the end of prefix
        if let Some(close) = find_matching_paren(&s[after_prefix - 1..]) {
            let cond = &s[after_prefix..after_prefix - 1 + close];
            let unwrapped = strip_outer_parens(cond);
            if unwrapped.len() < cond.len() {
                let rest = &s[after_prefix + close..];
                s = format!("{}{}){}", prefix, unwrapped, rest);
            }
        }
        break;
    }

    // Boolean switch -> ternary: switch(COND) { false: F, true: T } -> COND ? T : F
    s = rewrite_bool_switches(&s);

    s
}

/// Rewrite `switch(COND) { false: F, true: T }` to ternary form.
pub(super) fn rewrite_bool_switches(line: &str) -> String {
    let mut s = line.to_string();
    // Loop to handle multiple switches per line (process left-to-right)
    loop {
        let Some(result) = rewrite_one_bool_switch(&s) else {
            break;
        };
        s = result;
    }
    s
}

/// Find and rewrite the first bool switch in the string.
fn rewrite_one_bool_switch(input: &str) -> Option<String> {
    let switch_pos = input.find("switch(")?;

    // Extract COND by matching parens from the `(` after `switch`
    let paren_start = switch_pos + 6; // index of '('
    let cond_close = find_matching_paren(&input[paren_start..])?;
    let cond = &input[paren_start + 1..paren_start + cond_close];

    // Expect ` { ` after the closing paren
    let after_cond = &input[paren_start + cond_close + 1..];
    let after_cond = after_cond.strip_prefix(" { ")?;
    let brace_content_start = paren_start + cond_close + 1 + 3; // absolute pos of content after " { "

    // Parse the two cases. Track paren/brace depth to find `, ` and ` }` boundaries.
    let (expr_true, expr_false) = parse_bool_switch_cases(after_cond)?;

    // Find where the switch expression ends: scan for matching ` }` in original string
    let switch_end = find_switch_end(input, brace_content_start)?;

    // Identical branches: emit the expression directly (drop condition)
    if expr_true == expr_false {
        return Some(format!(
            "{}{}{}",
            &input[..switch_pos],
            expr_true,
            &input[switch_end..]
        ));
    }

    // Build ternary. Wrap condition in parens if compound.
    let cond_str = if expr_is_compound(cond) {
        format!("({})", cond)
    } else {
        cond.to_string()
    };

    let after_switch = &input[switch_end..];
    let before_switch = input[..switch_pos].trim_end();

    // Wrap ternary in parens when in operator context or method chain
    let needs_wrap = after_switch.starts_with('.')
        || before_switch.ends_with('+')
        || before_switch.ends_with('-')
        || before_switch.ends_with('*')
        || before_switch.ends_with('/')
        || before_switch.ends_with('%')
        || before_switch.ends_with("&&")
        || before_switch.ends_with("||")
        || after_switch.trim_start().starts_with("+ ")
        || after_switch.trim_start().starts_with("- ")
        || after_switch.trim_start().starts_with("* ")
        || after_switch.trim_start().starts_with("/ ")
        || after_switch.trim_start().starts_with("&& ")
        || after_switch.trim_start().starts_with("|| ");
    let ternary = format!("{} ? {} : {}", cond_str, expr_true, expr_false);
    let replacement = if needs_wrap {
        format!("({})", ternary)
    } else {
        ternary
    };

    Some(format!(
        "{}{}{}",
        &input[..switch_pos],
        replacement,
        after_switch
    ))
}

/// Parse case expressions inside a bool switch body. Returns (true_expr, false_expr).
fn parse_bool_switch_cases(content: &str) -> Option<(String, String)> {
    // Determine case order
    let (first_label, second_label, starts_false) = if content.starts_with("false: ") {
        ("false: ", "true: ", true)
    } else if content.starts_with("true: ") {
        ("true: ", "false: ", false)
    } else {
        return None;
    };

    let after_first_label = &content[first_label.len()..];

    // Find the `, second_label` separator at depth 0
    let sep = format!(", {}", second_label);
    let sep_pos = find_at_depth_zero(after_first_label, &sep)?;
    let first_expr = &after_first_label[..sep_pos];

    let after_sep = &after_first_label[sep_pos + sep.len()..];

    // Find closing ` }` at depth 0 for second expr
    let close_pos = find_at_depth_zero(after_sep, " }")?;
    let second_expr = &after_sep[..close_pos];

    // Reject if either expr is empty
    if first_expr.is_empty() || second_expr.is_empty() {
        return None;
    }

    // Reject if there's a `default:` anywhere (non-bool switch)
    if content.contains("default:") {
        return None;
    }

    if starts_false {
        Some((second_expr.to_string(), first_expr.to_string()))
    } else {
        Some((first_expr.to_string(), second_expr.to_string()))
    }
}

/// Find the position just past the closing `}` of a switch expression.
fn find_switch_end(input: &str, content_start: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, &b) in input.as_bytes().iter().enumerate().skip(content_start) {
        match b {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' => depth -= 1,
            b'}' => {
                if depth == 0 {
                    return Some(i + 1); // past the '}'
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

pub(super) fn has_toplevel_logical_op(input: &str) -> bool {
    find_at_depth_zero(input, " && ").is_some() || find_at_depth_zero(input, " || ").is_some()
}

/// Rewrite `if (!(COMPOUND)) return` -> `if (COMPOUND) { body }` when the
/// condition contains `&&`/`||` and the remaining body is <= 8 lines.
/// All text is flat; uses brace counting for body extent detection.
fn rewrite_negated_guards(lines: &mut Vec<String>) {
    let mut i = lines.len();
    while i > 0 {
        i -= 1;
        let line = &lines[i];
        let trimmed = line.trim();

        if !trimmed.starts_with("if (") {
            continue;
        }

        // Find matching ) for the ( after "if "
        let after_if = &trimmed[3..];
        let Some(close) = find_matching_paren(after_if) else {
            continue;
        };
        let rest = after_if[close + 1..].trim();
        if rest != "return" {
            continue;
        }

        let cond = after_if[1..close].trim();

        // Must be !(COMPOUND)
        if !cond.starts_with("!(") {
            continue;
        }
        let Some(inner_close) = find_matching_paren(&cond[1..]) else {
            continue;
        };
        if 1 + inner_close + 1 != cond.len() {
            continue;
        }

        let compound = &cond[2..1 + inner_close];

        // Only rewrite compound conditions
        if !compound.contains(" && ") && !compound.contains(" || ") {
            continue;
        }

        // Find body extent: scan forward, stop at section boundary, scope exit, or
        // a closing brace at the same brace depth as the guard
        let mut body_end = i + 1;
        let mut depth = 0i32;
        while body_end < lines.len() {
            let scan = lines[body_end].trim();
            if scan.starts_with("--- ") && scan.ends_with(" ---") {
                break;
            }
            if scan.is_empty() {
                body_end += 1;
                continue;
            }
            if scan.starts_with('}') {
                depth -= 1;
                if depth < 0 {
                    break;
                }
            }
            if scan == "}" && depth == 0 {
                break;
            }
            if scan.ends_with(" {") || scan == "{" {
                depth += 1;
            }
            body_end += 1;
        }

        // Trim trailing returns and empty lines from body
        let mut effective_end = body_end;
        while effective_end > i + 1 {
            let end_trimmed = lines[effective_end - 1].trim();
            if end_trimmed == "return" || end_trimmed.is_empty() {
                effective_end -= 1;
            } else {
                break;
            }
        }

        let body_count = effective_end - (i + 1);
        if body_count == 0 || body_count > 8 {
            continue;
        }

        // Rewrite: replace guard with positive if, wrap body in braces
        lines[i] = format!("if ({}) {{", compound);
        lines.insert(effective_end, "}".to_string());
    }
}

/// Remove empty if/else blocks, unreferenced labels, and bare temp assignments.
pub fn strip_orphaned_blocks(lines: &mut Vec<String>) {
    // Strip bare standalone expressions at brace depth 0 (top level).
    // In UberGraph event segments, InputAction events start with an unused
    // key parameter read ($InputActionEvent_Key_N) and sometimes bare true/false
    // literals. These are Kismet stack pushes with no consumer.
    {
        let mut depth = 0i32;
        lines.retain(|l| {
            let trimmed = l.trim();
            if trimmed.starts_with('}') {
                depth -= 1;
            }
            let at_top = depth <= 0;
            if trimmed.ends_with(" {") || trimmed == "{" {
                depth += 1;
            }
            // Standalone iface() calls at any depth
            if trimmed.starts_with("iface(") && !trimmed.contains(" = ") {
                if let Some(close) = find_matching_paren(&trimmed[5..]) {
                    if 5 + close + 1 == trimmed.len() {
                        return false;
                    }
                }
            }
            if at_top {
                if trimmed.starts_with('$') && !trimmed.contains('=') && !trimmed.contains('(') {
                    return false;
                }
                if trimmed == "true" || trimmed == "false" {
                    return false;
                }
            }
            true
        });
    }

    // Remove ForEach compiler artifacts: break-hit flag assignments are always
    // internal bookkeeping and never meaningful in pseudocode.
    lines.retain(|l| {
        let trimmed = l.trim();
        !trimmed.starts_with("Temp_bool_True_if_break_was_hit_Variable") || !trimmed.contains(" = ")
    });

    // Remove residual counter/index init lines that appear just before a while/for
    // loop (already absorbed by the loop syntax or semantically redundant).
    let mut remove_indices: HashSet<usize> = HashSet::new();
    for idx in 0..lines.len() {
        let trimmed = lines[idx].trim();
        if !(trimmed.starts_with("Temp_int_Loop_Counter_Variable")
            || trimmed.starts_with("Temp_int_Array_Index_Variable"))
        {
            continue;
        }
        if !trimmed.ends_with(" = 0") {
            continue;
        }
        // Check if a while/for loop follows within the next 3 lines
        let has_loop_nearby = lines[idx + 1..std::cmp::min(idx + 4, lines.len())]
            .iter()
            .any(|l| {
                let lt = l.trim();
                lt.starts_with("while (") || lt.starts_with("for (")
            });
        if has_loop_nearby {
            remove_indices.insert(idx);
        }
    }
    if !remove_indices.is_empty() {
        let mut kept_idx = 0;
        lines.retain(|_| {
            let keep = !remove_indices.contains(&kept_idx);
            kept_idx += 1;
            keep
        });
    }

    // Collect all goto targets so we know which labels are still referenced
    let goto_targets: HashSet<String> = lines
        .iter()
        .filter_map(|l| l.trim().strip_prefix("goto ").map(|s| s.to_string()))
        .collect();

    // Remove unreferenced generated labels (L_XXXX:)
    lines.retain(|line| {
        let trimmed = line.trim();
        if let Some(label) = trimmed.strip_suffix(':') {
            if label.starts_with("L_") && !goto_targets.contains(label) {
                return false;
            }
        }
        true
    });

    // Remove goto/label pairs that serve no structural purpose.
    strip_redundant_gotos(lines);

    // Iteratively remove empty if-blocks, orphaned else-blocks, and trailing braces.
    // Each pass may expose new patterns, so loop until stable.
    loop {
        let mut changed = false;

        // Strip trailing `} else {` (always orphaned at the end; else
        // with no body). Strip trailing `}` only when unmatched (depth < 0).
        while let Some(last) = lines.last() {
            let trimmed = last.trim();
            if trimmed == "} else {" {
                lines.pop();
                changed = true;
                continue;
            }
            if trimmed == "}" {
                let depth = brace_depth(lines);
                if depth < 0 {
                    lines.pop();
                    changed = true;
                    continue;
                }
            }
            break;
        }

        let mut i = 0;
        while i + 1 < lines.len() {
            let trimmed = lines[i].trim();
            let next_trimmed = lines[i + 1].trim();

            // Pattern: "if (...) {" followed by "} else {"
            // Remove the if line and the } else {, keep else body
            if trimmed.starts_with("if ") && trimmed.ends_with(" {") && next_trimmed == "} else {" {
                lines.remove(i);
                lines.remove(i); // was i+1, now shifted
                changed = true;
                continue;
            }

            // Pattern: "if (...) {" followed by "}"
            // Remove both (empty if-block)
            if trimmed.starts_with("if ") && trimmed.ends_with(" {") && next_trimmed == "}" {
                lines.remove(i);
                lines.remove(i);
                changed = true;
                continue;
            }

            // Pattern: "} else {" followed by "}"
            // Remove both (empty else-block)
            if trimmed == "} else {" && next_trimmed == "}" {
                lines.remove(i);
                lines.remove(i);
                changed = true;
                continue;
            }

            // Pattern: "if (...) {" / "    return" / "}" where the next line after
            // the close is also "return" -- both paths return, so the guard is
            // redundant. Remove the if-block, keep the return.
            if i + 2 < lines.len()
                && trimmed.starts_with("if ")
                && trimmed.ends_with(" {")
                && lines[i + 1].trim() == "return"
                && lines[i + 2].trim() == "}"
            {
                if i + 3 < lines.len() && lines[i + 3].trim() == "return" {
                    lines.drain(i..i + 3);
                    changed = true;
                    continue;
                }
                // If the if-return is at the end, just remove it (return is implicit)
                if i + 3 >= lines.len() {
                    lines.drain(i..i + 3);
                    changed = true;
                    continue;
                }
            }

            i += 1;
        }
        if !changed {
            break;
        }
    }
}

fn brace_depth(lines: &[String]) -> i32 {
    lines.iter().fold(0i32, |d, l| {
        let trimmed = l.trim();
        if trimmed.ends_with(" {") || trimmed == "{" {
            let close = i32::from(trimmed.starts_with("} "));
            d - close + 1
        } else if trimmed == "}" || trimmed.starts_with("} ") {
            d - 1
        } else {
            d
        }
    })
}

/// Remove unmatched `{`/`}` left from per-body processing.
/// Resets depth at section boundaries (`---`, `// sequence [`).
pub fn strip_unmatched_braces(lines: &mut Vec<String>) {
    fn is_boundary(trimmed: &str) -> bool {
        (trimmed.starts_with("---") && trimmed.ends_with("---"))
            || trimmed.starts_with("// sequence [")
    }

    // Pass 1: remove orphaned closing braces
    let mut depth: i32 = 0;
    lines.retain(|line| {
        let trimmed = line.trim();
        if is_boundary(trimmed) {
            depth = 0;
            return true;
        }
        if trimmed.ends_with(" {") || trimmed == "{" {
            // "} else {" both closes and opens, net zero depth change
            if trimmed.starts_with("} ") {
                if depth == 0 {
                    return false; // orphaned close
                }
                depth -= 1;
            }
            depth += 1;
            true
        } else if trimmed == "}" || trimmed.starts_with("} ") {
            if depth > 0 {
                depth -= 1;
                true
            } else {
                false
            }
        } else {
            true
        }
    });

    // Pass 2: remove opening braces that aren't closed before the next boundary.
    // Walk backwards within each section; if depth is positive at a boundary,
    // strip the unclosed `{` lines.
    let mut i = lines.len();
    depth = 0;
    while i > 0 {
        i -= 1;
        let trimmed = lines[i].trim().to_string();
        if is_boundary(&trimmed) {
            depth = 0;
            continue;
        }
        if trimmed == "}" || trimmed.starts_with("} ") {
            depth += 1;
        } else if trimmed.ends_with(" {") || trimmed == "{" {
            if depth > 0 {
                depth -= 1;
            } else {
                lines.remove(i);
            }
        }
    }
}

/// Remove goto/label pairs that are redundant in structured output
/// (single-reference labels near the end, start, or immediately after the goto).
fn strip_redundant_gotos(lines: &mut Vec<String>) {
    // Build goto -> label index map (only for generated L_XXXX labels)
    let mut goto_count: HashMap<String, usize> = HashMap::new();
    for line in lines.iter() {
        if let Some(label) = line.trim().strip_prefix("goto ") {
            if label.starts_with("L_") {
                *goto_count.entry(label.to_string()).or_default() += 1;
            }
        }
    }

    // Only process single-reference gotos (multi-ref handled by extract_convergence)
    let singles: HashSet<String> = goto_count
        .into_iter()
        .filter(|(_, count)| *count == 1)
        .map(|(label, _)| label)
        .collect();
    if singles.is_empty() {
        return;
    }

    // Find positions of each single-ref goto and its label
    let mut to_remove: HashSet<usize> = HashSet::new();
    for label_name in &singles {
        let label_line = format!("{}:", label_name);
        let goto_line = format!("goto {}", label_name);

        let label_idx = lines.iter().position(|l| l.trim() == label_line);
        let goto_idx = lines.iter().position(|l| l.trim() == goto_line);

        let (Some(li), Some(gi)) = (label_idx, goto_idx) else {
            continue;
        };

        // Check if label is at/near end: no meaningful code after the label
        // (excluding the goto itself, closing braces, and return)
        let has_code_after_label = lines[li + 1..].iter().enumerate().any(|(j, l)| {
            let idx = li + 1 + j;
            if idx == gi {
                return false; // skip the goto line itself
            }
            let trimmed = l.trim();
            !trimmed.is_empty() && trimmed != "}" && trimmed != "return" && !trimmed.ends_with(':')
        });

        // Check if goto is immediately before the label (fall-through)
        // allowing only closing braces between them
        let is_fall_through = gi < li
            && lines[gi + 1..li]
                .iter()
                .all(|l| l.trim() == "}" || l.trim().is_empty());

        // Backward goto to label at segment start (Sequence artifact)
        let is_backward_to_start = gi > li && li == 0;

        if !has_code_after_label || is_fall_through || is_backward_to_start {
            to_remove.insert(li);
            to_remove.insert(gi);
        }
    }

    if !to_remove.is_empty() {
        let mut idx = 0;
        lines.retain(|_| {
            let keep = !to_remove.contains(&idx);
            idx += 1;
            keep
        });
    }
}
