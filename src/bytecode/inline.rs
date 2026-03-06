use std::collections::HashMap;
use super::decode::BcStatement;

/// Inline single-use `$temp` variables to reduce noise.
/// Only inlines vars that:
/// - Start with `$` (compiler temporaries)
/// - Are assigned exactly once (`$X = expr`)
/// - Are referenced exactly once in a later statement
/// - Would not produce a line longer than MAX_LINE chars
pub fn inline_single_use_temps(stmts: &mut Vec<BcStatement>) {
    const MAX_LINE: usize = 120;
    const MAX_PASSES: usize = 6;

    for _ in 0..MAX_PASSES {
        let mut inlined_any = false;

        // Collect assignments: (index, var_name, expr)
        let assignments: Vec<(usize, String, String)> = stmts.iter().enumerate()
            .filter_map(|(i, s)| {
                let (var, expr) = parse_temp_assignment(&s.text)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        // Count how many times each var name is assigned
        let mut assign_counts: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
        for (_, var_name, _) in &assignments {
            *assign_counts.entry(var_name.as_str()).or_default() += 1;
        }

        // For each assignment, count references in all other statements
        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var_name, expr) in &assignments {
            // Skip if this var name is assigned more than once (reused across event handlers)
            if assign_counts.get(var_name.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, s) in stmts.iter().enumerate() {
                if i == *assign_idx { continue; }
                ref_count += count_var_refs(&s.text, var_name);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var_name.clone(), expr.clone()));
            }
        }

        // Apply substitutions — re-verify and re-read expr after each change
        let mut removed: Vec<usize> = Vec::new();
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) { continue; }

            // Re-read the current expr (may have been modified by earlier inlines)
            let current_expr = match parse_temp_assignment(&stmts[*assign_idx].text) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };

            // Re-verify: count refs in current (possibly modified) statements
            let mut current_refs = 0usize;
            let mut target_idx = None;
            for (i, s) in stmts.iter().enumerate() {
                if i == *assign_idx || removed.contains(&i) { continue; }
                let refs = count_var_refs(&s.text, var_name);
                current_refs += refs;
                if refs == 1 && target_idx.is_none() { target_idx = Some(i); }
            }
            if current_refs != 1 { continue; }
            let Some(target_idx) = target_idx else { continue };

            let replacement = substitute_var(&stmts[target_idx].text, var_name, &current_expr);

            if replacement.len() > MAX_LINE { continue; }

            stmts[target_idx].text = replacement;
            removed.push(*assign_idx);
            inlined_any = true;
        }

        // Remove inlined assignment lines (reverse order to preserve indices)
        removed.sort_unstable();
        for idx in removed.into_iter().rev() {
            stmts.remove(idx);
        }

        if !inlined_any { break; }
    }
}

/// Parse `$VarName = expression` assignments. Returns (var_name, expression).
fn parse_temp_assignment(text: &str) -> Option<(&str, &str)> {
    if !text.starts_with('$') { return None; }
    let eq_pos = text.find(" = ")?;
    let var = &text[..eq_pos];
    // Must be a simple $name (no dots, brackets, etc.)
    if var.contains('.') || var.contains('[') { return None; }
    let expr = &text[eq_pos + 3..];
    // Must not be a persistent frame assignment
    if expr.ends_with("[persistent]") { return None; }
    Some((var, expr))
}

/// Count non-overlapping occurrences of `$VarName` in text,
/// only at word boundaries (not part of a longer $name).
fn count_var_refs(text: &str, var: &str) -> usize {
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        let after = abs_pos + var.len();
        let at_boundary = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
        if at_boundary {
            count += 1;
        }
        start = after;
    }
    count
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Substitute `$VarName` with `expr` in `text`, adding parens if needed.
fn substitute_var(text: &str, var: &str, expr: &str) -> String {
    let Some(pos) = text.find(var) else { return text.to_string() };
    let after = pos + var.len();
    let needs_wrap = expr_is_compound(expr) && used_in_operator_context(text, pos, after);
    let sub = if needs_wrap { format!("({})", expr) } else { expr.to_string() };
    format!("{}{}{}", &text[..pos], sub, &text[after..])
}

fn expr_is_compound(expr: &str) -> bool {
    const TOKENS: &[&str] = &[
        " && ", " || ", " + ", " - ", " * ", " / ", " % ",
        " < ", " <= ", " > ", " >= ", " == ", " != ",
    ];
    TOKENS.iter().any(|tok| expr.contains(tok)) || expr.starts_with('!')
}

fn used_in_operator_context(text: &str, pos: usize, after: usize) -> bool {
    let before = &text[..pos];
    let after_text = &text[after..];
    let op_before = before.ends_with("!(") || before.ends_with("! ")
        || before.trim_end().ends_with("&&") || before.trim_end().ends_with("||")
        || before.trim_end().ends_with('+') || before.trim_end().ends_with('-')
        || before.trim_end().ends_with('*') || before.trim_end().ends_with('/')
        || before.trim_end().ends_with(">=") || before.trim_end().ends_with("<=")
        || before.trim_end().ends_with("==") || before.trim_end().ends_with("!=")
        || before.trim_end().ends_with('>') || before.trim_end().ends_with('<');
    let op_after = after_text.trim_start().starts_with("&&")
        || after_text.trim_start().starts_with("||")
        || after_text.trim_start().starts_with("+ ")
        || after_text.trim_start().starts_with("- ")
        || after_text.trim_start().starts_with("* ")
        || after_text.trim_start().starts_with("/ ")
        || after_text.trim_start().starts_with(">= ")
        || after_text.trim_start().starts_with("<= ")
        || after_text.trim_start().starts_with("== ")
        || after_text.trim_start().starts_with("!= ")
        || after_text.trim_start().starts_with("> ")
        || after_text.trim_start().starts_with("< ");
    op_before || op_after
}

/// Discard assignments to `$temp` variables that are never referenced.
/// Keeps the RHS call (side effects) but drops the `$var = ` prefix.
pub fn discard_unused_assignments(stmts: &mut Vec<BcStatement>) {
    // Count how many times each var is assigned
    let mut assign_counts: HashMap<String, usize> = HashMap::new();
    for s in stmts.iter() {
        if let Some((var, _)) = parse_temp_assignment(&s.text) {
            *assign_counts.entry(var.to_string()).or_default() += 1;
        }
    }

    // For each uniquely-assigned $var, count total refs across all statements
    let mut ref_counts: HashMap<String, usize> = HashMap::new();
    for (var, ac) in &assign_counts {
        if *ac != 1 { continue; }
        let mut total = 0usize;
        for s in stmts.iter() {
            total += count_var_refs(&s.text, var);
        }
        // total includes the assignment LHS itself (1 occurrence)
        ref_counts.insert(var.clone(), total.saturating_sub(1));
    }

    for s in stmts.iter_mut() {
        if let Some((var, expr)) = parse_temp_assignment(&s.text) {
            if ref_counts.get(var).copied() == Some(0) {
                // Drop the assignment, keep just the expression (function call)
                s.text = expr.to_string();
            }
        }
    }
}

/// Clean up structured output lines: double negation, extra parens, trailing returns.
pub fn cleanup_structured_output(lines: &mut Vec<String>) {
    // Pass 1: clean each line in place
    for line in lines.iter_mut() {
        let indent_len = line.len() - line.trim_start().len();
        let indent = &line[..indent_len];
        let trimmed = line[indent_len..].to_string();
        let cleaned = clean_line(&trimmed);
        if cleaned != trimmed {
            *line = format!("{}{}", indent, cleaned);
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

    // Pass 3: suppress dead code after unconditional return at indent 0
    // Only in non-ubergraph functions (no "---" labels)
    let has_labels = lines.iter().any(|l| l.starts_with("---"));
    if !has_labels {
        let mut dead = false;
        lines.retain(|line| {
            let trimmed = line.trim();
            if dead {
                // Closing braces are structural, keep them
                trimmed == "}" || trimmed.is_empty()
            } else {
                let indent_len = line.len() - line.trim_start().len();
                if indent_len == 0 && trimmed == "return" {
                    dead = true;
                }
                true
            }
        });
    }

    // Pass 4: rewrite negated guards with compound conditions
    rewrite_negated_guards(lines);
}

fn clean_line(text: &str) -> String {
    let mut s = text.to_string();

    // !(!X) → X — but only when the inner ! covers the entire expression.
    // Safe: !(!A) → A, !(!(A && B)) → (A && B)
    // Unsafe: !(!A && B) — inner ! only negates A, not the whole expression
    loop {
        if let Some(pos) = s.find("!(") {
            // Check if the char before ! is ( or space or start — i.e. it's a prefix not
            if pos > 0 {
                let prev = s.as_bytes()[pos - 1];
                if prev != b'(' && prev != b' ' && prev != b'!' {
                    break;
                }
            }
            // Find matching close paren
            let inner_start = pos + 2;
            if let Some(inner) = find_matching_paren(&s[pos + 1..]) {
                let inner_text = &s[inner_start..pos + 1 + inner];
                // Only simplify if inner_text starts with ! (double negation)
                // AND the ! covers the entire inner expression (no top-level && or ||)
                if inner_text.starts_with('!') {
                    let after_neg = &inner_text[1..];
                    if !has_toplevel_logical_op(after_neg) {
                        s = format!("{}{}{}", &s[..pos], after_neg, &s[pos + 2 + inner..]);
                        continue;
                    }
                }
            }
        }
        break;
    }

    // Outer extra parens in if-conditions: "if ((EXPR)) {" → "if (EXPR) {"
    // Also handles "if ((EXPR)) return"
    for prefix in &["if (", "} else if ("] {
        if !s.starts_with(prefix) { continue; }
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

    s
}

/// Check if a string contains ` && ` or ` || ` at paren depth 0.
/// Used to determine if `!` only negates the first operand in a compound expression.
fn has_toplevel_logical_op(s: &str) -> bool {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let len = bytes.len();
    for i in 0..len {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' if depth == 0 && i + 3 < len => {
                if &s[i..i + 4] == " && " || &s[i..i + 4] == " || " {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Strip one layer of redundant outer parentheses if they match.
fn strip_outer_parens(s: &str) -> &str {
    if !s.starts_with('(') || !s.ends_with(')') { return s; }
    // Verify the open paren at 0 matches the close at end
    let inner = &s[1..s.len() - 1];
    let mut depth = 0i32;
    for ch in inner.chars() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 { return s; } // close paren matched the outer open
            }
            _ => {}
        }
    }
    if depth == 0 { inner } else { s }
}

/// Find the position of the closing ')' matching the '(' at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    if !s.starts_with('(') { return None; }
    let mut depth = 0i32;
    for (i, ch) in s.chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 { return Some(i); }
            }
            _ => {}
        }
    }
    None
}

/// Rewrite `if (!(COMPOUND)) return` → `if (COMPOUND) { body }` when the
/// condition contains `&&` or `||` and the remaining body is ≤ 8 lines.
fn rewrite_negated_guards(lines: &mut Vec<String>) {
    let mut i = lines.len();
    while i > 0 {
        i -= 1;
        let line = &lines[i];
        let indent_len = line.len() - line.trim_start().len();
        let trimmed = &line[indent_len..];

        if !trimmed.starts_with("if (") { continue; }

        // Find matching ) for the ( after "if "
        let after_if = &trimmed[3..];
        let Some(close) = find_matching_paren(after_if) else { continue };
        let rest = after_if[close + 1..].trim();
        if rest != "return" { continue; }

        let cond = after_if[1..close].trim();

        // Must be !(COMPOUND)
        if !cond.starts_with("!(") { continue; }
        let Some(inner_close) = find_matching_paren(&cond[1..]) else { continue };
        if 1 + inner_close + 1 != cond.len() { continue; }

        let compound = &cond[2..1 + inner_close];

        // Only rewrite compound conditions
        if !compound.contains(" && ") && !compound.contains(" || ") { continue; }

        // Find body extent
        let guard_indent = indent_len;
        let mut body_end = i + 1;
        while body_end < lines.len() {
            let t = lines[body_end].trim();
            if t.starts_with("--- ") && t.ends_with(" ---") { break; }
            if t.is_empty() { body_end += 1; continue; }
            let li = lines[body_end].len() - lines[body_end].trim_start().len();
            if li < guard_indent { break; }
            if li == guard_indent && t == "}" { break; }
            body_end += 1;
        }

        // Trim trailing returns and empty lines from body
        let mut effective_end = body_end;
        while effective_end > i + 1 {
            let t = lines[effective_end - 1].trim();
            if t == "return" || t.is_empty() { effective_end -= 1; } else { break; }
        }

        let body_count = effective_end - (i + 1);
        if body_count == 0 || body_count > 8 { continue; }

        // Rewrite: replace guard with positive if + wrapped body
        let indent_str = lines[i][..indent_len].to_string();
        lines[i] = format!("{}if ({}) {{", indent_str, compound);
        for j in (i + 1)..effective_end {
            lines[j] = format!("    {}", lines[j]);
        }
        lines.insert(effective_end, format!("{}}}", indent_str));
    }
}
