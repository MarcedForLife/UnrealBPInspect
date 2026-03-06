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
