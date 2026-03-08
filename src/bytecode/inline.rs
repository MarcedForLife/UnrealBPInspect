use super::decode::BcStatement;
use std::collections::{HashMap, HashSet};

/// Inline single-use `$temp` variables to reduce noise.
/// Only inlines vars that:
/// - Start with `$` (compiler temporaries)
/// - Are assigned exactly once (`$X = expr`)
/// - Are referenced exactly once in a later statement
/// - Would not produce a line longer than MAX_LINE chars
pub fn inline_single_use_temps(stmts: &mut Vec<BcStatement>) {
    const MAX_LINE: usize = 120; // Skip inlining if result would exceed this (readability cap)
    const MAX_PASSES: usize = 6; // Iterative: inlining one temp may expose further inlines

    for _ in 0..MAX_PASSES {
        let mut inlined_any = false;

        // Collect assignments: (index, var_name, expr)
        let assignments: Vec<(usize, String, String)> = stmts
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                let (var, expr) = parse_temp_assignment(&s.text)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        // Count how many times each var name is assigned
        let mut assign_counts: std::collections::HashMap<&str, usize> =
            std::collections::HashMap::new();
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
                if i == *assign_idx {
                    continue;
                }
                ref_count += count_var_refs(&s.text, var_name);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var_name.clone(), expr.clone()));
            }
        }

        // Apply substitutions — re-verify and re-read expr after each change
        let mut removed: Vec<usize> = Vec::new();
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }

            // Re-read the current expr (may have been modified by earlier inlines)
            let current_expr = match parse_temp_assignment(&stmts[*assign_idx].text) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };

            // Re-verify: count refs in current (possibly modified) statements
            let mut current_refs = 0usize;
            let mut target_idx = None;
            for (i, s) in stmts.iter().enumerate() {
                if i == *assign_idx || removed.contains(&i) {
                    continue;
                }
                let refs = count_var_refs(&s.text, var_name);
                current_refs += refs;
                if refs == 1 && target_idx.is_none() {
                    target_idx = Some(i);
                }
            }
            if current_refs != 1 {
                continue;
            }
            let Some(target_idx) = target_idx else {
                continue;
            };

            let replacement = substitute_var(&stmts[target_idx].text, var_name, &current_expr);

            // Bypass MAX_LINE when expression (even with parens) is shorter than the variable —
            // the resulting line can only get shorter or stay the same length.
            let shortens = current_expr.len() + 2 <= var_name.len(); // +2 for possible (...)
            if !shortens && replacement.len() > MAX_LINE {
                continue;
            }

            stmts[target_idx].text = replacement;
            removed.push(*assign_idx);
            inlined_any = true;
        }

        // Remove inlined assignment lines (reverse order to preserve indices)
        removed.sort_unstable();
        for idx in removed.into_iter().rev() {
            stmts.remove(idx);
        }

        if !inlined_any {
            break;
        }
    }
}

/// Parse `$VarName = expression` or `Temp_* = expression` assignments.
/// Returns (var_name, expression).
fn parse_temp_assignment(text: &str) -> Option<(&str, &str)> {
    if !text.starts_with('$') && !text.starts_with("Temp_") {
        return None;
    }
    let eq_pos = text.find(" = ")?;
    let var = &text[..eq_pos];
    // Must be a simple $name (no dots, brackets, etc.)
    if var.contains('.') || var.contains('[') {
        return None;
    }
    let expr = &text[eq_pos + 3..];
    // Must not be a persistent frame assignment
    if expr.ends_with("[persistent]") {
        return None;
    }
    Some((var, expr))
}

/// Count non-overlapping occurrences of `$VarName` in text,
/// only at word boundaries (not part of a longer $name).
fn count_var_refs(text: &str, var: &str) -> usize {
    let needs_start_check = !var.starts_with('$');
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        let after = abs_pos + var.len();
        let at_start =
            !needs_start_check || abs_pos == 0 || !is_ident_char(text.as_bytes()[abs_pos - 1]);
        let at_end = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
        if at_start && at_end {
            count += 1;
        }
        start = after;
    }
    count
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Substitute `$VarName` or `Temp_*` with `expr` in `text`, adding parens if needed.
/// Only replaces at word boundaries (first match).
fn substitute_var(text: &str, var: &str, expr: &str) -> String {
    let needs_start_check = !var.starts_with('$');
    let mut start = 0;
    while let Some(rel) = text[start..].find(var) {
        let pos = start + rel;
        let after = pos + var.len();
        let at_start = !needs_start_check || pos == 0 || !is_ident_char(text.as_bytes()[pos - 1]);
        let at_end = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
        if at_start && at_end {
            let needs_wrap = expr_is_compound(expr) && used_in_operator_context(text, pos, after);
            let sub = if needs_wrap {
                format!("({})", expr)
            } else {
                expr.to_string()
            };
            return format!("{}{}{}", &text[..pos], sub, &text[after..]);
        }
        start = after;
    }
    text.to_string()
}

fn expr_is_compound(expr: &str) -> bool {
    const TOKENS: &[&str] = &[
        " && ", " || ", " + ", " - ", " * ", " / ", " % ", " < ", " <= ", " > ", " >= ", " == ",
        " != ", " >> ", " << ",
    ];
    TOKENS.iter().any(|tok| expr.contains(tok)) || expr.starts_with('!')
}

fn used_in_operator_context(text: &str, pos: usize, after: usize) -> bool {
    let before = &text[..pos];
    let after_text = &text[after..];
    let op_before = before.ends_with("!(")
        || before.ends_with("! ")
        || before.trim_end().ends_with("&&")
        || before.trim_end().ends_with("||")
        || before.trim_end().ends_with('+')
        || before.trim_end().ends_with('-')
        || before.trim_end().ends_with('*')
        || before.trim_end().ends_with('/')
        || before.trim_end().ends_with(">=")
        || before.trim_end().ends_with("<=")
        || before.trim_end().ends_with("==")
        || before.trim_end().ends_with("!=")
        || before.trim_end().ends_with(">>")
        || before.trim_end().ends_with("<<")
        || before.trim_end().ends_with('>')
        || before.trim_end().ends_with('<');
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
        || after_text.trim_start().starts_with(">> ")
        || after_text.trim_start().starts_with("<< ")
        || after_text.trim_start().starts_with("> ")
        || after_text.trim_start().starts_with("< ");
    op_before || op_after
}

/// Discard assignments to `$temp` variables that are never referenced.
/// Keeps the RHS call (side effects) but drops the `$var = ` prefix.
pub fn discard_unused_assignments(stmts: &mut [BcStatement]) {
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
        if *ac != 1 {
            continue;
        }
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

    // Strip bool(expr) → expr (Kismet cast-to-bool is redundant in pseudocode)
    let mut bstart = 0;
    while bstart < s.len() {
        let Some(rel_pos) = s[bstart..].find("bool(") else {
            break;
        };
        let pos = bstart + rel_pos;
        if pos > 0 && is_ident_char(s.as_bytes()[pos - 1]) {
            bstart = pos + 5;
            continue;
        }
        let paren_start = pos + 4;
        if let Some(close) = find_matching_paren(&s[paren_start..]) {
            let inner = s[paren_start + 1..paren_start + close].to_string();
            s = format!("{}{}{}", &s[..pos], inner, &s[paren_start + close + 1..]);
            bstart = 0; // restart — string changed
        } else {
            break;
        }
    }

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
                if let Some(after_neg) = inner_text.strip_prefix('!') {
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
    if !s.starts_with('(') || !s.ends_with(')') {
        return s;
    }
    // Verify the open paren at 0 matches the close at end
    let inner = &s[1..s.len() - 1];
    let mut depth = 0i32;
    for ch in inner.chars() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return s;
                } // close paren matched the outer open
            }
            _ => {}
        }
    }
    if depth == 0 {
        inner
    } else {
        s
    }
}

/// Find the position of the closing ')' matching the '(' at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    if !s.starts_with('(') {
        return None;
    }
    let mut depth = 0i32;
    for (i, ch) in s.chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
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

        // Find body extent
        let guard_indent = indent_len;
        let mut body_end = i + 1;
        while body_end < lines.len() {
            let t = lines[body_end].trim();
            if t.starts_with("--- ") && t.ends_with(" ---") {
                break;
            }
            if t.is_empty() {
                body_end += 1;
                continue;
            }
            let li = lines[body_end].len() - lines[body_end].trim_start().len();
            if li < guard_indent {
                break;
            }
            if li == guard_indent && t == "}" {
                break;
            }
            body_end += 1;
        }

        // Trim trailing returns and empty lines from body
        let mut effective_end = body_end;
        while effective_end > i + 1 {
            let t = lines[effective_end - 1].trim();
            if t == "return" || t.is_empty() {
                effective_end -= 1;
            } else {
                break;
            }
        }

        let body_count = effective_end - (i + 1);
        if body_count == 0 || body_count > 8 {
            continue;
        }

        // Rewrite: replace guard with positive if + wrapped body
        let indent_str = lines[i][..indent_len].to_string();
        lines[i] = format!("{}if ({}) {{", indent_str, compound);
        for line in lines.iter_mut().take(effective_end).skip(i + 1) {
            *line = format!("    {}", line);
        }
        lines.insert(effective_end, format!("{}}}", indent_str));
    }
}

// ============================================================
// Summary pattern folding (Break/Make, struct construction,
// unused out-param suppression, Make→short name renaming)
// ============================================================

/// Max output args for a Break* call to be fully inlined (replaced with dot access).
/// Above this threshold, the call is compacted instead (named params, skip underscores).
const BREAK_INLINE_MAX_ARGS: usize = 4;

/// Post-processing pass on structured output lines.
/// Folds Break/Make struct patterns, collapses struct construction,
/// suppresses unused out-params, and renames Make functions.
pub fn fold_summary_patterns(lines: &mut Vec<String>) {
    // Process each section independently (sections separated by --- markers)
    let mut result: Vec<String> = Vec::new();
    let mut section: Vec<String> = Vec::new();

    for line in lines.drain(..) {
        let trimmed = line.trim();
        if trimmed.starts_with("---") && trimmed.ends_with("---") {
            if !section.is_empty() {
                process_section(&mut section);
                result.append(&mut section);
            }
            result.push(line);
        } else {
            section.push(line);
        }
    }
    if !section.is_empty() {
        process_section(&mut section);
        result.append(&mut section);
    }

    // Global pass: rename Make functions (cosmetic, scope-independent)
    rename_make_functions(&mut result);

    *lines = result;
}

fn process_section(lines: &mut Vec<String>) {
    rewrite_foreach_loops(lines);
    fold_delegate_bindings(lines);
    fold_cast_guards(lines);
    fold_break_patterns(lines);
    fold_struct_construction(lines);
    dedup_completion_paths(lines);
    fold_section_temps(lines);
    suppress_unused_outparams(lines);
    compact_large_break_calls(lines);
}

/// Rewrite ForEach loop boilerplate into `for (ITEM in ARRAY)`.
/// Detects the pattern: counter/index init, while(COUNTER < Array_Length(ARRAY)),
/// index assignment, Array_Get, body, increment.
fn rewrite_foreach_loops(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        let indent_len = lines[i].len() - trimmed.len();

        // Step 1: Match "while (COUNTER < Array_Length(ARRAY)) {"
        let Some((counter, array)) = parse_foreach_while(trimmed) else {
            i += 1;
            continue;
        };

        // Step 2: Find two init lines before the while at same indent
        let Some((counter_idx, index_idx, index_var)) =
            find_foreach_init(lines, i, indent_len, &counter)
        else {
            i += 1;
            continue;
        };

        // Step 3: Validate body start: INDEX = COUNTER, then Array_Get(ARRAY, INDEX, ITEM)
        let body_indent = indent_len + 4;
        let Some((assign_idx, get_idx, item)) =
            validate_body_start(lines, i + 1, body_indent, &index_var, &counter, &array)
        else {
            i += 1;
            continue;
        };

        // Step 4: Find closing } and validate increment as last body line
        let Some((close_idx, incr_idx)) = find_close_and_increment(lines, i, indent_len, &counter)
        else {
            i += 1;
            continue;
        };

        // All checks passed — rewrite
        let indent_str = &lines[i][..indent_len];
        lines[i] = format!("{}for ({} in {}) {{", indent_str, item, array);

        // Remove lines in reverse order to preserve indices
        let mut to_remove = vec![incr_idx, get_idx, assign_idx, index_idx, counter_idx];
        to_remove.sort_unstable();
        to_remove.dedup();
        let removed_before_i = to_remove.iter().filter(|&&idx| idx < i).count();
        for idx in to_remove.into_iter().rev() {
            // Don't remove lines past close_idx (shouldn't happen, but safety)
            if idx < close_idx {
                lines.remove(idx);
            }
        }

        // Post-rewrite cleanup: remove redundant Array_Get re-fetches inside the loop body.
        // These reference the now-stale index variable and fetch into the same item variable
        // that the `for` header already provides.
        {
            // Adjust for_idx since lines before `i` were removed
            let for_idx = i - removed_before_i;
            let mut depth = 0i32;
            let mut new_close = for_idx;
            for (j, line) in lines.iter().enumerate().skip(for_idx) {
                let t = line.trim();
                if t.ends_with('{') {
                    depth += 1;
                }
                if t == "}" {
                    depth -= 1;
                    if depth == 0 {
                        new_close = j;
                        break;
                    }
                }
            }
            // Scan body for Array_Get(ARRAY, INDEX_VAR, ITEM) and remove
            let mut j = for_idx + 1;
            while j < new_close {
                let t = lines[j].trim();
                if let Some(rest) = t.strip_prefix("Array_Get(") {
                    if let Some(inner) = rest.strip_suffix(')') {
                        let ag_args = split_args(inner);
                        if ag_args.len() == 3
                            && ag_args[0] == array
                            && ag_args[1] == index_var
                            && ag_args[2] == item
                        {
                            lines.remove(j);
                            new_close -= 1;
                            continue; // don't advance j
                        }
                    }
                }
                j += 1;
            }
        }

        // Don't advance — recheck in case of nested loops
        i = 0;
    }
}

/// Parse "while (COUNTER < Array_Length(ARRAY)) {" → Some((counter, array))
fn parse_foreach_while(trimmed: &str) -> Option<(String, String)> {
    let rest = trimmed.strip_prefix("while (")?;
    let rest = rest.strip_suffix(") {")?;
    // Pattern: COUNTER < Array_Length(ARRAY)
    let lt_pos = rest.find(" < ")?;
    let counter = &rest[..lt_pos];
    let rhs = &rest[lt_pos + 3..];
    let inner = rhs.strip_prefix("Array_Length(")?;
    let array = inner.strip_suffix(')')?;
    Some((counter.to_string(), array.to_string()))
}

/// Scan backward from while_idx for COUNTER = 0 and INDEX = 0 init lines.
fn find_foreach_init(
    lines: &[String],
    while_idx: usize,
    indent_len: usize,
    counter: &str,
) -> Option<(usize, usize, String)> {
    // Look at up to 4 lines before while for counter=0 and index=0 (compiler may insert gaps)
    let start = while_idx.saturating_sub(4);
    let mut counter_idx = None;
    let mut index_idx = None;
    let mut index_var = None;

    for j in (start..while_idx).rev() {
        let t = lines[j].trim();
        if t.is_empty() {
            continue;
        }
        let li = lines[j].len() - t.len();
        if li != indent_len {
            break;
        }

        if t == format!("{} = 0", counter) {
            counter_idx = Some(j);
        } else if t.ends_with(" = 0") && t.starts_with("Temp_int_") {
            let var = &t[..t.len() - 4]; // strip " = 0"
            index_var = Some(var.to_string());
            index_idx = Some(j);
        }
    }

    Some((counter_idx?, index_idx?, index_var?))
}

/// Validate first two body lines: INDEX = COUNTER, then Array_Get(ARRAY, INDEX, ITEM).
fn validate_body_start(
    lines: &[String],
    start: usize,
    body_indent: usize,
    index: &str,
    counter: &str,
    array: &str,
) -> Option<(usize, usize, String)> {
    // Find the first two non-empty body lines
    let mut body_lines = Vec::new();
    let mut j = start;
    while j < lines.len() && body_lines.len() < 2 {
        let t = lines[j].trim();
        if t.is_empty() {
            j += 1;
            continue;
        }
        let li = lines[j].len() - t.len();
        if li < body_indent {
            return None;
        }
        body_lines.push((j, t.to_string()));
        j += 1;
    }
    if body_lines.len() < 2 {
        return None;
    }

    // Line 1: INDEX = COUNTER
    let expected_assign = format!("{} = {}", index, counter);
    if body_lines[0].1 != expected_assign {
        return None;
    }
    let assign_idx = body_lines[0].0;

    // Line 2: Array_Get(ARRAY, INDEX, ITEM)
    let t = &body_lines[1].1;
    let rest = t.strip_prefix("Array_Get(")?;
    let rest = rest.strip_suffix(')')?;
    let args = split_args(rest);
    if args.len() != 3 {
        return None;
    }
    if args[0] != array || args[1] != index {
        return None;
    }
    let item = args[2].to_string();
    let get_idx = body_lines[1].0;

    Some((assign_idx, get_idx, item))
}

/// Find closing `}` and validate COUNTER = COUNTER + 1 as the last body line before it.
fn find_close_and_increment(
    lines: &[String],
    while_idx: usize,
    indent_len: usize,
    counter: &str,
) -> Option<(usize, usize)> {
    // Find the closing } at the same indent as while
    let mut depth = 0i32;
    let mut close_idx = None;
    for (j, line) in lines.iter().enumerate().skip(while_idx) {
        let t = line.trim();
        if t.ends_with('{') {
            depth += 1;
        }
        if t == "}" {
            let li = line.len() - t.len();
            if li == indent_len {
                depth -= 1;
                if depth == 0 {
                    close_idx = Some(j);
                    break;
                }
            }
        }
    }
    let close_idx = close_idx?;

    // Last non-empty body line before close should be the increment
    let expected_incr = format!("{} = {} + 1", counter, counter);
    let mut incr_idx = None;
    for j in (while_idx + 1..close_idx).rev() {
        let t = lines[j].trim();
        if t.is_empty() {
            continue;
        }
        if t == expected_incr {
            incr_idx = Some(j);
        }
        break; // only check the last non-empty line
    }

    Some((close_idx, incr_idx?))
}

/// Fold `bind(FUNC, $DELEGATE, OBJ)` + `TARGET +=/-= $DELEGATE` into `TARGET +=/-= OBJ.FUNC`.
fn fold_delegate_bindings(lines: &mut Vec<String>) {
    let mut i = 0;
    while i + 1 < lines.len() {
        let trimmed = lines[i].trim();
        let Some((func, delegate, obj)) = parse_bind_call(trimmed) else {
            i += 1;
            continue;
        };
        let next_trimmed = lines[i + 1].trim();
        let Some((target, op, used_delegate)) = parse_delegate_op(next_trimmed) else {
            i += 1;
            continue;
        };
        if used_delegate != delegate {
            i += 1;
            continue;
        }

        // Verify delegate is not used elsewhere (expect exactly 1 ref outside bind line)
        let mut total_refs = 0;
        for (j, line) in lines.iter().enumerate() {
            if j == i {
                continue;
            } // skip the bind line itself
            total_refs += count_var_refs(line.trim(), &delegate);
        }
        if total_refs != 1 {
            i += 1;
            continue;
        }

        // Rewrite
        let indent = &lines[i][..lines[i].len() - trimmed.len()];
        lines[i] = format!("{}{} {} {}.{}", indent, target, op, obj, func);
        lines.remove(i + 1);
        // Don't advance — recheck current position
    }
}

/// Parse `bind(FUNC, $VAR, OBJ)` → Some((func, delegate_var, obj))
fn parse_bind_call(text: &str) -> Option<(String, String, String)> {
    let rest = text.strip_prefix("bind(")?;
    let rest = rest.strip_suffix(')')?;
    let args = split_args(rest);
    if args.len() != 3 {
        return None;
    }
    let func = args[0];
    let delegate = args[1];
    let obj = args[2];
    // Delegate must be a $temp variable
    if !delegate.starts_with('$') {
        return None;
    }
    Some((func.to_string(), delegate.to_string(), obj.to_string()))
}

/// Parse `TARGET += $VAR` or `TARGET -= $VAR` → Some((target, op, delegate_var))
fn parse_delegate_op(text: &str) -> Option<(String, String, String)> {
    for op in &[" += ", " -= "] {
        if let Some(pos) = text.find(op) {
            let target = &text[..pos];
            let var = &text[pos + op.len()..];
            if var.starts_with('$') {
                return Some((target.to_string(), op.trim().to_string(), var.to_string()));
            }
        }
    }
    None
}

/// Fold `$X = cast<T>(expr)` + `if (!$X) return` into `$X = cast<T>(expr) else return`.
fn fold_cast_guards(lines: &mut Vec<String>) {
    let mut i = 0;
    while i + 1 < lines.len() {
        let trimmed_a = lines[i].trim();
        let indent_a = lines[i].len() - trimmed_a.len();

        // Line A: $VAR = cast<...>(...) or icast<...>(...) or obj_cast<...>(...)
        let Some((var, _rhs)) = parse_cast_assignment(trimmed_a) else {
            i += 1;
            continue;
        };

        let trimmed_b = lines[i + 1].trim();
        let indent_b = lines[i + 1].len() - trimmed_b.len();

        // Same indent
        if indent_a != indent_b {
            i += 1;
            continue;
        }

        // Line B: exactly "if (!$VAR) return"
        let expected = format!("if (!{}) return", var);
        if trimmed_b != expected {
            i += 1;
            continue;
        }

        // Rewrite: append " else return" to line A, remove line B
        let indent_str = &lines[i][..indent_a];
        lines[i] = format!("{}{} else return", indent_str, trimmed_a);
        lines.remove(i + 1);
        // Don't advance — recheck
    }
}

/// Parse `$VAR = cast<...>(...)` assignment where RHS starts with cast</icast</obj_cast<.
fn parse_cast_assignment(text: &str) -> Option<(&str, &str)> {
    if !text.starts_with('$') {
        return None;
    }
    let eq_pos = text.find(" = ")?;
    let var = &text[..eq_pos];
    if var.contains('.') || var.contains('[') {
        return None;
    }
    let rhs = &text[eq_pos + 3..];
    if rhs.starts_with("cast<") || rhs.starts_with("icast<") || rhs.starts_with("obj_cast<") {
        Some((var, rhs))
    } else {
        None
    }
}

/// Fold small Break* calls into field accessors using dynamic field name inference.
/// `BreakTransform($src, $BreakTransform_Location, ...)` → replace with `$src.Location` etc.
/// Only applies when output arg count ≤ BREAK_INLINE_MAX_ARGS and all outputs are `$temp`.
fn fold_break_patterns(lines: &mut Vec<String>) {
    let mut to_remove: Vec<usize> = Vec::new();

    for i in 0..lines.len() {
        let trimmed = lines[i].trim().to_string();

        // Match Break* function calls at start of line
        let Some(paren_start) = trimmed.find('(') else {
            continue;
        };
        let func_name = &trimmed[..paren_start];
        if !func_name.starts_with("Break") || !trimmed.ends_with(')') {
            continue;
        }

        let args_str = &trimmed[paren_start + 1..trimmed.len() - 1];
        let args = split_args(args_str);

        // First arg is source, rest are output vars
        if args.len() < 2 {
            continue;
        }
        let output_args = &args[1..];
        if output_args.len() > BREAK_INLINE_MAX_ARGS {
            continue;
        }

        // All output vars must be $temp
        if !output_args.iter().all(|a| a.starts_with('$')) {
            continue;
        }

        let source = args[0].to_string();
        let prefix = format!("${}_", func_name);

        // Infer field names from $BreakName_FieldName convention
        let raw_fields: Vec<Option<&str>> = output_args
            .iter()
            .map(|a| a.strip_prefix(&prefix))
            .collect();

        // If any arg can't be resolved, skip this Break call
        if raw_fields.iter().any(|f| f.is_none()) {
            continue;
        }
        let raw_fields: Vec<&str> = raw_fields.into_iter().map(|f| f.unwrap()).collect();

        // Detect shared disambiguation suffix (_1, _2, etc.)
        // If all fields end with the same _N, strip it
        let fields: Vec<&str> = if let Some(common_suffix) = detect_common_suffix(&raw_fields) {
            raw_fields
                .iter()
                .map(|f| &f[..f.len() - common_suffix.len()])
                .collect()
        } else {
            raw_fields
        };

        // Replace each output var in subsequent lines with source.FieldName
        for (idx, &out_var) in output_args.iter().enumerate() {
            let replacement = format!("{}.{}", source, fields[idx]);

            for line in lines.iter_mut().skip(i + 1) {
                let indent_len = line.len() - line.trim_start().len();
                let content = &line[indent_len..];
                if count_var_refs(content, out_var) > 0 {
                    let new_content = replace_all_var_refs(content, out_var, &replacement);
                    *line = format!("{}{}", &line[..indent_len], new_content);
                }
            }
        }

        to_remove.push(i);
    }

    for idx in to_remove.into_iter().rev() {
        lines.remove(idx);
    }
}

/// Collapse `$MakeStruct_TYPE.Field = Value` runs into `TARGET = TYPE(fields...)`.
fn fold_struct_construction(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

        let Some((struct_var, _, _)) = parse_make_struct_field(trimmed) else {
            i += 1;
            continue;
        };

        let run_start = i;
        let indent_str = lines[i][..lines[i].len() - trimmed.len()].to_string();
        let expected_var = struct_var.to_string();

        // Collect consecutive field assignments
        let mut fields: Vec<(String, String)> = Vec::new();
        while i < lines.len() {
            let t = lines[i].trim();
            if let Some((sv, field, value)) = parse_make_struct_field(t) {
                if sv == expected_var {
                    fields.push((field.to_string(), value.to_string()));
                    i += 1;
                    continue;
                }
            }
            break;
        }

        if fields.is_empty() {
            i += 1;
            continue;
        }

        // Check if next line is TARGET = $MakeStruct_TYPE
        if i < lines.len() {
            let t = lines[i].trim();
            if let Some(eq_pos) = t.find(" = ") {
                let target = &t[..eq_pos];
                let src = &t[eq_pos + 3..];
                if src == expected_var {
                    let type_name = expected_var
                        .strip_prefix("$MakeStruct_")
                        .unwrap_or(&expected_var);

                    let args: Vec<String> = fields
                        .iter()
                        .map(|(field, value)| {
                            if field == value {
                                value.clone()
                            } else {
                                format!("{}: {}", field, value)
                            }
                        })
                        .collect();

                    let new_line = format!(
                        "{}{} = {}({})",
                        indent_str,
                        target,
                        type_name,
                        args.join(", ")
                    );

                    let run_end = i + 1;
                    lines.splice(run_start..run_end, std::iter::once(new_line));
                    i = run_start + 1;
                    continue;
                }
            }
        }
        // No matching assignment — skip past collected fields
    }
}

/// Replace unused `$temp` out-params with `_` in function calls.
/// A var is "unused" if it only ever appears as a simple argument in calls
/// to exactly one function name (i.e., it's never read by any other code).
fn suppress_unused_outparams(lines: &mut [String]) {
    let mut all_vars: Vec<String> = Vec::new();
    for line in lines.iter() {
        for var in extract_dollar_vars(line.trim()) {
            if !all_vars.contains(&var) {
                all_vars.push(var);
            }
        }
    }

    let to_suppress: Vec<String> = all_vars
        .into_iter()
        .filter(|var| is_unused_outparam(lines, var))
        .collect();

    for var in &to_suppress {
        for line in lines.iter_mut() {
            let indent_len = line.len() - line.trim_start().len();
            let content = &line[indent_len..];
            if count_var_refs(content, var) > 0 {
                let new_content = replace_all_var_refs(content, var, "_");
                *line = format!("{}{}", &line[..indent_len], new_content);
            }
        }
    }
}

/// Compact Break struct calls that have many `_` args by keeping only used params.
/// Field names are inferred from the `$BreakName_FieldName` variable naming convention.
/// `BreakHitResult(src, _, _, _, $BreakHitResult_Location, ...)` →
///   `BreakHitResult(src, Location: $BreakHitResult_Location, ...)`
/// Triggers when a Break call has ≥6 output args and ≥50% are `_`.
fn compact_large_break_calls(lines: &mut [String]) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        let indent_len = lines[i].len() - trimmed.len();

        // Match Break* calls above the inline threshold (small ones handled by fold_break_patterns)
        let Some(paren_start) = trimmed.find('(') else {
            i += 1;
            continue;
        };
        let func_name = &trimmed[..paren_start];
        if !func_name.starts_with("Break") || !trimmed.ends_with(')') {
            i += 1;
            continue;
        }

        let args_str = &trimmed[paren_start + 1..trimmed.len() - 1];
        let args = split_args(args_str);

        // Skip small Break calls (handled by fold_break_patterns) and need ≥50% underscores
        if args.len() < 2 {
            i += 1;
            continue;
        }
        let output_count = args.len() - 1;
        if output_count <= BREAK_INLINE_MAX_ARGS {
            i += 1;
            continue;
        }
        let underscore_count = args[1..].iter().filter(|a| **a == "_").count();
        if underscore_count * 2 < args.len() - 1 {
            i += 1;
            continue;
        }

        let source = args[0];
        let indent_str = lines[i][..indent_len].to_string();
        let prefix = format!("${}_", func_name);

        // Build compacted params: source first, then named used params
        let mut parts = vec![source.to_string()];
        for &arg in &args[1..] {
            if arg == "_" {
                continue;
            }
            // Infer field name from $BreakName_FieldName pattern
            if let Some(field) = arg.strip_prefix(&prefix) {
                parts.push(format!("{}: {}", field, arg));
            } else {
                parts.push(arg.to_string());
            }
        }

        let new_call = format!("{}{}({})", indent_str, func_name, parts.join(", "));
        lines[i] = new_call;
        i += 1;
    }
}

/// Rename Make* functions by stripping the `Make` prefix: MakeVector → Vector, etc.
fn rename_make_functions(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let indent_len = line.len() - line.trim_start().len();
        let content = &line[indent_len..];
        let changed = strip_make_prefix(content);
        if changed != content {
            *line = format!("{}{}", &line[..indent_len], changed);
        }
    }
}

/// Find `Make<Name>(` patterns and strip the `Make` prefix.
/// Only matches when preceded by a non-ident char (or start of string),
/// and when the char after `Make` is uppercase (avoids false positives).
fn strip_make_prefix(text: &str) -> String {
    let mut result = String::with_capacity(text.len());
    let mut start = 0;
    while let Some(pos) = text[start..].find("Make") {
        let abs_pos = start + pos;
        // Must not be preceded by ident char or $
        if abs_pos > 0 {
            let prev = text.as_bytes()[abs_pos - 1];
            if is_ident_char(prev) || prev == b'$' {
                result.push_str(&text[start..abs_pos + 4]);
                start = abs_pos + 4;
                continue;
            }
        }
        // Char after "Make" must be uppercase (MakeVector yes, Makefile no)
        let after_make = abs_pos + 4;
        if after_make >= text.len() || !text.as_bytes()[after_make].is_ascii_uppercase() {
            result.push_str(&text[start..abs_pos + 4]);
            start = abs_pos + 4;
            continue;
        }
        // Must be followed by `(` eventually (it's a function call)
        let rest = &text[after_make..];
        let has_paren = rest
            .find('(')
            .is_some_and(|p| rest[..p].chars().all(|c| c.is_alphanumeric() || c == '_'));
        if !has_paren {
            result.push_str(&text[start..abs_pos + 4]);
            start = abs_pos + 4;
            continue;
        }
        // Strip "Make" — keep everything after it
        result.push_str(&text[start..abs_pos]);
        start = after_make;
    }
    result.push_str(&text[start..]);
    result
}

/// Per-section inlining of single-use temp variables in structured output.
/// Runs on `Vec<String>` (indented lines) after structuring, catching temps
/// that survived pre-structure inlining due to cross-section ref counts.
fn fold_section_temps(lines: &mut Vec<String>) {
    const MAX_LINE: usize = 120;
    const MAX_PASSES: usize = 4;

    for _ in 0..MAX_PASSES {
        let mut inlined_any = false;

        // Collect assignments: (index, var_name, expr)
        let assignments: Vec<(usize, String, String)> = lines
            .iter()
            .enumerate()
            .filter_map(|(i, line)| {
                let trimmed = line.trim_start();
                let (var, expr) = parse_temp_assignment(trimmed)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        // Count assignments per var (skip multi-assigned)
        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var, _) in &assignments {
            *assign_counts.entry(var.as_str()).or_default() += 1;
        }

        // Find single-use vars within this section
        let mut to_inline = Vec::new();
        for (idx, var, expr) in &assignments {
            if assign_counts.get(var.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, line) in lines.iter().enumerate() {
                if i == *idx {
                    continue;
                }
                ref_count += count_var_refs(line.trim(), var);
            }
            if ref_count == 1 {
                to_inline.push((*idx, var.clone(), expr.clone()));
            }
        }

        // Apply substitutions with re-verification
        let mut removed = Vec::new();
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }
            let current_expr = match parse_temp_assignment(lines[*assign_idx].trim_start()) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };
            let mut refs = 0usize;
            let mut target = None;
            for (i, line) in lines.iter().enumerate() {
                if i == *assign_idx || removed.contains(&i) {
                    continue;
                }
                let r = count_var_refs(line.trim(), var_name);
                refs += r;
                if r == 1 && target.is_none() {
                    target = Some(i);
                }
            }
            if refs != 1 {
                continue;
            }
            let Some(target_idx) = target else { continue };

            let indent_len = lines[target_idx].len() - lines[target_idx].trim_start().len();
            let content = &lines[target_idx][indent_len..];
            let replacement = substitute_var(content, var_name, &current_expr);

            let shortens = current_expr.len() + 2 <= var_name.len();
            if !shortens && (indent_len + replacement.len()) > MAX_LINE {
                continue;
            }

            lines[target_idx] = format!("{}{}", &lines[target_idx][..indent_len], replacement);
            removed.push(*assign_idx);
            inlined_any = true;
        }

        removed.sort_unstable();
        for idx in removed.into_iter().rev() {
            lines.remove(idx);
        }
        if !inlined_any {
            break;
        }
    }
}

/// Deduplicate ForEach completion paths that repeat pre-loop setup code.
/// Removes lines from the completion block that are exact duplicates of
/// pre-loop lines, keeping only unique (non-duplicated) lines.
fn dedup_completion_paths(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        if lines[i].trim() != "// on loop complete:" {
            i += 1;
            continue;
        }

        let marker_idx = i;
        let marker_indent = lines[i].len() - lines[i].trim_start().len();

        // Collect completion block lines (until next structural boundary)
        let comp_start = marker_idx + 1;
        let mut comp_end = comp_start;
        while comp_end < lines.len() {
            let t = lines[comp_end].trim();
            if t.is_empty() {
                comp_end += 1;
                continue;
            }
            let li = lines[comp_end].len() - lines[comp_end].trim_start().len();
            if li <= marker_indent && (t.starts_with('}') || t.starts_with("---")) {
                break;
            }
            comp_end += 1;
        }
        if comp_end <= comp_start {
            i += 1;
            continue;
        }

        // Find the while/for loop above
        let while_idx = (0..marker_idx).rev().find(|&j| {
            let t = lines[j].trim();
            t.starts_with("while ") || t.starts_with("for ")
        });
        let Some(while_idx) = while_idx else {
            i = comp_end;
            continue;
        };

        // Collect pre-loop lines at same indent level
        let while_indent = lines[while_idx].len() - lines[while_idx].trim_start().len();
        let mut pre_start = while_idx;
        for j in (0..while_idx).rev() {
            let t = lines[j].trim();
            if t.is_empty() {
                continue;
            }
            let li = lines[j].len() - lines[j].trim_start().len();
            if li == while_indent && !t.starts_with('}') && !t.starts_with("//") {
                pre_start = j;
            } else {
                break;
            }
        }

        // Build set of pre-loop lines (trimmed) for duplicate detection
        let pre_set: HashSet<&str> = lines[pre_start..while_idx]
            .iter()
            .map(|l| l.trim())
            .filter(|l| !l.is_empty())
            .collect();

        // Check each completion line: is it a duplicate of a pre-loop line?
        let mut matched_count = 0usize;
        let mut total_count = 0usize;
        let mut unique_indices: Vec<usize> = Vec::new();
        for (j, line) in lines.iter().enumerate().take(comp_end).skip(comp_start) {
            let t = line.trim();
            if t.is_empty() {
                continue;
            }
            total_count += 1;
            if pre_set.contains(t) {
                matched_count += 1;
            } else {
                unique_indices.push(j);
            }
        }

        // Need at least 3 duplicated lines covering majority of completion
        if matched_count >= 3 && matched_count * 2 >= total_count {
            let indent = &lines[marker_idx][..marker_indent];
            let mut replacement: Vec<String> = Vec::new();
            if unique_indices.is_empty() {
                replacement.push(format!(
                    "{}// on loop complete: (same as pre-loop setup)",
                    indent
                ));
            } else {
                replacement.push(format!(
                    "{}// on loop complete: (repeats pre-loop setup)",
                    indent
                ));
                for &j in &unique_indices {
                    replacement.push(lines[j].clone());
                }
            }
            lines.splice(marker_idx..comp_end, replacement);
        }

        i += 1;
    }
}

// ============================================================
// Helpers for summary pattern folding
// ============================================================

/// Detect a shared `_N` disambiguation suffix across all field names.
/// Returns Some("_1") if all fields end with "_1", etc.
fn detect_common_suffix<'a>(fields: &[&'a str]) -> Option<&'a str> {
    if fields.is_empty() {
        return None;
    }
    // Find the last '_' in the first field
    let first = fields[0];
    let last_underscore = first.rfind('_')?;
    let suffix = &first[last_underscore..];
    // Suffix must be _N (underscore + all digits)
    if suffix.len() < 2 || !suffix[1..].chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    // All fields must share this suffix
    if fields
        .iter()
        .all(|f| f.ends_with(suffix) && f.len() > suffix.len())
    {
        Some(suffix)
    } else {
        None
    }
}

/// Split comma-separated arguments respecting nested parentheses.
fn split_args(s: &str) -> Vec<&str> {
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                args.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        args.push(last);
    }
    args
}

/// Parse `$MakeStruct_TYPE.FIELD = VALUE`.
fn parse_make_struct_field(text: &str) -> Option<(&str, &str, &str)> {
    if !text.starts_with("$MakeStruct_") {
        return None;
    }
    let dot_pos = text.find('.')?;
    let struct_var = &text[..dot_pos];
    let rest = &text[dot_pos + 1..];
    let eq_pos = rest.find(" = ")?;
    let field = &rest[..eq_pos];
    let value = &rest[eq_pos + 3..];
    Some((struct_var, field, value))
}

/// Replace all occurrences of `$VarName` in text (word-boundary aware).
fn replace_all_var_refs(text: &str, var: &str, replacement: &str) -> String {
    let mut result = String::with_capacity(text.len());
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        let after = abs_pos + var.len();
        let at_boundary = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
        if at_boundary {
            result.push_str(&text[start..abs_pos]);
            result.push_str(replacement);
        } else {
            result.push_str(&text[start..after]);
        }
        start = after;
    }
    result.push_str(&text[start..]);
    result
}

/// Extract all `$VarName` tokens from text.
fn extract_dollar_vars(text: &str) -> Vec<String> {
    let mut vars = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'$' {
            let start = i;
            i += 1;
            while i < bytes.len() && is_ident_char(bytes[i]) {
                i += 1;
            }
            if i > start + 1 {
                let var = text[start..i].to_string();
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
        } else {
            i += 1;
        }
    }
    vars
}

/// Check if a `$temp` var is an unused output parameter.
/// True when every occurrence is a simple comma-separated argument in calls
/// to exactly one function name, meaning it's never read by other code.
fn is_unused_outparam(lines: &[String], var: &str) -> bool {
    let mut func_names: HashSet<String> = HashSet::new();

    for line in lines {
        let trimmed = line.trim();
        let mut start = 0;
        while let Some(pos) = trimmed[start..].find(var) {
            let abs_pos = start + pos;
            let after = abs_pos + var.len();
            // Check word boundary
            if after < trimmed.len() && is_ident_char(trimmed.as_bytes()[after]) {
                start = after;
                continue;
            }
            // Check simple arg position: preceded by ( or , and followed by , or )
            let before = trimmed[..abs_pos].trim_end();
            let after_text = trimmed[after..].trim_start();
            let ok_before = before.ends_with('(') || before.ends_with(',');
            let ok_after = after_text.starts_with(',') || after_text.starts_with(')');
            if !ok_before || !ok_after {
                return false;
            }
            // Extract containing function name
            if let Some(func_name) = extract_containing_func_name(before) {
                func_names.insert(func_name);
            }
            start = after;
        }
    }

    // Must appear in exactly one function (all occurrences are out-params of same function)
    func_names.len() == 1
}

/// From the text before a function argument, find the name of the containing function.
/// Scans backward for the opening `(` at the right paren depth, then extracts
/// the identifier immediately before it.
fn extract_containing_func_name(before_text: &str) -> Option<String> {
    let trimmed = before_text.trim_end();
    let bytes = trimmed.as_bytes();
    let mut depth = 0i32;
    let mut paren_pos = None;

    for i in (0..bytes.len()).rev() {
        match bytes[i] {
            b')' | b']' => depth += 1,
            b'(' | b'[' => {
                if depth == 0 {
                    paren_pos = Some(i);
                    break;
                }
                depth -= 1;
            }
            _ => {}
        }
    }

    let paren = paren_pos?;
    if paren == 0 {
        return None;
    }
    let before_paren = &trimmed[..paren];
    let name_start = before_paren
        .rfind(|c: char| !c.is_alphanumeric() && c != '_')
        .map(|p| p + 1)
        .unwrap_or(0);
    let name = &trimmed[name_start..paren];
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // split_args
    #[test]
    fn split_args_empty() {
        assert_eq!(split_args(""), Vec::<&str>::new());
    }

    #[test]
    fn split_args_single() {
        assert_eq!(split_args("foo"), vec!["foo"]);
    }

    #[test]
    fn split_args_multiple() {
        assert_eq!(split_args("a, b, c"), vec!["a", "b", "c"]);
    }

    #[test]
    fn split_args_nested_parens() {
        assert_eq!(split_args("foo(a, b), bar"), vec!["foo(a, b)", "bar"]);
    }

    #[test]
    fn split_args_nested_brackets() {
        assert_eq!(split_args("a[0, 1], b"), vec!["a[0, 1]", "b"]);
    }

    #[test]
    fn split_args_whitespace_trimmed() {
        assert_eq!(split_args(" a , b "), vec!["a", "b"]);
    }

    // detect_common_suffix
    #[test]
    fn detect_suffix_shared() {
        let fields = vec!["Location_1", "Rotation_1", "Scale_1"];
        assert_eq!(detect_common_suffix(&fields), Some("_1"));
    }

    #[test]
    fn detect_suffix_mixed() {
        let fields = vec!["Location_1", "Rotation_2"];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    #[test]
    fn detect_suffix_none() {
        let fields = vec!["Location", "Rotation"];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    #[test]
    fn detect_suffix_empty() {
        let fields: Vec<&str> = vec![];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    // strip_make_prefix
    #[test]
    fn strip_make_vector() {
        assert_eq!(strip_make_prefix("MakeVector(1, 2, 3)"), "Vector(1, 2, 3)");
    }

    #[test]
    fn strip_make_no_uppercase() {
        // "Makefile" — no uppercase after "Make"
        assert_eq!(strip_make_prefix("Makefile"), "Makefile");
    }

    #[test]
    fn strip_make_preceded_by_dollar() {
        assert_eq!(strip_make_prefix("$MakeStruct_Foo"), "$MakeStruct_Foo");
    }

    #[test]
    fn strip_make_preceded_by_ident() {
        assert_eq!(strip_make_prefix("SomeMakeVector(x)"), "SomeMakeVector(x)");
    }

    #[test]
    fn strip_make_mid_line() {
        assert_eq!(
            strip_make_prefix("x = MakeRotator(1, 2, 3)"),
            "x = Rotator(1, 2, 3)"
        );
    }

    #[test]
    fn strip_make_no_paren() {
        assert_eq!(strip_make_prefix("MakeVector"), "MakeVector");
    }

    // clean_line
    #[test]
    fn clean_line_bool_strip() {
        assert_eq!(clean_line("bool(X)"), "X");
    }

    #[test]
    fn clean_line_bool_compound() {
        assert_eq!(clean_line("bool(A && B)"), "A && B");
    }

    #[test]
    fn clean_line_double_negation() {
        assert_eq!(clean_line("!(!X)"), "X");
    }

    #[test]
    fn clean_line_negation_compound_inner_safe() {
        // !(!A && B) — inner ! only negates A, should NOT simplify
        assert_eq!(clean_line("!(!A && B)"), "!(!A && B)");
    }

    #[test]
    fn clean_line_outer_parens_if() {
        assert_eq!(clean_line("if ((X)) {"), "if (X) {");
    }

    #[test]
    fn clean_line_no_change() {
        assert_eq!(clean_line("self.Foo.Bar()"), "self.Foo.Bar()");
    }

    // has_toplevel_logical_op
    #[test]
    fn toplevel_op_simple_and() {
        assert!(has_toplevel_logical_op("A && B"));
    }

    #[test]
    fn toplevel_op_inside_parens() {
        assert!(!has_toplevel_logical_op("(A && B)"));
    }

    #[test]
    fn toplevel_op_none() {
        assert!(!has_toplevel_logical_op("A"));
    }

    #[test]
    fn toplevel_op_mixed() {
        assert!(has_toplevel_logical_op("A || (B && C)"));
    }

    // parse_temp_assignment
    #[test]
    fn parse_temp_dollar_var() {
        assert_eq!(parse_temp_assignment("$Foo = bar"), Some(("$Foo", "bar")));
    }

    #[test]
    fn parse_temp_with_dot() {
        assert_eq!(parse_temp_assignment("$Foo.bar = x"), None);
    }

    #[test]
    fn parse_temp_non_temp() {
        assert_eq!(parse_temp_assignment("x = y"), None);
    }

    #[test]
    fn parse_temp_persistent() {
        assert_eq!(parse_temp_assignment("$X = foo [persistent]"), None);
    }

    #[test]
    fn parse_temp_underscore_var() {
        assert_eq!(parse_temp_assignment("Temp_0 = x"), Some(("Temp_0", "x")));
    }

    // count_var_refs
    #[test]
    fn count_refs_zero() {
        assert_eq!(count_var_refs("hello world", "$Foo"), 0);
    }

    #[test]
    fn count_refs_one() {
        assert_eq!(count_var_refs("$Foo + 1", "$Foo"), 1);
    }

    #[test]
    fn count_refs_multiple() {
        assert_eq!(count_var_refs("$Foo + $Foo", "$Foo"), 2);
    }

    #[test]
    fn count_refs_partial_no_match() {
        // $Foo in $FooBar should not match
        assert_eq!(count_var_refs("$FooBar + 1", "$Foo"), 0);
    }

    // substitute_var
    #[test]
    fn substitute_simple() {
        assert_eq!(substitute_var("$X + 1", "$X", "42"), "42 + 1");
    }

    #[test]
    fn substitute_compound_gets_parens() {
        assert_eq!(substitute_var("$X + 1", "$X", "A + B"), "(A + B) + 1");
    }

    #[test]
    fn substitute_no_match() {
        assert_eq!(substitute_var("$Y + 1", "$X", "42"), "$Y + 1");
    }

    // expr_is_compound
    #[test]
    fn compound_addition() {
        assert!(expr_is_compound("A + B"));
    }

    #[test]
    fn compound_negation() {
        assert!(expr_is_compound("!X"));
    }

    #[test]
    fn compound_function_call() {
        assert!(!expr_is_compound("foo()"));
    }

    #[test]
    fn compound_simple_var() {
        assert!(!expr_is_compound("$X"));
    }

    // find_matching_paren
    #[test]
    fn paren_balanced() {
        assert_eq!(find_matching_paren("(abc)"), Some(4));
    }

    #[test]
    fn paren_nested() {
        assert_eq!(find_matching_paren("(a(b)c)"), Some(6));
    }

    #[test]
    fn paren_no_open() {
        assert_eq!(find_matching_paren("abc"), None);
    }

    #[test]
    fn paren_unbalanced() {
        assert_eq!(find_matching_paren("(abc"), None);
    }

    // strip_outer_parens
    #[test]
    fn outer_parens_simple() {
        assert_eq!(strip_outer_parens("(X)"), "X");
    }

    #[test]
    fn outer_parens_double() {
        assert_eq!(strip_outer_parens("((X))"), "(X)");
    }

    #[test]
    fn outer_parens_not_matching() {
        // (A)(B) — the outer ( doesn't match the outer )
        assert_eq!(strip_outer_parens("(A)(B)"), "(A)(B)");
    }

    #[test]
    fn outer_parens_not_wrapped() {
        assert_eq!(strip_outer_parens("A + B"), "A + B");
    }

    // preceding boundary checks
    #[test]
    fn count_refs_temp_no_prefix_match() {
        assert_eq!(count_var_refs("SomeTemp_0 + 1", "Temp_0"), 0);
    }

    #[test]
    fn count_refs_temp_standalone() {
        assert_eq!(count_var_refs("Temp_0 + 1", "Temp_0"), 1);
    }

    #[test]
    fn substitute_temp_no_prefix_match() {
        assert_eq!(
            substitute_var("SomeTemp_0 + 1", "Temp_0", "42"),
            "SomeTemp_0 + 1"
        );
    }

    #[test]
    fn count_refs_dollar_prefix_safe() {
        assert_eq!(count_var_refs("pre$Foo + 1", "$Foo"), 1);
    }
}
