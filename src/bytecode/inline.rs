use super::decode::BcStatement;
use std::collections::{BTreeMap, HashMap, HashSet};

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

            // Bypass MAX_LINE for trivial expressions (property chains, $temp refs, literals)
            let shortens = current_expr.len() + 2 <= var_name.len(); // +2 for possible (...)
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > MAX_LINE {
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
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        if is_var_boundary(text, abs_pos, var) {
            count += 1;
        }
        start = abs_pos + var.len();
    }
    count
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Check if `var` appears at a word boundary at position `pos` in `text`.
/// For `$`-prefixed vars, the start boundary is always satisfied ($ isn't an ident char).
fn is_var_boundary(text: &str, pos: usize, var: &str) -> bool {
    let after = pos + var.len();
    let at_start = var.starts_with('$') || pos == 0 || !is_ident_char(text.as_bytes()[pos - 1]);
    let at_end = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
    at_start && at_end
}

/// Substitute `$VarName` or `Temp_*` with `expr` in `text`, adding parens if needed.
/// Only replaces at word boundaries (first match).
fn substitute_var(text: &str, var: &str, expr: &str) -> String {
    let mut start = 0;
    while let Some(rel) = text[start..].find(var) {
        let pos = start + rel;
        let after = pos + var.len();
        if is_var_boundary(text, pos, var) {
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

/// Substitute ALL occurrences of `var` in `text`, repeating until stable.
fn substitute_var_all(text: &str, var: &str, expr: &str) -> String {
    let mut result = text.to_string();
    loop {
        let next = substitute_var(&result, var, expr);
        if next == result {
            return result;
        }
        result = next;
    }
}

/// Check if an expression contains a function/method call (i.e., has side effects).
/// Returns true if there's an identifier followed by `(` where the identifier is not
/// a keyword like `switch` or `if`.  Pure expressions like `switch(X) { ... }` or
/// `(A + B)` return false.
fn expr_has_call(expr: &str) -> bool {
    let bytes = expr.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'(' && i > 0 {
            // Walk backward to find the identifier before the paren
            let mut j = i;
            while j > 0 && (bytes[j - 1].is_ascii_alphanumeric() || bytes[j - 1] == b'_') {
                j -= 1;
            }
            let word = &expr[j..i];
            if !word.is_empty() && word != "switch" && word != "if" && word != "bool" {
                return true;
            }
        }
    }
    false
}

fn expr_is_compound(expr: &str) -> bool {
    const TOKENS: &[&str] = &[
        " && ", " || ", " + ", " - ", " * ", " / ", " % ", " < ", " <= ", " > ", " >= ", " == ",
        " != ", " >> ", " << ", " ? ",
    ];
    TOKENS.iter().any(|tok| expr.contains(tok)) || expr.starts_with('!')
}

/// Check if an expression is trivial enough to inline regardless of line length.
/// Trivial = property chains, `$temp` refs, or literals (no calls, operators, or brackets).
fn is_trivial_expr(expr: &str) -> bool {
    !expr.is_empty() && !expr.contains(['(', ')', '[', ']']) && !expr_is_compound(expr)
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

/// Inline `Temp_*` / `$temp` variables that are always assigned the same value.
/// UE4 Select nodes re-assign the index input before every use; this pass
/// collapses `Temp_bool_Variable = LeftHand` + `switch(Temp_bool_Variable)`
/// into `switch(LeftHand)`.
pub fn inline_constant_temps(stmts: &mut Vec<BcStatement>) {
    // Collect all assignments for each temp variable: (stmt_index, expr)
    let mut assignments: HashMap<String, Vec<(usize, String)>> = HashMap::new();
    for (i, s) in stmts.iter().enumerate() {
        if let Some((var, expr)) = parse_temp_assignment(&s.text) {
            assignments
                .entry(var.to_string())
                .or_default()
                .push((i, expr.to_string()));
        }
    }

    // Keep only variables where ALL assignments have the same expression.
    // - Multi-assignment (any prefix): UE4 Select pattern re-assigns before each use
    // - Single-assignment (Temp_* only): safe to inline since Temp_ vars are read-only
    //   Select indices, never out-parameters.  $-prefixed temps may be out-params
    //   modified by function calls, so single assignments are left to inline_single_use_temps.
    let mut constant_vars: BTreeMap<String, String> = assignments
        .into_iter()
        .filter(|(var, entries)| {
            let all_same = entries.iter().all(|(_, e)| *e == entries[0].1);
            let multi = entries.len() > 1;
            all_same && (multi || var.starts_with("Temp_"))
        })
        .map(|(var, entries)| (var, entries[0].1.clone()))
        .collect();

    if constant_vars.is_empty() {
        return;
    }

    // Resolve expressions transitively: a constant var's expression may
    // reference another constant var.  Iterate until stable so that
    // substitution order in the per-statement pass doesn't matter.
    let keys: Vec<String> = constant_vars.keys().cloned().collect();
    for _ in 0..6 {
        let mut changed = false;
        for key in &keys {
            let expr = constant_vars[key].clone();
            let mut resolved = expr.clone();
            for (other_var, other_expr) in constant_vars.iter() {
                if other_var == key {
                    continue;
                }
                if count_var_refs(&resolved, other_var) > 0 {
                    resolved = substitute_var_all(&resolved, other_var, other_expr);
                }
            }
            if resolved != expr {
                constant_vars.insert(key.clone(), resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Collect assignment indices to remove
    let remove_indices: HashSet<usize> = stmts
        .iter()
        .enumerate()
        .filter_map(|(i, s)| {
            let (var, _) = parse_temp_assignment(&s.text)?;
            constant_vars.contains_key(var).then_some(i)
        })
        .collect();

    // Substitute the constant expression into all references
    for s in stmts.iter_mut() {
        for (var, expr) in &constant_vars {
            if count_var_refs(&s.text, var) > 0 {
                s.text = substitute_var_all(&s.text, var, expr);
            }
        }
    }

    // Remove the dead assignment statements
    let mut idx = 0;
    stmts.retain(|_| {
        let keep = !remove_indices.contains(&idx);
        idx += 1;
        keep
    });
}

/// Discard assignments to `$temp` variables that are never referenced.
/// Keeps the RHS expression only if it has side effects (contains a function call).
/// Pure expressions (no function call) are removed entirely.
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
                if expr_has_call(expr) {
                    // Keep: expression has side effects (function/method call)
                    s.text = expr.to_string();
                } else {
                    // Remove: pure expression with no side effects
                    s.text.clear();
                }
            }
        }
    }

    // Remove cleared statements
    stmts.retain(|s| !s.text.is_empty());
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
    // Remove "return" immediately before "// sequence [N]:" markers.
    // These are sentinel leaks from Sequence body boundaries (return nop).
    let mut i = 0;
    while i + 1 < lines.len() {
        if lines[i].trim() == "return" && lines[i + 1].trim().starts_with("// sequence [") {
            lines.remove(i);
            continue;
        }
        i += 1;
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

    // Pass 5: strip trailing unmatched closing braces.
    // The structurer's safety net (`while indent > 0`) emits a `}` for every
    // remaining open block.  When flow patterns (Sequences, loops) consume
    // statements that opened blocks but not those that close them, the output
    // ends with orphaned `}`.  Count block-level braces and strip the excess.
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

    // Double negation elimination: !(!X) → X
    // Only safe when the inner ! covers the entire expression:
    //   !(!A)         → A           (single identifier — safe)
    //   !(!(A && B))  → (A && B)    (inner ! wraps full parens — safe)
    //   !(!A && B)    → UNSAFE      (inner ! only negates A, not the compound)
    // We use has_toplevel_logical_op() to verify no bare && or || at paren depth 0.
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

    // Boolean switch → ternary: switch(COND) { false: F, true: T } → COND ? T : F
    s = rewrite_bool_switches(&s);

    s
}

/// Rewrite `switch(COND) { false: F, true: T }` → `COND ? T : F` in a single line.
/// Handles both orderings (false-first and true-first), nested switches, and
/// method chains after the closing `}`.
fn rewrite_bool_switches(line: &str) -> String {
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

/// Find and rewrite the first `switch(COND) { false: F, true: T }` in the string.
/// Returns None if no bool switch was found.
fn rewrite_one_bool_switch(s: &str) -> Option<String> {
    let switch_pos = s.find("switch(")?;

    // Extract COND by matching parens from the `(` after `switch`
    let paren_start = switch_pos + 6; // index of '('
    let cond_close = find_matching_paren(&s[paren_start..])?;
    let cond = &s[paren_start + 1..paren_start + cond_close];

    // Expect ` { ` after the closing paren
    let after_cond = &s[paren_start + cond_close + 1..];
    let after_cond = after_cond.strip_prefix(" { ")?;
    let brace_content_start = paren_start + cond_close + 1 + 3; // absolute pos of content after " { "

    // Parse the two cases. Track paren/brace depth to find `, ` and ` }` boundaries.
    let (expr_true, expr_false) = parse_bool_switch_cases(after_cond)?;

    // Find where the switch expression ends: scan for matching ` }` in original string
    let switch_end = find_switch_end(s, brace_content_start)?;

    // Identical branches: emit the expression directly (drop condition)
    if expr_true == expr_false {
        return Some(format!(
            "{}{}{}",
            &s[..switch_pos],
            expr_true,
            &s[switch_end..]
        ));
    }

    // Build ternary. Wrap condition in parens if compound.
    let cond_str = if expr_is_compound(cond) {
        format!("({})", cond)
    } else {
        cond.to_string()
    };

    let after_switch = &s[switch_end..];
    let before_switch = s[..switch_pos].trim_end();

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
        &s[..switch_pos],
        replacement,
        after_switch
    ))
}

/// Parse the case expressions inside `{ false: F, true: T }` or `{ true: T, false: F }`.
/// Returns (true_expr, false_expr). Returns None for non-bool switches (3+ cases, default:).
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

/// Find the position of `needle` in `s` at paren/brace depth 0.
fn find_at_depth_zero(s: &str, needle: &str) -> Option<usize> {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let needle_bytes = needle.as_bytes();
    let nlen = needle_bytes.len();
    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && i + nlen <= bytes.len() && &bytes[i..i + nlen] == needle_bytes {
            return Some(i);
        }
    }
    None
}

/// Find the absolute position just past the closing ` }` of a switch expression.
/// `content_start` is the absolute position in `s` where the brace content begins.
fn find_switch_end(s: &str, content_start: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, &b) in s.as_bytes().iter().enumerate().skip(content_start) {
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

/// Check if a string contains ` && ` or ` || ` at paren/bracket depth 0.
fn has_toplevel_logical_op(s: &str) -> bool {
    find_at_depth_zero(s, " && ").is_some() || find_at_depth_zero(s, " || ").is_some()
}

/// Strip one layer of redundant outer parentheses if they match.
fn strip_outer_parens(s: &str) -> &str {
    if let Some(close) = find_matching_paren(s) {
        if close == s.len() - 1 {
            return &s[1..close];
        }
    }
    s
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
    // Pipeline ordering: each pass may create patterns consumed by later passes.
    // 1. Structural rewrites (change control flow shape)
    rewrite_foreach_loops(lines); // foreach before temp inlining (creates new temps)
    fold_delegate_bindings(lines); // bind() + AddDelegate -> +=
    fold_cast_guards(lines); // cast-then-branch -> if let
    fold_cast_inline(lines); // inline single-use cast results
                             // 2. Expression folding (collapse multi-statement patterns into expressions)
    fold_break_patterns(lines); // Break/Make struct folding
    fold_struct_construction(lines); // constructor patterns
    dedup_completion_paths(lines); // remove duplicate completion branches
                                   // 3. Temp variable inlining (must run after folding creates final expressions)
    fold_section_temps(lines); // inline temps + constant folding
                               // 4. Cosmetic cleanup (simplify what remains)
    simplify_bool_comparisons(lines);
    hoist_repeated_ternaries(lines);
    suppress_unused_outparams(lines);
    fold_outparam_calls(lines);
    compact_large_break_calls(lines);
    fold_switch_enum_cascade(lines);
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
            // Scan body for ITEM = ARRAY[INDEX_VAR] re-fetches and remove
            let redundant_get = format!("{} = {}[{}]", item, array, index_var);
            let mut j = for_idx + 1;
            while j < new_close {
                let t = lines[j].trim();
                if t == redundant_get {
                    lines.remove(j);
                    new_close -= 1;
                    continue; // don't advance j
                }
                j += 1;
            }
        }

        // Don't advance — recheck in case of nested loops
        i = 0;
    }
}

/// Parse "while (COUNTER < ARRAY.Length()) {" → Some((counter, array))
fn parse_foreach_while(trimmed: &str) -> Option<(String, String)> {
    let rest = trimmed.strip_prefix("while (")?;
    let rest = rest.strip_suffix(") {")?;
    // Pattern: COUNTER < ARRAY.Length()
    let lt_pos = rest.find(" < ")?;
    let counter = &rest[..lt_pos];
    let rhs = &rest[lt_pos + 3..];
    let array = rhs.strip_suffix(".Length()")?;
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

    // Line 2: ITEM = ARRAY[INDEX]
    let t = &body_lines[1].1;
    let eq_pos = t.find(" = ")?;
    let item_part = &t[..eq_pos];
    let rhs = &t[eq_pos + 3..];
    let bracket_start = rhs.find('[')?;
    let arr_part = &rhs[..bracket_start];
    let idx_part = rhs[bracket_start + 1..].strip_suffix(']')?;
    if arr_part != array || idx_part != index {
        return None;
    }
    let item = item_part.to_string();
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

/// Inline cast-and-use patterns: `$X = cast<T>(expr)` + `if ($X) { ... $X ... }`
/// where `$X` is used only in the if-guard and a few body references.
/// Substitutes the cast expression everywhere and removes the assignment line.
fn fold_cast_inline(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim().to_string();
        let indent_len = lines[i].len() - trimmed.len();

        // Line i: $VAR = cast<T>(expr)
        let Some((var, rhs)) = parse_cast_assignment(&trimmed) else {
            i += 1;
            continue;
        };
        // Skip if already folded to "else return"
        if trimmed.ends_with("else return") {
            i += 1;
            continue;
        }
        let var = var.to_string();
        let rhs = rhs.to_string();

        // Next line must be `if ($VAR) {` at same indent
        if i + 1 >= lines.len() {
            i += 1;
            continue;
        }
        let next_trimmed = lines[i + 1].trim();
        let next_indent = lines[i + 1].len() - next_trimmed.len();
        let expected_if = format!("if ({}) {{", var);
        if next_indent != indent_len || next_trimmed != expected_if {
            i += 1;
            continue;
        }

        // Count total refs to $VAR in all lines except the assignment
        let mut total_refs = 0usize;
        for (j, line) in lines.iter().enumerate() {
            if j == i {
                continue;
            }
            total_refs += count_var_refs(line.trim(), &var);
        }

        // if-guard = 1 ref, body uses ≤ 2 refs → total ≤ 3
        if total_refs > 3 {
            i += 1;
            continue;
        }

        // Substitute cast expression for $VAR everywhere
        for (j, line) in lines.iter_mut().enumerate() {
            if j == i {
                continue;
            }
            let li = line.len() - line.trim_start().len();
            let content = &line[li..];
            if count_var_refs(content, &var) > 0 {
                let mut text = content.to_string();
                loop {
                    let new_text = replace_all_var_refs(&text, &var, &rhs);
                    if new_text == text {
                        break;
                    }
                    text = new_text;
                }
                *line = format!("{}{}", &line[..li], text);
            }
        }

        // Remove the assignment line
        lines.remove(i);
        // Don't advance — recheck current position
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

        // Collect consecutive field assignments, tolerating interleaved
        // $MakeStruct_* intermediate temps (UE5 pattern: temp assigned first,
        // then stored into struct field on the next line).
        let mut fields: Vec<(String, String)> = Vec::new();
        let mut intermediate_temps: Vec<(String, String)> = Vec::new();
        while i < lines.len() {
            let t = lines[i].trim();
            if let Some((sv, field, value)) = parse_make_struct_field(t) {
                if sv == expected_var {
                    fields.push((field.to_string(), value.to_string()));
                    i += 1;
                    continue;
                }
            }
            // Also consume $MakeStruct_* temp assignments (no dot) that feed
            // into subsequent field assignments
            if let Some((var, expr)) = parse_temp_assignment(t) {
                if var.starts_with("$MakeStruct_") {
                    intermediate_temps.push((var.to_string(), expr.to_string()));
                    i += 1;
                    continue;
                }
            }
            break;
        }

        // Resolve intermediate temps in field values
        for (_, value) in &mut fields {
            for (temp_var, temp_expr) in &intermediate_temps {
                if count_var_refs(value, temp_var) > 0 {
                    *value = replace_all_var_refs(value, temp_var, temp_expr);
                }
            }
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
/// Hoist repeated parenthesized ternary expressions into named local variables.
/// When the same `(COND ? T : F)` appears 3+ times in a section, insert
/// `$VarName = COND ? T : F` before the first use and replace all occurrences.
fn hoist_repeated_ternaries(lines: &mut Vec<String>) {
    // Phase 1: Extract and count all parenthesized ternary expressions
    let mut ternary_counts: BTreeMap<String, usize> = BTreeMap::new();
    for line in lines.iter() {
        for ternary in extract_parenthesized_ternaries(line.trim()) {
            *ternary_counts.entry(ternary).or_default() += 1;
        }
    }

    // Phase 2: Collect ternaries appearing 3+ times, longest first
    let mut to_hoist: Vec<(String, String)> = Vec::new();
    for (ternary, count) in &ternary_counts {
        if *count >= 3 {
            let var_name = generate_ternary_var_name(ternary, to_hoist.len());
            to_hoist.push((ternary.clone(), var_name));
        }
    }
    to_hoist.sort_by(|a, b| b.0.len().cmp(&a.0.len()));

    // Phase 3: For each hoisted ternary, insert assignment and replace
    for (ternary, var_name) in &to_hoist {
        let first_use = lines.iter().position(|l| l.contains(ternary.as_str()));
        let Some(idx) = first_use else { continue };
        let indent = lines[idx].len() - lines[idx].trim_start().len();
        let indent_str = " ".repeat(indent);
        // Strip outer parens for the assignment RHS
        let rhs = strip_outer_parens(ternary);
        lines.insert(idx, format!("{}{} = {}", indent_str, var_name, rhs));
        // Replace all occurrences in all lines
        for line in lines.iter_mut() {
            while line.contains(ternary.as_str()) {
                *line = line.replacen(ternary.as_str(), var_name, 1);
            }
        }
    }
}

/// Extract all parenthesized ternary expressions `(COND ? T : F)` from a line.
fn extract_parenthesized_ternaries(s: &str) -> Vec<String> {
    let mut results = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'(' {
            if let Some(close) = find_matching_paren(&s[i..]) {
                let inner = &s[i + 1..i + close];
                // Check for ` ? ` and ` : ` at paren depth 0 inside
                if has_ternary_at_depth_zero(inner) {
                    results.push(s[i..i + close + 1].to_string());
                }
                // Don't skip past close — there may be nested ternaries inside
                i += 1;
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    results
}

/// Check if a string contains ` ? ` and ` : ` at paren/brace depth 0.
fn has_ternary_at_depth_zero(s: &str) -> bool {
    let mut depth = 0i32;
    let mut has_question = false;
    let bytes = s.as_bytes();
    let len = bytes.len();
    for i in 0..len {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'?' if depth == 0 => {
                if i > 0 && i + 1 < len && bytes[i - 1] == b' ' && bytes[i + 1] == b' ' {
                    has_question = true;
                }
            }
            b':' if depth == 0 && has_question => {
                if i > 0 && i + 1 < len && bytes[i - 1] == b' ' && bytes[i + 1] == b' ' {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Generate a descriptive variable name for a hoisted ternary.
/// Tries to extract a common suffix from Left/Right branch patterns;
/// falls back to `$ternary_N`.
fn generate_ternary_var_name(ternary: &str, index: usize) -> String {
    let inner = strip_outer_parens(ternary);
    // Find ` ? ` and ` : ` at depth 0
    let mut depth = 0i32;
    let mut q_pos = None;
    let mut c_pos = None;
    let bytes = inner.as_bytes();
    let len = bytes.len();
    for i in 0..len {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'?' if depth == 0 && q_pos.is_none() => {
                if i > 0 && i + 1 < len && bytes[i - 1] == b' ' && bytes[i + 1] == b' ' {
                    q_pos = Some(i);
                }
            }
            b':' if depth == 0 && q_pos.is_some() && c_pos.is_none() => {
                if i > 0 && i + 1 < len && bytes[i - 1] == b' ' && bytes[i + 1] == b' ' {
                    c_pos = Some(i);
                }
            }
            _ => {}
        }
    }
    if let (Some(q), Some(c)) = (q_pos, c_pos) {
        let true_expr = inner[q + 2..c - 1].trim();
        let false_expr = inner[c + 2..].trim();
        // Try Left/Right suffix extraction
        if let Some(name) = extract_left_right_suffix(true_expr, false_expr) {
            return format!("${}", name);
        }
        // Use last dot-component of the true branch
        if let Some(dot) = true_expr.rfind('.') {
            let suffix = &true_expr[dot + 1..];
            if !suffix.is_empty()
                && suffix
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return format!("${}", suffix);
            }
        }
    }
    format!("$ternary_{}", index)
}

/// Given two branch expressions like `self.LeftVRHand` and `self.RightVRHand`,
/// extract the common suffix after stripping `Left`/`Right` prefixes.
fn extract_left_right_suffix(true_expr: &str, false_expr: &str) -> Option<String> {
    // Strip `self.` prefix if present on both
    let t = true_expr.strip_prefix("self.").unwrap_or(true_expr);
    let f = false_expr.strip_prefix("self.").unwrap_or(false_expr);
    // Try stripping Left/Right from true and Right/Left from false
    let suffix = if let Some(ts) = t.strip_prefix("Left") {
        if let Some(fs) = f.strip_prefix("Right") {
            if ts == fs {
                Some(ts)
            } else {
                None
            }
        } else {
            None
        }
    } else if let Some(ts) = t.strip_prefix("Right") {
        if let Some(fs) = f.strip_prefix("Left") {
            if ts == fs {
                Some(ts)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };
    suffix.map(|s| s.to_string())
}

/// Simplify redundant boolean comparisons: `!Func() == 1` → `!Func()`, etc.
/// Fixes precedence ambiguity where `!Func() == 1` reads as `!(Func() == 1)`.
fn simplify_bool_comparisons(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let indent_len = line.len() - line.trim_start().len();
        let content = &line[indent_len..];
        let simplified = simplify_negated_bool_comparison(content);
        if simplified != content {
            *line = format!("{}{}", &line[..indent_len], simplified);
        }
    }
}

/// Rewrite `!CALL(...) == 1` → `!CALL(...)`, `!CALL(...) == 0` → `CALL(...)`, etc.
/// Only matches function-call patterns (identifier followed by parens) to avoid
/// false positives on member access like `!self.Flag == 1`.
fn simplify_negated_bool_comparison(s: &str) -> String {
    let mut result = s.to_string();
    // Process all occurrences in the string
    let mut search_from = 0;
    loop {
        let remaining = &result[search_from..];
        // Find `!` that precedes an identifier (not `!(` or `! `)
        let Some(bang_rel) = remaining.find('!') else {
            break;
        };
        let bang_pos = search_from + bang_rel;

        // Must be followed by an identifier char (start of function name), not `(` or space
        let after_bang = &result[bang_pos + 1..];
        if after_bang.is_empty()
            || after_bang.starts_with('(')
            || after_bang.starts_with(' ')
            || after_bang.starts_with('=')
        {
            search_from = bang_pos + 1;
            continue;
        }

        // The char before `!` should be a non-identifier boundary (space, `(`, start, `=`)
        if bang_pos > 0 {
            let prev = result.as_bytes()[bang_pos - 1];
            if prev.is_ascii_alphanumeric() || prev == b'_' || prev == b'.' || prev == b'$' {
                search_from = bang_pos + 1;
                continue;
            }
        }

        // Find the opening paren of the call
        let call_start = bang_pos + 1;
        let Some(paren_offset) = result[call_start..].find('(') else {
            search_from = bang_pos + 1;
            continue;
        };
        let paren_abs = call_start + paren_offset;

        // Between `!` and `(` must be a simple identifier (no spaces, dots — avoids !self.X)
        let ident = &result[call_start..paren_abs];
        if ident.is_empty() || !ident.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            search_from = bang_pos + 1;
            continue;
        }

        // Match the closing paren
        let Some(close_rel) = find_matching_paren(&result[paren_abs..]) else {
            search_from = bang_pos + 1;
            continue;
        };
        let call_end = paren_abs + close_rel + 1; // position after closing `)`

        // Check what follows: ` == 0`, ` == 1`, ` != 0`, ` != 1`
        let after_call = &result[call_end..];
        let (op, val, suffix_len) = if let Some(rest) = after_call.strip_prefix(" == 1") {
            ("==", 1, 5 + (after_call.len() - rest.len() - 5))
        } else if let Some(rest) = after_call.strip_prefix(" == 0") {
            ("==", 0, 5 + (after_call.len() - rest.len() - 5))
        } else if let Some(rest) = after_call.strip_prefix(" != 0") {
            ("!=", 0, 5 + (after_call.len() - rest.len() - 5))
        } else if let Some(rest) = after_call.strip_prefix(" != 1") {
            ("!=", 1, 5 + (after_call.len() - rest.len() - 5))
        } else {
            search_from = bang_pos + 1;
            continue;
        };

        // Ensure what follows the ` == N` is a boundary (not more digits/identifiers)
        let after_cmp = &result[call_end + suffix_len..];
        if !after_cmp.is_empty() {
            let next = after_cmp.as_bytes()[0];
            if next.is_ascii_alphanumeric() || next == b'_' {
                search_from = bang_pos + 1;
                continue;
            }
        }

        // Apply rewrite rules:
        // !CALL == 1  →  !CALL     (negated == true → negated)
        // !CALL == 0  →  CALL      (negated == false → not negated)
        // !CALL != 0  →  !CALL     (negated != false → negated)
        // !CALL != 1  →  CALL      (negated != true → not negated)
        let keep_negation = (op == "==" && val == 1) || (op == "!=" && val == 0);
        let call_expr = &result[call_start..call_end];
        let replacement = if keep_negation {
            format!("!{}", call_expr)
        } else {
            call_expr.to_string()
        };

        result = format!(
            "{}{}{}",
            &result[..bang_pos],
            replacement,
            &result[call_end + suffix_len..]
        );
        search_from = bang_pos + replacement.len();
    }
    result
}

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

/// Fold single-out-param function calls into their usage site.
/// `obj.Func($outParam)` where `$outParam` is referenced exactly once later
/// → substitute `obj.Func()` for `$outParam` and remove the standalone call.
fn fold_outparam_calls(lines: &mut Vec<String>) {
    const MAX_LINE: usize = 120;
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim().to_string();

        // Must be a bare function call: contains `(`, no ` = `, no `if `, no `} `
        if !trimmed.contains('(')
            || trimmed.contains(" = ")
            || trimmed.starts_with("if ")
            || trimmed.starts_with("} ")
            || trimmed.starts_with("for ")
            || trimmed.starts_with("while ")
        {
            i += 1;
            continue;
        }

        // Extract args from the outermost call
        let Some(paren_start) = trimmed.find('(') else {
            i += 1;
            continue;
        };
        if !trimmed.ends_with(')') {
            i += 1;
            continue;
        }
        let args_str = &trimmed[paren_start + 1..trimmed.len() - 1];
        let args = split_args(args_str);

        // Find $-prefixed args that could be out-params
        let dollar_args: Vec<(usize, &str)> = args
            .iter()
            .enumerate()
            .filter(|(_, a)| a.starts_with('$'))
            .map(|(idx, a)| (idx, *a))
            .collect();

        // Must have exactly 1 foldable $-prefixed out-param
        if dollar_args.len() != 1 {
            i += 1;
            continue;
        }
        let (arg_idx, out_var) = dollar_args[0];

        // In UE4, out-params always follow input params. A $-var that isn't the
        // last argument in a multi-arg call is an input, not an out-param.
        if args.len() > 1 && arg_idx != args.len() - 1 {
            i += 1;
            continue;
        }
        let out_var = out_var.to_string();

        // The out-param must NOT have a separate assignment line (it's populated by the call)
        let has_assignment = lines.iter().any(|l| {
            let t = l.trim();
            parse_temp_assignment(t).is_some_and(|(v, _)| v == out_var)
        });
        if has_assignment {
            i += 1;
            continue;
        }

        // Count refs in other lines — must be exactly 1
        let mut ref_count = 0usize;
        let mut ref_line = None;
        for (j, line) in lines.iter().enumerate() {
            if j == i {
                continue;
            }
            let refs = count_var_refs(line.trim(), &out_var);
            ref_count += refs;
            if refs > 0 && ref_line.is_none() {
                ref_line = Some(j);
            }
        }
        if ref_count != 1 {
            i += 1;
            continue;
        }
        let ref_line = ref_line.unwrap();

        // Build the call expression with the out-param removed
        let mut new_args: Vec<&str> = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            if idx != arg_idx {
                new_args.push(arg);
            }
        }
        let call_prefix = &trimmed[..paren_start];
        let call_expr = format!("{}({})", call_prefix, new_args.join(", "));

        // Substitute $outParam with the call expression in the reference line
        let ref_indent = lines[ref_line].len() - lines[ref_line].trim_start().len();
        let ref_content = &lines[ref_line][ref_indent..];
        let replacement = replace_all_var_refs(ref_content, &out_var, &call_expr);

        // Check line length
        if ref_indent + replacement.len() > MAX_LINE {
            i += 1;
            continue;
        }

        lines[ref_line] = format!("{}{}", &lines[ref_line][..ref_indent], replacement);

        // Remove the standalone call line
        lines.remove(i);
        // Don't advance — recheck current position
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

/// Fold `$SwitchEnum_CmpSuccess` cascades into `// switch (VAR):` comments.
///
/// UE4's "Switch on Enum" node compiles to cascading comparisons:
///   `$SwitchEnum_CmpSuccess = VAR != N` / `if (!...) return` or `if (...) { ... }`
/// After structuring, this produces deeply nested if-blocks. This pass detects the
/// cascade fingerprint and replaces it with a readable switch comment, labeling the
/// first case body that follows.
fn fold_switch_enum_cascade(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        // Look for: INDENT $SwitchEnum_CmpSuccess... = VAR != VALUE
        let Some((switch_var, compared_var, first_value, base_indent)) =
            parse_switch_enum_assign(lines[i].trim(), &lines[i])
        else {
            i += 1;
            continue;
        };

        let cascade_start = i;
        let mut case_values = vec![first_value];

        // Scan forward to find the full cascade extent.
        // Track brace depth to find the matching closing braces.
        let mut j = i + 1;
        let mut brace_depth = 0i32;
        let mut cascade_end = i; // inclusive last cascade line

        while j < lines.len() {
            let trimmed = lines[j].trim();

            // Another assignment to the same SwitchEnum variable
            if let Some((sv, cv, val, _)) = parse_switch_enum_assign(trimmed, &lines[j]) {
                if sv == switch_var && cv == compared_var {
                    case_values.push(val);
                    cascade_end = j;
                    j += 1;
                    continue;
                }
            }

            // if ($SwitchEnum...) { or if (!$SwitchEnum...) return/break
            if trimmed.contains(&switch_var) {
                if trimmed.ends_with('{') {
                    brace_depth += 1;
                }
                cascade_end = j;
                j += 1;
                continue;
            }

            // Closing brace belonging to the cascade
            if trimmed == "}" && brace_depth > 0 {
                brace_depth -= 1;
                cascade_end = j;
                j += 1;
                continue;
            }

            break;
        }

        // Need at least 2 case values to be a valid switch
        if case_values.len() < 2 {
            i += 1;
            continue;
        }

        // Build replacement lines
        let indent_str = " ".repeat(base_indent);
        let cases_str = case_values
            .iter()
            .map(|v| v.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let switch_line = format!(
            "{}// switch ({}) [cases: {}]:",
            indent_str, compared_var, cases_str
        );

        // Check if there's a meaningful body after the cascade (not just return/break/})
        let has_body_after = j < lines.len()
            && !lines[j].trim().is_empty()
            && lines[j].trim() != "return"
            && lines[j].trim() != "break"
            && lines[j].trim() != "}";

        let mut replacement = vec![switch_line];
        if has_body_after {
            replacement.push(format!(
                "{}// case {} == {}:",
                indent_str, compared_var, case_values[0]
            ));
        }

        lines.splice(cascade_start..=cascade_end, replacement);
        i = cascade_start + 1;
    }
}

/// Parse `$SwitchEnum_CmpSuccess... = VAR != VALUE` from a trimmed line.
/// Returns (switch_var_name, compared_var, value, indent_len).
fn parse_switch_enum_assign(
    trimmed: &str,
    full_line: &str,
) -> Option<(String, String, String, usize)> {
    // Must start with $SwitchEnum_CmpSuccess
    if !trimmed.starts_with("$SwitchEnum_CmpSuccess") {
        return None;
    }
    let eq_pos = trimmed.find(" = ")?;
    let switch_var = &trimmed[..eq_pos];
    let rhs = &trimmed[eq_pos + 3..];
    // RHS must be `VAR != VALUE`
    let neq_pos = rhs.find(" != ")?;
    let compared_var = rhs[..neq_pos].to_string();
    let value = rhs[neq_pos + 4..].to_string();
    let indent_len = full_line.len() - full_line.trim_start().len();
    Some((switch_var.to_string(), compared_var, value, indent_len))
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
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && (indent_len + replacement.len()) > MAX_LINE {
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
/// to exactly one function name, AND the variable name contains the function name
/// (UE4 names out-params as `$FuncName_ParamName`). This prevents false positives
/// where a computed value like `$Add_FloatFloat` is used as an in-param to `FClamp`.
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

    // Must appear in exactly one function
    if func_names.len() != 1 {
        return false;
    }

    // Variable name must contain the function name (UE4 out-param naming: $FuncName_ParamName).
    // Strip leading `$` from the var for matching.
    let var_body = var.strip_prefix('$').unwrap_or(var);
    let func_name = func_names.iter().next().unwrap();
    var_body.starts_with(func_name)
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

/// Clean up structural artifacts from structuring.
///
/// Removes:
/// - Trailing orphaned `}` lines
/// - Empty `if (...) { }` blocks (if followed by content or end)
/// - Orphaned `} else {` ... `}` where the if-body was empty
/// - Leftover generated labels (`L_XXXX:`) with no corresponding goto
pub fn strip_orphaned_blocks(lines: &mut Vec<String>) {
    // Strip bare standalone expressions at top level (indent 0).
    // In UberGraph event segments, InputAction events start with an unused
    // key parameter read ($InputActionEvent_Key_N) and sometimes bare true/false
    // literals.  These are Kismet stack pushes with no consumer.
    lines.retain(|l| {
        let t = l.trim();
        // Standalone iface() calls — interface dispatch artifacts with no side effects.
        // Only strip when the closing `)` matches the opening `iface(` paren
        // (i.e., there's no method chain like `iface(X).Method()`).
        if t.starts_with("iface(") && !t.contains(" = ") {
            if let Some(close) = find_matching_paren(&t[5..]) {
                if 5 + close + 1 == t.len() {
                    return false;
                }
            }
        }
        let has_indent = l.len() > t.len();
        if !has_indent {
            // Bare temp variable (no assignment or call)
            if t.starts_with('$') && !t.contains('=') && !t.contains('(') {
                return false;
            }
            // Bare boolean literal
            if t == "true" || t == "false" {
                return false;
            }
        }
        true
    });

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

        // Strip trailing `} else {` (always orphaned at the end — else
        // with no body). Strip trailing `}` only when unmatched (depth < 0).
        while let Some(last) = lines.last() {
            let t = last.trim();
            if t == "} else {" {
                lines.pop();
                changed = true;
                continue;
            }
            if t == "}" {
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
            // → remove the if line and the } else {, keep else body
            if trimmed.starts_with("if ") && trimmed.ends_with(" {") && next_trimmed == "} else {" {
                lines.remove(i);
                lines.remove(i); // was i+1, now shifted
                changed = true;
                continue;
            }

            // Pattern: "if (...) {" followed by "}"
            // → remove both (empty if-block)
            if trimmed.starts_with("if ") && trimmed.ends_with(" {") && next_trimmed == "}" {
                lines.remove(i);
                lines.remove(i);
                changed = true;
                continue;
            }

            // Pattern: "} else {" followed by "}"
            // → remove both (empty else-block)
            if trimmed == "} else {" && next_trimmed == "}" {
                lines.remove(i);
                lines.remove(i);
                changed = true;
                continue;
            }

            i += 1;
        }
        if !changed {
            break;
        }
    }
}

/// Count net brace depth across all lines. Positive = unclosed `{`, negative = unmatched `}`.
fn brace_depth(lines: &[String]) -> i32 {
    lines.iter().fold(0i32, |d, l| {
        let t = l.trim();
        if t.ends_with(" {") || t == "{" {
            let close = i32::from(t.starts_with("} "));
            d - close + 1
        } else if t == "}" || t.starts_with("} ") {
            d - 1
        } else {
            d
        }
    })
}

/// Remove unmatched braces left over from per-body processing.
/// Resets depth at `---` and `// sequence [` boundaries. First pass
/// removes orphaned `}`; second pass removes `... {` that are never
/// closed before the next boundary.
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
            // "} else {" both closes and opens — net zero depth change
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

/// Remove goto/label pairs that are redundant in structured output.
///
/// A generated goto (to `L_XXXX`) is redundant when:
/// 1. Its label has only 1 referencing goto (no convergence from multiple paths)
/// 2. The label is either at/near the end of output, at the start (backward jump),
///    or immediately after the goto (fall-through)
fn strip_redundant_gotos(lines: &mut Vec<String>) {
    // Build goto → label index map (only for generated L_XXXX labels)
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
            let t = l.trim();
            !t.is_empty() && t != "}" && t != "return" && !t.ends_with(':')
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

// Inline tests: these test private functions (clean_line, parse_temp_assignment,
// substitute_var, split_args, etc.) that aren't accessible from tests/.
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

    // inline_constant_temps
    #[test]
    fn inline_constant_temps_same_expr() {
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "x = switch(Temp_bool_Variable) { false: A, true: B }".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 30,
                text: "y = switch(Temp_bool_Variable) { false: C, true: D }".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "x = switch(LeftHand) { false: A, true: B }");
        assert_eq!(stmts[1].text, "y = switch(LeftHand) { false: C, true: D }");
    }

    #[test]
    fn inline_constant_temps_different_exprs_skipped() {
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "x = Temp_bool_Variable".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "Temp_bool_Variable = RightHand".into(),
            },
            BcStatement {
                mem_offset: 30,
                text: "y = Temp_bool_Variable".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        // Different exprs → not inlined, all 4 remain
        assert_eq!(stmts.len(), 4);
    }

    #[test]
    fn inline_constant_temps_single_assign_multi_ref() {
        // Single Temp_* assignment, multiple references — should be inlined
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_0 = foo".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "bar(Temp_0)".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "baz(Temp_0)".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "bar(foo)");
        assert_eq!(stmts[1].text, "baz(foo)");
    }

    #[test]
    fn inline_constant_temps_dollar_single_assign_skipped() {
        // $-prefixed single assignment may be out-param — skip
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Param = _".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "Foo($Param)".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "x = $Param + 1".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 3); // unchanged
    }

    // discard_unused_assignments: pure expression removal
    #[test]
    fn discard_removes_pure_unused_assignment() {
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = SomeValue".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].text, "DoWork()");
    }

    #[test]
    fn discard_keeps_call_unused_assignment() {
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = SomeCall()".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "SomeCall()");
    }

    #[test]
    fn discard_removes_switch_unused_assignment() {
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = switch(X) { false: A, true: B }".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].text, "DoWork()");
    }

    // expr_has_call
    #[test]
    fn expr_has_call_function() {
        assert!(expr_has_call("IsValid(x)"));
    }

    #[test]
    fn expr_has_call_method() {
        assert!(expr_has_call("Foo.Bar()"));
    }

    #[test]
    fn expr_has_call_switch() {
        assert!(!expr_has_call("switch(X) { false: A, true: B }"));
    }

    #[test]
    fn expr_has_call_parens() {
        assert!(!expr_has_call("(A + B)"));
    }

    #[test]
    fn expr_has_call_none() {
        assert!(!expr_has_call("SomeValue"));
    }

    // cleanup_structured_output: return before sequence marker
    #[test]
    fn cleanup_strips_return_before_sequence_marker() {
        let mut lines = vec![
            "AdjustStatus(x, 0)".to_string(),
            "return".to_string(),
            "// sequence [1]:".to_string(),
            "AdjustStatus(y, 1)".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert!(!lines.iter().any(|l| l.trim() == "return"));
        assert!(lines.iter().any(|l| l.trim() == "// sequence [1]:"));
    }

    // cleanup_structured_output: trailing unmatched braces
    #[test]
    fn cleanup_strips_trailing_unmatched_braces() {
        let mut lines = vec![
            "if (cond) {".to_string(),
            "    do_something()".to_string(),
            "}".to_string(),
            "}".to_string(),
            "}".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert_eq!(lines, vec!["if (cond) {", "    do_something()", "}",]);
    }

    #[test]
    fn cleanup_keeps_matched_braces() {
        let mut lines = vec![
            "if (a) {".to_string(),
            "    if (b) {".to_string(),
            "        code()".to_string(),
            "    }".to_string(),
            "}".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert_eq!(lines.len(), 5); // all lines preserved
    }

    // ========== rewrite_bool_switches tests ==========

    #[test]
    fn bool_switch_basic() {
        assert_eq!(
            rewrite_bool_switches("switch(LeftHand) { false: self.Right, true: self.Left }"),
            "LeftHand ? self.Left : self.Right"
        );
    }

    #[test]
    fn bool_switch_true_first() {
        assert_eq!(
            rewrite_bool_switches("switch(X) { true: A, false: B }"),
            "X ? A : B"
        );
    }

    #[test]
    fn bool_switch_method_chain() {
        assert_eq!(
            rewrite_bool_switches(
                "switch(LeftHand) { false: self.RightHandle, true: self.LeftHandle }.SetTarget(x)"
            ),
            "(LeftHand ? self.LeftHandle : self.RightHandle).SetTarget(x)"
        );
    }

    #[test]
    fn bool_switch_compound_condition() {
        assert_eq!(
            rewrite_bool_switches("switch(self.Hunger == 0.0000) { false: 0.0000, true: rate }"),
            "(self.Hunger == 0.0000) ? rate : 0.0000"
        );
    }

    #[test]
    fn bool_switch_nested() {
        // Inner switch rewrites first (left-to-right), then outer.
        // Result is right-associative: X ? C : (Y ? B : A) ≡ X ? C : Y ? B : A
        assert_eq!(
            rewrite_bool_switches("switch(X) { false: switch(Y) { false: A, true: B }, true: C }"),
            "X ? C : Y ? B : A"
        );
    }

    #[test]
    fn bool_switch_in_assignment() {
        assert_eq!(
            rewrite_bool_switches(
                "Grip = switch(LeftHand) { false: self.RightGrip, true: self.LeftGrip }"
            ),
            "Grip = LeftHand ? self.LeftGrip : self.RightGrip"
        );
    }

    #[test]
    fn bool_switch_non_bool_not_rewritten() {
        let input = "switch(X) { 0: A, 1: B, 2: C }";
        assert_eq!(rewrite_bool_switches(input), input);
    }

    #[test]
    fn bool_switch_default_not_rewritten() {
        let input = "switch(X) { false: A, true: B, default: C }";
        assert_eq!(rewrite_bool_switches(input), input);
    }

    #[test]
    fn bool_switch_multiple_per_line() {
        assert_eq!(
            rewrite_bool_switches(
                "Foo(switch(A) { false: X, true: Y }, switch(B) { false: P, true: Q })"
            ),
            "Foo(A ? Y : X, B ? Q : P)"
        );
    }

    #[test]
    fn bool_switch_identical_branches() {
        assert_eq!(
            rewrite_bool_switches("out X = switch(IsValid) { false: src.Field, true: src.Field }"),
            "out X = src.Field"
        );
    }

    #[test]
    fn bool_switch_in_arithmetic_context() {
        assert_eq!(
            rewrite_bool_switches("0.0 + switch(A) { false: 0, true: X }"),
            "0.0 + (A ? X : 0)"
        );
    }

    #[test]
    fn bool_switch_chained_arithmetic() {
        assert_eq!(
            rewrite_bool_switches(
                "switch(A) { false: 0, true: X } + switch(B) { false: 0, true: Y }"
            ),
            "(A ? X : 0) + (B ? Y : 0)"
        );
    }

    #[test]
    fn bool_switch_simple_assignment_no_wrap() {
        assert_eq!(
            rewrite_bool_switches("x = switch(C) { false: A, true: B }"),
            "x = C ? B : A"
        );
    }

    // ========== fold_cast_inline tests ==========

    #[test]
    fn cast_inline_basic() {
        let mut lines = vec![
            "$Cast = cast<MyType>(GetObj())".to_string(),
            "if ($Cast) {".to_string(),
            "    self.Foo = $Cast".to_string(),
            "}".to_string(),
        ];
        fold_cast_inline(&mut lines);
        assert_eq!(lines[0], "if (cast<MyType>(GetObj())) {");
        assert_eq!(lines[1], "    self.Foo = cast<MyType>(GetObj())");
        assert_eq!(lines[2], "}");
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn cast_inline_too_many_refs() {
        let mut lines = vec![
            "$Cast = cast<T>(expr)".to_string(),
            "if ($Cast) {".to_string(),
            "    A($Cast)".to_string(),
            "    B($Cast)".to_string(),
            "    C($Cast)".to_string(),
            "}".to_string(),
        ];
        fold_cast_inline(&mut lines);
        // 4 refs (if + 3 body) > 3, should NOT inline
        assert_eq!(lines.len(), 6);
        assert_eq!(lines[0], "$Cast = cast<T>(expr)");
    }

    #[test]
    fn cast_inline_already_else_return() {
        let mut lines = vec![
            "$Cast = cast<T>(expr) else return".to_string(),
            "self.Foo = $Cast".to_string(),
        ];
        fold_cast_inline(&mut lines);
        // Should not touch "else return" lines
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0], "$Cast = cast<T>(expr) else return");
    }

    // ========== hoist_repeated_ternaries tests ==========

    #[test]
    fn hoist_repeated_ternary_3_uses() {
        let mut lines = vec![
            "    A((X ? self.Left : self.Right).Foo())".to_string(),
            "    B((X ? self.Left : self.Right).Bar())".to_string(),
            "    C((X ? self.Left : self.Right).Baz())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines.len(), 4);
        assert!(lines[0].contains(" = X ? self.Left : self.Right"));
        assert!(!lines[1].contains("X ? self.Left"));
        assert!(!lines[2].contains("X ? self.Left"));
        assert!(!lines[3].contains("X ? self.Left"));
    }

    #[test]
    fn hoist_no_change_for_2_uses() {
        let mut lines = vec![
            "    A((X ? L : R).Foo())".to_string(),
            "    B((X ? L : R).Bar())".to_string(),
        ];
        let original = lines.clone();
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines, original);
    }

    #[test]
    fn hoist_left_right_naming() {
        let mut lines = vec![
            "    A((H ? self.LeftVRHand : self.RightVRHand).M())".to_string(),
            "    B((H ? self.LeftVRHand : self.RightVRHand).N())".to_string(),
            "    C((H ? self.LeftVRHand : self.RightVRHand).O())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines.len(), 4);
        assert!(lines[0].contains("$VRHand = "));
        assert!(lines[1].contains("$VRHand.M()"));
    }

    #[test]
    fn hoist_preserves_indent() {
        let mut lines = vec![
            "        A((X ? L : R).F())".to_string(),
            "        B((X ? L : R).G())".to_string(),
            "        C((X ? L : R).H())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert!(lines[0].starts_with("        $"));
    }

    #[test]
    fn extract_ternaries_basic() {
        let result = extract_parenthesized_ternaries("A((X ? L : R).Foo(), (Y ? A : B))");
        assert_eq!(result.len(), 2);
        assert!(result.contains(&"(X ? L : R)".to_string()));
        assert!(result.contains(&"(Y ? A : B)".to_string()));
    }

    #[test]
    fn extract_left_right_suffix_test() {
        assert_eq!(
            extract_left_right_suffix("self.LeftVRHand", "self.RightVRHand"),
            Some("VRHand".to_string())
        );
        assert_eq!(
            extract_left_right_suffix("self.LeftMotionController", "self.RightMotionController"),
            Some("MotionController".to_string())
        );
        assert_eq!(extract_left_right_suffix("self.Foo", "self.Bar"), None);
    }

    // ========== simplify_bool_comparisons tests ==========

    #[test]
    fn simplify_not_call_eq_1() {
        let mut lines = vec!["    if (!GetIsHMDWorn() == 1) {".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    if (!GetIsHMDWorn()) {");
    }

    #[test]
    fn simplify_not_call_eq_0() {
        let mut lines = vec!["    if (!GetIsHMDWorn() == 0) {".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    if (GetIsHMDWorn()) {");
    }

    #[test]
    fn simplify_not_call_ne_0() {
        let mut lines = vec!["    x = !Func() != 0".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    x = !Func()");
    }

    #[test]
    fn simplify_not_call_ne_1() {
        let mut lines = vec!["    x = !Func() != 1".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    x = Func()");
    }

    #[test]
    fn simplify_does_not_match_member_access() {
        let mut lines = vec!["    if (!self.Flag == 1) {".to_string()];
        let original = lines.clone();
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines, original);
    }

    // ========== fold_outparam_calls tests ==========

    #[test]
    fn outparam_basic_fold() {
        let mut lines = vec![
            "self.Constraint.GetRotationAlpha($GetRotation_Alpha)".to_string(),
            "out Angle = ($GetRotation_Alpha * 2.0) - 1.0".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        assert_eq!(lines.len(), 1);
        assert_eq!(
            lines[0],
            "out Angle = (self.Constraint.GetRotationAlpha() * 2.0) - 1.0"
        );
    }

    #[test]
    fn outparam_multiple_dollar_args_skipped() {
        let mut lines = vec!["Func($A, $B)".to_string(), "x = $A + $B".to_string()];
        fold_outparam_calls(&mut lines);
        // Multiple $-args → skip
        assert_eq!(lines.len(), 2);
    }

    #[test]
    fn outparam_referenced_twice_skipped() {
        let mut lines = vec![
            "Func($Out)".to_string(),
            "x = $Out + 1".to_string(),
            "y = $Out + 2".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        // Used twice → skip
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn outparam_with_assignment_skipped() {
        let mut lines = vec![
            "$Out = someExpr".to_string(),
            "Func($Out)".to_string(),
            "x = $Out".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        // Has assignment → it's a regular temp, not an out-param
        assert_eq!(lines.len(), 3);
    }

    // is_unused_outparam — requires var name to match function name
    #[test]
    fn unused_outparam_matching_name() {
        let lines = vec![
            "BreakHitResult(src, $BreakHitResult_Location)".to_string(),
            "x = $BreakHitResult_Location".to_string(),
        ];
        // $BreakHitResult_Location starts with "BreakHitResult" → not suppressed
        // (it appears in non-arg context too, so it returns false anyway)
        assert!(!is_unused_outparam(&lines, "$BreakHitResult_Location"));
    }

    #[test]
    fn unused_outparam_non_matching_name() {
        let lines = vec!["FClamp($Add_FloatFloat, 0.0, 1.0)".to_string()];
        // $Add_FloatFloat doesn't start with "FClamp" → false
        assert!(!is_unused_outparam(&lines, "$Add_FloatFloat"));
    }

    #[test]
    fn unused_outparam_genuine() {
        let lines = vec![
            "GetFoo($GetFoo_Result)".to_string(),
            "GetFoo($GetFoo_Result)".to_string(),
        ];
        // $GetFoo_Result starts with "GetFoo", only appears as arg → true
        assert!(is_unused_outparam(&lines, "$GetFoo_Result"));
    }

    // fold_switch_enum_cascade
    #[test]
    fn switch_enum_cascade_flat() {
        let mut lines = vec![
            "$SwitchEnum_CmpSuccess = Status != 0".to_string(),
            "if ($SwitchEnum_CmpSuccess) {".to_string(),
            "    $SwitchEnum_CmpSuccess = Status != 1".to_string(),
            "    if (!$SwitchEnum_CmpSuccess) return".to_string(),
            "}".to_string(),
            "body_after_cascade()".to_string(),
        ];
        fold_switch_enum_cascade(&mut lines);
        assert!(lines[0].contains("// switch (Status)"));
        assert!(lines[1].contains("// case Status == 0:"));
        assert_eq!(lines[2], "body_after_cascade()");
    }

    #[test]
    fn switch_enum_cascade_no_body() {
        let mut lines = vec![
            "$SwitchEnum_CmpSuccess = X != 0".to_string(),
            "if ($SwitchEnum_CmpSuccess) {".to_string(),
            "    $SwitchEnum_CmpSuccess = X != 1".to_string(),
            "    if (!$SwitchEnum_CmpSuccess) return".to_string(),
            "}".to_string(),
            "return".to_string(),
        ];
        fold_switch_enum_cascade(&mut lines);
        assert!(lines[0].contains("// switch (X)"));
        // No case label before return
        assert_eq!(lines[1], "return");
    }
}
