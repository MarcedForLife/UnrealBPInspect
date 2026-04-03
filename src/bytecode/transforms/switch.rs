//! Switch/enum cascade folding: converts nested if-else chains from UE4's
//! "Switch on Enum" node into `switch (VAR) { case N: { ... } }` pseudocode.

use super::SWITCH_ENUM_PREFIX;
use crate::helpers::opens_block;

/// Fold `$SwitchEnum_CmpSuccess` cascades into `switch (VAR) { case: ... }`.
///
/// UE4's "Switch on Enum" node compiles to cascading comparisons:
///   `$SwitchEnum_CmpSuccess = VAR != N` / `if (!...) return` or `if (...) { ... }`
/// After structuring, this produces deeply nested if-blocks with case bodies at
/// decreasing indent levels. This pass detects the cascade, collects case
/// bodies (correctly handling `} else {` boundaries), and emits proper
/// `switch/case` pseudocode with braces for `apply_indentation`.
pub fn fold_switch_enum_cascade(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let Some((switch_var, compared_var, first_value)) =
            parse_switch_enum_assign(lines[i].trim())
        else {
            i += 1;
            continue;
        };

        let cascade_start = i;
        let (case_values, scaffold_end, mut brace_depth) =
            scan_cascade_scaffold(lines, i + 1, &switch_var, &compared_var, first_value);

        if case_values.len() < 2 {
            i += 1;
            continue;
        }

        let (body_groups, construct_end) =
            collect_case_bodies(lines, scaffold_end, &mut brace_depth);

        if body_groups.iter().all(Vec::is_empty) {
            i = construct_end;
            continue;
        }

        let replacement = build_switch_replacement(&compared_var, &case_values, body_groups);
        let replacement_len = replacement.len();
        lines.splice(cascade_start..construct_end, replacement);
        i = cascade_start + replacement_len;
    }
}

/// Scan the cascade scaffold: consecutive `$SwitchEnum_CmpSuccess = VAR != N`
/// assignments followed by if-checks and braces that reference the switch var.
/// Returns (case_values, next_line_index, brace_depth).
fn scan_cascade_scaffold(
    lines: &[String],
    start: usize,
    switch_var: &str,
    compared_var: &str,
    first_value: String,
) -> (Vec<String>, usize, i32) {
    let mut case_values = vec![first_value];
    let mut j = start;
    let mut brace_depth = 0i32;

    while j < lines.len() {
        let trimmed = lines[j].trim();
        if let Some((sv, cv, val)) = parse_switch_enum_assign(trimmed) {
            if sv == switch_var && cv == compared_var {
                case_values.push(val);
                j += 1;
                continue;
            }
        }
        if trimmed.contains(switch_var) {
            if opens_block(trimmed) {
                brace_depth += 1;
            }
            j += 1;
            continue;
        }
        if trimmed == "}" && brace_depth > 0 {
            brace_depth -= 1;
            j += 1;
            continue;
        }
        break;
    }

    (case_values, j, brace_depth)
}

/// Collect case bodies from the nested if/else structure after the scaffold.
/// Bodies are separated by `} else {` at the cascade level; nested braces within
/// bodies are tracked with body_depth to avoid splitting on inner if/else blocks.
/// Returns (body_groups, construct_end_index).
fn collect_case_bodies(
    lines: &[String],
    start: usize,
    brace_depth: &mut i32,
) -> (Vec<Vec<String>>, usize) {
    let mut body_groups: Vec<Vec<String>> = Vec::new();
    let mut current_body: Vec<String> = Vec::new();
    let mut body_depth = 0i32;
    let mut j = start;

    while j < lines.len() && *brace_depth > 0 {
        let trimmed = lines[j].trim();
        let is_open = opens_block(trimmed);
        let is_close = trimmed == "}";
        let is_else_chain = trimmed.starts_with("} ") && trimmed.ends_with('{');

        if body_depth > 0 && (is_close || is_else_chain) {
            body_depth -= 1;
            current_body.push(lines[j].clone());
            if is_else_chain {
                body_depth += 1;
            }
        } else if body_depth == 0 && (is_close || is_else_chain) {
            if !current_body.is_empty() {
                body_groups.push(std::mem::take(&mut current_body));
            }
            // Only bare `}` decrements brace_depth; `} else {` is neutral
            // because the opening `{` immediately re-enters the cascade
            if is_close {
                *brace_depth -= 1;
            }
        } else if is_open {
            current_body.push(lines[j].clone());
            body_depth += 1;
        } else if !trimmed.is_empty() {
            current_body.push(lines[j].clone());
        }
        j += 1;
    }

    // Outermost body (after cascade braces close)
    while j < lines.len() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() || trimmed == "return" || trimmed == "}" || trimmed == "break" {
            break;
        }
        current_body.push(lines[j].clone());
        j += 1;
    }
    if !current_body.is_empty() {
        body_groups.push(current_body);
    }

    (body_groups, j)
}

/// Build the switch/case replacement lines from collected bodies.
fn build_switch_replacement(
    compared_var: &str,
    case_values: &[String],
    mut body_groups: Vec<Vec<String>>,
) -> Vec<String> {
    // Cascade nesting produces bodies in reverse order (outermost = last case),
    // so flip them to get natural case ordering: case 0, case 1, ..., default
    body_groups.reverse();

    // Recursively fold inner switch cascades
    for body in &mut body_groups {
        fold_switch_enum_cascade(body);
    }

    // When there's one more body than case values, the extra one is the default branch
    let has_default = body_groups.len() == case_values.len() + 1;

    let mut replacement = vec![format!("switch ({}) {{", compared_var)];
    for (idx, body) in body_groups.iter().enumerate() {
        let label = if has_default && idx == body_groups.len() - 1 {
            "default: {".to_string()
        } else if idx < case_values.len() {
            format!("case {}: {{", case_values[idx])
        } else {
            format!("case {}: {{", idx)
        };
        replacement.push(label);
        for line in body {
            replacement.push(line.trim().to_string());
        }
        replacement.push("}".to_string());
    }
    replacement.push("}".to_string());
    replacement
}

/// Parse `$SwitchEnum_CmpSuccess... = VAR != VALUE` from a trimmed line.
fn parse_switch_enum_assign(trimmed: &str) -> Option<(String, String, String)> {
    if !trimmed.starts_with(SWITCH_ENUM_PREFIX) {
        return None;
    }
    let (switch_var, rhs) = trimmed.split_once(" = ")?;
    let (compared_var, value) = rhs.split_once(" != ")?;
    Some((
        switch_var.to_string(),
        compared_var.to_string(),
        value.to_string(),
    ))
}
