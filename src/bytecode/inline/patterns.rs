//! Summary pattern folding: Break/Make, struct construction, ForEach rewriting,
//! delegate binding, unused out-param suppression.

use super::{
    count_var_refs, find_matching_paren, is_ident_char, is_trivial_expr, parse_temp_assignment,
    split_args, strip_outer_parens, substitute_var,
};
use std::collections::{BTreeMap, HashMap, HashSet};

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
    // fold_switch_enum_cascade runs at the pipeline endpoint (after
    // strip_unmatched_braces, before apply_indentation) because it
    // adds new brace blocks that should not be touched by brace cleanup.
}

/// Rewrite ForEach loop boilerplate into `for (ITEM in ARRAY)`.
/// Detects the pattern: counter/index init, while(COUNTER < Array_Length(ARRAY)),
/// index assignment, Array_Get, body, increment.
fn rewrite_foreach_loops(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

        let Some((counter, array)) = parse_foreach_while(trimmed) else {
            i += 1;
            continue;
        };

        let Some((counter_idx, index_idx, index_var)) = find_foreach_init(lines, i, &counter)
        else {
            i += 1;
            continue;
        };

        let Some((assign_idx, get_idx, item)) =
            validate_body_start(lines, i + 1, &index_var, &counter, &array)
        else {
            i += 1;
            continue;
        };

        let Some((close_idx, incr_idx)) = find_close_and_increment(lines, i, &counter) else {
            i += 1;
            continue;
        };

        lines[i] = format!("for ({} in {}) {{", item, array);

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

        // Adjust for_idx since lines before `i` were removed
        let for_idx = i - removed_before_i;
        remove_redundant_gets(lines, for_idx, &item, &array, &index_var);

        // Don't advance; recheck in case of nested loops
        i = 0;
    }
}

/// Parse "while (COUNTER < ARRAY.Length()) {" -> Some((counter, array))
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
    counter: &str,
) -> Option<(usize, usize, String)> {
    let start = while_idx.saturating_sub(4);
    let mut counter_idx = None;
    let mut index_idx = None;
    let mut index_var = None;

    for j in (start..while_idx).rev() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() {
            continue;
        }
        // Stop at structural boundaries
        if trimmed.starts_with('}') || trimmed.ends_with(" {") {
            break;
        }

        if trimmed == format!("{} = 0", counter) {
            counter_idx = Some(j);
        } else if trimmed.ends_with(" = 0") && trimmed.starts_with("Temp_int_") {
            let var = &trimmed[..trimmed.len() - 4];
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
    index: &str,
    counter: &str,
    array: &str,
) -> Option<(usize, usize, String)> {
    let mut body_lines = Vec::new();
    let mut j = start;
    while j < lines.len() && body_lines.len() < 2 {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() {
            j += 1;
            continue;
        }
        // Stop at scope exit
        if trimmed == "}" {
            return None;
        }
        body_lines.push((j, trimmed.to_string()));
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
    let trimmed = &body_lines[1].1;
    let eq_pos = trimmed.find(" = ")?;
    let item_part = &trimmed[..eq_pos];
    let rhs = &trimmed[eq_pos + 3..];
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
    counter: &str,
) -> Option<(usize, usize)> {
    let mut depth = 0i32;
    let mut close_idx = None;
    for (j, line) in lines.iter().enumerate().skip(while_idx) {
        let trimmed = line.trim();
        if trimmed.ends_with(" {") || trimmed == "{" {
            depth += 1;
        }
        if trimmed == "}" || trimmed.starts_with("} ") {
            depth -= 1;
            if depth == 0 {
                close_idx = Some(j);
                break;
            }
        }
    }
    let close_idx = close_idx?;

    // Last non-empty body line before close should be the increment
    let expected_incr = format!("{} = {} + 1", counter, counter);
    let mut incr_idx = None;
    for j in (while_idx + 1..close_idx).rev() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed == expected_incr {
            incr_idx = Some(j);
        }
        break; // only check the last non-empty line
    }

    Some((close_idx, incr_idx?))
}

/// After rewriting a while-loop to a for-each, remove redundant Array_Get
/// re-fetches that reference the now-stale index variable.
fn remove_redundant_gets(
    lines: &mut Vec<String>,
    for_idx: usize,
    item: &str,
    array: &str,
    index_var: &str,
) {
    let mut depth = 0i32;
    let mut close = for_idx;
    for (j, line) in lines.iter().enumerate().skip(for_idx) {
        let trimmed = line.trim();
        if trimmed.ends_with(" {") || trimmed == "{" {
            depth += 1;
        }
        if trimmed == "}" || trimmed.starts_with("} ") {
            depth -= 1;
            if depth == 0 {
                close = j;
                break;
            }
        }
    }

    let redundant_get = format!("{} = {}[{}]", item, array, index_var);
    let mut j = for_idx + 1;
    while j < close {
        if lines[j].trim() == redundant_get {
            lines.remove(j);
            close -= 1;
            continue;
        }
        j += 1;
    }
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

        lines[i] = format!("{} {} {}.{}", target, op, obj, func);
        lines.remove(i + 1);
        // Don't advance; recheck current position
    }
}

/// Parse `bind(FUNC, $VAR, OBJ)` -> Some((func, delegate_var, obj))
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

/// Parse `TARGET += $VAR` or `TARGET -= $VAR` -> Some((target, op, delegate_var))
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
        let Some((var, _rhs)) = parse_cast_assignment(trimmed_a) else {
            i += 1;
            continue;
        };

        let expected = format!("if (!{}) return", var);
        if lines[i + 1].trim() != expected {
            i += 1;
            continue;
        }

        lines[i] = format!("{} else return", trimmed_a);
        lines.remove(i + 1);
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

/// Check if line `i` is a cast assignment followed by an if-guard on the same variable.
/// Returns (var_name, cast_rhs) if the pattern matches.
fn parse_cast_guard_pair(lines: &[String], i: usize) -> Option<(String, String)> {
    let trimmed = lines[i].trim();
    let (var, rhs) = parse_cast_assignment(trimmed)?;

    if trimmed.ends_with("else return") {
        return None;
    }

    let expected_if = format!("if ({}) {{", var);
    if lines.get(i + 1)?.trim() != expected_if {
        return None;
    }

    // Count total refs to $VAR in all lines except the assignment
    let mut total_refs = 0usize;
    for (j, line) in lines.iter().enumerate() {
        if j == i {
            continue;
        }
        total_refs += count_var_refs(line.trim(), var);
    }

    // if-guard = 1 ref, body uses <= 2 refs -> total <= 3
    if total_refs > 3 {
        return None;
    }

    Some((var.to_string(), rhs.to_string()))
}

/// Inline cast-and-use patterns: `$X = cast<T>(expr)` + `if ($X) { ... $X ... }`
/// where `$X` is used only in the if-guard and a few body references.
/// Substitutes the cast expression everywhere and removes the assignment line.
pub(super) fn fold_cast_inline(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let Some((var, rhs)) = parse_cast_guard_pair(lines, i) else {
            i += 1;
            continue;
        };

        // Substitute cast expression for $VAR everywhere
        for (j, line) in lines.iter_mut().enumerate() {
            if j == i {
                continue;
            }
            if count_var_refs(line.trim(), &var) > 0 {
                let mut text = line.trim().to_string();
                loop {
                    let new_text = replace_all_var_refs(&text, &var, &rhs);
                    if new_text == text {
                        break;
                    }
                    text = new_text;
                }
                *line = text;
            }
        }

        // Remove the assignment line
        lines.remove(i);
        // Don't advance; recheck current position
    }
}

/// Fold small Break* calls into field accessors using dynamic field name inference.
/// `BreakTransform($src, $BreakTransform_Location, ...)` -> replace with `$src.Location` etc.
/// Only applies when output arg count <= BREAK_INLINE_MAX_ARGS and all outputs are `$temp`.
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
                if count_var_refs(line.trim(), out_var) > 0 {
                    *line = replace_all_var_refs(line.trim(), out_var, &replacement);
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
        let expected_var = struct_var.to_string();

        // Collect consecutive field assignments, tolerating interleaved
        // $MakeStruct_* intermediate temps (UE5 pattern: temp assigned first,
        // then stored into struct field on the next line).
        let mut fields: Vec<(String, String)> = Vec::new();
        let mut intermediate_temps: Vec<(String, String)> = Vec::new();
        while i < lines.len() {
            let trimmed = lines[i].trim();
            if let Some((sv, field, value)) = parse_make_struct_field(trimmed) {
                if sv == expected_var {
                    fields.push((field.to_string(), value.to_string()));
                    i += 1;
                    continue;
                }
            }
            // Also consume $MakeStruct_* temp assignments (no dot) that feed
            // into subsequent field assignments
            if let Some((var, expr)) = parse_temp_assignment(trimmed) {
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
            let trimmed = lines[i].trim();
            if let Some(eq_pos) = trimmed.find(" = ") {
                let target = &trimmed[..eq_pos];
                let src = &trimmed[eq_pos + 3..];
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

                    let new_line = format!("{} = {}({})", target, type_name, args.join(", "));

                    let run_end = i + 1;
                    lines.splice(run_start..run_end, std::iter::once(new_line));
                    i = run_start + 1;
                    continue;
                }
            }
        }
        // No matching assignment, skip past collected fields
    }
}

/// Replace unused `$temp` out-params with `_` in function calls.
/// Hoist repeated parenthesized ternary expressions into named local variables.
/// When the same `(COND ? T : F)` appears 3+ times in a section, insert
/// `$VarName = COND ? T : F` before the first use and replace all occurrences.
pub(super) fn hoist_repeated_ternaries(lines: &mut Vec<String>) {
    // Extract and count all parenthesized ternary expressions
    let mut ternary_counts: BTreeMap<String, usize> = BTreeMap::new();
    for line in lines.iter() {
        for ternary in extract_parenthesized_ternaries(line.trim()) {
            *ternary_counts.entry(ternary).or_default() += 1;
        }
    }

    // Collect ternaries appearing 3+ times, longest first
    let mut to_hoist: Vec<(String, String)> = Vec::new();
    for (ternary, count) in &ternary_counts {
        if *count >= 3 {
            let var_name = generate_ternary_var_name(ternary, to_hoist.len());
            to_hoist.push((ternary.clone(), var_name));
        }
    }
    to_hoist.sort_by(|a, b| b.0.len().cmp(&a.0.len()));

    // Insert assignment before first use and replace all occurrences
    for (ternary, var_name) in &to_hoist {
        let first_use = lines.iter().position(|l| l.contains(ternary.as_str()));
        let Some(idx) = first_use else { continue };
        let rhs = strip_outer_parens(ternary);
        lines.insert(idx, format!("{} = {}", var_name, rhs));
        // Replace all occurrences in all lines
        for line in lines.iter_mut() {
            while line.contains(ternary.as_str()) {
                *line = line.replacen(ternary.as_str(), var_name, 1);
            }
        }
    }
}

/// Extract all parenthesized ternary expressions `(COND ? T : F)` from a line.
pub(super) fn extract_parenthesized_ternaries(input: &str) -> Vec<String> {
    let mut results = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'(' {
            if let Some(close) = find_matching_paren(&input[i..]) {
                let inner = &input[i + 1..i + close];
                // Check for ` ? ` and ` : ` at paren depth 0 inside
                if has_ternary_at_depth_zero(inner) {
                    results.push(input[i..i + close + 1].to_string());
                }
                // Don't skip past close; there may be nested ternaries inside
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
fn has_ternary_at_depth_zero(input: &str) -> bool {
    let mut depth = 0i32;
    let mut has_question = false;
    let bytes = input.as_bytes();
    let len = bytes.len();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
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
    for (i, &b) in bytes.iter().enumerate() {
        match b {
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
pub(super) fn extract_left_right_suffix(true_expr: &str, false_expr: &str) -> Option<String> {
    // Strip `self.` prefix if present on both
    let true_stripped = true_expr.strip_prefix("self.").unwrap_or(true_expr);
    let false_stripped = false_expr.strip_prefix("self.").unwrap_or(false_expr);
    // Try stripping Left/Right from true and Right/Left from false
    let suffix = if let Some(ts) = true_stripped.strip_prefix("Left") {
        if let Some(fs) = false_stripped.strip_prefix("Right") {
            if ts == fs {
                Some(ts)
            } else {
                None
            }
        } else {
            None
        }
    } else if let Some(ts) = true_stripped.strip_prefix("Right") {
        if let Some(fs) = false_stripped.strip_prefix("Left") {
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

/// Simplify redundant boolean comparisons: `!Func() == 1` -> `!Func()`, etc.
/// Fixes precedence ambiguity where `!Func() == 1` reads as `!(Func() == 1)`.
pub(super) fn simplify_bool_comparisons(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let simplified = simplify_negated_bool_comparison(line);
        if simplified != *line {
            *line = simplified;
        }
    }
}

/// Rewrite `!CALL(...) == 1` -> `!CALL(...)`, `!CALL(...) == 0` -> `CALL(...)`, etc.
/// Only matches function-call patterns (identifier followed by parens) to avoid
/// false positives on member access like `!self.Flag == 1`.
fn simplify_negated_bool_comparison(input: &str) -> String {
    let mut result = input.to_string();
    let mut search_from = 0;
    loop {
        let remaining = &result[search_from..];
        let Some(bang_rel) = remaining.find('!') else {
            break;
        };
        let bang_pos = search_from + bang_rel;

        if let Some(rewrite) = parse_negated_bool_at(&result, bang_pos) {
            let replacement = if rewrite.keep_negation {
                format!("!{}", &result[bang_pos + 1..rewrite.call_end])
            } else {
                result[bang_pos + 1..rewrite.call_end].to_string()
            };
            result = format!(
                "{}{}{}",
                &result[..bang_pos],
                replacement,
                &result[rewrite.call_end + rewrite.suffix_len..]
            );
            search_from = bang_pos + replacement.len();
        } else {
            search_from = bang_pos + 1;
        }
    }
    result
}

/// Result of parsing a `!Func(...) == N` pattern at a given `!` position.
struct NegatedBoolRewrite {
    call_end: usize,   // position after closing `)`
    suffix_len: usize, // length of the ` == N` suffix
    keep_negation: bool,
}

/// Try to parse `!Func(...) == N` starting at the `!` at `bang_pos`.
/// Returns None if the pattern doesn't match.
fn parse_negated_bool_at(text: &str, bang_pos: usize) -> Option<NegatedBoolRewrite> {
    let after_bang = &text[bang_pos + 1..];

    // Must be followed by an identifier char (start of function name)
    let first = after_bang.as_bytes().first()?;
    if matches!(first, b'(' | b' ' | b'=') || !first.is_ascii_alphanumeric() {
        return None;
    }

    // Char before `!` must be a non-identifier boundary
    if bang_pos > 0 {
        let prev = text.as_bytes()[bang_pos - 1];
        if prev.is_ascii_alphanumeric() || matches!(prev, b'_' | b'.' | b'$') {
            return None;
        }
    }

    // Find the call: simple identifier followed by matched parens
    let call_start = bang_pos + 1;
    let paren_offset = text[call_start..].find('(')?;
    let paren_abs = call_start + paren_offset;

    // Between `!` and `(` must be a simple identifier (no spaces/dots, avoids !self.X)
    let ident = &text[call_start..paren_abs];
    if ident.is_empty() || !ident.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }

    let close_rel = find_matching_paren(&text[paren_abs..])?;
    let call_end = paren_abs + close_rel + 1;

    // Parse the comparison suffix: ` == 0`, ` == 1`, ` != 0`, ` != 1`
    let after_call = &text[call_end..];
    let (op, val) = if after_call.starts_with(" == 1") {
        ("==", 1)
    } else if after_call.starts_with(" == 0") {
        ("==", 0)
    } else if after_call.starts_with(" != 0") {
        ("!=", 0)
    } else if after_call.starts_with(" != 1") {
        ("!=", 1)
    } else {
        return None;
    };
    let suffix_len = 5; // " == N" or " != N"

    // Ensure what follows is a boundary (not more digits/identifiers)
    let after_cmp = &text[call_end + suffix_len..];
    if let Some(&next) = after_cmp.as_bytes().first() {
        if next.is_ascii_alphanumeric() || next == b'_' {
            return None;
        }
    }

    let keep_negation = (op == "==" && val == 1) || (op == "!=" && val == 0);
    Some(NegatedBoolRewrite {
        call_end,
        suffix_len,
        keep_negation,
    })
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
            if count_var_refs(line, var) > 0 {
                *line = replace_all_var_refs(line, var, "_");
            }
        }
    }
}

/// Fold single-out-param function calls into their usage site.
/// `obj.Func($outParam)` where `$outParam` is referenced exactly once later
/// -> substitute `obj.Func()` for `$outParam` and remove the standalone call.
pub(super) fn fold_outparam_calls(lines: &mut Vec<String>) {
    const MAX_LINE: usize = 120;
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim().to_string();

        let Some(candidate) = parse_outparam_call(&trimmed) else {
            i += 1;
            continue;
        };

        // The out-param must not have a separate assignment (it's populated by the call itself)
        if has_temp_assignment(lines, &candidate.out_var) {
            i += 1;
            continue;
        }

        // Must be referenced exactly once in other lines
        let Some(ref_line) = find_single_ref(lines, i, &candidate.out_var) else {
            i += 1;
            continue;
        };

        // Substitute $outParam with the rewritten call expression
        let replacement = replace_all_var_refs(
            lines[ref_line].trim(),
            &candidate.out_var,
            &candidate.call_expr,
        );

        if replacement.len() > MAX_LINE {
            i += 1;
            continue;
        }

        lines[ref_line] = replacement;
        lines.remove(i);
    }
}

/// A bare function call with exactly one $-prefixed out-param.
struct OutparamCall {
    out_var: String,
    call_expr: String, // the call with the out-param removed
}

/// Parse a line as a bare function call with exactly one $-prefixed out-param.
fn parse_outparam_call(trimmed: &str) -> Option<OutparamCall> {
    // Must be a bare call: has parens, no assignment/control flow
    if !trimmed.contains('(')
        || trimmed.contains(" = ")
        || trimmed.starts_with("if ")
        || trimmed.starts_with("} ")
        || trimmed.starts_with("for ")
        || trimmed.starts_with("while ")
    {
        return None;
    }

    let paren_start = trimmed.find('(')?;
    if !trimmed.ends_with(')') {
        return None;
    }
    let args_str = &trimmed[paren_start + 1..trimmed.len() - 1];
    let args = split_args(args_str);

    // Find exactly one $-prefixed arg
    let dollar_args: Vec<(usize, &str)> = args
        .iter()
        .enumerate()
        .filter(|(_, a)| a.starts_with('$'))
        .map(|(idx, a)| (idx, *a))
        .collect();
    if dollar_args.len() != 1 {
        return None;
    }
    let (arg_idx, out_var) = dollar_args[0];

    // Out-params are always last in UE4 calling convention
    if args.len() > 1 && arg_idx != args.len() - 1 {
        return None;
    }

    // Build the call with the out-param removed
    let new_args: Vec<&str> = args
        .iter()
        .enumerate()
        .filter(|(idx, _)| *idx != arg_idx)
        .map(|(_, a)| *a)
        .collect();
    let call_prefix = &trimmed[..paren_start];
    let call_expr = format!("{}({})", call_prefix, new_args.join(", "));

    Some(OutparamCall {
        out_var: out_var.to_string(),
        call_expr,
    })
}

fn has_temp_assignment(lines: &[String], var: &str) -> bool {
    lines
        .iter()
        .any(|line| parse_temp_assignment(line.trim()).is_some_and(|(name, _)| name == var))
}

/// Find the single line (other than `skip_idx`) that references `var`.
/// Returns None if there are zero or multiple references.
fn find_single_ref(lines: &[String], skip_idx: usize, var: &str) -> Option<usize> {
    let mut ref_count = 0;
    let mut ref_line = None;
    for (j, line) in lines.iter().enumerate() {
        if j == skip_idx {
            continue;
        }
        let refs = count_var_refs(line.trim(), var);
        ref_count += refs;
        if refs > 0 && ref_line.is_none() {
            ref_line = Some(j);
        }
    }
    if ref_count == 1 {
        ref_line
    } else {
        None
    }
}

/// Compact Break struct calls that have many `_` args by keeping only used params.
/// Field names are inferred from the `$BreakName_FieldName` variable naming convention.
/// `BreakHitResult(src, _, _, _, $BreakHitResult_Location, ...)` ->
///   `BreakHitResult(src, Location: $BreakHitResult_Location, ...)`
/// Triggers when a Break call has ≥6 output args and ≥50% are `_`.
fn compact_large_break_calls(lines: &mut [String]) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

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

        let new_call = format!("{}({})", func_name, parts.join(", "));
        lines[i] = new_call;
        i += 1;
    }
}

/// Fold `$SwitchEnum_CmpSuccess` cascades into `// switch (VAR):` comments.
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
        let mut case_values = vec![first_value];

        // Phase 1: scan the cascade scaffold (assignments + if-checks + braces)
        let mut j = i + 1;
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
            if trimmed.contains(&switch_var) {
                if trimmed.ends_with(" {") || trimmed == "{" {
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

        if case_values.len() < 2 {
            i += 1;
            continue;
        }

        // Phase 2: collect case bodies from the nested if/else structure.
        // The cascade compiles to nested `if (cmpN) { if (cmpN+1) { ... } else { bodyN } }`.
        // Bodies are separated by `} else {` at the cascade level; nested braces within
        // bodies are tracked with body_depth to avoid splitting on inner if/else blocks.
        let mut body_groups: Vec<Vec<String>> = Vec::new();
        let mut current_body: Vec<String> = Vec::new();
        let mut body_depth = 0i32;

        while j < lines.len() && brace_depth > 0 {
            let trimmed = lines[j].trim();
            let opens_block = trimmed.ends_with(" {") || trimmed == "{";
            let is_close = trimmed == "}";
            let is_else_chain = trimmed.starts_with("} ") && trimmed.ends_with('{');

            if body_depth > 0 && (is_close || is_else_chain) {
                // Closing or chaining a nested block within the body
                body_depth -= 1;
                current_body.push(lines[j].clone());
                if is_else_chain {
                    body_depth += 1;
                }
                j += 1;
            } else if body_depth == 0 && (is_close || is_else_chain) {
                // Cascade-level boundary: end current body, start next
                if !current_body.is_empty() {
                    body_groups.push(std::mem::take(&mut current_body));
                }
                if is_close {
                    brace_depth -= 1;
                }
                j += 1;
            } else if opens_block {
                current_body.push(lines[j].clone());
                body_depth += 1;
                j += 1;
            } else if !trimmed.is_empty() {
                current_body.push(lines[j].clone());
                j += 1;
            } else {
                j += 1;
            }
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

        let construct_end = j;

        // Skip if no actual case bodies
        if body_groups.iter().all(Vec::is_empty) {
            i = construct_end;
            continue;
        }

        // Recursively fold inner switch cascades
        for body in &mut body_groups {
            fold_switch_enum_cascade(body);
        }

        // Build replacement as proper pseudocode with braces
        let mut replacement = vec![format!("switch ({}) {{", compared_var)];
        let num_bodies = body_groups.len();
        let num_cases = case_values.len();
        for (idx, body) in body_groups.iter().enumerate() {
            let case_idx = num_bodies.saturating_sub(1 + idx);
            let is_default = num_bodies == num_cases + 1 && idx == 0;
            let label = if is_default {
                "default: {".to_string()
            } else if case_idx < num_cases {
                format!("case {}: {{", case_values[case_idx])
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

        let replacement_len = replacement.len();
        lines.splice(cascade_start..construct_end, replacement);
        i = cascade_start + replacement_len;
    }
}

/// Parse `$SwitchEnum_CmpSuccess... = VAR != VALUE` from a trimmed line.
fn parse_switch_enum_assign(trimmed: &str) -> Option<(String, String, String)> {
    if !trimmed.starts_with("$SwitchEnum_CmpSuccess") {
        return None;
    }
    let eq_pos = trimmed.find(" = ")?;
    let switch_var = &trimmed[..eq_pos];
    let rhs = &trimmed[eq_pos + 3..];
    let neq_pos = rhs.find(" != ")?;
    let compared_var = rhs[..neq_pos].to_string();
    let value = rhs[neq_pos + 4..].to_string();
    Some((switch_var.to_string(), compared_var, value))
}

/// Rename Make* functions by stripping the `Make` prefix: MakeVector -> Vector, etc.
fn rename_make_functions(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let changed = strip_make_prefix(line);
        if changed != *line {
            *line = changed;
        }
    }
}

/// Find `Make<Name>(` patterns and strip the `Make` prefix.
/// Only matches when preceded by a non-ident char (or start of string),
/// and when the char after `Make` is uppercase (avoids false positives).
pub(super) fn strip_make_prefix(text: &str) -> String {
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
        // Strip "Make", keep everything after it
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
                let ref_count = count_var_refs(line.trim(), var_name);
                refs += ref_count;
                if ref_count == 1 && target.is_none() {
                    target = Some(i);
                }
            }
            if refs != 1 {
                continue;
            }
            let Some(target_idx) = target else { continue };

            let replacement = substitute_var(lines[target_idx].trim(), var_name, &current_expr);

            let shortens = current_expr.len() + 2 <= var_name.len();
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > MAX_LINE {
                continue;
            }

            lines[target_idx] = replacement;
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

/// Find the completion block extent (lines after "// on loop complete:" until the next
/// scope exit or section boundary). Uses brace counting.
fn find_completion_block(lines: &[String], marker_idx: usize) -> Option<(usize, usize)> {
    let comp_start = marker_idx + 1;
    let mut comp_end = comp_start;
    let mut depth = 0i32;
    while comp_end < lines.len() {
        let trimmed = lines[comp_end].trim();
        if trimmed.is_empty() {
            comp_end += 1;
            continue;
        }
        if trimmed.starts_with("---") {
            break;
        }
        if trimmed.starts_with('}') {
            depth -= 1;
            if depth < 0 {
                break;
            }
        }
        if trimmed.ends_with(" {") || trimmed == "{" {
            depth += 1;
        }
        comp_end += 1;
    }
    if comp_end <= comp_start {
        None
    } else {
        Some((comp_start, comp_end))
    }
}

/// Find the pre-loop setup lines: flat statements immediately before the while/for
/// loop (no braces between them). Returns (pre_start, while_idx).
fn find_pre_loop_setup(lines: &[String], marker_idx: usize) -> Option<(usize, usize)> {
    let while_idx = (0..marker_idx).rev().find(|&j| {
        let trimmed = lines[j].trim();
        trimmed.starts_with("while ") || trimmed.starts_with("for ")
    })?;

    let mut pre_start = while_idx;
    for j in (0..while_idx).rev() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() {
            continue;
        }
        // Stop at braces or comments (structural boundaries)
        if trimmed.starts_with('}') || trimmed.starts_with("//") || trimmed.ends_with(" {") {
            break;
        }
        pre_start = j;
    }

    Some((pre_start, while_idx))
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

        let Some((comp_start, comp_end)) = find_completion_block(lines, marker_idx) else {
            i += 1;
            continue;
        };

        let Some((pre_start, while_idx)) = find_pre_loop_setup(lines, marker_idx) else {
            i = comp_end;
            continue;
        };

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
            let trimmed = line.trim();
            if trimmed.is_empty() {
                continue;
            }
            total_count += 1;
            if pre_set.contains(trimmed) {
                matched_count += 1;
            } else {
                unique_indices.push(j);
            }
        }

        // Need at least 3 duplicated lines covering majority of completion
        if matched_count >= 3 && matched_count * 2 >= total_count {
            let mut replacement: Vec<String> = Vec::new();
            if unique_indices.is_empty() {
                replacement.push("// on loop complete: (same as pre-loop setup)".to_string());
            } else {
                replacement.push("// on loop complete: (repeats pre-loop setup)".to_string());
                for &j in &unique_indices {
                    replacement.push(lines[j].clone());
                }
            }
            lines.splice(marker_idx..comp_end, replacement);
        }

        i += 1;
    }
}

/// Detect a shared `_N` disambiguation suffix across all field names.
/// Returns Some("_1") if all fields end with "_1", etc.
pub(super) fn detect_common_suffix<'a>(fields: &[&'a str]) -> Option<&'a str> {
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
pub(super) fn is_unused_outparam(lines: &[String], var: &str) -> bool {
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
