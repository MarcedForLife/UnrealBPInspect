//! Summary pipeline orchestration and expression transforms: delegates, casts,
//! ternaries, out-param suppression, section temps, completion dedup.

use super::loops::rewrite_loops;
use super::structs::{
    compact_large_break_calls, fold_break_patterns, fold_struct_construction,
    rename_make_functions, replace_all_var_refs,
};
use super::{
    count_var_refs, find_matching_paren, is_loop_header, is_trivial_expr, parse_temp_assignment,
    split_args, strip_outer_parens, substitute_var,
};
use crate::bytecode::{
    LOOP_COMPLETE_MARKER, LOOP_COMPLETE_REPEATS_PRELOOP, LOOP_COMPLETE_SAME_AS_PRELOOP,
};
use crate::helpers::{is_section_separator, opens_block, SECTION_SEPARATOR};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Post-processing pass on structured output lines.
/// Folds Break/Make struct patterns, collapses struct construction,
/// suppresses unused out-params, and renames Make functions.
pub fn fold_summary_patterns(lines: &mut Vec<String>) {
    // Process each section independently (sections separated by --- markers)
    let mut result: Vec<String> = Vec::new();
    let mut section: Vec<String> = Vec::new();

    for line in lines.drain(..) {
        let trimmed = line.trim();
        if is_section_separator(trimmed) {
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

    // Structural rewrites (change control flow shape)
    rewrite_loops(lines);
    fold_delegate_bindings(lines);

    // Expression folding (collapse multi-statement patterns into expressions)
    fold_break_patterns(lines);
    fold_struct_construction(lines);
    dedup_completion_paths(lines);

    // Temp variable inlining (must run after folding creates final expressions)
    fold_section_temps(lines);

    // Cosmetic cleanup
    simplify_bool_comparisons(lines);
    hoist_repeated_ternaries(lines);
    fold_outparam_calls(lines);
    compact_large_break_calls(lines);
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
    to_hoist.sort_by_key(|entry| std::cmp::Reverse(entry.0.len()));

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
            // Skip function-call parens: `(` preceded by an identifier char
            // is a call argument list, not a ternary grouping.
            let is_call = i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
            if !is_call {
                if let Some(close) = find_matching_paren(&input[i..]) {
                    let inner = &input[i + 1..i + close];
                    // Check for ` ? ` and ` : ` at paren depth 0 inside
                    if has_ternary_at_depth_zero(inner) {
                        results.push(input[i..i + close + 1].to_string());
                    }
                }
            }
            i += 1;
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
            b'?' if depth == 0
                && i > 0
                && i + 1 < len
                && bytes[i - 1] == b' '
                && bytes[i + 1] == b' ' =>
            {
                has_question = true;
            }
            b':' if depth == 0
                && has_question
                && i > 0
                && i + 1 < len
                && bytes[i - 1] == b' '
                && bytes[i + 1] == b' ' =>
            {
                return true;
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
            b'?' if depth == 0
                && q_pos.is_none()
                && i > 0
                && i + 1 < len
                && bytes[i - 1] == b' '
                && bytes[i + 1] == b' ' =>
            {
                q_pos = Some(i);
            }
            b':' if depth == 0
                && q_pos.is_some()
                && c_pos.is_none()
                && i > 0
                && i + 1 < len
                && bytes[i - 1] == b' '
                && bytes[i + 1] == b' ' =>
            {
                c_pos = Some(i);
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

/// Fold single-out-param function calls into their usage site.
/// `obj.Func($outParam)` where `$outParam` is referenced exactly once later
/// -> substitute `obj.Func()` for `$outParam` and remove the standalone call.
pub(super) fn fold_outparam_calls(lines: &mut Vec<String>) {
    use crate::bytecode::MAX_LINE_WIDTH;
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

        if replacement.len() > MAX_LINE_WIDTH {
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
        || is_loop_header(trimmed)
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

    // Out-params are always last in UE calling convention
    if args.len() > 1 && arg_idx != args.len() - 1 {
        return None;
    }

    // For single-arg calls, the $-variable must relate to the function name.
    // UE auto-generates out-param temps as $FuncName_ParamName, so the variable
    // name starts with or shares a substantial prefix with the function name.
    // Without this check, event parameters like $ComponentBoundEvent_OtherActor_1
    // passed as input to AddUnique() get falsely treated as out-params.
    if args.len() == 1 {
        let prefix = &trimmed[..paren_start];
        let func_name = prefix
            .rsplit_once('.')
            .map(|(_, name)| name)
            .unwrap_or(prefix);
        let var_name = out_var.strip_prefix('$').unwrap_or(out_var);
        // The var name must start with the function name (ignoring underscores
        // that UE inserts into temp names as word separators).
        let func_lower = func_name.to_ascii_lowercase();
        let var_lower = var_name.replace('_', "").to_ascii_lowercase();
        if !var_lower.starts_with(&func_lower) {
            return None;
        }
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

/// Per-section inlining of single-use temp variables in structured output.
/// Runs on `Vec<String>` (indented lines) after structuring, catching temps
/// that survived pre-structure inlining due to cross-section ref counts.
fn fold_section_temps(lines: &mut Vec<String>) {
    use crate::bytecode::MAX_LINE_WIDTH;
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
            if !shortens && !trivial && replacement.len() > MAX_LINE_WIDTH {
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

/// Find the completion block extent (lines after LOOP_COMPLETE_MARKER until the next
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
        if trimmed.starts_with(SECTION_SEPARATOR) {
            break;
        }
        if trimmed.starts_with('}') {
            depth -= 1;
            if depth < 0 {
                break;
            }
        }
        if opens_block(trimmed) {
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
        is_loop_header(trimmed)
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
        if lines[i].trim() != LOOP_COMPLETE_MARKER {
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
                replacement.push(LOOP_COMPLETE_SAME_AS_PRELOOP.to_string());
            } else {
                replacement.push(LOOP_COMPLETE_REPEATS_PRELOOP.to_string());
                for &j in &unique_indices {
                    replacement.push(lines[j].clone());
                }
            }
            lines.splice(marker_idx..comp_end, replacement);
        }

        i += 1;
    }
}
