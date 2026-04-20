//! Temp variable inlining and dead assignment removal.

use super::{
    count_var_refs, expr_has_call, is_trivial_expr, parse_temp_assignment, substitute_var,
};
use crate::bytecode::decode::BcStatement;
use crate::bytecode::flow::{parse_if_jump, parse_jump};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Collect all bytecode offsets that are jump targets (conditional and unconditional).
/// Used to protect these offsets from being lost when inline passes remove statements.
pub fn collect_jump_targets(stmts: &[BcStatement]) -> HashSet<usize> {
    let mut targets = HashSet::new();
    for stmt in stmts {
        if let Some((_, target)) = parse_if_jump(&stmt.text) {
            targets.insert(target);
        }
        if let Some(target) = parse_jump(&stmt.text) {
            targets.insert(target);
        }
    }
    targets
}

/// Substitute ALL occurrences of `var` in `text`, repeating until stable.
fn substitute_var_all(text: &str, var: &str, expr: &str) -> String {
    // Bail immediately if expr contains var (would loop forever).
    if count_var_refs(expr, var) > 0 {
        return text.to_string();
    }
    let mut result = text.to_string();
    // Limit iterations to the number of references (each call replaces one).
    let limit = count_var_refs(text, var) + 1;
    for _ in 0..limit {
        let next = substitute_var(&result, var, expr);
        if next == result {
            return result;
        }
        result = next;
    }
    result
}

/// Inline `Temp_*` / `$temp` variables that are always assigned the same value.
/// UE Select nodes re-assign the index input before every use; this pass
/// collapses `Temp_bool_Variable = LeftHand` + `switch(Temp_bool_Variable)`
/// into `switch(LeftHand)`.
pub fn inline_constant_temps(stmts: &mut Vec<BcStatement>, jump_targets: &HashSet<usize>) {
    let texts: Vec<&str> = stmts.iter().map(|s| s.text.as_str()).collect();
    let Some((constant_vars, remove_indices)) = resolve_constant_vars(&texts) else {
        return;
    };

    for s in stmts.iter_mut() {
        for (var, expr) in &constant_vars {
            if count_var_refs(&s.text, var) > 0 {
                s.text = substitute_var_all(&s.text, var, expr);
            }
        }
    }

    let sorted_targets = sorted_jump_targets(jump_targets);
    let removed: Vec<usize> = remove_indices.iter().copied().collect();
    transfer_offsets_on_removal(stmts, &removed, &sorted_targets);

    let mut idx = 0;
    stmts.retain(|_| {
        let keep = !remove_indices.contains(&idx);
        idx += 1;
        keep
    });
}

/// Inline single-use `$temp` variables to reduce noise.
///
/// Only inlines vars that:
/// - Start with `$` (compiler temporaries)
/// - Are assigned exactly once (`$X = expr`)
/// - Are referenced exactly once in a later statement
/// - Would not produce a line longer than MAX_LINE_WIDTH chars
pub fn inline_single_use_temps(stmts: &mut Vec<BcStatement>) {
    const MAX_PASSES: usize = 6;

    for _ in 0..MAX_PASSES {
        let assignments: Vec<(usize, String, String)> = stmts
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                let (var, expr) = parse_temp_assignment(&s.text)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var, _) in &assignments {
            *assign_counts.entry(var.as_str()).or_default() += 1;
        }

        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var, expr) in &assignments {
            if assign_counts.get(var.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, stmt) in stmts.iter().enumerate() {
                if i == *assign_idx {
                    continue;
                }
                ref_count += count_var_refs(&stmt.text, var);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var.clone(), expr.clone()));
            }
        }

        let mut removed: HashSet<usize> = HashSet::new();
        let mut inlined_any = false;
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }
            let current_expr = match parse_temp_assignment(&stmts[*assign_idx].text) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };
            let mut refs = 0usize;
            let mut target_idx = None;
            for (i, stmt) in stmts.iter().enumerate() {
                if i == *assign_idx || removed.contains(&i) {
                    continue;
                }
                let count = count_var_refs(&stmt.text, var_name);
                refs += count;
                if count == 1 && target_idx.is_none() {
                    target_idx = Some(i);
                }
            }
            if refs != 1 {
                continue;
            }
            let Some(target_idx) = target_idx else {
                continue;
            };
            let replacement = substitute_var(&stmts[target_idx].text, var_name, &current_expr);
            let shortens = current_expr.len() + 2 <= var_name.len();
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > crate::bytecode::MAX_LINE_WIDTH {
                continue;
            }
            stmts[target_idx].text = replacement;
            removed.insert(*assign_idx);
            inlined_any = true;
        }

        let mut idx = 0;
        stmts.retain(|_| {
            let keep = !removed.contains(&idx);
            idx += 1;
            keep
        });
        if !inlined_any {
            break;
        }
    }
}

/// Transfer mem_offsets from removed statements to the next surviving statement
/// when the removed offset is near a known jump target.
fn transfer_offsets_on_removal(
    stmts: &mut [BcStatement],
    removed: &[usize],
    sorted_targets: &[usize],
) {
    let tolerance = crate::bytecode::JUMP_OFFSET_TOLERANCE;
    let is_near_target = |off: usize| -> bool {
        let pos = sorted_targets.partition_point(|&t| t < off.saturating_sub(tolerance));
        pos < sorted_targets.len() && sorted_targets[pos].abs_diff(off) <= tolerance
    };
    let removed_set: HashSet<usize> = removed.iter().copied().collect();
    let mut pending: Vec<usize> = Vec::new();
    for (i, stmt) in stmts.iter_mut().enumerate() {
        if removed_set.contains(&i) {
            let off = stmt.mem_offset;
            if off > 0 && is_near_target(off) {
                pending.push(off);
            }
        } else if !pending.is_empty() {
            stmt.offset_aliases.append(&mut pending);
        }
    }
}

/// Build sorted jump target array for binary search.
fn sorted_jump_targets(jump_targets: &HashSet<usize>) -> Vec<usize> {
    let mut sorted: Vec<usize> = jump_targets.iter().copied().collect();
    sorted.sort_unstable();
    sorted
}

/// Discard assignments to `$temp` variables that are never referenced.
/// Keeps the RHS expression only if it has side effects (contains a function call).
/// Pure expressions (no function call) are removed entirely.
pub fn discard_unused_assignments(stmts: &mut Vec<BcStatement>) {
    let texts: Vec<&str> = stmts.iter().map(|s| s.text.as_str()).collect();
    let ref_counts = count_unused_assignments(&texts);

    for s in stmts.iter_mut() {
        if let Some((var, expr)) = parse_temp_assignment(&s.text) {
            if ref_counts.get(var).copied() == Some(0) {
                if expr_has_call(expr) {
                    s.text = expr.to_string();
                } else {
                    s.text.clear();
                }
            }
        }
    }

    stmts.retain(|s| !s.text.is_empty());
}

/// Text-based constant temp inlining for post-structure pipelines.
///
/// Operates on structured text lines (`Vec<String>`) after `structure_bytecode`.
/// Uses the shared `resolve_constant_vars` core for the algorithm.
pub fn inline_constant_temps_text(lines: &mut Vec<String>) {
    let texts: Vec<&str> = lines.iter().map(|l| l.trim()).collect();
    let Some((constant_vars, remove_indices)) = resolve_constant_vars(&texts) else {
        return;
    };

    for line in lines.iter_mut() {
        for (var, expr) in &constant_vars {
            if count_var_refs(line.trim(), var) > 0 {
                *line = substitute_var_all(line.trim(), var, expr);
            }
        }
    }

    let mut idx = 0;
    lines.retain(|_| {
        let keep = !remove_indices.contains(&idx);
        idx += 1;
        keep
    });
}

/// Text-based single-use temp inlining for post-structure pipelines.
///
/// Operates on structured text lines (`Vec<String>`) after `structure_bytecode`.
/// Mirrors `inline_single_use_temps` but respects brace scoping: an assignment
/// only inlines into a consumer that sits in the same logical block or a
/// nested child block, never across an `if` / `else` boundary that would
/// change semantics.
pub fn inline_single_use_temps_text(lines: &mut Vec<String>) {
    use crate::bytecode::MAX_LINE_WIDTH;
    const MAX_PASSES: usize = 6;

    for _ in 0..MAX_PASSES {
        let assignments: Vec<(usize, String, String)> = lines
            .iter()
            .enumerate()
            .filter_map(|(i, line)| {
                let trimmed = line.trim();
                let (var, expr) = parse_temp_assignment(trimmed)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var, _) in &assignments {
            *assign_counts.entry(var.as_str()).or_default() += 1;
        }

        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var, expr) in &assignments {
            if assign_counts.get(var.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, line) in lines.iter().enumerate() {
                if i == *assign_idx {
                    continue;
                }
                ref_count += count_var_refs(line.trim(), var);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var.clone(), expr.clone()));
            }
        }

        let mut removed: HashSet<usize> = HashSet::new();
        let mut inlined_any = false;
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }
            let current_expr = match parse_temp_assignment(lines[*assign_idx].trim()) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };

            let Some(target_idx) =
                find_single_use_target_in_scope(lines, *assign_idx, var_name, &removed)
            else {
                continue;
            };

            let replacement = substitute_var(lines[target_idx].trim(), var_name, &current_expr);
            let shortens = current_expr.len() + 2 <= var_name.len();
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > MAX_LINE_WIDTH {
                continue;
            }

            // Preserve the consumer's indentation.
            let consumer_indent = &lines[target_idx]
                [..lines[target_idx].len() - lines[target_idx].trim_start().len()];
            lines[target_idx] = format!("{}{}", consumer_indent, replacement);
            removed.insert(*assign_idx);
            inlined_any = true;
        }

        let mut idx = 0;
        lines.retain(|_| {
            let keep = !removed.contains(&idx);
            idx += 1;
            keep
        });
        if !inlined_any {
            break;
        }
    }
}

/// Find the consumer line for `var_name` in the same block or a nested child
/// block as the assignment. Returns `None` when the var is referenced more
/// than once in scope, zero times, or only in a sibling block.
fn find_single_use_target_in_scope(
    lines: &[String],
    assign_idx: usize,
    var_name: &str,
    removed: &HashSet<usize>,
) -> Option<usize> {
    let assign_depth = indent_depth(&lines[assign_idx]);

    let mut depth = assign_depth;
    let mut target = None;
    let mut refs = 0usize;

    for (i, line) in lines.iter().enumerate().skip(assign_idx + 1) {
        if removed.contains(&i) {
            continue;
        }
        let trimmed = line.trim();

        // A closing brace that returns us below the assignment's depth
        // means we've left the scope the assignment lives in.
        if trimmed.starts_with('}') && indent_depth(line) < assign_depth {
            break;
        }

        let count = count_var_refs(trimmed, var_name);
        if count > 0 {
            refs += count;
            if refs > 1 {
                return None;
            }
            if target.is_none() {
                target = Some(i);
            }
        }

        // Track depth transitions so a `} else {` on one line still counts as
        // leaving the original branch.
        if trimmed.starts_with('}') {
            depth = depth.saturating_sub(1);
            if depth < assign_depth {
                break;
            }
        }
        if trimmed.ends_with('{') {
            depth += 1;
        }
    }

    if refs == 1 {
        target
    } else {
        None
    }
}

fn indent_depth(line: &str) -> usize {
    // Treat each 4-space stride as one depth level; tabs count as one each.
    let mut spaces = 0usize;
    for b in line.as_bytes() {
        match b {
            b' ' => spaces += 1,
            b'\t' => spaces += 4,
            _ => break,
        }
    }
    spaces / 4
}

/// Text-based dead-assignment removal for post-structure pipelines.
///
/// Removes `$temp = expr` lines with zero external references.
/// Keeps the RHS expression when it has side effects (function calls).
pub fn discard_unused_assignments_text(lines: &mut Vec<String>) {
    let texts: Vec<&str> = lines.iter().map(|l| l.trim()).collect();
    let ref_counts = count_unused_assignments(&texts);

    for line in lines.iter_mut() {
        if let Some((var, expr)) = parse_temp_assignment(line.trim()) {
            if ref_counts.get(var).copied() == Some(0) {
                if expr_has_call(expr) {
                    *line = expr.to_string();
                } else {
                    line.clear();
                }
            }
        }
    }

    lines.retain(|line| !line.trim().is_empty());
}

/// Resolve constant temp variables from a slice of text lines.
///
/// Shared core for both `inline_constant_temps` (BcStatement) and
/// `inline_constant_temps_text` (Vec<String>). Returns the resolved
/// variable map and the set of assignment indices to remove.
fn resolve_constant_vars(texts: &[&str]) -> Option<(BTreeMap<String, String>, HashSet<usize>)> {
    let mut assignments: HashMap<String, Vec<(usize, String)>> = HashMap::new();
    for (i, text) in texts.iter().enumerate() {
        if let Some((var, expr)) = parse_temp_assignment(text) {
            assignments
                .entry(var.to_string())
                .or_default()
                .push((i, expr.to_string()));
        }
    }

    // Multi-assignment same-value (Select pattern) or single Temp_* assignment
    let mut constant_vars: BTreeMap<String, String> = assignments
        .into_iter()
        .filter(|(var, entries)| {
            let all_same = entries.iter().all(|(_, expr)| *expr == entries[0].1);
            let multi = entries.len() > 1;
            all_same && (multi || var.starts_with("Temp_"))
        })
        .map(|(var, entries)| (var, entries[0].1.clone()))
        .collect();

    if constant_vars.is_empty() {
        return None;
    }

    // Resolve transitively: a constant var's expression may reference another
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

    // Drop circular dependencies (FlipFlop: A = !B, B = A)
    constant_vars.retain(|var, expr| count_var_refs(expr, var) == 0);

    if constant_vars.is_empty() {
        return None;
    }

    let remove_indices: HashSet<usize> = texts
        .iter()
        .enumerate()
        .filter_map(|(i, text)| {
            let (var, _) = parse_temp_assignment(text)?;
            constant_vars.contains_key(var).then_some(i)
        })
        .collect();

    Some((constant_vars, remove_indices))
}

/// Count unreferenced single-assignment temp variables.
///
/// Shared core for both `discard_unused_assignments` variants.
/// Returns a map of variable names to their external reference count (0 = unused).
fn count_unused_assignments(texts: &[&str]) -> HashMap<String, usize> {
    let mut assign_counts: HashMap<String, usize> = HashMap::new();
    for text in texts {
        if let Some((var, _)) = parse_temp_assignment(text) {
            *assign_counts.entry(var.to_string()).or_default() += 1;
        }
    }

    let mut ref_counts: HashMap<String, usize> = HashMap::new();
    for (var, ac) in &assign_counts {
        if *ac != 1 {
            continue;
        }
        let mut total = 0usize;
        for text in texts {
            total += count_var_refs(text, var);
        }
        // total includes the assignment LHS (1 occurrence)
        ref_counts.insert(var.clone(), total.saturating_sub(1));
    }
    ref_counts
}
