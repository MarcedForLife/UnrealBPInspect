//! Temp variable inlining and dead assignment removal.

use super::{
    count_var_refs, expr_has_call, is_trivial_expr, parse_temp_assignment, substitute_var,
};
use crate::bytecode::decode::BcStatement;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Collect all bytecode offsets that are targets of if-jumps.
/// Used to protect these offsets from being lost when inline passes remove statements.
pub fn collect_jump_targets(stmts: &[BcStatement]) -> HashSet<usize> {
    let mut targets = HashSet::new();
    for stmt in stmts {
        if let Some(pos) = stmt.text.rfind(") jump 0x") {
            if let Ok(target) = usize::from_str_radix(&stmt.text[pos + 9..], 16) {
                targets.insert(target);
            }
        }
    }
    targets
}

/// Collect all `(statement_index, var_name, expression)` tuples from temp assignments.
fn collect_temp_assignments(stmts: &[BcStatement]) -> Vec<(usize, String, String)> {
    stmts
        .iter()
        .enumerate()
        .filter_map(|(i, s)| {
            let (var, expr) = parse_temp_assignment(&s.text)?;
            Some((i, var.to_string(), expr.to_string()))
        })
        .collect()
}

/// Re-verify each substitution candidate against current statement text, then apply.
/// Each entry is `(assign_idx, var_name, expr)`. The expr is re-read from the statement
/// in case earlier substitutions modified it.
fn apply_temp_substitutions(
    stmts: &mut Vec<BcStatement>,
    to_inline: &[(usize, String, String)],
    max_line: Option<usize>,
) -> bool {
    let mut removed: Vec<usize> = Vec::new();
    let mut inlined_any = false;

    for (assign_idx, var_name, _) in to_inline {
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

        // Bypass max_line for trivial expressions (property chains, $temp refs, literals)
        if let Some(limit) = max_line {
            let shortens = current_expr.len() + 2 <= var_name.len(); // +2 for possible (...)
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > limit {
                continue;
            }
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

    inlined_any
}

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
        let assignments = collect_temp_assignments(stmts);

        // Count how many times each var name is assigned
        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var_name, _) in &assignments {
            *assign_counts.entry(var_name.as_str()).or_default() += 1;
        }

        // Filter to single-assignment, single-reference candidates
        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var_name, expr) in &assignments {
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

        if !apply_temp_substitutions(stmts, &to_inline, Some(MAX_LINE)) {
            break;
        }
    }
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
    // - Multi-assignment (any prefix): UE Select pattern re-assigns before each use
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

    // Drop vars whose resolved expression still references themselves
    // (circular dependencies like FlipFlop: A = !B, B = A).
    constant_vars.retain(|var, expr| count_var_refs(expr, var) == 0);

    if constant_vars.is_empty() {
        return;
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

    // Transfer mem_offsets from removed statements to the next surviving
    // statement when the removed offset is a known jump target. This keeps
    // the OffsetMap entry alive so the structurer can resolve else branches.
    let mut pending_offset: Option<usize> = None;
    for (i, stmt) in stmts.iter_mut().enumerate() {
        if remove_indices.contains(&i) {
            let off = stmt.mem_offset;
            if off > 0
                && jump_targets.contains(&off)
                && (pending_offset.is_none() || off < pending_offset.unwrap())
            {
                pending_offset = Some(off);
            }
        } else if let Some(off) = pending_offset.take() {
            if off < stmt.mem_offset {
                stmt.mem_offset = off;
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
