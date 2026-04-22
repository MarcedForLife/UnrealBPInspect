use std::collections::HashSet;

use super::super::decode::BcStatement;
use super::super::flow::{parse_if_jump, parse_jump, parse_push_flow};
use super::super::{BLOCK_CLOSE, POP_FLOW, STRUCTURE_OFFSET_TOLERANCE};
use super::transform::alias_removed_offsets;

/// Detect FlipFlop toggle patterns:
/// ```text
/// $Not_PreBool = !Temp_bool_Variable
/// Temp_bool_Variable = $Not_PreBool
/// jump [to branch check]
/// ```
/// Returns `(toggle_var_name, stmt_indices_to_remove)` per detected toggle.
pub(super) fn detect_flipflop_toggle(stmts: &[BcStatement]) -> Vec<(String, Vec<usize>)> {
    let mut toggles = Vec::new();

    for (idx, stmt) in stmts.iter().enumerate() {
        let trimmed = stmt.text.trim();
        let Some((lhs, rhs)) = trimmed.split_once(" = ") else {
            continue;
        };
        let Some(negated_var) = rhs.strip_prefix('!') else {
            continue;
        };
        if !negated_var.starts_with("Temp_bool_Variable") {
            continue;
        }
        let assign_idx = idx + 1;
        if assign_idx >= stmts.len() {
            continue;
        }
        let expected_assign = format!("{} = {}", negated_var, lhs);
        if stmts[assign_idx].text.trim() != expected_assign {
            continue;
        }
        let jump_idx = assign_idx + 1;
        if jump_idx >= stmts.len() || parse_jump(stmts[jump_idx].text.trim()).is_none() {
            continue;
        }

        let branch_if_idx = stmts.iter().enumerate().find_map(|(si, ss)| {
            if let Some((cond, _)) = parse_if_jump(ss.text.trim()) {
                if cond == negated_var {
                    return Some(si);
                }
            }
            None
        });

        let mut indices = vec![idx, assign_idx, jump_idx];
        if let Some(branch_idx) = branch_if_idx {
            indices.push(branch_idx);
        }

        toggles.push((negated_var.to_string(), indices));
    }

    toggles
}

/// Derive a display name for a FlipFlop from its toggle variable.
pub(super) fn derive_flipflop_name(stmts: &[BcStatement], toggle_var: &str) -> String {
    let assign_pattern = format!(" = {}", toggle_var);
    for stmt in stmts {
        let trimmed = stmt.text.trim();
        if let Some(lhs) = trimmed.strip_suffix(&assign_pattern) {
            if let Some(field) = lhs.strip_prefix("self.") {
                return field.to_string();
            }
        }
    }
    if let Some(rest) = toggle_var.strip_prefix("$FlipFlop_") {
        if let Some(name) = rest.strip_suffix("_IsA") {
            return name.to_string();
        }
    }
    toggle_var
        .strip_prefix("Temp_bool_Variable")
        .unwrap_or("")
        .trim_start_matches('_')
        .to_string()
}

/// Rename `Temp_bool_Variable` references to `$FlipFlop_<name>_IsA` for readability.
pub(super) fn rename_flipflop_refs(stmts: &mut [BcStatement], toggle_var: &str, name: &str) {
    let display_name = format!("$FlipFlop_{}_IsA", name);
    for stmt in stmts.iter_mut() {
        if stmt.text.contains(toggle_var) {
            stmt.text = stmt.text.replace(toggle_var, &display_name);
        }
    }
}

/// Collapse FlipFlops where both A and B branches converge on the same body.
/// Replaces toggle+branch scaffolding with `FlipFlop(name) {` + `A|B: {` and
/// rewrites the body-end pop_flow as a closing brace.
pub(super) fn collapse_converged_flipflops(
    stmts: &mut Vec<BcStatement>,
    flipflop_names: &[(String, String)],
) {
    let offset_map = super::super::OffsetMap::build(stmts);
    let toggles = detect_flipflop_toggle(stmts);
    if toggles.is_empty() {
        return;
    }

    let mut remove = vec![false; stmts.len()];
    let mut body_end_replacements: Vec<(usize, String)> = Vec::new();

    for (toggle_var, indices) in &toggles {
        let Some(branch_idx) = stmts.iter().enumerate().find_map(|(si, ss)| {
            let (cond, _) = parse_if_jump(ss.text.trim())?;
            (cond == toggle_var.as_str()).then_some(si)
        }) else {
            continue;
        };

        let (_, branch_target) = parse_if_jump(stmts[branch_idx].text.trim()).unwrap();

        // A-path: fallthrough from branch, expected to be a bare jump.
        let a_idx = branch_idx + 1;
        if a_idx >= stmts.len() {
            continue;
        }
        let Some(a_target) = parse_jump(stmts[a_idx].text.trim()) else {
            continue;
        };

        // B-path: branch's jump target, also expected to be a bare jump.
        let Some(b_idx) = offset_map.find_fuzzy_forward(branch_target, STRUCTURE_OFFSET_TOLERANCE)
        else {
            continue;
        };
        let Some(b_target) = parse_jump(stmts[b_idx].text.trim()) else {
            continue;
        };

        if a_target != b_target {
            continue;
        }

        let negate_idx = indices[0];
        let store_idx = indices[1];
        let jump_to_branch_idx = indices[2];

        let display_name = flipflop_names
            .iter()
            .find(|(var, _)| var == toggle_var)
            .map(|(_, name)| name.as_str())
            .unwrap_or("FlipFlop");

        stmts[negate_idx].text = format!("FlipFlop({}) {{", display_name);
        stmts[store_idx].text = "A|B: {".to_string();
        stmts[jump_to_branch_idx].text = format!("jump 0x{:x}", a_target);
        remove[branch_idx] = true;
        remove[a_idx] = true;
        remove[b_idx] = true;

        // FlipFlop needs two closers: one for `A|B: {` and one for `FlipFlop(name) {`.
        if let Some(body_start_idx) =
            offset_map.find_fuzzy_forward(a_target, STRUCTURE_OFFSET_TOLERANCE)
        {
            let mut depth = 0i32;
            for body_idx in body_start_idx..stmts.len() {
                if remove[body_idx] {
                    continue;
                }
                let body_text = stmts[body_idx].text.trim();
                if parse_push_flow(body_text).is_some() {
                    depth += 1;
                } else if body_text == POP_FLOW {
                    if depth > 0 {
                        depth -= 1;
                    } else {
                        body_end_replacements.push((body_idx, BLOCK_CLOSE.to_string()));
                        break;
                    }
                }
            }
        }
    }

    for (idx, text) in &body_end_replacements {
        if *idx < stmts.len() {
            stmts[*idx].text = text.clone();
            remove[*idx] = false;
        }
    }

    if !remove.iter().any(|&r| r) && body_end_replacements.is_empty() {
        return;
    }

    alias_removed_offsets(stmts, &remove);

    // Insert the extra `}` right after each FlipFlop body-end.
    let body_end_set: HashSet<usize> = body_end_replacements.iter().map(|(idx, _)| *idx).collect();
    let mut new_stmts: Vec<BcStatement> = Vec::with_capacity(stmts.len());
    for (idx, stmt) in stmts.iter().enumerate() {
        if remove[idx] {
            continue;
        }
        new_stmts.push(stmt.clone());
        if body_end_set.contains(&idx) {
            new_stmts.push(BcStatement::new(stmt.mem_offset, BLOCK_CLOSE.to_string()));
        }
    }
    *stmts = new_stmts;
}

/// Pre-compute FlipFlop toggle names from the full UberGraph statement list.
/// Must run before CFG partitioning, because the `self.X = Temp_bool_Variable`
/// assignment that `derive_flipflop_name` needs can end up in a different
/// event than the toggle pattern.
pub fn precompute_flipflop_names(stmts: &[BcStatement]) -> Vec<(String, String)> {
    detect_flipflop_toggle(stmts)
        .iter()
        .map(|(var, _)| {
            let name = derive_flipflop_name(stmts, var);
            (var.clone(), name)
        })
        .collect()
}
