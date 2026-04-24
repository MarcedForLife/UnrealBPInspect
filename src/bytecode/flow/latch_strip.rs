//! Pre-structuring latch boilerplate strip. Removes DoOnce/FlipFlop bookkeeping
//! (`Temp_bool_IsClosed_*`, `Temp_bool_Has_Been_Initd_*`) and their wrapping
//! push_flow/jump pairs before structuring runs.
//!
//! Separate from `latch/transform.rs`'s same-named helpers: those trim text,
//! track surviving-statement jump targets, and take a replacements map; this
//! pass runs before any rewrites so it can stay simpler.

use std::collections::HashSet;

use super::super::decode::{BcStatement, StmtKind};

/// Strip FlipFlop/DoOnce latch boilerplate from raw bytecode.
///
/// These nodes compile to `Temp_bool_IsClosed_Variable*` (gate state) and
/// `Temp_bool_Has_Been_Initd_Variable*` (first-exec flag) plus push_flow /
/// pop_flow scope boundaries. State is node-internal and not meaningful for
/// pseudocode; stripping before flow reordering keeps the pop_flow boundaries
/// from fragmenting the event body.
pub fn strip_latch_boilerplate(stmts: &mut Vec<BcStatement>) {
    let latch_vars = collect_latch_vars(stmts);
    if latch_vars.is_empty() {
        return;
    }

    let mut remove = vec![false; stmts.len()];
    mark_latch_stmts(stmts, &latch_vars, &mut remove);
    mark_latch_wrappers(stmts, &mut remove);
    mark_orphaned_pop_flows(stmts, &mut remove);

    let mut kept_idx = 0;
    stmts.retain(|_| {
        let keep = !remove[kept_idx];
        kept_idx += 1;
        keep
    });
}

/// Collect latch-variable names from assignment statements.
fn collect_latch_vars(stmts: &[BcStatement]) -> HashSet<String> {
    let mut vars = HashSet::new();
    for stmt in stmts {
        if let Some((var, _)) = stmt.text.trim().split_once(" = ") {
            if var.starts_with("Temp_bool_IsClosed_Variable")
                || var.starts_with("Temp_bool_Has_Been_Initd_Variable")
            {
                vars.insert(var.to_string());
            }
        }
    }
    vars
}

/// Mark latch-var assignments, conditional jumps on latch vars (plus the
/// trailing pop_flow), and constant-condition gates for removal.
fn mark_latch_stmts(stmts: &[BcStatement], latch_vars: &HashSet<String>, remove: &mut [bool]) {
    for (idx, stmt) in stmts.iter().enumerate() {
        let trimmed = stmt.text.trim();

        if let Some((var, _)) = trimmed.split_once(" = ") {
            if latch_vars.contains(var) {
                remove[idx] = true;
                continue;
            }
        }

        if let Some((cond, _)) = stmt.if_jump() {
            if latch_vars.contains(cond) {
                remove[idx] = true;
                if idx + 1 < stmts.len() && stmts[idx + 1].kind == StmtKind::PopFlow {
                    remove[idx + 1] = true;
                }
                continue;
            }
        }

        if trimmed == "pop_flow_if_not(true)" || trimmed == "pop_flow_if_not(false)" {
            remove[idx] = true;
        }
    }
}

/// Mark push_flow/jump wrapper pairs whose target is already-removed (the
/// wrapper belonged to the stripped latch node).
fn mark_latch_wrappers(stmts: &[BcStatement], remove: &mut [bool]) {
    for idx in 0..stmts.len().saturating_sub(1) {
        if remove[idx] || stmts[idx].push_flow_target().is_none() {
            continue;
        }
        let Some(jump_target) = stmts[idx + 1].jump_target() else {
            continue;
        };
        let targets_removed = stmts
            .iter()
            .enumerate()
            .any(|(j, s)| remove[j] && s.mem_offset > 0 && s.mem_offset.abs_diff(jump_target) <= 4);
        if targets_removed {
            remove[idx] = true;
            remove[idx + 1] = true;
        }
    }
}

/// Mark pop_flow statements that became empty scope boundaries after
/// boilerplate removal (nearest preceding kept statement is itself pop_flow,
/// or nothing precedes).
fn mark_orphaned_pop_flows(stmts: &[BcStatement], remove: &mut [bool]) {
    for idx in 0..stmts.len() {
        if remove[idx] || stmts[idx].kind != StmtKind::PopFlow {
            continue;
        }
        let prev_kept = (0..idx).rev().find(|&j| !remove[j]);
        let orphaned = match prev_kept {
            Some(prev) => stmts[prev].kind == StmtKind::PopFlow,
            None => true,
        };
        if orphaned {
            remove[idx] = true;
        }
    }
}
