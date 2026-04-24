use std::collections::HashSet;

use super::super::decode::BcStatement;
use super::super::{POP_FLOW, STRUCTURE_OFFSET_TOLERANCE};
use super::{GATE_PREFIX, INIT_PREFIX};

pub(super) struct InitBlock {
    pub(super) init_var: String,
    pub(super) gate_var: String,
    /// Statement indices to remove.
    pub(super) stmt_indices: Vec<usize>,
}

/// Detect latch init blocks. Two layouts depending on whether UE placed the
/// init body before or after the init check:
///
/// Layout A (backward jump, body before check):
/// ```text
/// Has_Been_Initd_N = true; pop_flow_if_not(const);
/// IsClosed_M = true; pop_flow;
/// ... if !(Has_Been_Initd_N) jump [backward]; pop_flow
/// ```
///
/// Layout B (forward jump, body after check):
/// ```text
/// if !(Has_Been_Initd_N) jump [forward]; pop_flow;
/// Has_Been_Initd_N = true; pop_flow_if_not(const);
/// IsClosed_M = true; pop_flow
/// ```
pub(super) fn detect_init_blocks(stmts: &[BcStatement]) -> Vec<InitBlock> {
    let mut blocks = Vec::new();

    for (idx, stmt) in stmts.iter().enumerate() {
        let Some((cond, _target)) = stmt.if_jump() else {
            continue;
        };
        if !cond.starts_with(INIT_PREFIX) {
            continue;
        }
        let init_var = cond.to_string();
        let init_assign_target = format!("{} = true", init_var);

        // Layout A (before if-jump) vs Layout B (after). Validate candidate:
        // next statement must be pop_flow_if_not.
        let backward_assign = (0..idx)
            .rev()
            .find(|&si| stmts[si].text.trim() == init_assign_target);
        let forward_assign = ((idx + 1)..stmts.len().min(idx + 5))
            .find(|&si| stmts[si].text.trim() == init_assign_target);

        let init_assign = [backward_assign, forward_assign]
            .into_iter()
            .flatten()
            .find(|&candidate| {
                let pfn = candidate + 1;
                pfn < stmts.len() && stmts[pfn].pop_flow_if_not_cond().is_some()
            });
        let Some(init_assign) = init_assign else {
            continue;
        };

        let pfn_idx = init_assign + 1;
        if pfn_idx >= stmts.len() {
            continue;
        }
        if stmts[pfn_idx].pop_flow_if_not_cond().is_none() {
            continue;
        }

        let gate_assign_idx = pfn_idx + 1;
        if gate_assign_idx >= stmts.len() {
            continue;
        }
        let gate_trimmed = stmts[gate_assign_idx].text.trim();
        let Some((gate_var, gate_val)) = gate_trimmed.split_once(" = ") else {
            continue;
        };
        if !gate_var.starts_with(GATE_PREFIX) || gate_val != "true" {
            continue;
        }
        let gate_var = gate_var.to_string();

        let final_pop_idx = gate_assign_idx + 1;
        if final_pop_idx >= stmts.len() || stmts[final_pop_idx].text.trim() != POP_FLOW {
            continue;
        }

        let mut stmt_indices = vec![init_assign, pfn_idx, gate_assign_idx, final_pop_idx, idx];

        // Layout A tail: pop_flow after the if-jump, plus optional push_flow/jump wrapper.
        let after_if_pop = idx + 1;
        if after_if_pop < stmts.len() && stmts[after_if_pop].text.trim() == POP_FLOW {
            stmt_indices.push(after_if_pop);

            let wrapper_start = after_if_pop + 1;
            if wrapper_start + 1 < stmts.len()
                && stmts[wrapper_start].push_flow_target().is_some()
                && stmts[wrapper_start + 1].jump_target().is_some()
            {
                stmt_indices.push(wrapper_start);
                stmt_indices.push(wrapper_start + 1);
            }
        }

        stmt_indices.sort();
        stmt_indices.dedup();

        blocks.push(InitBlock {
            init_var,
            gate_var,
            stmt_indices,
        });
    }

    blocks
}

/// UE math/library prefixes skipped when deriving a DoOnce display name
/// (common in latch bodies, but don't describe the action).
const LIBRARY_FUNC_PREFIXES: &[&str] = &[
    "Select",
    "Multiply_",
    "Add_",
    "Subtract_",
    "Divide_",
    "Abs",
    "FClamp",
    "MakeVector",
    "MakeRotator",
    "MakeTransform",
    "BreakVector",
    "BreakRotator",
    "ComposeRotators",
    "VSize",
    "Normalize",
    "GetPlayerController",
    "GetPlayerCameraManager",
    "GetWorldDeltaSeconds",
    "IsValid",
    "PrintString",
];

/// Derive a display name for a DoOnce from its body: scan forward for the
/// first meaningful call, skipping UE library/math utilities. Fall back to
/// the gate variable suffix.
pub(super) fn derive_doonce_name(
    stmts: &[BcStatement],
    body_start: usize,
    gate_var: &str,
    offset_map: &super::super::OffsetMap,
) -> String {
    // Follow bare jumps: UberGraph gate-close can jump backward to a body at
    // lower offsets, so a linear scan from the trampoline finds nothing.
    let mut scan_start = body_start;
    let mut jump_visited: HashSet<usize> = HashSet::new();
    while scan_start < stmts.len() && jump_visited.insert(scan_start) {
        if stmts[scan_start].push_flow_target().is_some() {
            break;
        }
        if let Some(target) = stmts[scan_start].jump_target() {
            if let Some(target_idx) =
                offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                scan_start = target_idx;
                continue;
            }
        }
        break;
    }

    let mut first_call = None;

    for stmt in stmts.iter().skip(scan_start) {
        let trimmed = stmt.text.trim();
        if trimmed.starts_with(GATE_PREFIX)
            || trimmed.starts_with(INIT_PREFIX)
            || trimmed == POP_FLOW
            || trimmed.starts_with("pop_flow_if_not(")
        {
            continue;
        }
        if (trimmed.starts_with('$') || trimmed.starts_with("self.")) && !trimmed.contains('(') {
            continue; // non-call assignment
        }
        if stmt.jump_target().is_some() || stmt.push_flow_target().is_some() {
            break;
        }
        if let Some(paren_pos) = trimmed.find('(') {
            let call_part = &trimmed[..paren_pos];
            // Strip assignment prefix ("$var = FuncCall" -> "FuncCall").
            let func_part = call_part
                .rfind(" = ")
                .map_or(call_part, |eq| &call_part[eq + 3..])
                .trim();
            if func_part.is_empty()
                || func_part.starts_with(GATE_PREFIX)
                || func_part.starts_with(INIT_PREFIX)
            {
                continue;
            }
            // Strip object prefix ("self.Obj.Method" -> "Method").
            let func_name = func_part
                .rfind('.')
                .map_or(func_part, |dot| &func_part[dot + 1..]);
            let is_library = LIBRARY_FUNC_PREFIXES
                .iter()
                .any(|prefix| func_name.starts_with(prefix));
            if !is_library {
                return func_name.to_string();
            }
            if first_call.is_none() {
                first_call = Some(func_name.to_string());
            }
        }
    }
    // Fallback order: first (library) call, then gate-var suffix.
    first_call.unwrap_or_else(|| {
        let suffix = gate_var
            .strip_prefix(GATE_PREFIX)
            .unwrap_or("")
            .trim_start_matches('_');
        if suffix.is_empty() {
            "DoOnce".to_string()
        } else {
            format!("DoOnce_{}", suffix)
        }
    })
}
