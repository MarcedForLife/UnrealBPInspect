//! DoOnce and FlipFlop latch node transformation.
//!
//! Replaces raw latch bytecode with structured pseudocode (`DoOnce(name) {`,
//! `ResetDoOnce(name)`, `FlipFlop(name) { A|B: { ... } }`). Runs after CFG
//! partitioning in the ubergraph pipeline, per-event, so each event's latch
//! patterns are transformed in isolation without cross-event interference.
//!
//! DoOnce compiles to two hidden vars per instance:
//! - `Temp_bool_IsClosed_Variable[_N]` (gate, true = closed/already fired)
//! - `Temp_bool_Has_Been_Initd_Variable[_M]` (first-execution flag)
//!
//! The init block checks `Has_Been_Initd`, sets it true, then conditionally
//! sets `IsClosed` based on the "Start Closed" parameter. The gate block checks
//! `IsClosed` and jumps past the body when closed. After the gate check, the gate
//! is immediately closed (`IsClosed = true`), then the body executes. Resets
//! elsewhere set `IsClosed = false`.
//!
//! FlipFlop adds a `Temp_bool_Variable` toggle (IsA flag) that gets negated
//! each execution, with branches for A and B paths.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use super::decode::BcStatement;
use super::flow::{parse_if_jump, parse_jump, parse_pop_flow_if_not, parse_push_flow};
use super::POP_FLOW;

const GATE_PREFIX: &str = "Temp_bool_IsClosed_Variable";
const INIT_PREFIX: &str = "Temp_bool_Has_Been_Initd_Variable";

/// An init check block pairing an init variable with its gate variable.
struct InitBlock {
    init_var: String,
    gate_var: String,
    /// Statement indices belonging to this init block (to be removed)
    stmt_indices: Vec<usize>,
}

/// Detect latch-related init blocks from the raw bytecode.
///
/// Two layouts exist depending on whether UE placed the init body before or
/// after the init check:
///
/// Layout A (backward jump, init body before check):
/// ```text
/// Has_Been_Initd_Variable_N = true
/// pop_flow_if_not(true|false)
/// IsClosed_Variable_M = true
/// pop_flow
/// ...
/// if !(Has_Been_Initd_Variable_N) jump [backward to init body]
/// pop_flow
/// ```
///
/// Layout B (forward jump, init body after check):
/// ```text
/// if !(Has_Been_Initd_Variable_N) jump [forward past pop_flow to init body]
/// pop_flow                              <- already-initialized exit
/// Has_Been_Initd_Variable_N = true
/// pop_flow_if_not(true|false)
/// IsClosed_Variable_M = true
/// pop_flow
/// ```
fn detect_init_blocks(stmts: &[BcStatement]) -> Vec<InitBlock> {
    let mut blocks = Vec::new();

    for (idx, stmt) in stmts.iter().enumerate() {
        let trimmed = stmt.text.trim();
        let Some((cond, _target)) = parse_if_jump(trimmed) else {
            continue;
        };
        if !cond.starts_with(INIT_PREFIX) {
            continue;
        }
        let init_var = cond.to_string();
        let init_assign_target = format!("{} = true", init_var);

        // Try Layout A: init assign BEFORE the if-jump (backward jump)
        let backward_assign = (0..idx)
            .rev()
            .find(|&si| stmts[si].text.trim() == init_assign_target);

        // Try Layout B: init assign AFTER the if-jump (forward jump)
        let forward_assign = ((idx + 1)..stmts.len().min(idx + 5))
            .find(|&si| stmts[si].text.trim() == init_assign_target);

        // Validate each candidate: the statement after init_assign must be
        // pop_flow_if_not. Try backward first, fall back to forward.
        let init_assign = [backward_assign, forward_assign]
            .into_iter()
            .flatten()
            .find(|&candidate| {
                let pfn = candidate + 1;
                pfn < stmts.len() && parse_pop_flow_if_not(stmts[pfn].text.trim()).is_some()
            });
        let Some(init_assign) = init_assign else {
            continue;
        };

        // After init_assign: pop_flow_if_not(true|false)
        let pfn_idx = init_assign + 1;
        if pfn_idx >= stmts.len() {
            continue;
        }
        if parse_pop_flow_if_not(stmts[pfn_idx].text.trim()).is_none() {
            continue;
        }

        // After pop_flow_if_not: IsClosed_Y = true
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

        // After gate assign: pop_flow
        let final_pop_idx = gate_assign_idx + 1;
        if final_pop_idx >= stmts.len() || stmts[final_pop_idx].text.trim() != POP_FLOW {
            continue;
        }

        let mut stmt_indices = vec![init_assign, pfn_idx, gate_assign_idx, final_pop_idx, idx];

        // For Layout A: the pop_flow after the if-jump and optional push_flow/jump wrapper
        let after_if_pop = idx + 1;
        if after_if_pop < stmts.len() && stmts[after_if_pop].text.trim() == POP_FLOW {
            // Only add if this pop_flow is separate from the init body
            // (in Layout B, the pop_flow after if-jump is the "already initialized" exit)
            stmt_indices.push(after_if_pop);

            // Optional push_flow/jump wrapper
            let wrapper_start = after_if_pop + 1;
            if wrapper_start + 1 < stmts.len()
                && parse_push_flow(stmts[wrapper_start].text.trim()).is_some()
                && parse_jump(stmts[wrapper_start + 1].text.trim()).is_some()
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

/// Detect FlipFlop toggle patterns.
///
/// ```text
/// $Not_PreBool = !Temp_bool_Variable
/// Temp_bool_Variable = $Not_PreBool
/// jump [to branch check]
/// ```
/// Returns Vec<(toggle_var_name, statement_indices_to_remove)>.
fn detect_flipflop_toggle(stmts: &[BcStatement]) -> Vec<(String, Vec<usize>)> {
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

        // Find the branch check: `if !(toggle_var) jump 0xXXX`
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

/// UE math/library function prefixes that should not be used as DoOnce names.
/// These are common in latch bodies but don't describe the action.
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

/// Derive a human-readable name for a DoOnce instance from its body.
///
/// Scans forward from the gate close to find the first meaningful function call,
/// skipping UE library/math utilities. Falls back to the gate variable suffix.
fn derive_doonce_name(
    stmts: &[BcStatement],
    body_start: usize,
    gate_var: &str,
    offset_map: &super::OffsetMap,
) -> String {
    // Follow bare jumps from body_start to reach the actual body code.
    // In UberGraph events, the gate close jumps backward to the body at
    // lower offsets. Without following the jump, name derivation scans
    // from the trampoline and finds nothing meaningful.
    let mut scan_start = body_start;
    let mut jump_visited: HashSet<usize> = HashSet::new();
    while scan_start < stmts.len() && jump_visited.insert(scan_start) {
        let trimmed = stmts[scan_start].text.trim();
        if parse_push_flow(trimmed).is_some() {
            break;
        }
        if let Some(target) = parse_jump(trimmed) {
            if let Some(target_idx) = offset_map.find_fuzzy_forward(target, 8) {
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
        // Skip non-call assignments
        if (trimmed.starts_with('$') || trimmed.starts_with("self.")) && !trimmed.contains('(') {
            continue;
        }
        // Stop scanning at control flow boundaries
        if parse_jump(trimmed).is_some() || parse_push_flow(trimmed).is_some() {
            break;
        }
        if let Some(paren_pos) = trimmed.find('(') {
            let call_part = &trimmed[..paren_pos];
            // Strip assignment prefix: "$var = FuncCall" -> "FuncCall"
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
            // Strip object prefix: "self.Obj.Method" -> "Method"
            let func_name = func_part
                .rfind('.')
                .map_or(func_part, |dot| &func_part[dot + 1..]);
            // Skip UE library functions, but remember the first call as fallback
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
    // Fall back to first call (even if library), then to gate var suffix
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

/// Derive a human-readable name for a FlipFlop instance from its toggle variable.
fn derive_flipflop_name(stmts: &[BcStatement], toggle_var: &str) -> String {
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

/// Follow bare jumps from a body-entry position to reach the first real
/// statement of a DoOnce body. Returns the resolved statement index, or
/// `None` if jumps can't be resolved within tolerance.
///
/// Used to identify each gate's body entry point so other gates' body walks
/// can stop before crossing into it.
fn resolve_body_entry(
    stmts: &[BcStatement],
    body_start: usize,
    offset_map: &super::OffsetMap,
) -> Option<usize> {
    let mut pos = body_start;
    let mut visited: HashSet<usize> = HashSet::new();
    while pos < stmts.len() && visited.insert(pos) {
        let text = stmts[pos].text.trim();
        if parse_push_flow(text).is_some() {
            return Some(pos);
        }
        if let Some(target) = parse_jump(text) {
            if let Some(next) = offset_map.find_fuzzy_forward(target, 8) {
                pos = next;
                continue;
            }
            return None;
        }
        return Some(pos);
    }
    None
}

/// Transform DoOnce and FlipFlop latch patterns into structured pseudocode.
///
/// The gate check pattern in raw bytecode is:
/// ```text
/// if !(gate_var) jump PAST       <- skip when gate is closed
/// pop_flow                        <- exit for closed path
/// [init block if present]         <- first-run initialization (removed separately)
/// gate_var = true                 <- close gate immediately (before body)
/// ... body ...                    <- actual DoOnce body code
/// pop_flow                        <- body end
/// ```
///
/// This function replaces the gate check with `DoOnce(name) {`, removes the
/// skip-path pop_flow and the gate close assignment, and directly replaces
/// body-end pop_flows with `}`. Gate resets become `ResetDoOnce(name)`.
fn transform_latches(stmts: &mut Vec<BcStatement>) {
    let init_blocks = detect_init_blocks(stmts);
    if init_blocks.is_empty() {
        return;
    }

    // Collect all init block statement indices
    let init_block_indices: HashSet<usize> = init_blocks
        .iter()
        .flat_map(|b| b.stmt_indices.iter().copied())
        .collect();

    // Collect gate_var -> init_var mapping
    let gate_to_init_var: BTreeMap<String, String> = init_blocks
        .iter()
        .map(|b| (b.gate_var.clone(), b.init_var.clone()))
        .collect();

    let gate_vars: BTreeSet<String> = gate_to_init_var.keys().cloned().collect();
    let init_vars: BTreeSet<String> = gate_to_init_var.values().cloned().collect();

    // For each gate variable, find gate checks and derive names.
    // Gate check: `if !(gate_var) jump 0xXXX` + pop_flow + ... + gate_var = true
    // The "close" assignment (gate = true) is the first one after the pop_flow
    // that is NOT inside an init block.
    struct GateSite {
        if_idx: usize,
        pop_idx: usize,
        close_idx: Option<usize>,
        body_start: usize,
        body_end: Option<usize>,
        body_path: Vec<usize>,
    }

    let mut gate_sites: BTreeMap<String, Vec<GateSite>> = BTreeMap::new();

    for gate_var in &gate_vars {
        let close_pattern = format!("{} = true", gate_var);
        let mut sites = Vec::new();

        for (idx, stmt) in stmts.iter().enumerate() {
            let trimmed = stmt.text.trim();
            let Some((cond, _target)) = parse_if_jump(trimmed) else {
                continue;
            };
            if cond != gate_var.as_str() {
                continue;
            }
            let pop_idx = idx + 1;
            if pop_idx >= stmts.len() || stmts[pop_idx].text.trim() != POP_FLOW {
                continue;
            }

            // Find the close assignment: first `gate_var = true` after pop_idx
            // that is NOT inside an init block.
            let close_idx = ((pop_idx + 1)..stmts.len()).find(|&si| {
                stmts[si].text.trim() == close_pattern && !init_block_indices.contains(&si)
            });

            let body_start = close_idx.map_or(pop_idx + 1, |ci| ci + 1);

            sites.push(GateSite {
                if_idx: idx,
                pop_idx,
                close_idx,
                body_start,
                body_end: None,
                body_path: Vec::new(),
            });
        }
        gate_sites.insert(gate_var.clone(), sites);
    }

    let offset_map = super::OffsetMap::build(stmts);

    // Derive names for each gate variable from the first gate site's body
    let mut gate_names: BTreeMap<String, String> = BTreeMap::new();
    for (gate_var, sites) in &gate_sites {
        let name = if let Some(first_site) = sites.first() {
            derive_doonce_name(stmts, first_site.body_start, gate_var, &offset_map)
        } else {
            gate_var
                .strip_prefix(GATE_PREFIX)
                .unwrap_or("")
                .trim_start_matches('_')
                .to_string()
        };
        gate_names.insert(gate_var.clone(), name);
    }

    // Build removal and replacement maps
    let mut remove = vec![false; stmts.len()];
    let mut replacements: BTreeMap<usize, String> = BTreeMap::new();
    let mut body_end_indices: HashSet<usize> = HashSet::new();

    // Remove all init block statements
    for &idx in &init_block_indices {
        if idx < remove.len() {
            remove[idx] = true;
        }
    }

    // Pre-compute each site's body-entry index and the set of gate-check
    // indices so walks can stop at foreign gate boundaries. Without these
    // bounds, interleaved DoOnce bodies in UberGraph events get pulled into
    // each other's body_path and duplicated during relocation.
    let mut site_entries: BTreeMap<(String, usize), usize> = BTreeMap::new();
    let mut all_gate_checks: HashSet<usize> = HashSet::new();
    for (gate_var, sites) in &gate_sites {
        for (si, site) in sites.iter().enumerate() {
            all_gate_checks.insert(site.if_idx);
            if let Some(entry) = resolve_body_entry(stmts, site.body_start, &offset_map) {
                site_entries.insert((gate_var.clone(), si), entry);
            }
        }
    }
    let all_body_entries: HashSet<usize> = site_entries.values().copied().collect();

    // Transform gate checks into DoOnce blocks
    for (gate_var, sites) in &mut gate_sites {
        let name = &gate_names[gate_var];

        for (site_idx, site) in sites.iter_mut().enumerate() {
            replacements.insert(site.if_idx, format!("DoOnce({}) {{", name));
            remove[site.pop_idx] = true;
            if let Some(close_idx) = site.close_idx {
                remove[close_idx] = true;
            }

            let own_entry = site_entries.get(&(gate_var.clone(), site_idx)).copied();
            // Find the body-end pop_flow by following bare jumps (CFG walk).
            // When DoOnce body code is at lower offsets than the gate check
            // (backward jumps in UberGraph events), the linear forward scan
            // misses the body. The CFG walk follows jump targets to reach it.
            {
                let mut pos = site.body_start;
                let mut depth = 0i32;
                let mut walk_visited: HashSet<usize> = HashSet::new();
                let mut body_path: Vec<usize> = Vec::new();

                loop {
                    if pos >= stmts.len() || !walk_visited.insert(pos) {
                        break;
                    }
                    // Foreign-boundary stop: another gate's check or body
                    // entry. Crossing either means our linear walk has left
                    // this DoOnce's extent.
                    let is_own_entry = own_entry == Some(pos);
                    let hit_foreign_entry = all_body_entries.contains(&pos) && !is_own_entry;
                    let hit_foreign_check = all_gate_checks.contains(&pos) && pos != site.if_idx;
                    if hit_foreign_entry || hit_foreign_check {
                        break;
                    }
                    if remove[pos] || init_block_indices.contains(&pos) {
                        pos += 1;
                        continue;
                    }
                    let body_text = stmts[pos].text.trim().to_string();

                    if parse_push_flow(&body_text).is_none() {
                        if let Some(target) = parse_jump(&body_text) {
                            if let Some(target_pos) = offset_map.find_fuzzy_forward(target, 8) {
                                pos = target_pos;
                                continue;
                            }
                            break;
                        }
                    }

                    if parse_push_flow(&body_text).is_some() {
                        body_path.push(pos);
                        depth += 1;
                        pos += 1;
                        continue;
                    }
                    if body_text == POP_FLOW {
                        if depth > 0 {
                            body_path.push(pos);
                            depth -= 1;
                            pos += 1;
                            continue;
                        }
                        replacements.insert(pos, "}".to_string());
                        body_end_indices.insert(pos);
                        site.body_end = Some(pos);
                        break;
                    }
                    body_path.push(pos);
                    pos += 1;
                }
                site.body_path = body_path;
            }
        }

        // Transform resets: `gate_var = false` -> `ResetDoOnce(name)`
        let reset_pattern = format!("{} = false", gate_var);
        for (idx, stmt) in stmts.iter().enumerate() {
            if stmt.text.trim() == reset_pattern {
                replacements.insert(idx, format!("ResetDoOnce({})", name));
            }
        }
    }

    // Remove init-related assignments outside detected init blocks
    for (idx, stmt) in stmts.iter().enumerate() {
        if remove[idx] || replacements.contains_key(&idx) {
            continue;
        }
        let trimmed = stmt.text.trim();
        if let Some((var, val)) = trimmed.split_once(" = ") {
            if init_vars.contains(var) && val == "true" {
                remove[idx] = true;
            }
        }
    }

    // Apply replacements
    for (&idx, text) in &replacements {
        if idx < stmts.len() {
            stmts[idx].text = text.clone();
            remove[idx] = false;
        }
    }

    // Remove push_flow/jump wrappers targeting removed statements
    mark_latch_wrappers(stmts, &mut remove);

    // Remove orphaned pop_flows
    mark_orphaned_pop_flows(stmts, &mut remove, &replacements);

    // Remove constant-condition gates
    for (idx, stmt) in stmts.iter().enumerate() {
        if !remove[idx] {
            let trimmed = stmt.text.trim();
            if trimmed == "pop_flow_if_not(true)" || trimmed == "pop_flow_if_not(false)" {
                remove[idx] = true;
            }
        }
    }

    // Remove remaining latch variable assignments/checks not already handled
    for (idx, stmt) in stmts.iter().enumerate() {
        if remove[idx] || replacements.contains_key(&idx) {
            continue;
        }
        let trimmed = stmt.text.trim();
        if let Some((var, _val)) = trimmed.split_once(" = ") {
            if var.starts_with(GATE_PREFIX) || var.starts_with(INIT_PREFIX) {
                remove[idx] = true;
            }
        }
        if let Some((cond, _)) = parse_if_jump(trimmed) {
            if (cond.starts_with(GATE_PREFIX) || cond.starts_with(INIT_PREFIX))
                && !replacements.contains_key(&idx)
            {
                remove[idx] = true;
                if idx + 1 < stmts.len() && stmts[idx + 1].text.trim() == POP_FLOW {
                    remove[idx + 1] = true;
                }
            }
        }
    }

    // Relocate statements to fix DoOnce structure:
    // - Forward body: gap stmts (between header and body_start) move after body-end
    // - Backward body: body_path + body_end + gap stmts move after header
    let mut relocations: Vec<(usize, Vec<usize>)> = Vec::new();
    for sites in gate_sites.values() {
        for site in sites {
            let Some(body_end) = site.body_end else {
                continue;
            };
            let gap_indices: Vec<usize> = ((site.if_idx + 1)..site.body_start)
                .filter(|&idx| !remove[idx])
                .collect();

            if body_end < site.if_idx {
                // Backward body: relocate body content + closing brace + gap
                // after the DoOnce header. Filter body_path against remove since
                // later cleanup passes may have marked some entries.
                let mut indices: Vec<usize> = site
                    .body_path
                    .iter()
                    .copied()
                    .filter(|&idx| !remove[idx])
                    .collect();
                indices.push(body_end);
                indices.extend(gap_indices);
                if !indices.is_empty() {
                    relocations.push((site.if_idx, indices));
                }
                // Mark the trampoline jump at body_start for removal
                if site.body_start < stmts.len() {
                    let trimmed = stmts[site.body_start].text.trim();
                    if parse_jump(trimmed).is_some() && parse_push_flow(trimmed).is_none() {
                        remove[site.body_start] = true;
                    }
                }
            } else if !gap_indices.is_empty() {
                relocations.push((body_end, gap_indices));
            }
        }
    }

    alias_removed_offsets(stmts, &remove);

    if !relocations.is_empty() {
        let relocated_set: HashSet<usize> = relocations
            .iter()
            .flat_map(|(_, indices)| indices.iter().copied())
            .collect();

        let mut new_stmts: Vec<BcStatement> = Vec::with_capacity(stmts.len());
        for (idx, stmt) in stmts.iter().enumerate() {
            if remove[idx] || relocated_set.contains(&idx) {
                continue;
            }
            new_stmts.push(stmt.clone());

            for (after_idx, reloc_indices) in &relocations {
                if *after_idx == idx {
                    for &ri in reloc_indices {
                        new_stmts.push(stmts[ri].clone());
                    }
                }
            }
        }
        *stmts = new_stmts;
    } else {
        let mut kept_idx = 0;
        stmts.retain(|_| {
            let keep = !remove[kept_idx];
            kept_idx += 1;
            keep
        });
    }
}

/// Add offset aliases from removed statements to the next forward surviving statement.
///
/// Latch removal creates gaps (init blocks, gate checks, wrappers) that precede the
/// structured replacement (DoOnce header, body). Jumps targeting offsets inside the
/// gap should resolve forward to the replacement, not backward to a preceding pop_flow.
fn alias_removed_offsets(stmts: &mut [BcStatement], remove: &[bool]) {
    let survivors: Vec<(usize, usize)> = stmts
        .iter()
        .enumerate()
        .filter(|(idx, stmt)| !remove[*idx] && stmt.mem_offset > 0)
        .map(|(idx, stmt)| (stmt.mem_offset, idx))
        .collect();
    if survivors.is_empty() {
        return;
    }
    let aliases: Vec<(usize, usize)> = stmts
        .iter()
        .enumerate()
        .filter(|(idx, stmt)| remove[*idx] && stmt.mem_offset > 0)
        .filter_map(|(_idx, stmt)| {
            let removed_off = stmt.mem_offset;
            let pos = survivors.partition_point(|&(off, _)| off < removed_off);
            let above = if pos < survivors.len() {
                Some(survivors[pos])
            } else {
                None
            };
            let below = if pos > 0 {
                Some(survivors[pos - 1])
            } else {
                None
            };
            let target_idx = match (above, below) {
                (Some((_, idx)), _) => idx,
                (_, Some((_, idx))) => idx,
                (None, None) => return None,
            };
            Some((removed_off, target_idx))
        })
        .collect();
    for (removed_off, target_idx) in aliases {
        stmts[target_idx].offset_aliases.push(removed_off);
    }
}

/// Mark push_flow/jump wrapper pairs whose jump target lands on a removed statement.
fn mark_latch_wrappers(stmts: &[BcStatement], remove: &mut [bool]) {
    for idx in 0..stmts.len().saturating_sub(1) {
        if remove[idx] || parse_push_flow(stmts[idx].text.trim()).is_none() {
            continue;
        }
        let Some(jump_target) = parse_jump(stmts[idx + 1].text.trim()) else {
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

/// Mark pop_flow statements that became empty scope boundaries after latch removal.
///
/// Preserves pop_flows that are jump targets from surviving code, even if they
/// follow another pop_flow. These serve as branch exits (e.g. if/else scope
/// closers) that happen to be adjacent to event boundary pop_flows.
fn mark_orphaned_pop_flows(
    stmts: &[BcStatement],
    remove: &mut [bool],
    replacements: &BTreeMap<usize, String>,
) {
    let jump_targets: HashSet<usize> = stmts
        .iter()
        .enumerate()
        .filter(|(idx, _)| !remove[*idx])
        .filter_map(|(_, stmt)| {
            let trimmed = stmt.text.trim();
            if let Some((_, target)) = parse_if_jump(trimmed) {
                return Some(target);
            }
            parse_jump(trimmed)
        })
        .collect();

    let orphans: Vec<usize> = (0..stmts.len())
        .filter(|&idx| {
            if remove[idx] || stmts[idx].text.trim() != POP_FLOW {
                return false;
            }
            let offset = stmts[idx].mem_offset;
            if offset > 0
                && jump_targets
                    .iter()
                    .any(|&target| offset.abs_diff(target) <= 4)
            {
                return false;
            }
            let prev_kept = (0..idx).rev().find(|&j| !remove[j]);
            match prev_kept {
                Some(prev) => {
                    let prev_text = replacements
                        .get(&prev)
                        .map_or_else(|| stmts[prev].text.trim(), |rep| rep.as_str());
                    prev_text == POP_FLOW
                }
                None => true,
            }
        })
        .collect();
    for idx in orphans {
        remove[idx] = true;
    }
}

/// Rename `Temp_bool_Variable` references to `$FlipFlop_<name>_IsA` for readability.
fn rename_flipflop_refs(stmts: &mut [BcStatement], toggle_var: &str, name: &str) {
    let display_name = format!("$FlipFlop_{}_IsA", name);
    for stmt in stmts.iter_mut() {
        if stmt.text.contains(toggle_var) {
            stmt.text = stmt.text.replace(toggle_var, &display_name);
        }
    }
}

/// Collapse converged FlipFlop patterns where both A and B branches jump to
/// the same body. Replaces the toggle+branch scaffolding with a `FlipFlop(name) {`
/// header and `A|B: {` sub-header, removing the redundant branch and jump statements.
/// Body-end pop_flows are replaced directly with closing braces.
fn collapse_converged_flipflops(stmts: &mut Vec<BcStatement>, flipflop_names: &[(String, String)]) {
    let offset_map = super::OffsetMap::build(stmts);
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

        // A-path: fallthrough from branch (branch_idx + 1), should be a bare jump
        let a_idx = branch_idx + 1;
        if a_idx >= stmts.len() {
            continue;
        }
        let Some(a_target) = parse_jump(stmts[a_idx].text.trim()) else {
            continue;
        };

        // B-path: the branch's jump target, should also be a bare jump
        let Some(b_idx) = offset_map.find_fuzzy_forward(branch_target, 8) else {
            continue;
        };
        let Some(b_target) = parse_jump(stmts[b_idx].text.trim()) else {
            continue;
        };

        // Only collapse if both branches go to the same body
        if a_target != b_target {
            continue;
        }

        let negate_idx = indices[0];
        let store_idx = indices[1];
        let jump_to_branch_idx = indices[2];

        // Resolve the display name from pre-computed rename pairs
        let display_name = flipflop_names
            .iter()
            .find(|(var, _)| var == toggle_var)
            .map(|(_, name)| name.as_str())
            .unwrap_or("FlipFlop");

        // Replace negate with FlipFlop header, store with A|B sub-header
        stmts[negate_idx].text = format!("FlipFlop({}) {{", display_name);
        stmts[store_idx].text = "A|B: {".to_string();
        stmts[jump_to_branch_idx].text = format!("jump 0x{:x}", a_target);
        remove[branch_idx] = true;
        remove[a_idx] = true;
        remove[b_idx] = true;

        // Find the body-end pop_flow and replace directly with closing braces.
        // FlipFlop needs two: `}` for `A|B: {` and `}` for `FlipFlop(name) {`.
        if let Some(body_start_idx) = offset_map.find_fuzzy_forward(a_target, 8) {
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
                        body_end_replacements.push((body_idx, "}".to_string()));
                        break;
                    }
                }
            }
        }
    }

    // Apply body-end replacements and insert extra `}` for FlipFlop wrapper
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

    // Build new statement list, inserting extra `}` after FlipFlop body-ends
    let body_end_set: HashSet<usize> = body_end_replacements.iter().map(|(idx, _)| *idx).collect();
    let mut new_stmts: Vec<BcStatement> = Vec::with_capacity(stmts.len());
    for (idx, stmt) in stmts.iter().enumerate() {
        if remove[idx] {
            continue;
        }
        new_stmts.push(stmt.clone());
        if body_end_set.contains(&idx) {
            new_stmts.push(BcStatement::new(stmt.mem_offset, "}".to_string()));
        }
    }
    *stmts = new_stmts;
}

/// Pre-compute FlipFlop toggle variable names from the full UberGraph statement list.
///
/// Must run before CFG partitioning because `derive_flipflop_name` scans all
/// statements for `self.X = Temp_bool_Variable` assignments, and after partitioning
/// the assignment may be in a different event than the toggle pattern.
pub fn precompute_flipflop_names(stmts: &[BcStatement]) -> Vec<(String, String)> {
    detect_flipflop_toggle(stmts)
        .iter()
        .map(|(var, _)| {
            let name = derive_flipflop_name(stmts, var);
            (var.clone(), name)
        })
        .collect()
}

/// Top-level entry point: detect and transform all latch patterns.
///
/// When `flipflop_names` is provided (pre-computed from the full UberGraph),
/// those names are used for FlipFlop renaming. Otherwise names are derived
/// from the local statement list.
pub fn transform_latch_patterns(
    stmts: &mut Vec<BcStatement>,
    flipflop_names: Option<&[(String, String)]>,
) {
    let has_latches = stmts.iter().any(|s| {
        let trimmed = s.text.trim();
        trimmed.contains(GATE_PREFIX)
            || trimmed.contains(INIT_PREFIX)
            || trimmed.contains("Temp_bool_Variable")
    });
    if !has_latches {
        return;
    }

    // Use pre-computed names or derive locally
    let local_names;
    let flipflop_rename_pairs: &[(String, String)] = match flipflop_names {
        Some(names) => names,
        None => {
            local_names = precompute_flipflop_names(stmts);
            &local_names
        }
    };

    // Collapse converged FlipFlops before DoOnce transform so their branch
    // scaffolding doesn't interfere with init block detection.
    collapse_converged_flipflops(stmts, flipflop_rename_pairs);

    transform_latches(stmts);

    for (toggle_var, name) in flipflop_rename_pairs {
        rename_flipflop_refs(stmts, toggle_var, name);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stmt(offset: usize, text: &str) -> BcStatement {
        BcStatement::new(offset, text.to_string())
    }

    #[test]
    fn detect_init_block_start_open() {
        let stmts = vec![
            stmt(0x00e4, "Temp_bool_Has_Been_Initd_Variable = true"),
            stmt(0x00f0, "pop_flow_if_not(false)"),
            stmt(0x0104, "Temp_bool_IsClosed_Variable_2 = true"),
            stmt(0x0110, "pop_flow"),
            stmt(0x0113, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0xf1"),
            stmt(0x0122, "pop_flow"),
        ];
        let blocks = detect_init_blocks(&stmts);
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].init_var, "Temp_bool_Has_Been_Initd_Variable");
        assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable_2");
    }

    #[test]
    fn detect_init_block_start_closed() {
        let stmts = vec![
            stmt(0x0289, "Temp_bool_Has_Been_Initd_Variable_1 = true"),
            stmt(0x0297, "pop_flow_if_not(true)"),
            stmt(0x029b, "Temp_bool_IsClosed_Variable = true"),
            stmt(0x02a7, "pop_flow"),
            stmt(
                0x02aa,
                "if !(Temp_bool_Has_Been_Initd_Variable_1) jump 0x288",
            ),
            stmt(0x02b9, "pop_flow"),
        ];
        let blocks = detect_init_blocks(&stmts);
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable");
    }

    #[test]
    fn detect_init_block_forward_layout() {
        // Layout B: init body AFTER the if-check (forward jump)
        let stmts = vec![
            stmt(
                0x0b0e,
                "if !(Temp_bool_Has_Been_Initd_Variable_5) jump 0xb1e",
            ),
            stmt(0x0b1d, "pop_flow"),
            stmt(0x0b1f, "Temp_bool_Has_Been_Initd_Variable_5 = true"),
            stmt(0x0b2d, "pop_flow_if_not(false)"),
            stmt(0x0b31, "Temp_bool_IsClosed_Variable_5 = true"),
            stmt(0x0b3d, "pop_flow"),
        ];
        let blocks = detect_init_blocks(&stmts);
        assert_eq!(blocks.len(), 1, "Should detect forward-layout init block");
        assert_eq!(blocks[0].init_var, "Temp_bool_Has_Been_Initd_Variable_5");
        assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable_5");
    }

    #[test]
    fn gate_resets_found() {
        let stmts = [
            stmt(0x063d, "Temp_bool_IsClosed_Variable_2 = false"),
            stmt(0x0649, "jump 0xe3"),
        ];
        let reset_pattern = format!("{} = false", "Temp_bool_IsClosed_Variable_2");
        let resets: Vec<usize> = stmts
            .iter()
            .enumerate()
            .filter(|(_, s)| s.text.trim() == reset_pattern)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(resets.len(), 1);
        assert_eq!(resets[0], 0);
    }

    #[test]
    fn detect_flipflop_toggle_pattern() {
        let stmts = vec![
            stmt(0x05ed, "$Not_PreBool = !Temp_bool_Variable"),
            stmt(0x060b, "Temp_bool_Variable = $Not_PreBool"),
            stmt(0x061f, "jump 0x5ce"),
            stmt(0x05d0, "if !(Temp_bool_Variable) jump 0x5e6"),
        ];
        let toggles = detect_flipflop_toggle(&stmts);
        assert_eq!(toggles.len(), 1);
        assert_eq!(toggles[0].0, "Temp_bool_Variable");
    }

    #[test]
    fn simple_doonce_transform() {
        let mut stmts = vec![
            // Init block
            stmt(0x10, "Temp_bool_Has_Been_Initd_Variable = true"),
            stmt(0x20, "pop_flow_if_not(false)"),
            stmt(0x30, "Temp_bool_IsClosed_Variable = true"),
            stmt(0x40, "pop_flow"),
            // Init check
            stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0x11"),
            stmt(0x60, "pop_flow"),
            // Gate check
            stmt(0x70, "if !(Temp_bool_IsClosed_Variable) jump 0x90"),
            stmt(0x80, "pop_flow"),
            // Gate close (before body)
            stmt(0x84, "Temp_bool_IsClosed_Variable = true"),
            // Body
            stmt(0x85, "MyFunction(42)"),
            // Body end
            stmt(0x90, "pop_flow"),
        ];
        transform_latch_patterns(&mut stmts, None);

        let texts: Vec<&str> = stmts.iter().map(|s| s.text.trim()).collect();
        assert!(
            texts.contains(&"DoOnce(MyFunction) {"),
            "Expected DoOnce header, got: {:?}",
            texts
        );
        assert!(
            texts.contains(&"MyFunction(42)"),
            "Expected body preserved, got: {:?}",
            texts
        );
        assert!(
            !texts.iter().any(|t| t.contains("Has_Been_Initd")),
            "Init statements should be removed, got: {:?}",
            texts
        );
        assert!(
            !texts.iter().any(|t| t.contains("IsClosed")),
            "Gate close should be removed, got: {:?}",
            texts
        );
        // Body-end pop_flow replaced directly with `}`
        assert!(
            texts.contains(&"}"),
            "Body-end should be closing brace, got: {:?}",
            texts
        );
        assert!(
            !texts.contains(&"pop_flow"),
            "No pop_flow should remain, got: {:?}",
            texts
        );
    }

    #[test]
    fn interleaved_doonce_bodies_kept_separate() {
        // Two DoOnce instances whose bodies sit next to each other at low
        // offsets, with both gate checks at higher offsets jumping backward.
        // This mirrors the UberGraph InputAxis_GripLeftAxis layout where each
        // branch of an outer if-else contains its own DoOnce and UE emits the
        // bodies interleaved before the gate scaffolding.
        //
        // Each gate's body_path walk must stop at body-end and not pull in
        // the adjacent gate's body. When the walk tangles, statements get
        // relocated under the wrong DoOnce header, duplicating bodies and
        // destroying the outer if-else boundary.
        let mut stmts = vec![
            // Init block A
            stmt(0x00, "Temp_bool_Has_Been_Initd_Variable_A = true"),
            stmt(0x04, "pop_flow_if_not(false)"),
            stmt(0x08, "Temp_bool_IsClosed_Variable_A = true"),
            stmt(0x0c, "pop_flow"),
            // Init block B
            stmt(0x10, "Temp_bool_Has_Been_Initd_Variable_B = true"),
            stmt(0x14, "pop_flow_if_not(false)"),
            stmt(0x18, "Temp_bool_IsClosed_Variable_B = true"),
            stmt(0x1c, "pop_flow"),
            // Interleaved bodies: action-A, action-B, pop-A, pop-B
            stmt(0x20, "ActionA()"),
            stmt(0x24, "ActionB()"),
            stmt(0x28, "pop_flow"),
            stmt(0x2c, "pop_flow"),
            // Gate A scaffolding with backward jump to body-A
            stmt(0x30, "if !(Temp_bool_Has_Been_Initd_Variable_A) jump 0x1"),
            stmt(0x34, "pop_flow"),
            stmt(0x38, "if !(Temp_bool_IsClosed_Variable_A) jump 0x50"),
            stmt(0x3c, "pop_flow"),
            stmt(0x40, "Temp_bool_IsClosed_Variable_A = true"),
            stmt(0x44, "jump 0x20"),
            // Gate B scaffolding with backward jump to body-B
            stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable_B) jump 0x11"),
            stmt(0x54, "pop_flow"),
            stmt(0x58, "if !(Temp_bool_IsClosed_Variable_B) jump 0x70"),
            stmt(0x5c, "pop_flow"),
            stmt(0x60, "Temp_bool_IsClosed_Variable_B = true"),
            stmt(0x64, "jump 0x24"),
            stmt(0x70, "pop_flow"),
        ];
        transform_latch_patterns(&mut stmts, None);

        let texts: Vec<String> = stmts.iter().map(|s| s.text.trim().to_string()).collect();

        assert!(
            texts.iter().any(|t| t == "DoOnce(ActionA) {"),
            "Missing DoOnce(ActionA) header, got: {:?}",
            texts
        );
        assert!(
            texts.iter().any(|t| t == "DoOnce(ActionB) {"),
            "Missing DoOnce(ActionB) header, got: {:?}",
            texts
        );

        let action_a_count = texts.iter().filter(|t| t.as_str() == "ActionA()").count();
        let action_b_count = texts.iter().filter(|t| t.as_str() == "ActionB()").count();
        assert_eq!(
            action_a_count, 1,
            "ActionA() appears {} times, expected 1. Output: {:?}",
            action_a_count, texts
        );
        assert_eq!(
            action_b_count, 1,
            "ActionB() appears {} times, expected 1. Output: {:?}",
            action_b_count, texts
        );
    }

    #[test]
    fn doonce_reset_transformed() {
        let mut stmts = vec![
            // Init block
            stmt(0x10, "Temp_bool_Has_Been_Initd_Variable = true"),
            stmt(0x20, "pop_flow_if_not(false)"),
            stmt(0x30, "Temp_bool_IsClosed_Variable = true"),
            stmt(0x40, "pop_flow"),
            stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0x11"),
            stmt(0x60, "pop_flow"),
            // Gate check
            stmt(0x70, "if !(Temp_bool_IsClosed_Variable) jump 0x90"),
            stmt(0x80, "pop_flow"),
            stmt(0x84, "Temp_bool_IsClosed_Variable = true"),
            stmt(0x85, "DoSomething()"),
            stmt(0x90, "pop_flow"),
            // Reset somewhere else
            stmt(0xA0, "Temp_bool_IsClosed_Variable = false"),
        ];
        transform_latch_patterns(&mut stmts, None);

        let texts: Vec<&str> = stmts.iter().map(|s| s.text.trim()).collect();
        assert!(
            texts.contains(&"ResetDoOnce(DoSomething)"),
            "Expected ResetDoOnce, got: {:?}",
            texts
        );
    }
}
