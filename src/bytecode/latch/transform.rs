use std::collections::{BTreeMap, BTreeSet, HashSet};

use super::super::decode::BcStatement;
use super::super::flow::{parse_if_jump, parse_jump, parse_push_flow};
use super::super::{BLOCK_CLOSE, POP_FLOW, STRUCTURE_OFFSET_TOLERANCE};
use super::doonce::{derive_doonce_name, detect_init_blocks};
use super::{GATE_PREFIX, INIT_PREFIX};

/// Follow bare jumps from a body-entry position to reach the first real
/// body statement. Each gate's resolved entry is used as a stop point for
/// other gates' body walks so they don't cross into a neighbour.
pub(super) fn resolve_body_entry(
    stmts: &[BcStatement],
    body_start: usize,
    offset_map: &super::super::OffsetMap,
) -> Option<usize> {
    let mut pos = body_start;
    let mut visited: HashSet<usize> = HashSet::new();
    while pos < stmts.len() && visited.insert(pos) {
        let text = stmts[pos].text.trim();
        if parse_push_flow(text).is_some() {
            return Some(pos);
        }
        if let Some(target) = parse_jump(text) {
            if let Some(next) = offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE) {
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
/// The raw gate pattern is:
/// ```text
/// if !(gate_var) jump PAST   // skip when closed
/// pop_flow                    // closed-path exit
/// [init block]                // removed separately
/// gate_var = true             // close gate before body
/// ... body ...
/// pop_flow                    // body end
/// ```
///
/// Rewrites the gate check to `DoOnce(name) {`, removes the skip-path pop_flow
/// and close assignment, replaces body-end pop_flow with `}`, and rewrites
/// `gate_var = false` resets as `ResetDoOnce(name)`.
///
/// `close_idx` is the first `gate_var = true` after the skip-path pop_flow that
/// is NOT inside an init block.
struct GateSite {
    if_idx: usize,
    pop_idx: usize,
    close_idx: Option<usize>,
    body_start: usize,
    body_end: Option<usize>,
    body_path: Vec<usize>,
}

pub(super) fn transform_latches(stmts: &mut Vec<BcStatement>) {
    let init_blocks = detect_init_blocks(stmts);
    if init_blocks.is_empty() {
        return;
    }

    let (init_block_indices, gate_vars, init_vars) = collect_gate_mapping(&init_blocks);
    let mut gate_sites = find_gate_sites(stmts, &gate_vars, &init_block_indices);

    let offset_map = super::super::OffsetMap::build(stmts);
    let gate_names = derive_gate_names(stmts, &gate_sites, &offset_map);

    let mut remove = vec![false; stmts.len()];
    let mut replacements: BTreeMap<usize, String> = BTreeMap::new();

    for &idx in &init_block_indices {
        if idx < remove.len() {
            remove[idx] = true;
        }
    }

    let bounds = precompute_site_entries(stmts, &gate_sites, &offset_map);

    transform_gate_sites_to_doonce(
        stmts,
        &mut gate_sites,
        &gate_names,
        &mut remove,
        &mut replacements,
        &init_block_indices,
        &bounds,
        &offset_map,
    );

    remove_init_assignments(stmts, &init_vars, &mut remove, &replacements);

    for (&idx, text) in &replacements {
        if idx < stmts.len() {
            stmts[idx].text = text.clone();
            remove[idx] = false;
        }
    }

    mark_latch_wrappers(stmts, &mut remove);
    mark_orphaned_pop_flows(stmts, &mut remove, &replacements);

    remove_residual_latch_stmts(stmts, &mut remove, &replacements);

    let relocations = plan_doonce_relocations(stmts, &gate_sites, &mut remove);

    alias_removed_offsets(stmts, &remove);

    apply_relocations(stmts, &remove, &relocations);
}

/// Collect init block statement indices, gate variables, and init variables.
fn collect_gate_mapping(
    init_blocks: &[super::doonce::InitBlock],
) -> (HashSet<usize>, BTreeSet<String>, BTreeSet<String>) {
    let init_block_indices: HashSet<usize> = init_blocks
        .iter()
        .flat_map(|b| b.stmt_indices.iter().copied())
        .collect();

    let gate_to_init_var: BTreeMap<String, String> = init_blocks
        .iter()
        .map(|b| (b.gate_var.clone(), b.init_var.clone()))
        .collect();

    let gate_vars: BTreeSet<String> = gate_to_init_var.keys().cloned().collect();
    let init_vars: BTreeSet<String> = gate_to_init_var.values().cloned().collect();
    (init_block_indices, gate_vars, init_vars)
}

/// For each gate variable, locate `if !(gate) jump` + `pop_flow` + close-assignment sites.
fn find_gate_sites(
    stmts: &[BcStatement],
    gate_vars: &BTreeSet<String>,
    init_block_indices: &HashSet<usize>,
) -> BTreeMap<String, Vec<GateSite>> {
    let mut gate_sites: BTreeMap<String, Vec<GateSite>> = BTreeMap::new();

    for gate_var in gate_vars {
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

    gate_sites
}

/// Derive display names for each gate variable from the first gate site's body.
fn derive_gate_names(
    stmts: &[BcStatement],
    gate_sites: &BTreeMap<String, Vec<GateSite>>,
    offset_map: &super::super::OffsetMap,
) -> BTreeMap<String, String> {
    let mut gate_names: BTreeMap<String, String> = BTreeMap::new();
    for (gate_var, sites) in gate_sites {
        let name = if let Some(first_site) = sites.first() {
            derive_doonce_name(stmts, first_site.body_start, gate_var, offset_map)
        } else {
            gate_var
                .strip_prefix(GATE_PREFIX)
                .unwrap_or("")
                .trim_start_matches('_')
                .to_string()
        };
        gate_names.insert(gate_var.clone(), name);
    }
    gate_names
}

/// Walk-bound state shared across gate sites. Without these bounds,
/// interleaved DoOnce bodies in UberGraph events get pulled into each other's
/// body_path and duplicated during relocation.
struct SiteBounds {
    /// (gate_var, site_index) -> resolved body-entry statement index.
    entries: BTreeMap<(String, usize), usize>,
    /// All `if !(gate)` indices across every gate site.
    gate_checks: HashSet<usize>,
    /// All resolved body-entry indices across every gate site.
    body_entries: HashSet<usize>,
}

fn precompute_site_entries(
    stmts: &[BcStatement],
    gate_sites: &BTreeMap<String, Vec<GateSite>>,
    offset_map: &super::super::OffsetMap,
) -> SiteBounds {
    let mut entries: BTreeMap<(String, usize), usize> = BTreeMap::new();
    let mut gate_checks: HashSet<usize> = HashSet::new();
    for (gate_var, sites) in gate_sites {
        for (si, site) in sites.iter().enumerate() {
            gate_checks.insert(site.if_idx);
            if let Some(entry) = resolve_body_entry(stmts, site.body_start, offset_map) {
                entries.insert((gate_var.clone(), si), entry);
            }
        }
    }
    let body_entries: HashSet<usize> = entries.values().copied().collect();
    SiteBounds {
        entries,
        gate_checks,
        body_entries,
    }
}

/// Transform gate checks into `DoOnce(name) {` headers, locate body-end via a
/// CFG walk (follows bare jumps because UberGraph events can place the body
/// at lower offsets than the gate check), and rewrite `gate = false` resets
/// as `ResetDoOnce(name)`.
#[allow(clippy::too_many_arguments)]
fn transform_gate_sites_to_doonce(
    stmts: &[BcStatement],
    gate_sites: &mut BTreeMap<String, Vec<GateSite>>,
    gate_names: &BTreeMap<String, String>,
    remove: &mut [bool],
    replacements: &mut BTreeMap<usize, String>,
    init_block_indices: &HashSet<usize>,
    bounds: &SiteBounds,
    offset_map: &super::super::OffsetMap,
) {
    for (gate_var, sites) in gate_sites.iter_mut() {
        let name = &gate_names[gate_var];

        for (site_idx, site) in sites.iter_mut().enumerate() {
            replacements.insert(site.if_idx, format!("DoOnce({}) {{", name));
            remove[site.pop_idx] = true;
            if let Some(close_idx) = site.close_idx {
                remove[close_idx] = true;
            }

            let own_entry = bounds.entries.get(&(gate_var.clone(), site_idx)).copied();
            let mut pos = site.body_start;
            let mut depth = 0i32;
            let mut walk_visited: HashSet<usize> = HashSet::new();
            let mut body_path: Vec<usize> = Vec::new();

            loop {
                if pos >= stmts.len() || !walk_visited.insert(pos) {
                    break;
                }
                // Foreign-boundary stop: another gate's check or body entry
                // means our linear walk has left this DoOnce.
                let is_own_entry = own_entry == Some(pos);
                let hit_foreign_entry = bounds.body_entries.contains(&pos) && !is_own_entry;
                let hit_foreign_check = bounds.gate_checks.contains(&pos) && pos != site.if_idx;
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
                        if let Some(target_pos) =
                            offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
                        {
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
                    replacements.insert(pos, BLOCK_CLOSE.to_string());
                    site.body_end = Some(pos);
                    break;
                }
                body_path.push(pos);
                pos += 1;
            }
            site.body_path = body_path;
        }

        let reset_pattern = format!("{} = false", gate_var);
        for (idx, stmt) in stmts.iter().enumerate() {
            if stmt.text.trim() == reset_pattern {
                replacements.insert(idx, format!("ResetDoOnce({})", name));
            }
        }
    }
}

/// Remove init-related assignments outside detected init blocks (`init_var = true`).
fn remove_init_assignments(
    stmts: &[BcStatement],
    init_vars: &BTreeSet<String>,
    remove: &mut [bool],
    replacements: &BTreeMap<usize, String>,
) {
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
}

/// Remove constant-condition gates and any remaining latch-var assignments or
/// checks not already handled.
fn remove_residual_latch_stmts(
    stmts: &[BcStatement],
    remove: &mut [bool],
    replacements: &BTreeMap<usize, String>,
) {
    for (idx, stmt) in stmts.iter().enumerate() {
        if !remove[idx] {
            let trimmed = stmt.text.trim();
            if trimmed == "pop_flow_if_not(true)" || trimmed == "pop_flow_if_not(false)" {
                remove[idx] = true;
            }
        }
    }

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
}

/// Plan relocations to fix DoOnce structure:
/// - Forward body: gap stmts (header..body_start) move after body-end.
/// - Backward body: body_path + body_end + gap stmts move after header, and
///   the trampoline jump at body_start is marked for removal.
fn plan_doonce_relocations(
    stmts: &[BcStatement],
    gate_sites: &BTreeMap<String, Vec<GateSite>>,
    remove: &mut [bool],
) -> Vec<(usize, Vec<usize>)> {
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
                // Backward body: relocate content + close + gap after the
                // header. Filter body_path against `remove` (later passes may
                // have marked entries).
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
    relocations
}

/// Rebuild `stmts` applying removal flags and relocation plan. Simple
/// `retain` when no relocations; otherwise rebuild skipping removed/relocated
/// indices and splicing relocated ones after their anchor.
fn apply_relocations(
    stmts: &mut Vec<BcStatement>,
    remove: &[bool],
    relocations: &[(usize, Vec<usize>)],
) {
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

            for (after_idx, reloc_indices) in relocations {
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

/// Alias removed statement offsets to the next surviving statement so jumps
/// targeting a gap resolve forward to the structured replacement, not
/// backward to a preceding pop_flow.
pub(super) fn alias_removed_offsets(stmts: &mut [BcStatement], remove: &[bool]) {
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
pub(super) fn mark_latch_wrappers(stmts: &[BcStatement], remove: &mut [bool]) {
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

/// Mark pop_flow statements that became empty scope boundaries after latch
/// removal. Preserves pop_flows that are jump targets from surviving code
/// (branch exits adjacent to event-boundary pop_flows).
pub(super) fn mark_orphaned_pop_flows(
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
