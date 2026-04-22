//! Event-stream linearization pipeline: split, linearize, renumber, and collapse jump chains.

use std::collections::{HashMap, HashSet};

use crate::bytecode::cfg::{
    build_stmt_cfg, extract_partition_stmts, linearize_blocks, partition_by_reachability, BlockCfg,
};
use crate::bytecode::flow::{
    parse_if_jump, parse_jump, parse_push_flow, reorder_convergence, reorder_flow_patterns,
};
use crate::bytecode::latch::{precompute_flipflop_names, transform_latch_patterns};
use crate::bytecode::pipeline::structure_segment;
use crate::bytecode::structure::apply_indentation;
use crate::bytecode::transforms::{
    fold_switch_enum_cascade, strip_orphaned_blocks, strip_unmatched_braces,
};
use crate::bytecode::{
    split_by_sequence_markers, BcStatement, OffsetMap, BARE_RETURN, BLOCK_CLOSE, POP_FLOW,
    RETURN_NOP, STRUCTURE_OFFSET_TOLERANCE,
};

use super::super::{ResumeBlock, UbergraphSection, LATENT_RESUME_SECTION};

/// Split a latent-resume segment at `return nop` / `pop_flow` boundaries so
/// each resume continuation is structured independently (dead-code
/// elimination would otherwise discard blocks after the first return).
pub(super) fn split_at_return_nop(stmts: &[BcStatement]) -> Vec<Vec<BcStatement>> {
    let mut blocks: Vec<Vec<BcStatement>> = Vec::new();
    let mut current: Vec<BcStatement> = Vec::new();
    for stmt in stmts {
        if stmt.text == RETURN_NOP || stmt.text == POP_FLOW {
            if !current.is_empty() {
                blocks.push(std::mem::take(&mut current));
            }
        } else {
            current.push(stmt.clone());
        }
    }
    if !current.is_empty() {
        blocks.push(current);
    }
    if blocks.is_empty() {
        blocks.push(Vec::new());
    }
    blocks
}

/// Split structured ubergraph output into per-event sections and resume blocks.
pub(in crate::output_summary) fn split_ubergraph_sections(
    lines: &[String],
) -> (Vec<UbergraphSection>, Vec<ResumeBlock>) {
    let mut sections: Vec<UbergraphSection> = Vec::new();
    let mut current = UbergraphSection {
        name: String::new(),
        lines: Vec::new(),
    };
    for line in lines {
        let trimmed = line.trim();
        if trimmed.starts_with("--- ") && trimmed.ends_with(" ---") {
            if !current.lines.is_empty() || !current.name.is_empty() {
                sections.push(current);
            }
            current = UbergraphSection {
                name: trimmed[4..trimmed.len() - 4].to_string(),
                lines: Vec::new(),
            };
        } else {
            current.lines.push(line.clone());
        }
    }
    if !current.lines.is_empty() || !current.name.is_empty() {
        sections.push(current);
    }

    let mut resume_blocks: Vec<ResumeBlock> = Vec::new();
    for section in &sections {
        if section.name != LATENT_RESUME_SECTION {
            continue;
        }
        let mut block_lines: Vec<String> = Vec::new();
        for line in &section.lines {
            if line.trim() == BARE_RETURN {
                if !block_lines.is_empty() {
                    resume_blocks.push(ResumeBlock { lines: block_lines });
                    block_lines = Vec::new();
                }
            } else {
                block_lines.push(line.clone());
            }
        }
        if !block_lines.is_empty() {
            resume_blocks.push(ResumeBlock { lines: block_lines });
        }
    }

    (sections, resume_blocks)
}

/// Linearize a partition in CFG-topological order from the event entry.
///
/// DoOnce/FlipFlop bodies can live at lower offsets than their gate check, so
/// naive rotation leaves the body between the gate's if-jump and its else
/// target. This does a block-CFG DFS from the entry, sweeps any unemitted
/// blocks, then monotonically [`renumber_offsets`] so emission order equals
/// offset order (required by `detect_for_loops` / `reorder_convergence`).
/// Skipped when the entry is already the first statement.
///
/// Sequence dispatch chains survive the walk because `BlockCfg::build`
/// collapses each Sequence into a `SequenceSuperBlock` emitted verbatim;
/// downstream detectors re-identify the raw push_flow/jump layout.
pub(super) fn linearize_from_entry(
    stmts: &mut Vec<BcStatement>,
    global_entry_idx: usize,
    all_stmts: &[BcStatement],
) {
    if stmts.is_empty() {
        return;
    }

    let entry_offset = all_stmts
        .get(global_entry_idx)
        .map(|s| s.mem_offset)
        .unwrap_or(0);

    // When the entry is already first, skip: the DFS + renumber_offsets
    // collapses both branches onto a monotonic stride, which loses the
    // offset gap `reorder_convergence` and `find_convergence_target` rely
    // on for backward-edge / shared-post-branch detection. Symptom: nested
    // `if` emerges at the wrong indent (VRPlayer axis handlers).
    if stmts.first().is_some_and(|s| s.mem_offset == entry_offset) {
        return;
    }

    let offset_map = OffsetMap::build(stmts);
    let mut cfg = BlockCfg::build(stmts, &offset_map);
    if cfg.blocks.is_empty() {
        return;
    }

    // Entry stub may be a few bytes off because filtered wire_trace /
    // tracepoint opcodes can sit at the exact entry address.
    let entry_block = offset_map
        .find_fuzzy_forward(entry_offset, STRUCTURE_OFFSET_TOLERANCE)
        .and_then(|stmt_idx| cfg.stmt_to_block.get(&stmt_idx).copied())
        .unwrap_or(0);

    let in_degree = cfg.compute_in_degree();
    let predecessors = cfg.compute_predecessors();
    let blocks = &mut cfg.blocks;

    let mut output: Vec<BcStatement> = Vec::with_capacity(stmts.len() + 4);

    // Primary DFS from the entry emits then/else/convergence in structurer order.
    linearize_blocks(
        blocks,
        stmts,
        &in_degree,
        &predecessors,
        entry_block,
        &mut output,
    );

    // Sweep blocks unreachable from the entry (shared code, orphan
    // trampolines) in original block order so nothing is lost.
    for bid in 0..blocks.len() {
        linearize_blocks(blocks, stmts, &in_degree, &predecessors, bid, &mut output);
    }

    // Strip leading pop_flows (leftovers from adjacent event boundaries).
    while output.first().is_some_and(|s| s.text.trim() == POP_FLOW) {
        output.remove(0);
    }

    renumber_offsets(&mut output);

    *stmts = output;
}

/// Reassign `mem_offset`s so emission-index order equals offset order, and
/// rewrite every jump/push_flow/if-jump target to the new values. After CFG
/// linearization, backward jumps (in offset order) often sit in forward
/// emission positions; for-loop detection and goto handling would misread
/// them as back-edges without monotonic offsets.
///
/// Target resolution: fuzzy-forward on a pre-renumber [`OffsetMap`] (jumps
/// can land off by a wire_trace/tracepoint, and latch transforms leave
/// gate-check offsets just past a visible statement). Synthetic jumps from
/// `linearize_blocks` (mem_offset == 0) reference the target block's old
/// offset and resolve the same way.
fn renumber_offsets(stmts: &mut [BcStatement]) {
    if stmts.is_empty() {
        return;
    }

    // Strided to leave headroom for fuzzy match + no collisions.
    const STRIDE: usize = 16;

    let pre_map = OffsetMap::build(stmts);
    let resolve = |target: usize| -> Option<usize> {
        pre_map
            .find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            .or_else(|| pre_map.find_fuzzy(target, STRUCTURE_OFFSET_TOLERANCE))
            .map(|stmt_idx| (stmt_idx + 1) * STRIDE)
    };

    for (idx, stmt) in stmts.iter_mut().enumerate() {
        let new_offset = (idx + 1) * STRIDE;
        let trimmed = stmt.text.trim().to_string();
        if let Some((cond, target)) = parse_if_jump(&trimmed) {
            if let Some(new_target) = resolve(target) {
                stmt.text = format!("if !({}) jump 0x{:x}", cond, new_target);
            }
        } else if parse_push_flow(&trimmed).is_none() {
            if let Some(target) = parse_jump(&trimmed) {
                if let Some(new_target) = resolve(target) {
                    stmt.text = format!("jump 0x{:x}", new_target);
                }
            }
        }
        if let Some(target) = parse_push_flow(&trimmed) {
            if let Some(new_target) = resolve(target) {
                stmt.text = format!("push_flow 0x{:x}", new_target);
            }
        }
        stmt.mem_offset = new_offset;
        stmt.offset_aliases.clear();
    }
}

/// Renumber mem_offsets to match vec order (offset-sorted equals vec-sorted)
/// and rewrite jump / if-jump / push_flow text to the new offsets. Reorder
/// passes can leave higher-vec-index stmts with lower mem_offsets than their
/// predecessors, which makes the structurer drop "lexically mid-range"
/// blocks as dead code.
const RENUMBER_STRIDE: usize = 0x10;

pub(super) fn renumber_to_vec_order(stmts: &mut [BcStatement]) {
    if stmts.len() < 2 {
        return;
    }
    let base = stmts[0].mem_offset;
    let old_to_new: Vec<(usize, usize)> = stmts
        .iter()
        .enumerate()
        .map(|(i, s)| (s.mem_offset, base + i * RENUMBER_STRIDE))
        .collect();
    if old_to_new.iter().all(|(o, n)| o == n) {
        return;
    }
    let old_map: std::collections::HashMap<usize, usize> = old_to_new.iter().copied().collect();
    let old_offset_map = OffsetMap::build(stmts);
    // Exact map lookup first, else fuzzy-forward to the nearest mapped stmt.
    // `None` if the target falls outside this event's partition.
    let map_target = |target: usize| -> Option<usize> {
        if let Some(&new_t) = old_map.get(&target) {
            return Some(new_t);
        }
        let target_idx = old_offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)?;
        old_map.get(&old_to_new[target_idx].0).copied()
    };
    for stmt in stmts.iter_mut() {
        let trimmed = stmt.text.trim();
        if let Some(target) = parse_push_flow(trimmed) {
            if let Some(new_t) = map_target(target) {
                stmt.text = format!("push_flow 0x{:x}", new_t);
            }
        } else if let Some(target) = parse_jump(trimmed) {
            if let Some(new_t) = map_target(target) {
                stmt.text = format!("jump 0x{:x}", new_t);
            }
        } else if let Some((cond, target)) = parse_if_jump(trimmed) {
            if let Some(new_t) = map_target(target) {
                stmt.text = format!("if !({}) jump 0x{:x}", cond, new_t);
            }
        }
    }
    for (i, stmt) in stmts.iter_mut().enumerate() {
        stmt.mem_offset = base + i * RENUMBER_STRIDE;
    }
}

pub(super) fn normalize_jump_targets(stmts: &mut [BcStatement]) {
    if stmts.is_empty() {
        return;
    }
    let offset_map = OffsetMap::build(stmts);
    for idx in 0..stmts.len() {
        let trimmed = stmts[idx].text.trim().to_string();
        if let Some(target) = parse_jump(&trimmed) {
            if parse_push_flow(&trimmed).is_some() {
                continue;
            }
            if let Some(target_idx) =
                offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                let exact = stmts[target_idx].mem_offset;
                if exact != target {
                    stmts[idx].text = format!("jump 0x{:x}", exact);
                }
            }
        } else if let Some((cond, target)) = parse_if_jump(&trimmed) {
            if let Some(target_idx) =
                offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                let exact = stmts[target_idx].mem_offset;
                if exact != target {
                    stmts[idx].text = format!("if !({}) jump 0x{:x}", cond, exact);
                }
            }
        } else if let Some(target) = parse_push_flow(&trimmed) {
            if let Some(target_idx) =
                offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                let exact = stmts[target_idx].mem_offset;
                if exact != target {
                    stmts[idx].text = format!("push_flow 0x{:x}", exact);
                }
            }
        }
    }
}

/// Collapse `jump A -> jump B -> jump C -> code` into `jump C` and drop
/// unreferenced trampolines. Event partitions can reach shared code through
/// several hops that would otherwise confuse the structurer.
pub(super) fn collapse_jump_chains(stmts: &mut Vec<BcStatement>) {
    if stmts.len() < 3 {
        return;
    }

    // Normalize jump targets first so the chain walk sees exact offsets.
    normalize_jump_targets(stmts);

    // Invariant: a jump's offset lands here iff the chain-walk rewrote a
    // predecessor to skip over it. The retain filter below only drops
    // offsets in this set. Absent jumps are legitimate edges later passes
    // (`BlockCfg::build`, `reorder_convergence`, structurer goto handling)
    // still need. Callers adding new jump rewrites must update this set.
    let mut elided_offsets: HashSet<usize> = HashSet::new();

    let mut changed = true;
    while changed {
        changed = false;
        let chain_map = OffsetMap::build(stmts);
        for idx in 0..stmts.len() {
            let trimmed = stmts[idx].text.trim().to_string();

            if let Some(target) = parse_jump(&trimmed) {
                if parse_push_flow(&trimmed).is_some() {
                    continue;
                }
                let Some(target_idx) =
                    chain_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
                else {
                    continue;
                };
                let target_text = stmts[target_idx].text.trim().to_string();
                if parse_push_flow(&target_text).is_some() {
                    continue;
                }
                if let Some(final_target) = parse_jump(&target_text) {
                    elided_offsets.insert(stmts[target_idx].mem_offset);
                    stmts[idx].text = format!("jump 0x{:x}", final_target);
                    changed = true;
                }
                continue;
            }

            if let Some((cond, target)) = parse_if_jump(&trimmed) {
                let Some(target_idx) =
                    chain_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
                else {
                    continue;
                };
                let target_text = stmts[target_idx].text.trim().to_string();
                if parse_push_flow(&target_text).is_some() {
                    continue;
                }
                if let Some(final_target) = parse_jump(&target_text) {
                    elided_offsets.insert(stmts[target_idx].mem_offset);
                    stmts[idx].text = format!("if !({}) jump 0x{:x}", cond, final_target);
                    changed = true;
                }
            }
        }
    }

    // Drop unreferenced trampolines, preserving Sequence pin `jump` that
    // follows a `push_flow` (reached by fallthrough, must stay).
    let final_offset_map = OffsetMap::build(stmts);
    let mut referenced_offsets: HashSet<usize> = HashSet::new();
    for stmt in stmts.iter() {
        let trimmed = stmt.text.trim();
        if let Some(target) = parse_jump(trimmed) {
            if let Some(idx) =
                final_offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                referenced_offsets.insert(stmts[idx].mem_offset);
            }
        }
        if let Some((_, target)) = parse_if_jump(trimmed) {
            if let Some(idx) =
                final_offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                referenced_offsets.insert(stmts[idx].mem_offset);
            }
        }
        if let Some(target) = parse_push_flow(trimmed) {
            if let Some(idx) =
                final_offset_map.find_fuzzy_forward(target, STRUCTURE_OFFSET_TOLERANCE)
            {
                referenced_offsets.insert(stmts[idx].mem_offset);
            }
        }
    }

    // Protect jumps reached by fallthrough (after push_flow or if-jump).
    let mut fallthrough_offsets: HashSet<usize> = HashSet::new();
    // Track jumps whose predecessor is a flow terminator: unreachable by
    // fallthrough, only live if targeted directly. Covers trampolines after
    // a `}` (latch close), a prior bare jump, or pop_flow.
    let mut after_terminator_offsets: HashSet<usize> = HashSet::new();
    for window in stmts.windows(2) {
        let prev_text = window[0].text.trim();
        if parse_push_flow(prev_text).is_some() || parse_if_jump(prev_text).is_some() {
            fallthrough_offsets.insert(window[1].mem_offset);
        } else if is_flow_terminator(prev_text) {
            after_terminator_offsets.insert(window[1].mem_offset);
        }
    }

    stmts.retain(|stmt| {
        let trimmed = stmt.text.trim();
        if parse_jump(trimmed).is_none() || parse_push_flow(trimmed).is_some() {
            return true;
        }
        // After-terminator jumps survive only if directly targeted.
        if after_terminator_offsets.contains(&stmt.mem_offset) {
            return referenced_offsets.contains(&stmt.mem_offset);
        }
        // Only strip rewritten trampolines; leave other jumps intact.
        if !elided_offsets.contains(&stmt.mem_offset) {
            return true;
        }
        referenced_offsets.contains(&stmt.mem_offset)
            || fallthrough_offsets.contains(&stmt.mem_offset)
    });
}

/// True if a statement ends control flow (next sequential stmt unreachable).
fn is_flow_terminator(text: &str) -> bool {
    let trimmed = text.trim();
    if parse_jump(trimmed).is_some() && parse_push_flow(trimmed).is_none() {
        return true;
    }
    matches!(trimmed, POP_FLOW | RETURN_NOP | BARE_RETURN | BLOCK_CLOSE)
}

/// Build structured ubergraph output from raw bytecode statements and event labels.
///
/// Pipeline: build CFG on raw bytecode, partition events by reachability,
/// then run latch transforms and structuring per-event. This avoids cross-event
/// contamination from running latch transforms on interleaved events.
pub(in crate::output_summary) fn build_ubergraph_structured(
    stmts: Vec<BcStatement>,
    ubergraph_labels: &HashMap<usize, String>,
) -> Option<Vec<String>> {
    if stmts.is_empty() {
        return None;
    }

    let cleaned = stmts;

    // Pre-compute FlipFlop names from the full UberGraph before partitioning.
    // derive_flipflop_name scans all statements for `self.X = toggle_var`
    // assignments, which may be in a different event than the toggle pattern.
    let flipflop_names = precompute_flipflop_names(&cleaned);

    // Build a lightweight CFG on raw bytecode and partition statements by
    // reachability from each event entry point. Latch patterns are still
    // intact, but push_flow edges bridge past their internal pop_flows.
    // Event boundary pop_flows have no such bypass, so BFS stops correctly.
    let sorted_labels: Vec<(usize, &String)> = {
        let mut labels: Vec<(usize, &String)> =
            ubergraph_labels.iter().map(|(k, v)| (*k, v)).collect();
        labels.sort_by_key(|(offset, _)| *offset);
        labels
    };

    let offset_map = OffsetMap::build(&cleaned);
    let cfg = build_stmt_cfg(&cleaned, &offset_map);
    let partitions = partition_by_reachability(&cfg, &cleaned, &sorted_labels, &offset_map);

    let mut all_lines: Vec<String> = Vec::new();
    for partition in &partitions {
        if !partition.name.is_empty() {
            all_lines.push(format!("--- {} ---", partition.name));
        } else if !partition.indices.is_empty() {
            all_lines.push(format!("--- {} ---", LATENT_RESUME_SECTION));
        }
        if partition.indices.is_empty() {
            continue;
        }

        let mut event_stmts = extract_partition_stmts(&cleaned, &partition.indices);

        // Transform DoOnce/FlipFlop latch patterns per-event.
        // Each event's bytecode is small and self-contained, so the latch
        // transform operates in isolation without cross-event interference.
        transform_latch_patterns(&mut event_stmts, Some(&flipflop_names));

        // Latent resume segments contain multiple independent blocks separated
        // by `return nop`. Split and structure each block independently so that
        // dead-code elimination doesn't kill all blocks after the first return.
        if partition.name.is_empty() {
            let resume_blocks = split_at_return_nop(&event_stmts);
            for (bi, block) in resume_blocks.iter().enumerate() {
                if bi > 0 {
                    all_lines.push("return".to_string());
                }
                if !block.is_empty() {
                    all_lines.extend(structure_segment(block));
                }
            }
            continue;
        }

        // Normalize jump targets first so the block-CFG built by
        // `linearize_from_entry` sees clean boundaries. Full
        // `collapse_jump_chains` runs later, once any entry trampolines the
        // block-CFG needed have already been processed.
        normalize_jump_targets(&mut event_stmts);

        // When the entry point is not the first statement (body code at lower
        // offsets than the entry trampoline), walk the block-level CFG so the
        // entry block comes first and then/else/convergence order matches
        // control flow instead of offset order.
        if let Some(global_entry) = partition.entry_idx {
            linearize_from_entry(&mut event_stmts, global_entry, &cleaned);
        }

        collapse_jump_chains(&mut event_stmts);

        // Flow reorder and convergence fix per-event, so Sequence body blocks
        // and backward jumps are resolved within each event's scope.
        let mut reordered = reorder_flow_patterns(&event_stmts);
        reorder_convergence(&mut reordered);

        // After reorder, renumber mem_offsets to match vec order. Some reorder
        // paths leave stmts where a later vec index has a lower mem_offset than
        // its predecessor (e.g. a shared DoOnce body whose original offset
        // sits below the else-body that reaches it via push_flow/pop_flow).
        // structure_segment walks by vec index but bounds regions by offset, so
        // such "lexically mid-range" blocks get dropped as dead code. Renumbering
        // flattens offset-order onto vec-order.
        renumber_to_vec_order(&mut reordered);

        let sub_segments = split_by_sequence_markers(&reordered);
        // Scope the current event's function key so the structurer's pin-aware
        // else-branch fallback can consult branch hints keyed by
        // `(function_key, bytecode_offset)`.
        let event_start = all_lines.len();
        crate::pin_hints_scope::with_function_key(&partition.name, || {
            if sub_segments.len() <= 1 {
                all_lines.extend(structure_segment(&reordered));
            } else {
                for (marker, body) in &sub_segments {
                    if let Some(marker_text) = marker {
                        all_lines.push(marker_text.clone());
                    }
                    if !body.is_empty() {
                        all_lines.extend(structure_segment(body));
                    }
                }
            }

            // Pin-aware post-structure relocation: move orphan
            // `DoOnce(X) { ... }` blocks into the branch of the adjacent
            // if-block indicated by this event's branch hints. Operates
            // only on lines appended during this event so earlier events
            // are not disturbed.
            let mut event_slice: Vec<String> = all_lines.split_off(event_start);
            super::super::relocate::relocate_orphan_doonces_via_hints(&mut event_slice);
            all_lines.extend(event_slice);
        });
    }

    strip_unmatched_braces(&mut all_lines);
    strip_orphaned_blocks(&mut all_lines);
    fold_switch_enum_cascade(&mut all_lines);
    apply_indentation(&mut all_lines);
    if all_lines.is_empty() {
        None
    } else {
        Some(all_lines)
    }
}
