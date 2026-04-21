//! Ubergraph event splitting, latent resume block matching, and structured output processing.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::block_graph::{linearize_blocks, BlockCfg};
use crate::bytecode::cfg::{build_stmt_cfg, extract_partition_stmts, partition_by_reachability};
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
use crate::helpers::indent_of;
use crate::prop_query::find_prop_str_items_any;
use crate::types::{NodePinData, Property};

use super::comments::{
    build_node_index, build_ownership_index, classify_comment_by_pins, find_comment_line,
    find_comment_line_clustered, map_export_to_line, CommentPlacement,
};
use super::edgraph::EdGraphData;
use super::{
    emit_comment, find_local_calls, section_sep, strip_resume_annotation, CommentBox, NodeInfo,
    ResumeBlock, UbergraphSection, LATENT_RESUME_SECTION,
};

/// Maximum number of events a comment box can contain and still be treated as
/// an intentional multi-event group. Boxes containing more events are likely
/// organizational section dividers placed for visual layout, not semantic groupings.
const MAX_MULTI_EVENT_GROUP_SIZE: usize = 3;

/// Split a latent resume segment at `return nop` or `pop_flow` boundaries.
///
/// Each sub-block is an independent resume continuation that should be
/// structured separately so dead-code elimination doesn't discard blocks
/// after the first return.
fn split_at_return_nop(stmts: &[BcStatement]) -> Vec<Vec<BcStatement>> {
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
pub(super) fn split_ubergraph_sections(
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

/// Linearize a partition's statements in CFG-topological order starting from
/// the event entry block.
///
/// Replaces the earlier offset-based rotation. The compiler places DoOnce /
/// FlipFlop bodies at lower offsets than their gate check, so simple
/// rotation leaves the body physically between the gate's if-jump and its
/// else target. A full block-level CFG walk would place then-body /
/// else-body / convergence in the correct order — but it would also split
/// latch bodies (DoOnce(Name) { ... }) and Sequence chains that the
/// structurer treats as atomic units.
///
/// For this phase, the function does exactly as much as is safe:
///
/// 1. Build a block-CFG, locate the entry block by offset.
/// 2. Emit blocks via DFS from the entry (shared
///    `block_graph::linearize_blocks`).
/// 3. Sweep any unemitted blocks to preserve orphaned code.
/// 4. [`renumber_offsets`] monotonically rewrites `mem_offset` and all
///    jump/push_flow targets so emission-index order equals offset order,
///    keeping `detect_for_loops` / `reorder_convergence` heuristics correct.
///
/// Skipped when:
/// - The entry is already the first statement (natural order, further
///   passes handle it correctly).
///
/// Sequence dispatch chains are preserved through the walk because
/// `BlockCfg::build` collapses each Sequence into a single
/// `SequenceSuperBlock` whose range is emitted verbatim. Downstream
/// `detect_grouped_sequences` / `detect_interleaved_sequences` can then
/// re-detect the raw `push_flow`/`jump` layout.
fn linearize_from_entry(
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

    // When the entry is already the first statement, the partition is already
    // in natural control-flow order. Running the CFG walk here collapses
    // if/else structures that `reorder_convergence` would otherwise linearize
    // correctly: DFS emits then-body then else-body in offset order, but the
    // later `renumber_offsets` rewrites both branches onto a single monotonic
    // stride, losing the offset gap that `reorder_convergence`'s backward-edge
    // detection and `block_graph::find_convergence_target` use to identify the
    // shared post-branch block. The visible symptom is a nested `if` emerging
    // at the wrong indent (observed on VRPlayer axis handlers).
    if stmts.first().is_some_and(|s| s.mem_offset == entry_offset) {
        return;
    }

    let offset_map = OffsetMap::build(stmts);
    let mut cfg = BlockCfg::build(stmts, &offset_map);
    if cfg.blocks.is_empty() {
        return;
    }

    // Locate the entry block by offset. The event's entry stub may be a few
    // bytes away from any decoded statement because filtered wire_trace /
    // tracepoint opcodes sit at the exact entry address.
    let entry_block = offset_map
        .find_fuzzy_forward(entry_offset, STRUCTURE_OFFSET_TOLERANCE)
        .and_then(|stmt_idx| cfg.stmt_to_block.get(&stmt_idx).copied())
        .unwrap_or(0);

    let in_degree = cfg.compute_in_degree();
    let predecessors = cfg.compute_predecessors();
    let blocks = &mut cfg.blocks;

    let mut output: Vec<BcStatement> = Vec::with_capacity(stmts.len() + 4);

    // Primary DFS from the event entry. Emits then-body, else-body, and
    // convergence in the order the structurer expects.
    linearize_blocks(
        blocks,
        stmts,
        &in_degree,
        &predecessors,
        entry_block,
        &mut output,
    );

    // Sweep pass: any blocks sitting before the entry in offset order that
    // aren't reachable from the entry (shared code, orphaned trampolines)
    // are emitted in their original block order so data isn't lost.
    for bid in 0..blocks.len() {
        linearize_blocks(blocks, stmts, &in_degree, &predecessors, bid, &mut output);
    }

    // Strip leading pop_flows (leftovers from adjacent event boundaries). The
    // old rotation-based reorder also did this; with block-graph walking the
    // same artifact can appear if the entry block sits after a pop_flow.
    while output.first().is_some_and(|s| s.text.trim() == POP_FLOW) {
        output.remove(0);
    }

    renumber_offsets(&mut output);

    *stmts = output;
}

/// Reassign mem_offsets so that emission-index order equals offset order,
/// then rewrite every jump/push_flow/conditional-jump target in text to
/// match the new offsets.
///
/// After CFG linearization, backward jumps (in offset order) often sit in
/// forward emission positions. Downstream passes that reason about offsets
/// (for-loop detection, structurer goto handling) would misread these as
/// loop back-edges. Monotonically-increasing offsets fix that.
///
/// Targets are resolved by building a pre-renumber [`OffsetMap`] and using
/// fuzzy-forward lookup. Jumps can land a few bytes from the nearest
/// statement (filtered wire_trace / tracepoint opcodes), and the latch
/// transforms may leave gate-check offsets that no longer correspond to a
/// visible statement but point just past one. Synthetic jumps inserted by
/// `linearize_blocks` (mem_offset == 0) reference the target block's *old*
/// offset, which we resolve the same way.
fn renumber_offsets(stmts: &mut [BcStatement]) {
    if stmts.is_empty() {
        return;
    }

    // Strided offsets leave headroom so fuzzy-match tolerances stay within
    // reasonable bounds and no pair of statements can collide.
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

/// Rewrite jump/push_flow/conditional-jump targets to the exact `mem_offset`
/// of the nearest statement within the fuzzy tolerance.
///
/// Cross-event jumps often land on aliased offsets 5+ bytes from the nearest
/// statement, exceeding downstream tolerances. Running this before CFG
/// construction keeps block boundaries stable without removing any
/// statements.
/// Renumber mem_offsets to match vec order so offset-sorted and vec-sorted
/// views agree. Reorder passes can leave stmts in an order where higher-vec-index
/// stmts have lower mem_offsets than predecessors, which causes the structurer
/// to drop "lexically mid-range" blocks as dead code. Rewrites jump / if-jump /
/// push_flow text to point at the new offsets.
/// Spacing between synthetic mem_offsets when renumbering to vec order.
/// Arbitrary; only needs to be nonzero so offsets stay distinct and fuzzy
/// lookups remain bounded.
const RENUMBER_STRIDE: usize = 0x10;

fn renumber_to_vec_order(stmts: &mut [BcStatement]) {
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
    // Exact match; otherwise fuzzy-forward resolution to the nearest stmt
    // whose old offset has a known mapping. `None` when the target falls
    // outside this event's partition.
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

fn normalize_jump_targets(stmts: &mut [BcStatement]) {
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

/// Collapse bare jump chains so intermediate trampolines don't confuse structuring.
///
/// When event partitions include shared code at distant offsets, the jump path
/// from the event's own code to the shared code may go through several bare jumps.
/// This collapses `jump A -> jump B -> jump C -> actual_code` into `jump C`
/// and removes dead trampoline statements that are no longer referenced.
fn collapse_jump_chains(stmts: &mut Vec<BcStatement>) {
    if stmts.len() < 3 {
        return;
    }

    // Normalize jump targets to exact offsets first so the chain walk below
    // sees consistent addresses.
    normalize_jump_targets(stmts);

    // Invariant: a jump's offset is inserted here iff the chain-walk rewrote
    // some predecessor to skip over it, making it a trampoline candidate. The
    // retain filter below removes only offsets in this set (if also
    // unreferenced and not reachable by fallthrough). Any bare jump absent
    // from this set is a legitimate control-flow edge the later passes
    // (`BlockCfg::build`, `reorder_convergence`, structurer goto handling)
    // need, e.g. backward edges out of latch bodies or forward edges the walk
    // chose not to collapse. Callers that introduce new jump rewrites must
    // update this set, otherwise stale trampolines survive.
    let mut elided_offsets: HashSet<usize> = HashSet::new();

    // Collapse bare jump chains: jump A -> jump B -> actual_code becomes jump B
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

    // Remove bare jump trampolines that are unreferenced and not part of
    // a push_flow/jump sequence pair. Sequence pin markers look like:
    //   push_flow RESUME_ADDR
    //   jump BODY_ADDR          <- reached by fallthrough, must be preserved
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

    // Also protect jumps that follow push_flow (sequence pin bodies)
    // or follow if-jumps (branch targets reached by fallthrough).
    let mut fallthrough_offsets: HashSet<usize> = HashSet::new();
    // Track jumps whose predecessor is itself a flow terminator. These cannot
    // be reached by fallthrough and so are only live if something jumps to
    // them directly. Covers leftover trampolines the compiler emits after a
    // `}` (latch close), a preceding unconditional jump, or a pop_flow.
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
        // Jumps immediately following a flow terminator (`}`, `pop_flow`,
        // another bare jump, or `return`) are unreachable by fallthrough.
        // They survive only if some other jump targets them.
        if after_terminator_offsets.contains(&stmt.mem_offset) {
            return referenced_offsets.contains(&stmt.mem_offset);
        }
        // Only strip jumps that were rewritten as elided trampolines.
        // Preserve legitimate backward/forward jumps that the chain walk
        // left alone; they carry real control-flow information.
        if !elided_offsets.contains(&stmt.mem_offset) {
            return true;
        }
        referenced_offsets.contains(&stmt.mem_offset)
            || fallthrough_offsets.contains(&stmt.mem_offset)
    });
}

/// Return true if a statement ends control flow such that the next
/// sequential statement is unreachable by fallthrough.
fn is_flow_terminator(text: &str) -> bool {
    let trimmed = text.trim();
    // An unconditional jump terminates fallthrough.
    if parse_jump(trimmed).is_some() && parse_push_flow(trimmed).is_none() {
        return true;
    }
    if trimmed == POP_FLOW || trimmed == RETURN_NOP || trimmed == BARE_RETURN {
        return true;
    }
    // A closing brace from latch/loop/if block emission.
    if trimmed == BLOCK_CLOSE {
        return true;
    }
    false
}

/// Build structured ubergraph output from raw bytecode statements and event labels.
///
/// Pipeline: build CFG on raw bytecode, partition events by reachability,
/// then run latch transforms and structuring per-event. This avoids cross-event
/// contamination from running latch transforms on interleaved events.
pub(super) fn build_ubergraph_structured(
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
            super::relocate::relocate_orphan_doonces_via_hints(&mut event_slice);
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

/// Extract the short action name from an InputAction event stub.
///
/// `InpActEvt_Fly_K2Node_InputActionEvent_6` returns `Some("Fly")`.
fn extract_input_action_name(section_name: &str) -> Option<&str> {
    let rest = section_name.strip_prefix("InpActEvt_")?;
    let end = rest.find("_K2Node_InputActionEvent_")?;
    Some(&rest[..end])
}

/// Extract the trailing numeric suffix from an InputAction or InputAxis event.
fn extract_event_suffix_number(section_name: &str) -> Option<u32> {
    let last_underscore = section_name.rfind('_')?;
    section_name[last_underscore + 1..].parse().ok()
}

/// Extract the axis name from an InputAxis event stub.
///
/// `InpAxisEvt_MouseX_K2Node_InputAxisEvent_0` returns `Some("MouseX")`.
fn extract_input_axis_name(section_name: &str) -> Option<&str> {
    let rest = section_name.strip_prefix("InpAxisEvt_")?;
    let end = rest.find("_K2Node_InputAxisEvent_")?;
    Some(&rest[..end])
}

/// Pre-compute Pressed/Released labels for InputAction events.
///
/// Groups events by action name. When an action has two events, the lower
/// suffix number is Pressed, the higher is Released. Single events are Pressed.
fn compute_action_key_events(section_names: &[&str]) -> HashMap<String, String> {
    let mut by_action: HashMap<&str, Vec<(&str, u32)>> = HashMap::new();
    for &name in section_names {
        if let Some(action) = extract_input_action_name(name) {
            let num = extract_event_suffix_number(name).unwrap_or(0);
            by_action.entry(action).or_default().push((name, num));
        }
    }
    let mut result = HashMap::new();
    for (_, mut events) in by_action {
        events.sort_by_key(|&(_, num)| num);
        if events.len() == 1 {
            result.insert(events[0].0.to_string(), "Pressed".to_string());
        } else {
            result.insert(events[0].0.to_string(), "Pressed".to_string());
            for &(name, _) in &events[1..] {
                result.insert(name.to_string(), "Released".to_string());
            }
        }
    }
    result
}

/// Convert a raw UberGraph section name to a clean display name with signature.
///
/// `InpActEvt_Jump_K2Node_InputActionEvent_13` with Pressed -> `InputAction_Jump_Pressed()`
/// `InpAxisEvt_MouseX_K2Node_InputAxisEvent_0` -> `InputAxis_MouseX(AxisValue: float)`
/// Custom events pass through unchanged with `()` appended.
fn clean_event_header(raw_name: &str, action_key_events: &HashMap<String, String>) -> String {
    if let Some(action) = extract_input_action_name(raw_name) {
        let key_event = action_key_events
            .get(raw_name)
            .map(|s| s.as_str())
            .unwrap_or("Pressed");
        return format!("InputAction_{}_{}", action, key_event);
    }
    if let Some(axis) = extract_input_axis_name(raw_name) {
        return format!("InputAxis_{}(AxisValue: float)", axis);
    }
    raw_name.to_string()
}

/// Resolve an event's graph node position by section name.
///
/// Primary: exact match in event_positions.
/// Fallback: K2Node_InputAction stubs are named `InpActEvt_{ActionName}_K2Node_*`,
/// so extract the action name and look up in input_action_positions.
fn resolve_event_position(
    section_name: &str,
    event_positions: &HashMap<String, (i32, i32, String)>,
    input_action_positions: &HashMap<String, (i32, i32, String)>,
) -> Option<(i32, i32, String)> {
    if let Some(pos) = event_positions.get(section_name) {
        return Some(pos.clone());
    }
    let action = extract_input_action_name(section_name)?;
    input_action_positions.get(action).cloned()
}

/// Resolve an event name to its ubergraph section name.
///
/// Most events match directly. K2Node_InputAction events store the short
/// InputActionName (e.g. "Fly") in event_export_indices, but sections use
/// the full stub name (e.g. "InpActEvt_Fly_K2Node_InputActionEvent_6").
fn resolve_section_name<'a>(event_name: &str, sections: &'a [UbergraphSection]) -> Option<&'a str> {
    if let Some(section) = sections.iter().find(|s| s.name == event_name) {
        return Some(&section.name);
    }
    sections
        .iter()
        .find(|s| extract_input_action_name(&s.name) == Some(event_name))
        .map(|s| s.name.as_str())
}

/// Map a line index in the full structured output to its enclosing section (name, start_line).
fn section_for_line<'a>(
    line_idx: usize,
    boundaries: &[(usize, &'a str)],
) -> Option<(usize, &'a str)> {
    boundaries
        .iter()
        .rev()
        .find(|(start, _)| *start <= line_idx)
        .map(|&(start, name)| (start, name))
}

/// Pre-computed ubergraph comment data shared across event sections.
struct UbergraphCommentCtx<'a> {
    small_group_idxs: HashSet<usize>,
    /// Inline comments matched against the full unsplit bytecode, then mapped
    /// to sections. Key is section name, value is (section-local line index, comment).
    section_inline: HashMap<String, Vec<(usize, &'a CommentBox)>>,
    /// Event-wrapping comments per section (box comments containing the event node).
    section_wrapping: HashMap<String, Vec<&'a CommentBox>>,
}

/// Identify box comments that span multiple event nodes (group headers / section dividers).
/// Returns (multi_event_indices, small_group_indices) where small groups have 2-3 events.
fn classify_multi_event_comments(
    comments: &[CommentBox],
    edgraph: &EdGraphData,
) -> (HashSet<usize>, HashSet<usize>) {
    let mut multi_event_idxs: HashSet<usize> = HashSet::new();
    let mut small_group_idxs: HashSet<usize> = HashSet::new();
    for (i, cb) in comments.iter().enumerate() {
        if cb.is_bubble {
            continue;
        }
        let event_count = edgraph
            .event_positions
            .values()
            .chain(edgraph.input_action_positions.values())
            .filter(|(ex, ey, page)| page == &cb.graph_page && cb.contains_point(*ex, *ey))
            .count();
        if event_count > 1 {
            multi_event_idxs.insert(i);
            if event_count <= MAX_MULTI_EVENT_GROUP_SIZE {
                small_group_idxs.insert(i);
            }
        }
    }
    (multi_event_idxs, small_group_idxs)
}

/// Place a comment classified as BubbleOwned or InlineAtEntry into a section.
///
/// Uses BFS ownership to find the preferred event section, then validates against
/// bytecode. Falls back to trying each section in order when ownership is ambiguous.
fn place_pin_classified_comment(
    cb: &CommentBox,
    owner_export: usize,
    ownership_index: &HashMap<usize, String>,
    sections: &[UbergraphSection],
    nodes: &[NodeInfo],
    node_index: &HashMap<usize, &NodeInfo>,
    pin_data: &HashMap<usize, NodePinData>,
) -> Option<(String, usize)> {
    let try_section = |section: &UbergraphSection| -> Option<(String, usize)> {
        let local_idx =
            map_export_to_line(owner_export, nodes, node_index, pin_data, &section.lines)?;
        let refined = if !cb.is_bubble {
            find_comment_line(cb, nodes, &section.lines).unwrap_or(local_idx)
        } else {
            local_idx
        };
        Some((section.name.clone(), refined))
    };

    // Prefer the BFS-owned event's section
    if let Some(event_name) = ownership_index.get(&owner_export) {
        let resolved = resolve_section_name(event_name, sections);
        if let Some(section) = resolved.and_then(|n| sections.iter().find(|s| s.name == n)) {
            if let Some(result) = try_section(section) {
                return Some(result);
            }
        }
    }
    // Fallback: try each event section in order
    sections
        .iter()
        .filter(|s| s.is_event())
        .find_map(try_section)
}

/// Try spatial and cluster fallback paths for a comment that pin-based placement couldn't resolve.
fn place_comment_by_fallback<'a>(
    cb: &'a CommentBox,
    sections: &[UbergraphSection],
    nodes: &[NodeInfo],
    full_lines: &[String],
    section_boundaries: &[(usize, &str)],
    edgraph: &EdGraphData,
    section_inline: &mut HashMap<String, Vec<(usize, &'a CommentBox)>>,
) {
    // Spatial: match against same-page event sections
    for section in sections {
        if !section.is_event() {
            continue;
        }
        let event_page = resolve_event_position(
            &section.name,
            &edgraph.event_positions,
            &edgraph.input_action_positions,
        )
        .map(|(_, _, page)| page);
        if event_page.as_ref().is_some_and(|p| p == &cb.graph_page) {
            if let Some(local_idx) = find_comment_line(cb, nodes, &section.lines) {
                section_inline
                    .entry(section.name.clone())
                    .or_default()
                    .push((local_idx, cb));
                return;
            }
        }
    }

    // Cluster: match against full bytecode, then map to a section
    if let Some(full_line_idx) = find_comment_line_clustered(cb, nodes, full_lines) {
        if let Some((start, section_name)) = section_for_line(full_line_idx, section_boundaries) {
            section_inline
                .entry(section_name.to_string())
                .or_default()
                .push((full_line_idx - start, cb));
        }
    }
}

/// Build all ubergraph comment data in a single pass.
///
/// Uses pin-based event ownership to assign comments to sections when all
/// contained nodes belong to a single event. Falls back to cluster-based
/// matching against full bytecode when ownership is ambiguous or unavailable.
fn build_ubergraph_comment_ctx<'a>(
    comments: &'a [CommentBox],
    nodes: &[NodeInfo],
    full_lines: &[String],
    section_boundaries: &[(usize, &str)],
    sections: &[UbergraphSection],
    edgraph: &EdGraphData,
    pin_data: &HashMap<usize, NodePinData>,
) -> UbergraphCommentCtx<'a> {
    let (multi_event_idxs, small_group_idxs) = classify_multi_event_comments(comments, edgraph);

    let node_index = build_node_index(nodes);
    let section_names: Vec<&str> = sections.iter().map(|s| s.name.as_str()).collect();
    let ownership_index = build_ownership_index(&edgraph.event_node_ownership, &section_names);

    let mut section_wrapping: HashMap<String, Vec<&CommentBox>> = HashMap::new();
    let mut section_inline: HashMap<String, Vec<(usize, &CommentBox)>> = HashMap::new();

    for (i, cb) in comments.iter().enumerate() {
        if multi_event_idxs.contains(&i) {
            continue;
        }

        let placement = classify_comment_by_pins(
            cb,
            pin_data,
            &edgraph.all_node_positions,
            &edgraph.event_export_indices,
        );

        let placed = match placement {
            CommentPlacement::BubbleOwned { owner_export }
            | CommentPlacement::InlineAtEntry {
                entry_export: owner_export,
            } => {
                if let Some((name, idx)) = place_pin_classified_comment(
                    cb,
                    owner_export,
                    &ownership_index,
                    sections,
                    nodes,
                    &node_index,
                    pin_data,
                ) {
                    section_inline.entry(name).or_default().push((idx, cb));
                    true
                } else {
                    false
                }
            }
            CommentPlacement::EventWrapping { ref event_name } => {
                let key = resolve_section_name(event_name, sections)
                    .unwrap_or(event_name)
                    .to_string();
                section_wrapping.entry(key).or_default().push(cb);
                true
            }
            CommentPlacement::Fallback => false,
        };

        if !placed {
            place_comment_by_fallback(
                cb,
                sections,
                nodes,
                full_lines,
                section_boundaries,
                edgraph,
                &mut section_inline,
            );
        }
    }
    for list in section_inline.values_mut() {
        list.sort_by_key(|(idx, _)| *idx);
    }

    UbergraphCommentCtx {
        small_group_idxs,
        section_inline,
        section_wrapping,
    }
}

/// Extract `/*resume:0xHEX*/` offset from a bytecode line.
fn parse_resume_offset(line: &str) -> Option<usize> {
    let marker = line.find("/*resume:0x")?;
    let hex_start = marker + 11;
    let hex_end = line[hex_start..].find("*/")? + hex_start;
    usize::from_str_radix(&line[hex_start..hex_end], 16).ok()
}

/// Build a map of (section_index, resume_block_index) pairs by matching
/// `/*resume:0xHEX*/` annotations in order of appearance to resume blocks.
fn build_delay_resume_map(
    sections: &[UbergraphSection],
    resume_count: usize,
) -> Vec<(usize, usize)> {
    let mut map: Vec<(usize, usize)> = Vec::new();
    let mut resume_idx = 0usize;
    for (si, section) in sections.iter().enumerate() {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            if parse_resume_offset(line).is_some() && resume_idx < resume_count {
                map.push((si, resume_idx));
                resume_idx += 1;
            }
        }
    }
    map
}

/// Build a table mapping full-output line indices to event section names.
fn build_section_boundaries(lines: &[String]) -> Vec<(usize, String)> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| {
            let trimmed = line.trim();
            if trimmed.starts_with("--- ") && trimmed.ends_with(" ---") {
                let name = &trimmed[4..trimmed.len() - 4];
                if !name.is_empty() && name != LATENT_RESUME_SECTION {
                    return Some((i + 1, name.to_string()));
                }
            }
            None
        })
        .collect()
}

/// Emit bytecode lines with interleaved inline comments and resume blocks.
fn emit_section_body(
    buf: &mut String,
    section: &UbergraphSection,
    inline_comments: &[(usize, &CommentBox)],
    resume_blocks: &[ResumeBlock],
    section_resumes: &[usize],
    body_indent: &str,
) {
    let mut resume_pos = 0;
    let mut inline_idx = 0;
    for (i, line) in section.lines.iter().enumerate() {
        while inline_idx < inline_comments.len() && inline_comments[inline_idx].0 == i {
            let ws_len = indent_of(line);
            let indent = format!("{}{}", body_indent, &line[..ws_len]);
            emit_comment(buf, &inline_comments[inline_idx].1.text, &indent);
            inline_idx += 1;
        }

        let clean = strip_resume_annotation(line);
        if clean.trim() == BARE_RETURN {
            continue;
        }
        writeln!(buf, "{}{}", body_indent, clean).unwrap();

        if parse_resume_offset(line).is_some() && resume_pos < section_resumes.len() {
            if let Some(rb) = resume_blocks.get(section_resumes[resume_pos]) {
                for rline in &rb.lines {
                    writeln!(buf, "{}{}", body_indent, rline).unwrap();
                }
            }
            resume_pos += 1;
        }
    }
}

/// Split ubergraph structured output into per-event sections and inline latent resumes.
pub(super) fn emit_ubergraph_events(
    buf: &mut String,
    lines: &[String],
    comments: Option<&[CommentBox]>,
    nodes: Option<&[NodeInfo]>,
    edgraph: &EdGraphData,
    pin_data: &HashMap<usize, NodePinData>,
    callers_map: &HashMap<String, Vec<String>>,
) {
    let (sections, resume_blocks) = split_ubergraph_sections(lines);
    let delay_resume_map = build_delay_resume_map(&sections, resume_blocks.len());

    let section_boundaries = build_section_boundaries(lines);
    let boundary_refs: Vec<(usize, &str)> = section_boundaries
        .iter()
        .map(|(i, name)| (*i, name.as_str()))
        .collect();

    let ctx = if let Some(cbs) = comments {
        build_ubergraph_comment_ctx(
            cbs,
            nodes.unwrap_or(&[]),
            lines,
            &boundary_refs,
            &sections,
            edgraph,
            pin_data,
        )
    } else {
        UbergraphCommentCtx {
            small_group_idxs: HashSet::new(),
            section_inline: HashMap::new(),
            section_wrapping: HashMap::new(),
        }
    };

    // Pre-compute per-section resume block indices from the flat delay_resume_map.
    let mut section_resume_map: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(si, ri) in &delay_resume_map {
        section_resume_map.entry(si).or_default().push(ri);
    }

    let section_names: Vec<&str> = sections.iter().map(|s| s.name.as_str()).collect();
    let action_key_events = compute_action_key_events(&section_names);

    let mut emitted_group_comments: HashSet<usize> = HashSet::new();
    let mut emitted_event_count = 0usize;

    for (si, section) in sections.iter().enumerate() {
        if !section.is_event() {
            continue;
        }
        if section.name.is_empty() {
            let has_content = section.lines.iter().any(|l| {
                let trimmed = l.trim();
                !trimmed.is_empty() && trimmed != "return"
            });
            if !has_content {
                continue;
            }
        }

        section_sep(buf, &mut emitted_event_count);

        let (sig_indent, body_indent) = (super::INDENT, super::BODY_INDENT);

        let empty_wrapping: Vec<&CommentBox> = Vec::new();
        let empty_inline: Vec<(usize, &CommentBox)> = Vec::new();
        let top_level = ctx
            .section_wrapping
            .get(&section.name)
            .unwrap_or(&empty_wrapping);
        let inline = ctx
            .section_inline
            .get(&section.name)
            .unwrap_or(&empty_inline);

        // Emit section header: group comments, callers, wrapping comments, signature
        if !section.name.is_empty() {
            if let Some(cbs) = comments {
                let event_pos = resolve_event_position(
                    &section.name,
                    &edgraph.event_positions,
                    &edgraph.input_action_positions,
                );
                if let Some((ex, ey, ref page)) = event_pos {
                    for (i, cb) in cbs.iter().enumerate() {
                        if ctx.small_group_idxs.contains(&i)
                            && !emitted_group_comments.contains(&i)
                            && cb.graph_page == *page
                            && cb.contains_point(ex, ey)
                        {
                            emit_comment(buf, &cb.text, super::INDENT);
                            emitted_group_comments.insert(i);
                        }
                    }
                }
            }
            if let Some(callers) = callers_map.get(&section.name) {
                writeln!(buf, "{}// called by: {}", sig_indent, callers.join(", ")).unwrap();
            }
            for cb in top_level {
                emit_comment(buf, &cb.text, sig_indent);
            }
            let display_name = clean_event_header(&section.name, &action_key_events);
            if display_name.contains('(') {
                writeln!(buf, "{}{}:", sig_indent, display_name).unwrap();
            } else {
                writeln!(buf, "{}{}():", sig_indent, display_name).unwrap();
            }
        }

        let section_resumes = section_resume_map
            .get(&si)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);
        emit_section_body(
            buf,
            section,
            inline,
            &resume_blocks,
            section_resumes,
            body_indent,
        );
    }
}

/// Scan structured ubergraph output for calls to local functions.
/// Splits by `--- EventName ---` markers and attributes calls to the current event.
/// Also handles latent resume blocks: Delay() with `/*resume:0xHEX*/` annotations
/// trigger resume blocks from `(latent resume)` sections.
pub(super) fn scan_structured_calls(
    lines: &[String],
    local_functions: &HashSet<String>,
    callees_map: &mut HashMap<String, Vec<String>>,
    callers_map: &mut HashMap<String, Vec<String>>,
) {
    let (sections, resume_blocks) = split_ubergraph_sections(lines);

    // Build resume mapping: for each event section with a Delay()+resume annotation,
    // associate the resume block with that event
    let mut resume_idx = 0usize;
    let mut event_resume_lines: HashMap<String, Vec<String>> = HashMap::new();
    for section in &sections {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            if line.contains("/*resume:0x") && resume_idx < resume_blocks.len() {
                event_resume_lines
                    .entry(section.name.clone())
                    .or_default()
                    .extend(resume_blocks[resume_idx].lines.iter().cloned());
                resume_idx += 1;
            }
        }
    }

    // Helper to record a caller->callee edge
    let mut record_call = |caller: &str, callee: &str| {
        let entry = callees_map.entry(caller.to_string()).or_default();
        if !entry.contains(&callee.to_string()) {
            entry.push(callee.to_string());
        }
        let entry = callers_map.entry(callee.to_string()).or_default();
        if !entry.contains(&caller.to_string()) {
            entry.push(caller.to_string());
        }
    };

    // Scan each event section + its resume blocks for local function calls
    for section in &sections {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            for callee in find_local_calls(line.trim(), local_functions) {
                if callee != section.name {
                    record_call(&section.name, &callee);
                }
            }
        }
        if let Some(resume_lines) = event_resume_lines.get(&section.name) {
            for line in resume_lines {
                for callee in find_local_calls(line.trim(), local_functions) {
                    if callee != section.name {
                        record_call(&section.name, &callee);
                    }
                }
            }
        }
    }
}

/// Check if a function is a stub that just dispatches to the ubergraph.
/// Stubs contain only an ExecuteUbergraph_X(N) call, plus optional return/persistent-frame lines.
pub(super) fn is_ubergraph_stub(props: &[Property], ug_name: &str) -> bool {
    let lines = find_prop_str_items_any(props, &["BytecodeSummary", "Bytecode"]);
    let meaningful: Vec<&str> = lines
        .iter()
        .map(|line| super::strip_offset_prefix(line).trim())
        .filter(|code| !matches!(*code, "" | BARE_RETURN | RETURN_NOP))
        .collect();
    if meaningful.is_empty() {
        return false;
    }
    let prefix = format!("{}(", ug_name);
    meaningful.iter().any(|line| line.starts_with(&prefix))
        && meaningful
            .iter()
            .all(|line| line.starts_with(&prefix) || line.contains("[persistent]"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::pipeline::resolve_cross_segment_jumps;

    fn stmt(offset: usize, text: &str) -> BcStatement {
        BcStatement::new(offset, text.to_string())
    }

    #[test]
    fn cross_segment_jump_past_end_not_rewritten() {
        // jump 0x2000 is past max offset (120) -> find_target_idx_or_end resolves
        // this as jump-to-end, so resolve_cross_segment_jumps leaves it alone
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x2000"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x2000"); // unchanged, past-end is resolvable
                                                  // Sentinel still appended
        assert_eq!(stmts.last().unwrap().text, "return nop");
        assert_eq!(stmts.last().unwrap().mem_offset, 121);
    }

    #[test]
    fn unresolvable_jump_rewritten() {
        // jump 0x50 (=80) is before the segment start and >4 bytes from any
        // statement -> find_target_idx would return None -> rewritten to sentinel
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x50"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x79"); // rewritten to sentinel (121)
    }

    #[test]
    fn unresolvable_conditional_jump_rewritten() {
        // if !(cond) jump 0x50, target not resolvable -> rewritten
        let mut stmts = vec![
            stmt(100, "if !(IsValid(X)) jump 0x50"),
            stmt(110, "DoThing()"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[0].text, "if !(IsValid(X)) jump 0x79");
    }

    #[test]
    fn local_jump_preserved() {
        // jump 0x78 (=120) is within the segment -> preserved
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x78"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x78"); // unchanged
    }

    #[test]
    fn local_fuzzy_jump_preserved() {
        // jump 0x75 (=117) is within +/-4 of offset 120 -> preserved as local
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x75"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x75"); // unchanged, fuzzy match
    }

    #[test]
    fn fuzzy_jump_beyond_4_bytes_rewritten() {
        // jump 0x73 (=115) is 5 bytes from offset 120, outside +/-4 window
        // and >4 from offset 110 too -> unresolvable -> rewritten
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x73"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x79"); // rewritten, outside +/-4
    }

    #[test]
    fn strip_orphaned_empty_if() {
        let mut lines = vec![
            "if (cond) {".to_string(),
            "}".to_string(),
            "DoThing()".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(lines, vec!["DoThing()"]);
    }

    #[test]
    fn strip_orphaned_empty_if_else() {
        // An `if (cond) { } else { body }` pattern with an empty then-branch
        // should become `if (!cond) { body }`, preserving the guard rather
        // than unconditionally emitting the else body.
        let mut lines = vec![
            "if (cond) {".to_string(),
            "} else {".to_string(),
            "    DoThing()".to_string(),
            "}".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(
            lines,
            vec![
                "if (!cond) {".to_string(),
                "    DoThing()".to_string(),
                "}".to_string(),
            ]
        );
    }

    #[test]
    fn strip_orphaned_else_empty() {
        let mut lines = vec![
            "    DoThing()".to_string(),
            "} else {".to_string(),
            "}".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(lines, vec!["    DoThing()"]);
    }

    #[test]
    fn strip_goto_label_at_end() {
        // goto L_01fa where label is at end of output (convergence to end).
        // The trailing `}` is balanced (closes the if-block) and preserved.
        let mut lines = vec![
            "if (cast(X)) {".to_string(),
            "    iface(X).CanConsume(Y)".to_string(),
            "    L_01fa:".to_string(),
            "}".to_string(),
            "goto L_01fa".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(
            lines,
            vec![
                "if (cast(X)) {".to_string(),
                "    iface(X).CanConsume(Y)".to_string(),
                "}".to_string(),
            ]
        );
    }

    #[test]
    fn strip_backward_goto_to_start() {
        // backward goto to label at start of segment (Sequence artifact)
        let mut lines = vec![
            "L_0c3e:".to_string(),
            "AttemptGrip(true)".to_string(),
            "goto L_0c3e".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(lines, vec!["AttemptGrip(true)"]);
    }

    #[test]
    fn strip_goto_fall_through() {
        // goto immediately before its label with only } between (fall-through)
        // The } is structural (closes an if-block) and stays
        let mut lines = vec![
            "DoThing()".to_string(),
            "goto L_0100".to_string(),
            "}".to_string(),
            "L_0100:".to_string(),
            "DoOther()".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(
            lines,
            vec![
                "DoThing()".to_string(),
                "}".to_string(),
                "DoOther()".to_string(),
            ]
        );
    }

    #[test]
    fn preserve_multi_ref_goto() {
        // Labels with 2+ gotos are preserved (handled by extract_convergence)
        let mut lines = vec![
            "goto L_0100".to_string(),
            "L_0100:".to_string(),
            "DoThing()".to_string(),
            "goto L_0100".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert!(lines.iter().any(|l| l.contains("L_0100")));
    }

    #[test]
    fn strip_bare_temp_expression() {
        let mut lines = vec![
            "$InputActionEvent_Key_4".to_string(),
            "self.EnableDebugHandRotation = true".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(lines, vec!["self.EnableDebugHandRotation = true"]);
    }

    #[test]
    fn strip_bare_boolean_literal() {
        let mut lines = vec!["false".to_string()];
        strip_orphaned_blocks(&mut lines);
        assert!(lines.is_empty());
    }

    #[test]
    fn keep_indented_bare_expression() {
        // Inside a block, bare expressions should be preserved
        let mut lines = vec![
            "if (cond) {".to_string(),
            "    $SomeVar".to_string(),
            "}".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert!(lines.iter().any(|l| l.contains("$SomeVar")));
    }

    #[test]
    fn collapse_preserves_non_trampoline_backward_jump() {
        // Backward jump that the chain-walk cannot collapse (target is a real
        // statement, not another bare jump) must survive collapse_jump_chains.
        // The predecessor is a plain call (not a flow terminator) and nothing
        // else references the jump's offset, so the only thing keeping it alive
        // is the elided_offsets invariant: offsets absent from that set are
        // never stripped.
        let mut stmts = vec![
            stmt(0x10, "loop_body_call()"),
            stmt(0x20, "another_call()"),
            stmt(0x30, "jump 0x10"),
            stmt(0x40, "tail_call()"),
        ];
        collapse_jump_chains(&mut stmts);
        let has_backward_jump = stmts.iter().any(|s| s.text.trim() == "jump 0x10");
        assert!(
            has_backward_jump,
            "backward jump not in elided_offsets must survive collapse_jump_chains; got {:?}",
            stmts.iter().map(|s| s.text.clone()).collect::<Vec<_>>()
        );
    }
}
