//! Bytecode structuring pipeline: flow reordering, temp inlining,
//! if/else reconstruction, expression cleanup, and pattern folding.
//!
//! Three entry points cover different structuring contexts:
//! - [`structure_function`]: full pipeline for regular functions (sequence splitting, cascade folding)
//! - [`structure_segment`]: single-segment pipeline for ubergraph events (cross-segment jump resolution)
//! - [`structure_and_cleanup`]: core structure + cleanup for one contiguous block

use std::collections::HashMap;

use super::decode::BcStatement;
use super::flow::{reorder_convergence, reorder_flow_patterns, strip_latch_boilerplate};
use super::structure::{apply_indentation, structure_bytecode};
use super::transforms::{
    cleanup_structured_output, collect_jump_targets, discard_unused_assignments,
    discard_unused_assignments_text, eliminate_constant_condition_branches,
    fold_cascade_across_sequences, fold_summary_patterns, fold_switch_enum_cascade,
    inline_constant_temps, inline_constant_temps_text, inline_single_use_temps,
    rename_loop_temp_vars, strip_inlined_break_calls, strip_orphaned_blocks,
    strip_unmatched_braces,
};
use super::{
    split_by_sequence_markers, OffsetMap, JUMP_OFFSET_TOLERANCE, RETURN_NOP, SEQUENCE_MARKER_PREFIX,
};

/// Run the full statement structuring pipeline: flow reordering, temp inlining,
/// if/else reconstruction, expression cleanup, and pattern folding.
///
/// When the function has Sequence pins, splits by `// sequence [N]:` markers
/// and structures each body independently. This prevents switch cascades and
/// other control flow from spanning across sequence boundaries.
pub fn structure_function(stmts: &[BcStatement]) -> Vec<String> {
    let mut cleaned = stmts.to_vec();
    strip_latch_boilerplate(&mut cleaned);
    let mut reordered = reorder_flow_patterns(&cleaned);
    reorder_convergence(&mut reordered);
    let jump_targets = collect_jump_targets(&reordered);
    inline_constant_temps(&mut reordered, &jump_targets);
    inline_single_use_temps(&mut reordered);
    discard_unused_assignments(&mut reordered);

    let sub_segments = split_by_sequence_markers(&reordered);

    // When a switch-enum cascade in the prefix targets sequence pin bodies,
    // fold it into switch/case text with each case body structured
    // independently. This prevents the cascade scaffold from being separated
    // from its targets by sequence splitting.
    if sub_segments.len() > 1 {
        let first_marker_idx = reordered
            .iter()
            .position(|s| s.text.starts_with(SEQUENCE_MARKER_PREFIX))
            .unwrap_or(0);
        if first_marker_idx > 0 {
            if let Some(mut lines) =
                fold_cascade_across_sequences(&reordered, first_marker_idx, structure_and_cleanup)
            {
                // Re-apply indentation on the combined output so the
                // switch/case wrapper and case bodies are properly nested.
                apply_indentation(&mut lines);
                return lines;
            }
        }
    }
    if sub_segments.len() <= 1 {
        return structure_and_cleanup(&reordered);
    }

    // Structure each pin independently (proper if/else blocks per pin),
    // but defer pattern folding to the combined output so cross-pin
    // variable references are preserved.
    let mut all_lines = Vec::new();
    for (marker, body) in &sub_segments {
        if let Some(marker_text) = marker {
            all_lines.push(marker_text.clone());
        }
        if !body.is_empty() {
            let mut structured = structure_bytecode(body, &HashMap::new());
            cleanup_structured_output(&mut structured);
            all_lines.extend(structured);
        }
    }
    post_structure_cleanup(&mut all_lines);
    all_lines
}

/// Structure a single segment of bytecode (no sequence splitting).
///
/// Resolves cross-segment jumps, inlines temps, then runs the full
/// structure + cleanup pipeline. Used by ubergraph per-event processing.
pub fn structure_segment(stmts: &[BcStatement]) -> Vec<String> {
    let mut seg = stmts.to_vec();
    resolve_cross_segment_jumps(&mut seg);
    let jump_targets = collect_jump_targets(&seg);
    inline_constant_temps(&mut seg, &jump_targets);
    inline_single_use_temps(&mut seg);
    discard_unused_assignments(&mut seg);
    structure_and_cleanup(&seg)
}

/// Core: structure + cleanup for one contiguous block of bytecode.
///
/// Also used as the callback for [`fold_cascade_across_sequences`].
pub fn structure_and_cleanup(stmts: &[BcStatement]) -> Vec<String> {
    let mut structured = structure_bytecode(stmts, &HashMap::new());
    cleanup_structured_output(&mut structured);
    post_structure_cleanup(&mut structured);
    structured
}

/// Post-structure cleanup pipeline: temp inlining, pattern folding,
/// dead code removal, switch cascade folding, indentation, and brace fixup.
///
/// Called after `structure_bytecode` + initial `cleanup_structured_output` on
/// both single-segment and multi-segment paths.
fn post_structure_cleanup(lines: &mut Vec<String>) {
    // Temp inlining runs post-structure so that structure detection has the
    // full statement array with intact mem_offsets for jump target resolution.
    inline_constant_temps_text(lines);
    discard_unused_assignments_text(lines);
    fold_summary_patterns(lines);
    // Remove Break* calls left orphaned by fold_break_patterns: when out params
    // were inlined by an earlier pass, fold_break_patterns skips the call but
    // the accessor-form arguments make the call dead code.
    strip_inlined_break_calls(lines);
    // Re-run after pattern folding: temp inlining can create new constant-condition
    // branches (e.g., inlining `Temp_bool = true` into `if (!Temp_bool) return`).
    eliminate_constant_condition_branches(lines);
    strip_orphaned_blocks(lines);
    rename_loop_temp_vars(lines);
    fold_switch_enum_cascade(lines);
    // Re-run cleanup: switch folding can expose dead code from pin-boundary
    // sentinels that were hidden inside the cascade's brace nesting.
    cleanup_structured_output(lines);
    strip_unmatched_braces(lines);
    apply_indentation(lines);
    // Strip bare "// on loop complete:" markers (used internally by dedup_completion_paths
    // but redundant in output since the closing brace already shows the loop ended).
    // Annotated variants like "// on loop complete: (same as pre-loop setup)" are kept.
    lines.retain(|line| line.trim() != "// on loop complete:");
}

/// Rewrite jumps targeting offsets outside or unresolvable within the current segment.
///
/// Uses the same +/-4 byte fuzzy lookup as `structure_bytecode`. Unresolvable targets
/// become past-end sentinels (implicit return/break).
pub(crate) fn resolve_cross_segment_jumps(stmts: &mut Vec<BcStatement>) {
    if stmts.is_empty() {
        return;
    }

    let offset_map = OffsetMap::build(stmts);
    let max_offset = stmts.iter().map(|s| s.mem_offset).max().unwrap();
    let sentinel_offset = max_offset + 1;

    for stmt in stmts.iter_mut() {
        // Pattern: "if !(COND) jump 0xHEX"
        if let Some(jump_pos) = stmt.text.find(") jump 0x") {
            let hex_start = jump_pos + 9; // after ") jump 0x"
            let hex_str = &stmt.text[hex_start..];
            let hex_end = hex_str
                .find(|c: char| !c.is_ascii_hexdigit())
                .unwrap_or(hex_str.len());
            if let Ok(t) = usize::from_str_radix(&hex_str[..hex_end], 16) {
                if t <= max_offset && offset_map.find_fuzzy(t, JUMP_OFFSET_TOLERANCE).is_none() {
                    stmt.text =
                        format!("{}jump 0x{:x}", &stmt.text[..jump_pos + 2], sentinel_offset);
                }
            }
        }
        // Pattern: standalone "jump 0xHEX"
        else if let Some(hex_str) = stmt.text.strip_prefix("jump 0x") {
            if let Ok(t) = usize::from_str_radix(hex_str, 16) {
                if t <= max_offset && offset_map.find_fuzzy(t, JUMP_OFFSET_TOLERANCE).is_none() {
                    stmt.text = format!("jump 0x{:x}", sentinel_offset);
                }
            }
        }
    }

    // Add sentinel so find_target_idx_or_end can resolve to it
    stmts.push(BcStatement::new(sentinel_offset, RETURN_NOP.to_string()));
}
