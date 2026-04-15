//! Ubergraph event splitting, latent resume block matching, and structured output processing.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::flow::{
    find_first_unmatched_pop, parse_jump, reorder_convergence, reorder_flow_patterns,
    strip_latch_boilerplate,
};
use crate::bytecode::pipeline::structure_segment;
use crate::bytecode::structure::apply_indentation;
use crate::bytecode::transforms::{
    fold_switch_enum_cascade, strip_orphaned_blocks, strip_unmatched_braces,
};
use crate::bytecode::{
    split_by_sequence_markers, BcStatement, OffsetMap, JUMP_OFFSET_TOLERANCE, POP_FLOW, RETURN_NOP,
};
use crate::helpers::indent_of;
use crate::resolve::find_prop_str_items_any;
use crate::types::{NodePinData, Property};

use super::comments::{
    build_node_index, build_ownership_index, classify_comment_by_pins, find_comment_line,
    find_comment_line_clustered, map_export_to_line, CommentPlacement,
};
use super::edgraph::EdGraphData;
use super::{
    emit_comment, find_local_calls, section_sep, strip_resume_annotation, CommentBox, NodeInfo,
    ResumeBlock, UbergraphSection, FUZZY_LABEL_WINDOW, LATENT_RESUME_SECTION,
};

/// Maximum number of events a comment box can contain and still be treated as
/// an intentional multi-event group. Boxes containing more events are likely
/// organizational section dividers placed for visual layout, not semantic groupings.
const MAX_MULTI_EVENT_GROUP_SIZE: usize = 3;

/// Relocate event body code that the compiler placed non-contiguously.
///
/// UE4 sometimes compiles an event entry point as a bare backward `jump 0xXXX`
/// (a trampoline), with the actual body sitting physically within another event's
/// offset range. Label-based splitting would misattribute the body to the wrong
/// event. This pass detects those trampolines and moves the target block inline
/// at the entry point so splitting works correctly.
fn inline_event_trampolines(stmts: &mut Vec<BcStatement>, sorted_labels: &[(usize, &String)]) {
    // Collect label entry offsets for the "no other label in the block" safety check.
    let label_offsets: HashSet<usize> = sorted_labels.iter().map(|&(off, _)| off).collect();

    // Process one trampoline per iteration because each relocation shifts indices.
    loop {
        let offset_map = OffsetMap::build(stmts);
        let mut relocated = false;

        for &(label_off, _) in sorted_labels {
            // Find entry statement (same fuzzy matching as split_stmts_by_labels)
            let entry_idx = match stmts.iter().position(|s| {
                s.mem_offset >= label_off && s.mem_offset <= label_off + FUZZY_LABEL_WINDOW
            }) {
                Some(i) => i,
                None => continue,
            };

            // Must be a bare unconditional jump
            let target_off = match parse_jump(&stmts[entry_idx].text) {
                Some(t) => t,
                None => continue,
            };

            // Resolve target in current statement list
            let target_idx = match offset_map.find_fuzzy(target_off, JUMP_OFFSET_TOLERANCE) {
                Some(i) => i,
                None => continue,
            };

            // Only backward jumps (body placed earlier than entry point)
            if target_idx >= entry_idx {
                continue;
            }

            // Block ends at the first pop_flow at depth 0 (inclusive),
            // which exits the event back to the ubergraph's initial push_flow.
            let Some(block_end) = find_first_unmatched_pop(stmts, target_idx, entry_idx) else {
                continue;
            };

            // Safety: skip if another label entry falls within the block we'd move
            let block_start_off = stmts[target_idx].mem_offset;
            let block_end_off = stmts[block_end].mem_offset;
            let other_label_in_block = label_offsets
                .iter()
                .any(|&off| off != label_off && off >= block_start_off && off <= block_end_off);
            if other_label_in_block {
                continue;
            }

            // Extract the block, then replace the trampoline jump with it.
            // After drain, entry_idx shifts backward by block length.
            let trampoline_off = stmts[entry_idx].mem_offset;
            let block_len = block_end - target_idx + 1;
            let mut block: Vec<BcStatement> =
                stmts.drain(target_idx..target_idx + block_len).collect();

            // Stamp the first relocated statement with the trampoline's offset so
            // split_stmts_by_labels can still match the label to this event.
            block[0].mem_offset = trampoline_off;

            let new_entry_idx = entry_idx - block_len;
            stmts.splice(new_entry_idx..new_entry_idx + 1, block);

            relocated = true;
            break; // Restart: indices have shifted
        }

        if !relocated {
            break;
        }
    }
}

/// Split raw BcStatements into per-event segments using label offsets.
/// Each segment gets its own name (from the label) and a slice of statements.
/// Statements before the first label get an empty name (latent resume code).
///
/// Uses exact offset matching (not watermark) because flow reordering moves
/// Sequence body blocks inline; those blocks retain their original (high)
/// offsets which would trigger wrong segment splits with a >= comparison.
fn split_stmts_by_labels(
    stmts: &[BcStatement],
    sorted_labels: &[(usize, &String)],
) -> Vec<(String, Vec<BcStatement>)> {
    // Pre-match each label to the first statement at or just after its offset.
    // Exact matching fails because trace opcodes (filtered by the decoder) cause
    // event entry points to land a few bytes before the first visible statement.
    // We use a bounded window (8 bytes) instead of unbounded >= to prevent
    // moved Sequence body blocks from triggering wrong splits.
    let mut matched: HashMap<usize, String> = HashMap::new(); // stmt_idx -> label name
    let mut used_labels: HashSet<usize> = HashSet::new();
    for &(label_off, label_name) in sorted_labels {
        for (i, stmt) in stmts.iter().enumerate() {
            if matched.contains_key(&i) {
                continue; // already claimed by another label
            }
            if stmt.mem_offset >= label_off && stmt.mem_offset <= label_off + FUZZY_LABEL_WINDOW {
                matched.insert(i, label_name.clone());
                used_labels.insert(label_off);
                break;
            }
        }
    }

    let mut segments: Vec<(String, Vec<BcStatement>)> = Vec::new();
    let mut current_name = String::new();
    let mut current_stmts: Vec<BcStatement> = Vec::new();

    for (i, stmt) in stmts.iter().enumerate() {
        if let Some(name) = matched.get(&i) {
            if !current_stmts.is_empty() || !current_name.is_empty() {
                segments.push((current_name.clone(), current_stmts));
                current_stmts = Vec::new();
            }
            current_name = name.clone();
        }
        current_stmts.push(stmt.clone());
    }
    if !current_stmts.is_empty() || !current_name.is_empty() {
        segments.push((current_name, current_stmts));
    }
    segments
}

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
            if line.trim() == "return" {
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

/// Build structured ubergraph output from raw bytecode statements and event labels.
///
/// Flow-reorders the entire ubergraph, splits into per-event segments, structures
/// each independently, and produces the final line output.
pub(super) fn build_ubergraph_structured(
    stmts: Vec<BcStatement>,
    ubergraph_labels: &HashMap<usize, String>,
) -> Option<Vec<String>> {
    if stmts.is_empty() {
        return None;
    }

    // Strip FlipFlop/DoOnce latch boilerplate before flow reordering,
    // so their pop_flow boundaries don't fragment event bodies.
    let mut cleaned = stmts;
    strip_latch_boilerplate(&mut cleaned);
    // Flow reorder the entire UberGraph; Sequence node body blocks are
    // scattered across events and push_flow/pop_flow pairs need the
    // whole function to resolve correctly.
    let mut reordered = reorder_flow_patterns(&cleaned);
    reorder_convergence(&mut reordered);

    // Now split into per-event segments and process each through
    // inline/structure/cleanup independently. This produces much
    // cleaner pseudocode because the structurer and inliner aren't
    // confused by cross-event jumps and shared temp variables.
    let mut sorted_labels: Vec<(usize, &String)> =
        ubergraph_labels.iter().map(|(k, v)| (*k, v)).collect();
    sorted_labels.sort_by_key(|(offset, _)| *offset);

    // Relocate event bodies that the compiler placed as backward trampolines.
    inline_event_trampolines(&mut reordered, &sorted_labels);

    let segments = split_stmts_by_labels(&reordered, &sorted_labels);
    let mut all_lines: Vec<String> = Vec::new();
    for (name, segment_stmts) in &segments {
        if !name.is_empty() {
            all_lines.push(format!("--- {} ---", name));
        } else if !segment_stmts.is_empty() {
            all_lines.push(format!("--- {} ---", LATENT_RESUME_SECTION));
        }
        if segment_stmts.is_empty() {
            continue;
        }

        // Latent resume segments contain multiple independent blocks separated
        // by `return nop`. Split and structure each block independently so that
        // dead-code elimination doesn't kill all blocks after the first return.
        if name.is_empty() {
            let resume_blocks = split_at_return_nop(segment_stmts);
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

        let sub_segments = split_by_sequence_markers(segment_stmts);
        if sub_segments.len() <= 1 {
            all_lines.extend(structure_segment(segment_stmts));
        } else {
            // Process each sequence body independently so that
            // cross-body jumps don't cause if-blocks to span
            // across sequence boundaries.
            for (marker, body) in &sub_segments {
                if let Some(m) = marker {
                    all_lines.push(m.clone());
                }
                if !body.is_empty() {
                    all_lines.extend(structure_segment(body));
                }
            }
        }
    }
    // Final cleanup: strip cross-body orphaned braces left
    // over from per-body processing, then remove any empty
    // if-blocks or else-blocks that the brace removal exposed.
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

/// Resolve indentation for an event section based on group membership.
fn event_indentation(
    section_name: &str,
    ctx: &UbergraphCommentCtx,
    comments: Option<&[CommentBox]>,
    edgraph: &EdGraphData,
) -> (&'static str, &'static str) {
    let event_pos = if !section_name.is_empty() {
        resolve_event_position(
            section_name,
            &edgraph.event_positions,
            &edgraph.input_action_positions,
        )
    } else {
        None
    };
    let in_group = match (comments, &event_pos) {
        (Some(cbs), Some((ex, ey, page))) => cbs.iter().enumerate().any(|(i, cb)| {
            ctx.small_group_idxs.contains(&i)
                && cb.graph_page == *page
                && cb.contains_point(*ex, *ey)
        }),
        _ => false,
    };
    if in_group {
        ("    ", "        ")
    } else {
        ("  ", "    ")
    }
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
        if clean.trim() == "return" {
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

        let (sig_indent, body_indent) = event_indentation(&section.name, &ctx, comments, edgraph);

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
                            emit_comment(buf, &cb.text, "  ");
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
            writeln!(buf, "{}{}():", sig_indent, section.name).unwrap();
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
        .filter(|code| !matches!(*code, "" | "return" | RETURN_NOP))
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
    fn split_exact_match_ignores_high_offsets() {
        // Simulate flow-reordered UberGraph: Event A at offset 100 has a Sequence
        // body moved inline from offset 5000. Event B starts at offset 1000.
        // The old watermark approach would split at offset 5000 >= 1000.
        let stmts = vec![
            stmt(100, "// sequence [0]:"),
            stmt(5000, "body_stmt_1"),
            stmt(5010, "body_stmt_2"),
            stmt(100, "// sequence [1]:"),
            stmt(150, "inline_stmt"),
            stmt(1000, "event_b_start"),
            stmt(1020, "event_b_stmt"),
        ];
        let event_a = "EventA".to_string();
        let event_b = "EventB".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event_a), (1000, &event_b)];

        let segments = split_stmts_by_labels(&stmts, &labels);

        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].0, "EventA");
        assert_eq!(segments[0].1.len(), 5); // all stmts before EventB
        assert_eq!(segments[1].0, "EventB");
        assert_eq!(segments[1].1.len(), 2);
    }

    #[test]
    fn split_latent_resume_before_first_label() {
        let stmts = vec![
            stmt(50, "latent_code"),
            stmt(100, "event_start"),
            stmt(120, "event_stmt"),
        ];
        let event_a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event_a)];

        let segments = split_stmts_by_labels(&stmts, &labels);

        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].0, ""); // unnamed latent resume
        assert_eq!(segments[0].1.len(), 1);
        assert_eq!(segments[1].0, "EventA");
        assert_eq!(segments[1].1.len(), 2);
    }

    #[test]
    fn split_fuzzy_match_within_8_bytes() {
        // Label offset 97 matches first stmt at offset 100 (3 bytes off, within 8-byte window)
        let stmts = vec![stmt(100, "event_start"), stmt(120, "event_stmt")];
        let event_a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(97, &event_a)];

        let segments = split_stmts_by_labels(&stmts, &labels);

        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].0, "EventA");
        assert_eq!(segments[0].1.len(), 2);
    }

    #[test]
    fn split_rejects_match_beyond_8_bytes() {
        // Label offset 90 does NOT match stmt at offset 100 (10 bytes off, beyond window)
        let stmts = vec![stmt(100, "event_start"), stmt(120, "event_stmt")];
        let event_a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(90, &event_a)];

        let segments = split_stmts_by_labels(&stmts, &labels);

        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].0, ""); // unmatched, no label found
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
        let mut lines = vec![
            "if (cond) {".to_string(),
            "} else {".to_string(),
            "    DoThing()".to_string(),
            "}".to_string(),
        ];
        strip_orphaned_blocks(&mut lines);
        assert_eq!(lines, vec!["    DoThing()"]);
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
}
