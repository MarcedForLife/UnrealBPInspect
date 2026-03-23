//! Ubergraph event splitting, latent resume block matching, and structured output processing.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::{
    cleanup_structured_output, discard_unused_assignments, fold_summary_patterns,
    inline_constant_temps, inline_single_use_temps, reorder_convergence, reorder_flow_patterns,
    strip_orphaned_blocks, strip_unmatched_braces, structure_bytecode, BcStatement,
};
use crate::resolve::*;
use crate::types::*;

use super::comments::find_comment_line;
use super::{
    emit_comment, find_local_calls, section_sep, strip_resume_annotation, CommentBox, NodeInfo,
    ResumeBlock, UbergraphSection, FUZZY_LABEL_WINDOW,
};

/// Rewrite unresolvable jumps to point past the end of the segment.
///
/// In UberGraph bytecode, each event is processed as an independent segment.
/// Jumps targeting offsets outside the current segment are always "return from
/// this event"; control goes back to the dispatcher.  But even intra-segment
/// jumps can fail to resolve when filtered trace opcodes shift the visible
/// statement offsets away from the raw bytecode targets.
///
/// This function uses the **same +/-4-byte sorted-offset lookup** that
/// `structure_bytecode`'s `find_target_idx` uses.  Any jump target that would
/// return `None` there (and isn't past the end) is rewritten to a sentinel
/// offset, which `find_target_idx_or_end` resolves as jump-to-end (implicit
/// return or break).
fn resolve_cross_segment_jumps(stmts: &mut Vec<BcStatement>) {
    if stmts.is_empty() {
        return;
    }

    // Build exact map and sorted offsets, mirrors structure_bytecode logic
    let exact_map: HashSet<usize> = stmts.iter().map(|s| s.mem_offset).collect();
    let mut sorted_offsets: Vec<usize> = exact_map.iter().copied().collect();
    sorted_offsets.sort();

    let max_offset = *sorted_offsets.last().unwrap();
    let sentinel_offset = max_offset + 1;

    // Replicate structure_bytecode's find_target_idx: exact match, then +/-4
    // binary-search fallback.  Returns true if the target would resolve.
    let is_resolvable = |target: usize| -> bool {
        // Past end -> find_target_idx_or_end returns stmts.len() (end sentinel)
        if target > max_offset {
            return true;
        }
        // Exact match
        if exact_map.contains(&target) {
            return true;
        }
        // +/-4 fuzzy match via sorted offsets (same as structure.rs)
        let pos = sorted_offsets.partition_point(|&off| off <= target);
        let below_dist = if pos > 0 {
            target.saturating_sub(sorted_offsets[pos - 1])
        } else {
            usize::MAX
        };
        let above_dist = if pos < sorted_offsets.len() {
            sorted_offsets[pos].saturating_sub(target)
        } else {
            usize::MAX
        };
        below_dist.min(above_dist) <= 4
    };

    for stmt in stmts.iter_mut() {
        // Pattern: "if !(COND) jump 0xHEX"
        if let Some(jump_pos) = stmt.text.find(") jump 0x") {
            let hex_start = jump_pos + 9; // after ") jump 0x"
            let hex_str = &stmt.text[hex_start..];
            let hex_end = hex_str
                .find(|c: char| !c.is_ascii_hexdigit())
                .unwrap_or(hex_str.len());
            if let Ok(t) = usize::from_str_radix(&hex_str[..hex_end], 16) {
                if !is_resolvable(t) {
                    stmt.text =
                        format!("{}jump 0x{:x}", &stmt.text[..jump_pos + 2], sentinel_offset);
                }
            }
        }
        // Pattern: standalone "jump 0xHEX"
        else if let Some(hex_str) = stmt.text.strip_prefix("jump 0x") {
            if let Ok(t) = usize::from_str_radix(hex_str, 16) {
                if !is_resolvable(t) {
                    stmt.text = format!("jump 0x{:x}", sentinel_offset);
                }
            }
        }
    }

    // Add sentinel so find_target_idx_or_end can resolve to it
    stmts.push(BcStatement {
        mem_offset: sentinel_offset,
        text: "return nop".to_string(),
    });
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

/// Run the full structuring pipeline on a slice of BcStatements:
/// resolve cross-segment jumps, inline temps, structure, cleanup.
fn structure_segment(stmts: &[BcStatement]) -> Vec<String> {
    let mut seg = stmts.to_vec();
    resolve_cross_segment_jumps(&mut seg);
    inline_constant_temps(&mut seg);
    inline_single_use_temps(&mut seg);
    discard_unused_assignments(&mut seg);
    let mut structured = structure_bytecode(&seg, &HashMap::new());
    cleanup_structured_output(&mut structured);
    fold_summary_patterns(&mut structured);
    strip_orphaned_blocks(&mut structured);
    structured
}

/// Split a segment's BcStatements at `// sequence [N]:` markers.
/// Returns a list of (optional marker text, body statements).
/// When the segment has no sequence markers, returns a single entry.
fn split_by_sequence_markers(stmts: &[BcStatement]) -> Vec<(Option<String>, Vec<BcStatement>)> {
    let marker_indices: Vec<usize> = stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| s.text.starts_with("// sequence ["))
        .map(|(i, _)| i)
        .collect();

    if marker_indices.is_empty() {
        return vec![(None, stmts.to_vec())];
    }

    let mut result = Vec::new();

    // Statements before the first marker (prefix)
    if marker_indices[0] > 0 {
        result.push((None, stmts[..marker_indices[0]].to_vec()));
    }

    for (i, &start) in marker_indices.iter().enumerate() {
        let marker_text = stmts[start].text.clone();
        let body_start = start + 1;
        let body_end = if i + 1 < marker_indices.len() {
            marker_indices[i + 1]
        } else {
            stmts.len()
        };
        let body: Vec<BcStatement> = if body_start < body_end {
            stmts[body_start..body_end].to_vec()
        } else {
            Vec::new()
        };
        result.push((Some(marker_text), body));
    }

    result
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
        if section.name != "(latent resume)" {
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

    // Flow reorder the entire UberGraph first; Sequence node
    // body blocks are scattered across events and push_flow/pop_flow
    // pairs need the whole function to resolve correctly.
    let mut reordered = reorder_flow_patterns(&stmts);
    reorder_convergence(&mut reordered);

    // Now split into per-event segments and process each through
    // inline/structure/cleanup independently. This produces much
    // cleaner pseudocode because the structurer and inliner aren't
    // confused by cross-event jumps and shared temp variables.
    let mut sorted_labels: Vec<(usize, &String)> =
        ubergraph_labels.iter().map(|(k, v)| (*k, v)).collect();
    sorted_labels.sort_by_key(|(offset, _)| *offset);

    let segments = split_stmts_by_labels(&reordered, &sorted_labels);
    let mut all_lines: Vec<String> = Vec::new();
    for (name, segment_stmts) in &segments {
        if !name.is_empty() {
            all_lines.push(format!("--- {} ---", name));
        } else if !segment_stmts.is_empty() {
            all_lines.push("--- (latent resume) ---".to_string());
        }
        if !segment_stmts.is_empty() {
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
    }
    // Final cleanup: strip cross-body orphaned braces left
    // over from per-body processing, then remove any empty
    // if-blocks or else-blocks that the brace removal exposed.
    strip_unmatched_braces(&mut all_lines);
    strip_orphaned_blocks(&mut all_lines);
    if all_lines.is_empty() {
        None
    } else {
        Some(all_lines)
    }
}

/// Split ubergraph structured output into per-event sections and inline latent resumes.
pub(super) fn emit_ubergraph_events(
    buf: &mut String,
    lines: &[String],
    comments: Option<&[CommentBox]>,
    nodes: Option<&[NodeInfo]>,
    event_positions: &HashMap<String, (i32, i32)>,
    callers_map: &HashMap<String, Vec<String>>,
) {
    let (sections, resume_blocks) = split_ubergraph_sections(lines);

    // Latent resume matching: latent actions (Delay, MoveTo, etc.) pause execution
    // and resume at a bytecode offset stored in LatentActionInfo.skip_offset. The decoder
    // annotates these calls with /*resume:0xHEX*/ (see decode.rs). Resume blocks appear
    // at the start of the ubergraph as "(latent resume)" sections. We match them to their
    // originating Delay() calls by order of appearance and inline them after the call.
    let parse_resume_offset = |line: &str| -> Option<usize> {
        let marker = line.find("/*resume:0x")?;
        let hex_start = marker + 11;
        let hex_end = line[hex_start..].find("*/")? + hex_start;
        usize::from_str_radix(&line[hex_start..hex_end], 16).ok()
    };

    // Build a map of resume_offset -> resume_block_index
    // Resume blocks appear in order at the start of the ubergraph, and offsets
    // are the bytecode positions where each block starts
    let mut delay_resume_map: Vec<(usize, usize)> = Vec::new(); // (section_idx, resume_block_idx)
    let mut resume_idx = 0usize;
    for (si, section) in sections.iter().enumerate() {
        if section.name == "(latent resume)" {
            continue;
        }
        for line in &section.lines {
            if let Some(_offset) = parse_resume_offset(line) {
                if resume_idx < resume_blocks.len() {
                    delay_resume_map.push((si, resume_idx));
                    resume_idx += 1;
                }
            }
        }
    }

    // Identify comment boxes covering multiple events, emit once as group header
    let multi_event_idxs: HashSet<usize> = if let Some(cbs) = comments {
        cbs.iter()
            .enumerate()
            .filter_map(|(i, cb)| {
                if cb.is_bubble {
                    return None;
                }
                let count = event_positions
                    .values()
                    .filter(|&&(ex, ey)| cb.contains_point(ex, ey))
                    .count();
                if count > 1 {
                    Some(i)
                } else {
                    None
                }
            })
            .collect()
    } else {
        HashSet::new()
    };
    let mut emitted_group_comments: HashSet<usize> = HashSet::new();
    let mut emitted_event_count = 0usize;

    // Emit each event section as a standalone function
    for (si, section) in sections.iter().enumerate() {
        if section.name == "(latent resume)" {
            continue;
        }
        if section.name.is_empty() && section.lines.is_empty() {
            continue;
        }

        // Skip empty unnamed preamble sections
        if section.name.is_empty() {
            let has_content = section.lines.iter().any(|l| {
                let t = l.trim();
                !t.is_empty() && t != "return"
            });
            if !has_content {
                continue;
            }
        }

        section_sep(buf, &mut emitted_event_count);

        // Classify comments for this event section
        let (top_level_comments, inline_comments) = if !section.name.is_empty() {
            if let (Some(cbs), Some(&(ex, ey))) = (comments, event_positions.get(&section.name)) {
                // Event-wrapping comment boxes (contain the event node) -> top-level
                // Exclude multi-event comments (handled as group headers)
                let mut event_wrapping: Vec<&CommentBox> = cbs
                    .iter()
                    .enumerate()
                    .filter(|(i, c)| {
                        !c.is_bubble && c.contains_point(ex, ey) && !multi_event_idxs.contains(i)
                    })
                    .map(|(_, c)| c)
                    .collect();
                event_wrapping.sort_by_key(|c| ((c.width as i64) * (c.height as i64), c.x, c.y));
                event_wrapping.truncate(2);

                // Remaining comments: try to inline using node-to-bytecode matching.
                // Scope to the Y range of the event's wrapping comment box to prevent
                // leaking between nearby events.
                let node_slice = nodes.unwrap_or(&[]);
                let mut inline: Vec<(usize, &CommentBox)> = Vec::new();
                if !node_slice.is_empty() {
                    let (scope_y_min, scope_y_max) = event_wrapping
                        .iter()
                        .fold(None, |acc: Option<(i32, i32)>, c| {
                            let (y1, y2) = (c.y, c.y + c.height);
                            match acc {
                                Some((min_y, max_y)) => Some((min_y.min(y1), max_y.max(y2))),
                                None => Some((y1, y2)),
                            }
                        })
                        .unwrap_or((ey - 400, ey + 400));

                    // Scope nodes to the event's Y range for correct rank computation.
                    // Without this, node_rank counts duplicates across all events
                    // (e.g. two Delay nodes), inflating the rank beyond what the
                    // scoped bytecode lines contain.
                    let scoped_nodes: Vec<NodeInfo> = node_slice
                        .iter()
                        .filter(|n| n.y >= scope_y_min && n.y <= scope_y_max)
                        .cloned()
                        .collect();

                    let remaining: Vec<&CommentBox> = cbs
                        .iter()
                        .enumerate()
                        .filter(|(i, c)| {
                            if event_wrapping.iter().any(|ew| std::ptr::eq(*ew, *c)) {
                                return false;
                            }
                            if multi_event_idxs.contains(i) {
                                return false;
                            }
                            let cy = if c.is_bubble { c.y } else { c.y + c.height / 2 };
                            cy >= scope_y_min && cy <= scope_y_max
                        })
                        .map(|(_, c)| c)
                        .collect();
                    for cb in remaining {
                        if let Some(line_idx) = find_comment_line(cb, &scoped_nodes, &section.lines)
                        {
                            inline.push((line_idx, cb));
                        }
                    }
                    inline.sort_by_key(|(idx, _)| *idx);
                }

                (event_wrapping, inline)
            } else {
                (Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new())
        };

        // Determine if this event is inside a multi-event comment group
        let in_group = if let Some(cbs) = comments {
            if let Some(&(ex, ey)) = event_positions.get(&section.name) {
                cbs.iter()
                    .enumerate()
                    .any(|(i, cb)| multi_event_idxs.contains(&i) && cb.contains_point(ex, ey))
            } else {
                false
            }
        } else {
            false
        };
        let sig_indent = if in_group { "    " } else { "  " };
        let body_indent = if in_group { "        " } else { "    " };

        if !section.name.is_empty() {
            // Emit multi-event group headers (once, on first event in group)
            if let Some(cbs) = comments {
                if let Some(&(ex, ey)) = event_positions.get(&section.name) {
                    for (i, cb) in cbs.iter().enumerate() {
                        if multi_event_idxs.contains(&i)
                            && !emitted_group_comments.contains(&i)
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
            // Per-event comments before signature
            for cb in &top_level_comments {
                emit_comment(buf, &cb.text, sig_indent);
            }
            writeln!(buf, "{}{}():", sig_indent, section.name).unwrap();
        }
        // Find the first entry in delay_resume_map for this section
        let mut drm_pos = delay_resume_map
            .iter()
            .position(|&(s, _)| s == si)
            .unwrap_or(delay_resume_map.len());

        let mut inline_idx = 0;
        for (i, line) in section.lines.iter().enumerate() {
            // Emit any inline comments targeting this line
            while inline_idx < inline_comments.len() && inline_comments[inline_idx].0 == i {
                let ws_len = line.len() - line.trim_start().len();
                let indent = format!("{}{}", body_indent, &line[..ws_len]);
                emit_comment(buf, &inline_comments[inline_idx].1.text, &indent);
                inline_idx += 1;
            }

            // Strip resume annotations from displayed output
            let clean = strip_resume_annotation(line);
            let trimmed = clean.trim();
            if trimmed == "return" {
                continue;
            } // trailing returns are implicit
            writeln!(buf, "{}{}", body_indent, clean).unwrap();

            // If this line had a Delay with a resume, inline the next resume block
            if parse_resume_offset(line).is_some()
                && drm_pos < delay_resume_map.len()
                && delay_resume_map[drm_pos].0 == si
            {
                let ri = delay_resume_map[drm_pos].1;
                if let Some(rb) = resume_blocks.get(ri) {
                    writeln!(buf, "{}// after delay:", body_indent).unwrap();
                    for rline in &rb.lines {
                        writeln!(buf, "{}{}", body_indent, rline).unwrap();
                    }
                }
                drm_pos += 1;
            }
        }
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
        if section.name.is_empty() || section.name == "(latent resume)" {
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
        if section.name.is_empty() || section.name == "(latent resume)" {
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
    let bc_prop = find_prop(props, "BytecodeSummary").or_else(|| find_prop(props, "Bytecode"));
    let items = match bc_prop {
        Some(Property {
            value: PropValue::Array { items, .. },
            ..
        }) => items,
        _ => return false,
    };
    let meaningful: Vec<&str> = items
        .iter()
        .filter_map(|item| {
            if let PropValue::Str(line) = item {
                let code = super::strip_offset_prefix(line).trim();
                match code {
                    "" | "return" | "return nop" => None,
                    _ => Some(code),
                }
            } else {
                None
            }
        })
        .collect();
    if meaningful.is_empty() {
        return false;
    }
    meaningful
        .iter()
        .any(|line| line.starts_with(&format!("{}(", ug_name)))
        && meaningful
            .iter()
            .all(|line| line.starts_with(&format!("{}(", ug_name)) || line.contains("[persistent]"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stmt(offset: usize, text: &str) -> BcStatement {
        BcStatement {
            mem_offset: offset,
            text: text.to_string(),
        }
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
        let a = "EventA".to_string();
        let b = "EventB".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &a), (1000, &b)];

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
        let a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &a)];

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
        let a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(97, &a)];

        let segments = split_stmts_by_labels(&stmts, &labels);

        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].0, "EventA");
        assert_eq!(segments[0].1.len(), 2);
    }

    #[test]
    fn split_rejects_match_beyond_8_bytes() {
        // Label offset 90 does NOT match stmt at offset 100 (10 bytes off, beyond window)
        let stmts = vec![stmt(100, "event_start"), stmt(120, "event_stmt")];
        let a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(90, &a)];

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
