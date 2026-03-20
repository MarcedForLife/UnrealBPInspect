use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::{
    cleanup_structured_output, discard_unused_assignments, fold_summary_patterns,
    inline_constant_temps, inline_single_use_temps, reorder_convergence, reorder_flow_patterns,
    strip_orphaned_blocks, strip_unmatched_braces, structure_bytecode, BcStatement,
};
use crate::resolve::*;
use crate::types::*;

struct CommentBox {
    text: String,
    x: i32,
    y: i32,
    width: i32,
    height: i32,
    is_bubble: bool,
}

impl CommentBox {
    fn contains_point(&self, px: i32, py: i32) -> bool {
        px >= self.x && py >= self.y && px <= self.x + self.width && py <= self.y + self.height
    }
}

#[derive(Clone)]
struct NodeInfo {
    x: i32,
    y: i32,
    identifier: String,
}

struct UbergraphSection {
    name: String,
    lines: Vec<String>,
}

struct ResumeBlock {
    lines: Vec<String>,
}

const COMMENT_WRAP_WIDTH: usize = 100;
const MAX_BUBBLE_DISTANCE_SQ: i64 = 640_000; // 800²
const FUZZY_LABEL_WINDOW: usize = 8;

/// Strip the `XXXX: ` offset prefix from a bytecode line (e.g. `0012: expr` → `expr`).
fn strip_offset_prefix(line: &str) -> &str {
    if line.len() > 6 && line.as_bytes()[4] == b':' {
        &line[6..]
    } else {
        line
    }
}

fn emit_comment(buf: &mut String, text: &str, indent: &str) {
    let prefix = format!("{}// ", indent);
    let avail = COMMENT_WRAP_WIDTH.saturating_sub(prefix.len() + 1);
    for paragraph in text.lines() {
        let para = paragraph.trim();
        if para.is_empty() {
            continue;
        }
        let mut wrapped: Vec<String> = Vec::new();
        let mut cur = String::new();
        for word in para.split_whitespace() {
            if cur.is_empty() {
                cur = word.to_string();
            } else if cur.len() + 1 + word.len() <= avail {
                cur.push(' ');
                cur.push_str(word);
            } else {
                wrapped.push(cur);
                cur = word.to_string();
            }
        }
        if !cur.is_empty() {
            wrapped.push(cur);
        }
        match wrapped.len() {
            0 => {}
            1 => writeln!(buf, "{}\"{}\"", prefix, wrapped[0]).unwrap(),
            n => {
                writeln!(buf, "{}\"{}", prefix, wrapped[0]).unwrap();
                for (i, segment) in wrapped.iter().enumerate().take(n).skip(1) {
                    if i == n - 1 {
                        writeln!(buf, "{} {}\"", prefix, segment).unwrap();
                    } else {
                        writeln!(buf, "{} {}", prefix, segment).unwrap();
                    }
                }
            }
        }
    }
}

/// Rewrite unresolvable jumps to point past the end of the segment.
///
/// In UberGraph bytecode, each event is processed as an independent segment.
/// Jumps targeting offsets outside the current segment are always "return from
/// this event" — control goes back to the dispatcher.  But even intra-segment
/// jumps can fail to resolve when filtered trace opcodes shift the visible
/// statement offsets away from the raw bytecode targets.
///
/// This function uses the **same ±4-byte sorted-offset lookup** that
/// `structure_bytecode`'s `find_target_idx` uses.  Any jump target that would
/// return `None` there (and isn't past the end) is rewritten to a sentinel
/// offset, which `find_target_idx_or_end` resolves as jump-to-end (implicit
/// return or break).
fn resolve_cross_segment_jumps(stmts: &mut Vec<BcStatement>) {
    if stmts.is_empty() {
        return;
    }

    // Build exact map and sorted offsets — mirrors structure_bytecode logic
    let exact_map: HashSet<usize> = stmts.iter().map(|s| s.mem_offset).collect();
    let mut sorted_offsets: Vec<usize> = exact_map.iter().copied().collect();
    sorted_offsets.sort();

    let max_offset = *sorted_offsets.last().unwrap();
    let sentinel_offset = max_offset + 1;

    // Replicate structure_bytecode's find_target_idx: exact match, then ±4
    // binary-search fallback.  Returns true if the target would resolve.
    let is_resolvable = |target: usize| -> bool {
        // Past end → find_target_idx_or_end returns stmts.len() (end sentinel)
        if target > max_offset {
            return true;
        }
        // Exact match
        if exact_map.contains(&target) {
            return true;
        }
        // ±4 fuzzy match via sorted offsets (same as structure.rs)
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
/// Sequence body blocks inline — those blocks retain their original (high)
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
    let mut matched: HashMap<usize, String> = HashMap::new(); // stmt_idx → label name
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
fn split_ubergraph_sections(lines: &[String]) -> (Vec<UbergraphSection>, Vec<ResumeBlock>) {
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

fn find_local_calls(line: &str, local_fns: &HashSet<String>) -> Vec<String> {
    let mut found = Vec::new();
    for func in local_fns {
        let pattern = format!("{}(", func);
        if let Some(pos) = line.find(&pattern) {
            let is_boundary = pos == 0 || {
                let prev = line.as_bytes()[pos - 1];
                !(prev.is_ascii_alphanumeric() || prev == b'_' || prev == b'.')
            };
            if is_boundary {
                found.push(func.clone());
            }
        }
    }
    found
}

fn strip_node_func_prefix(name: &str) -> String {
    name.strip_prefix("K2_")
        .or_else(|| name.strip_prefix("Conv_"))
        .unwrap_or(name)
        .to_string()
}

fn line_contains_identifier(line: &str, identifier: &str) -> bool {
    if identifier == "__branch__" {
        let trimmed = line.trim_start();
        return trimmed.starts_with("if (") || trimmed.starts_with("} else if (");
    }
    let mut start = 0;
    while start + identifier.len() <= line.len() {
        if let Some(pos) = line[start..].find(identifier) {
            let abs_pos = start + pos;
            let is_start = abs_pos == 0 || {
                let prev = line.as_bytes()[abs_pos - 1];
                !(prev.is_ascii_alphanumeric() || prev == b'_')
            };
            let end = abs_pos + identifier.len();
            let is_end = end >= line.len() || {
                let next = line.as_bytes()[end];
                !(next.is_ascii_alphanumeric() || next == b'_')
            };
            if is_start && is_end {
                return true;
            }
            start = abs_pos + 1;
        } else {
            break;
        }
    }
    false
}

/// Find the Nth occurrence of `identifier` in bytecode lines (0-based rank).
fn find_nth_identifier_line(
    identifier: &str,
    rank: usize,
    bytecode_lines: &[String],
) -> Option<usize> {
    let mut count = 0;
    for (i, line) in bytecode_lines.iter().enumerate() {
        if line_contains_identifier(line, identifier) {
            if count == rank {
                return Some(i);
            }
            count += 1;
        }
    }
    None
}

/// Determine a node's rank among all nodes sharing its identifier.
/// Uses (Y, X) sort order — UE4 graphs branch vertically (true=up, false=down),
/// which generally matches bytecode order (true branches processed first).
fn node_rank(node: &NodeInfo, all_nodes: &[NodeInfo]) -> Option<usize> {
    let mut same_id: Vec<(i32, i32)> = all_nodes
        .iter()
        .filter(|n| n.identifier == node.identifier)
        .map(|n| (n.y, n.x))
        .collect();
    same_id.sort();
    same_id
        .iter()
        .position(|&(y, x)| y == node.y && x == node.x)
}

/// Walk backward from `anchor_line` to find the nearest `if` at a shallower indent.
fn find_enclosing_if(bytecode_lines: &[String], anchor_line: usize) -> Option<usize> {
    let anchor_indent =
        bytecode_lines[anchor_line].len() - bytecode_lines[anchor_line].trim_start().len();
    for i in (0..anchor_line).rev() {
        let line = &bytecode_lines[i];
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        if indent < anchor_indent
            && (trimmed.starts_with("if (") || trimmed.starts_with("} else if ("))
        {
            return Some(i);
        }
    }
    None
}

fn find_comment_line(
    comment: &CommentBox,
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> Option<usize> {
    let contained: Vec<&NodeInfo> = if comment.is_bubble {
        // Bubble comments sit on a specific node. The node itself may not have an
        // identifier (e.g. K2Node_IfThenElse), so find the closest identifiable nodes.
        // UE4 execution flows left-to-right, so prefer nodes to the right (downstream).
        // Two-pass: first try right-side only, fall back to all directions.
        let dist_limit = MAX_BUBBLE_DISTANCE_SQ;
        let mut right: Vec<(&NodeInfo, i64)> = nodes
            .iter()
            .filter(|n| n.x >= comment.x)
            .map(|n| {
                let dx = (n.x - comment.x) as i64;
                let dy = (n.y - comment.y) as i64;
                (n, dx * dx + dy * dy)
            })
            .filter(|&(_, d)| d < dist_limit)
            .collect();
        right.sort_by_key(|&(n, d)| (d, n.y, n.x));
        right.truncate(5);
        if !right.is_empty() {
            right.into_iter().map(|(n, _)| n).collect()
        } else {
            let mut all: Vec<(&NodeInfo, i64)> = nodes
                .iter()
                .map(|n| {
                    let dx = (n.x - comment.x) as i64;
                    let dy = (n.y - comment.y) as i64;
                    (n, dx * dx + dy * dy)
                })
                .filter(|&(_, d)| d < dist_limit)
                .collect();
            all.sort_by_key(|&(n, d)| (d, n.y, n.x));
            all.truncate(5);
            all.into_iter().map(|(n, _)| n).collect()
        }
    } else {
        nodes
            .iter()
            .filter(|n| comment.contains_point(n.x, n.y))
            .collect()
    };

    if contained.is_empty() {
        return None;
    }

    // When a comment covers both Branch nodes and regular identifiable nodes,
    // anchor on the regular nodes and walk backward to the enclosing `if`.
    let has_branch = contained.iter().any(|n| n.identifier == "__branch__");
    if has_branch {
        let regular: Vec<&&NodeInfo> = contained
            .iter()
            .filter(|n| n.identifier != "__branch__")
            .collect();
        if !regular.is_empty() {
            let mut anchor_line: Option<usize> = None;
            for node in &regular {
                let rank = match node_rank(node, nodes) {
                    Some(r) => r,
                    None => continue,
                };
                if let Some(line_idx) =
                    find_nth_identifier_line(&node.identifier, rank, bytecode_lines)
                {
                    anchor_line = Some(anchor_line.map_or(line_idx, |m: usize| m.min(line_idx)));
                    if comment.is_bubble {
                        break;
                    }
                }
            }
            if let Some(anchor) = anchor_line {
                return Some(find_enclosing_if(bytecode_lines, anchor).unwrap_or(anchor));
            }
        }
    }

    let mut min_line: Option<usize> = None;
    for node in &contained {
        let rank = match node_rank(node, nodes) {
            Some(r) => r,
            None => continue,
        };
        if let Some(line_idx) = find_nth_identifier_line(&node.identifier, rank, bytecode_lines) {
            min_line = Some(min_line.map_or(line_idx, |m: usize| m.min(line_idx)));
            // For bubbles, use the first match (closest node) rather than minimum line
            if comment.is_bubble {
                return min_line;
            }
        }
    }

    min_line
}

fn classify_comments<'a>(
    comments: &'a [CommentBox],
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> (Vec<&'a CommentBox>, Vec<(usize, &'a CommentBox)>) {
    let total_nodes = nodes.len();
    let mut top_level: Vec<&CommentBox> = Vec::new();
    let mut inline: Vec<(usize, &CommentBox)> = Vec::new();

    for comment in comments {
        if comment.is_bubble {
            if let Some(line_idx) = find_comment_line(comment, nodes, bytecode_lines) {
                inline.push((line_idx, comment));
            } else {
                top_level.push(comment);
            }
            continue;
        }

        let contained = nodes
            .iter()
            .filter(|n| comment.contains_point(n.x, n.y))
            .count();

        if total_nodes > 0 && contained > 0 && contained * 100 / total_nodes > 80 {
            top_level.push(comment);
        } else if let Some(line_idx) = find_comment_line(comment, nodes, bytecode_lines) {
            inline.push((line_idx, comment));
        } else {
            top_level.push(comment);
        }
    }

    inline.sort_by_key(|(idx, _)| *idx);

    (top_level, inline)
}

pub fn format_summary(asset: &ParsedAsset, filters: &[String]) -> String {
    let mut buf = String::new();
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();

    let mut bp_name = String::new();
    let mut bp_parent = String::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if class.ends_with(".Blueprint") {
            bp_name = hdr.object_name.clone();
            if let Some(p) = find_prop(props, "ParentClass") {
                if let PropValue::Object(idx) = &p.value {
                    bp_parent = resolve_index(&asset.imports, &export_names, *idx);
                    if let Some(stripped) = bp_parent.strip_suffix("'") {
                        bp_parent = stripped.to_string();
                    }
                    bp_parent = bp_parent.replace("Default__", "");
                }
            }
            break;
        }
    }

    writeln!(
        buf,
        "Blueprint: {} (extends {})",
        bp_name,
        short_class(&bp_parent)
    )
    .unwrap();
    writeln!(buf).unwrap();

    // Components from SCS_Node exports
    let mut scs_nodes: HashMap<String, (String, String, Vec<String>)> = HashMap::new();
    let mut components: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".SCS_Node") {
            continue;
        }
        let comp_name = find_prop_str(props, "InternalVariableName")
            .or_else(|| {
                find_prop(props, "ComponentTemplate").and_then(|p| match &p.value {
                    PropValue::Object(idx) => {
                        let tpl = resolve_index(&asset.imports, &export_names, *idx);
                        Some(tpl.trim_end_matches("_GEN_VARIABLE").to_string())
                    }
                    _ => None,
                })
            })
            .unwrap_or_else(|| hdr.object_name.clone());
        let comp_class = find_prop(props, "ComponentClass")
            .and_then(|p| match &p.value {
                PropValue::Object(idx) => Some(short_class(&resolve_index(
                    &asset.imports,
                    &export_names,
                    *idx,
                ))),
                _ => None,
            })
            .unwrap_or_else(|| "?".into());
        let children = find_prop(props, "ChildNodes")
            .and_then(|p| match &p.value {
                PropValue::Array { items, .. } => Some(
                    items
                        .iter()
                        .filter_map(|i| match i {
                            PropValue::Object(idx) => {
                                Some(resolve_index(&asset.imports, &export_names, *idx))
                            }
                            _ => None,
                        })
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_default();
        components.push((comp_name.clone(), comp_class.clone()));
        scs_nodes.insert(hdr.object_name.clone(), (comp_name, comp_class, children));
    }

    let all_children: Vec<String> = scs_nodes
        .values()
        .flat_map(|(_, _, children)| children.iter().cloned())
        .collect();
    let mut root_nodes: Vec<String> = scs_nodes
        .keys()
        .filter(|k| !all_children.contains(k))
        .cloned()
        .collect();
    root_nodes.sort();

    let mut comp_props: HashMap<String, &[Property]> = HashMap::new();
    for (hdr, props) in &asset.exports {
        if let Some(comp_name) = hdr.object_name.strip_suffix("_GEN_VARIABLE") {
            comp_props.insert(comp_name.to_string(), props);
        }
    }

    let mut cat_exports: HashMap<String, (String, &[Property])> = HashMap::new();
    for (hdr, props) in &asset.exports {
        if hdr.object_name.contains("_CAT") {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            cat_exports.insert(hdr.object_name.clone(), (short_class(&class), props));
        }
    }

    const COMP_SKIP_PROPS: &[&str] = &[
        "StaticMeshImportVersion",
        "bVisualizeComponent",
        "CreationMethod",
    ];

    fn fmt_prop_list(
        buf: &mut String,
        indent: &str,
        props: &[Property],
        skip: &[&str],
        imports: &[ImportEntry],
        export_names: &[String],
    ) {
        for prop in props {
            if skip.contains(&prop.name.as_str()) {
                continue;
            }
            if let PropValue::Struct {
                struct_type,
                fields,
            } = &prop.value
            {
                match struct_type.as_str() {
                    "Vector" | "Rotator" => {
                        let val = prop_value_short(&prop.value, imports, export_names);
                        writeln!(buf, "{}{}: {}", indent, prop.name, val).unwrap();
                    }
                    _ => {
                        let summary: Vec<String> = fields
                            .iter()
                            .filter_map(|f| match &f.value {
                                PropValue::Struct { .. }
                                | PropValue::Array { .. }
                                | PropValue::Map { .. } => None,
                                _ => {
                                    let v = prop_value_short(&f.value, imports, export_names);
                                    Some(format!("{}: {}", f.name, v))
                                }
                            })
                            .collect();
                        if !summary.is_empty() {
                            writeln!(buf, "{}{}: {}", indent, prop.name, summary.join(", "))
                                .unwrap();
                        }
                    }
                }
                continue;
            }
            let val = prop_value_short(&prop.value, imports, export_names);
            writeln!(buf, "{}{}: {}", indent, prop.name, val).unwrap();
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fmt_comp_props(
        buf: &mut String,
        name: &str,
        class: &str,
        depth: usize,
        comp_props: &HashMap<String, &[Property]>,
        cat_exports: &HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry],
        export_names: &[String],
    ) {
        let indent = "  ".repeat(depth + 1);
        let prop_indent = "  ".repeat(depth + 2);
        writeln!(buf, "{}{} ({})", indent, name, class).unwrap();
        if let Some(props) = comp_props.get(name) {
            let skip = &[
                "ChildActorTemplate",
                COMP_SKIP_PROPS[0],
                COMP_SKIP_PROPS[1],
                COMP_SKIP_PROPS[2],
            ];
            fmt_prop_list(buf, &prop_indent, props, skip, imports, export_names);
            // Handle ChildActorTemplate
            let child_actor_tpl = props.iter().find_map(|p| {
                if p.name == "ChildActorTemplate" {
                    if let PropValue::Object(idx) = &p.value {
                        return Some(resolve_index(imports, export_names, *idx));
                    }
                }
                None
            });
            if let Some(tpl_name) = child_actor_tpl {
                if let Some((tpl_class, tpl_props)) = cat_exports.get(&tpl_name) {
                    writeln!(buf, "{}[template: {}]", prop_indent, tpl_class).unwrap();
                    let tpl_indent = format!("{}  ", prop_indent);
                    fmt_prop_list(
                        buf,
                        &tpl_indent,
                        tpl_props,
                        COMP_SKIP_PROPS,
                        imports,
                        export_names,
                    );
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fmt_comp_tree(
        buf: &mut String,
        node_name: &str,
        depth: usize,
        scs_nodes: &HashMap<String, (String, String, Vec<String>)>,
        comp_props: &HashMap<String, &[Property]>,
        cat_exports: &HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry],
        export_names: &[String],
    ) {
        if let Some((comp_name, comp_class, children)) = scs_nodes.get(node_name) {
            fmt_comp_props(
                buf,
                comp_name,
                comp_class,
                depth,
                comp_props,
                cat_exports,
                imports,
                export_names,
            );
            for child in children {
                fmt_comp_tree(
                    buf,
                    child,
                    depth + 1,
                    scs_nodes,
                    comp_props,
                    cat_exports,
                    imports,
                    export_names,
                );
            }
        }
    }

    if !components.is_empty() {
        writeln!(buf, "Components:").unwrap();
        for root in &root_nodes {
            fmt_comp_tree(
                &mut buf,
                root,
                0,
                &scs_nodes,
                &comp_props,
                &cat_exports,
                &asset.imports,
                &export_names,
            );
        }
        writeln!(buf).unwrap();
    }

    // Member variables
    let mut members: Vec<String> = Vec::new();
    let component_names: Vec<&str> = components.iter().map(|(n, _)| n.as_str()).collect();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".BlueprintGeneratedClass") {
            continue;
        }
        if let Some(members_prop) = find_prop(props, "Members") {
            if let PropValue::Array { items, .. } = &members_prop.value {
                for item in items {
                    if let PropValue::Str(decl) = item {
                        let var_name = decl.split(':').next().unwrap_or("");
                        if component_names.contains(&var_name) {
                            continue;
                        }
                        if var_name == "UberGraphFrame" {
                            continue;
                        }
                        members.push(decl.clone());
                    }
                }
            }
        }
    }

    let mut defaults: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        if hdr.object_name.starts_with("Default__") && !props.is_empty() {
            for prop in props {
                if matches!(prop.name.as_str(), "ActorLabel" | "bCanProxyPhysics") {
                    continue;
                }
                let val_str = prop_value_short(&prop.value, &asset.imports, &export_names);
                defaults.push((prop.name.clone(), val_str));
            }
        }
    }

    if !members.is_empty() {
        writeln!(buf, "Variables:").unwrap();
        for decl in &members {
            let var_name = decl.split(':').next().unwrap_or("");
            if let Some((_, val)) = defaults.iter().find(|(n, _)| n == var_name) {
                writeln!(buf, "  {} = {}", decl, val).unwrap();
            } else {
                writeln!(buf, "  {}", decl).unwrap();
            }
        }
        writeln!(buf).unwrap();
    } else if !defaults.is_empty() {
        writeln!(buf, "Default values:").unwrap();
        for (name, val) in &defaults {
            writeln!(buf, "  {} = {}", name, val).unwrap();
        }
        writeln!(buf).unwrap();
    }

    // Ubergraph entry points
    let ubergraph_name: Option<String> = asset
        .exports
        .iter()
        .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))
        .map(|(hdr, _)| hdr.object_name.clone());
    let ubergraph_labels: HashMap<usize, String> = if let Some(ref ug_name) = ubergraph_name {
        let mut labels = HashMap::new();
        let call_prefix = format!("{}(", ug_name);
        for (hdr, props) in &asset.exports {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            if !class.ends_with(".Function") {
                continue;
            }
            if hdr.object_name.starts_with("ExecuteUbergraph_") {
                continue;
            }
            for prop_name in &["BytecodeSummary", "Bytecode"] {
                if let Some(bc_prop) = find_prop(props, prop_name) {
                    if let PropValue::Array { items, .. } = &bc_prop.value {
                        for item in items {
                            if let PropValue::Str(line) = item {
                                if let Some(start) = line.find(&call_prefix) {
                                    let after = &line[start + call_prefix.len()..];
                                    if let Some(end) = after.find(')') {
                                        if let Ok(offset) = after[..end].trim().parse::<usize>() {
                                            labels.insert(offset, hdr.object_name.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if !labels.is_empty() {
                    break;
                }
            }
        }
        labels
    } else {
        HashMap::new()
    };

    // Collect blueprint comment boxes, node positions, and event positions from EdGraph exports
    let mut graph_comments: HashMap<String, Vec<CommentBox>> = HashMap::new();
    let mut graph_nodes: HashMap<String, Vec<NodeInfo>> = HashMap::new();
    let mut event_positions: HashMap<String, (i32, i32)> = HashMap::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".EdGraph") {
            continue;
        }
        let graph_name = &hdr.object_name;

        let node_indices: Vec<i32> = find_prop(props, "Nodes")
            .or_else(|| find_prop(props, "AllNodes"))
            .map(|p| match &p.value {
                PropValue::Array { items, .. } => items
                    .iter()
                    .filter_map(|item| {
                        if let PropValue::Object(idx) = item {
                            Some(*idx)
                        } else {
                            None
                        }
                    })
                    .collect(),
                _ => Vec::new(),
            })
            .unwrap_or_default();

        for idx in &node_indices {
            if *idx <= 0 {
                continue;
            }
            let export_idx = (*idx - 1) as usize;
            let Some((node_hdr, node_props)) = asset.exports.get(export_idx) else {
                continue;
            };
            let node_class = resolve_index(&asset.imports, &export_names, node_hdr.class_index);
            let short = short_class(&node_class);

            if short == "EdGraphNode_Comment" {
                let comment_text =
                    find_prop(node_props, "NodeComment").and_then(|p| match &p.value {
                        PropValue::Str(s) | PropValue::Name(s) | PropValue::Text(s) => {
                            Some(s.clone())
                        }
                        _ => None,
                    });
                if let Some(text) = comment_text {
                    let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                    let y = find_prop_i32(node_props, "NodePosY").unwrap_or(0);
                    let w = find_prop_i32(node_props, "NodeWidth").unwrap_or(0);
                    let h = find_prop_i32(node_props, "NodeHeight").unwrap_or(0);
                    graph_comments
                        .entry(graph_name.clone())
                        .or_default()
                        .push(CommentBox {
                            text,
                            x,
                            y,
                            width: w,
                            height: h,
                            is_bubble: false,
                        });
                }
            } else {
                // Collect bubble comments from non-comment nodes (skip reroute knots —
                // their labels describe wire routing, not logic)
                let has_bubble = short != "K2Node_Knot"
                    && find_prop(node_props, "bCommentBubbleVisible")
                        .is_some_and(|p| matches!(p.value, PropValue::Bool(true)));
                if has_bubble {
                    if let Some(text) =
                        find_prop(node_props, "NodeComment").and_then(|p| match &p.value {
                            PropValue::Str(s) | PropValue::Name(s) | PropValue::Text(s) => {
                                Some(s.clone())
                            }
                            _ => None,
                        })
                    {
                        let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                        let y = find_prop_i32(node_props, "NodePosY").unwrap_or(0);
                        graph_comments
                            .entry(graph_name.clone())
                            .or_default()
                            .push(CommentBox {
                                text,
                                x,
                                y,
                                width: 0,
                                height: 0,
                                is_bubble: true,
                            });
                    }
                }

                // Collect node positions with identifiers for comment placement
                let node_identifier = match short.as_str() {
                    "K2Node_CallFunction" | "K2Node_CommutativeAssociativeBinaryOperator" => {
                        find_prop(node_props, "FunctionReference").and_then(|p| {
                            if let PropValue::Struct { fields, .. } = &p.value {
                                find_prop_str(fields, "MemberName")
                                    .map(|n| strip_node_func_prefix(&n))
                            } else {
                                None
                            }
                        })
                    }
                    "K2Node_VariableSet" => {
                        find_prop(node_props, "VariableReference").and_then(|p| {
                            if let PropValue::Struct { fields, .. } = &p.value {
                                find_prop_str(fields, "MemberName")
                            } else {
                                None
                            }
                        })
                    }
                    "K2Node_IfThenElse" => Some("__branch__".to_string()),
                    _ => None,
                };
                if let Some(identifier) = node_identifier {
                    let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                    let y = find_prop_i32(node_props, "NodePosY").unwrap_or(0);
                    graph_nodes
                        .entry(graph_name.clone())
                        .or_default()
                        .push(NodeInfo { x, y, identifier });
                }
            }

            if graph_name == "EventGraph"
                && (short == "K2Node_Event" || short == "K2Node_CustomEvent")
            {
                let event_name = if short == "K2Node_CustomEvent" {
                    find_prop_str(node_props, "CustomFunctionName")
                        .or_else(|| get_event_name_opt(node_props))
                } else {
                    get_event_name_opt(node_props)
                };
                if let Some(name) = event_name {
                    let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                    let y = find_prop_i32(node_props, "NodePosY").unwrap_or(0);
                    event_positions.insert(name, (x, y));
                }
            }
        }
    }

    // Build call graph: collect local function names and scan bytecodes for cross-references
    let local_functions: HashSet<String> = {
        let mut names: HashSet<String> = asset
            .exports
            .iter()
            .filter(|(hdr, _)| {
                let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
                class.ends_with(".Function") && !hdr.object_name.starts_with("ExecuteUbergraph_")
            })
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        // Include ubergraph event names
        for event_name in ubergraph_labels.values() {
            names.insert(event_name.clone());
        }
        names
    };

    // Sort ubergraph labels by offset for attributing statements to events
    let mut ug_label_offsets: Vec<(usize, &str)> = ubergraph_labels
        .iter()
        .map(|(off, name)| (*off, name.as_str()))
        .collect();
    ug_label_offsets.sort_by_key(|(off, _)| *off);

    let mut callees_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut callers_map: HashMap<String, Vec<String>> = HashMap::new();

    // Scan non-ubergraph functions for calls to local functions
    // (ubergraph is scanned later via structured output to catch latent resume blocks)
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }

        // Skip ubergraph stubs
        if ubergraph_name.is_some()
            && is_ubergraph_stub(props, ubergraph_name.as_deref().unwrap_or(""))
        {
            continue;
        }

        let bc_prop = find_prop(props, "Bytecode").or_else(|| find_prop(props, "BytecodeSummary"));
        let items = match bc_prop {
            Some(Property {
                value: PropValue::Array { items, .. },
                ..
            }) => items,
            _ => continue,
        };

        for item in items {
            let line = match item {
                PropValue::Str(s) => s.as_str(),
                _ => continue,
            };
            let code = strip_offset_prefix(line);

            let calls = find_local_calls(code, &local_functions);
            for callee in &calls {
                if *callee == hdr.object_name {
                    continue;
                }
                let entry = callees_map.entry(hdr.object_name.clone()).or_default();
                if !entry.contains(callee) {
                    entry.push(callee.clone());
                }
                let entry = callers_map.entry(callee.clone()).or_default();
                if !entry.contains(&hdr.object_name) {
                    entry.push(hdr.object_name.clone());
                }
            }
        }
    }

    // Pre-compute structured ubergraph output for call graph scanning
    let ubergraph_structured: Option<Vec<String>> = if !ubergraph_labels.is_empty() {
        asset
            .exports
            .iter()
            .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))
            .and_then(|(_, props)| find_prop(props, "Bytecode"))
            .and_then(|bc_prop| {
                if let PropValue::Array { items, .. } = &bc_prop.value {
                    let stmts: Vec<BcStatement> = items
                        .iter()
                        .filter_map(|item| {
                            if let PropValue::Str(line) = item {
                                if line.len() > 6 && line.as_bytes()[4] == b':' {
                                    let offset = usize::from_str_radix(&line[..4], 16).ok()?;
                                    Some(BcStatement {
                                        mem_offset: offset,
                                        text: line[6..].to_string(),
                                    })
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        })
                        .collect();
                    if stmts.is_empty() {
                        return None;
                    }

                    // Flow reorder the entire UberGraph first — Sequence node
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
                                // No sequence markers — process as a single block
                                let mut seg = segment_stmts.clone();
                                resolve_cross_segment_jumps(&mut seg);
                                inline_constant_temps(&mut seg);
                                inline_single_use_temps(&mut seg);
                                discard_unused_assignments(&mut seg);
                                let mut structured = structure_bytecode(&seg, &HashMap::new());
                                cleanup_structured_output(&mut structured);
                                fold_summary_patterns(&mut structured);
                                strip_orphaned_blocks(&mut structured);
                                all_lines.extend(structured);
                            } else {
                                // Process each sequence body independently so that
                                // cross-body jumps don't cause if-blocks to span
                                // across sequence boundaries.
                                for (marker, body) in &sub_segments {
                                    if let Some(m) = marker {
                                        all_lines.push(m.clone());
                                    }
                                    if body.is_empty() {
                                        continue;
                                    }
                                    let mut seg = body.clone();
                                    resolve_cross_segment_jumps(&mut seg);
                                    inline_constant_temps(&mut seg);
                                    inline_single_use_temps(&mut seg);
                                    discard_unused_assignments(&mut seg);
                                    let mut structured = structure_bytecode(&seg, &HashMap::new());
                                    cleanup_structured_output(&mut structured);
                                    fold_summary_patterns(&mut structured);
                                    strip_orphaned_blocks(&mut structured);
                                    all_lines.extend(structured);
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
                } else {
                    None
                }
            })
    } else {
        None
    };
    // Scan structured ubergraph output for local calls per event section
    if let Some(ref structured) = ubergraph_structured {
        scan_structured_calls(
            structured,
            &local_functions,
            &mut callees_map,
            &mut callers_map,
        );
    }

    // Emit call graph section (only functions with local callees)
    if !callees_map.is_empty() {
        let mut entries: Vec<(&String, &mut Vec<String>)> = callees_map.iter_mut().collect();
        entries.sort_by_key(|(name, _)| name.to_string());
        writeln!(buf, "Call graph:").unwrap();
        for (caller, callees) in &mut entries {
            callees.sort();
            writeln!(buf, "  {} \u{2192} {}", caller, callees.join(", ")).unwrap();
        }
        writeln!(buf).unwrap();
    }

    // Functions with signatures and bytecode
    let mut has_functions = false;
    let mut functions_with_bytecode: HashSet<String> = HashSet::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if !matches_filter(&hdr.object_name, filters) {
            continue;
        }

        // Skip stub dispatchers when ubergraph bytecode is present
        if ubergraph_name.is_some()
            && !hdr.object_name.starts_with("ExecuteUbergraph_")
            && is_ubergraph_stub(props, ubergraph_name.as_deref().unwrap_or(""))
        {
            continue;
        }

        let sig =
            find_prop_str(props, "Signature").unwrap_or_else(|| format!("{}()", hdr.object_name));
        let flags = find_prop_str(props, "FunctionFlags")
            .map(|f| filter_flags_for_summary(&f))
            .and_then(|f| {
                if f.is_empty() {
                    None
                } else {
                    Some(format!(" [{}]", f))
                }
            })
            .unwrap_or_default();

        // For ubergraph: use pre-computed structured output
        if hdr.object_name.starts_with("ExecuteUbergraph_") && !ubergraph_labels.is_empty() {
            if let Some(ref structured) = ubergraph_structured {
                if !has_functions {
                    writeln!(buf, "Functions:").unwrap();
                    has_functions = true;
                }
                let ug_comments = graph_comments.get("EventGraph").map(|v| v.as_slice());
                let ug_nodes = graph_nodes.get("EventGraph").map(|v| v.as_slice());
                emit_ubergraph_events(
                    &mut buf,
                    structured,
                    ug_comments,
                    ug_nodes,
                    &event_positions,
                    &callers_map,
                );
                functions_with_bytecode.insert(hdr.object_name.clone());
            }
            continue;
        }

        if !has_functions {
            writeln!(buf, "Functions:").unwrap();
            has_functions = true;
        }
        if let Some(callers) = callers_map.get(&hdr.object_name) {
            writeln!(buf, "  // called by: {}", callers.join(", ")).unwrap();
        }
        writeln!(buf, "  {}{}", sig, flags).unwrap();

        // Collect bytecode lines
        let bc_prop_name = if find_prop(props, "BytecodeSummary").is_some() {
            "BytecodeSummary"
        } else {
            "Bytecode"
        };
        let bc_lines: Vec<String> = find_prop(props, bc_prop_name)
            .and_then(|p| {
                if let PropValue::Array { items, .. } = &p.value {
                    Some(
                        items
                            .iter()
                            .filter_map(|item| {
                                if let PropValue::Str(line) = item {
                                    Some(if bc_prop_name == "Bytecode" {
                                        strip_offset_prefix(line).to_string()
                                    } else {
                                        line.clone()
                                    })
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    )
                } else {
                    None
                }
            })
            .unwrap_or_default();

        // Classify comments as top-level vs inline using node positions
        let comments = graph_comments.get(&hdr.object_name);
        let nodes = graph_nodes.get(&hdr.object_name);
        let (top_level, inline) = if let Some(cbs) = comments {
            let node_slice = nodes.map(|v| v.as_slice()).unwrap_or(&[]);
            classify_comments(cbs, node_slice, &bc_lines)
        } else {
            (Vec::new(), Vec::new())
        };

        // Emit top-level comments after signature
        if !top_level.is_empty() {
            let mut sorted_top = top_level;
            sorted_top.sort_by(|a, b| a.x.cmp(&b.x).then(a.y.cmp(&b.y)).then(a.text.cmp(&b.text)));
            for cb in &sorted_top {
                emit_comment(&mut buf, &cb.text, "    ");
            }
        }

        // Emit bytecode lines with inline comments interleaved
        if !bc_lines.is_empty() {
            let mut inline_idx = 0;
            for (i, line) in bc_lines.iter().enumerate() {
                while inline_idx < inline.len() && inline[inline_idx].0 == i {
                    let ws_len = line.len() - line.trim_start().len();
                    let indent = format!("    {}", &line[..ws_len]);
                    emit_comment(&mut buf, &inline[inline_idx].1.text, &indent);
                    inline_idx += 1;
                }
                writeln!(buf, "    {}", line).unwrap();
            }
            functions_with_bytecode.insert(hdr.object_name.clone());
        }
    }
    if has_functions {
        writeln!(buf).unwrap();
    }

    buf
}

pub fn print_summary(asset: &ParsedAsset, filters: &[String]) {
    print!("{}", format_summary(asset, filters));
}

fn get_event_name_opt(props: &[Property]) -> Option<String> {
    // Try EventReference.MemberName first, then FunctionReference.MemberName
    for ref_name in &["EventReference", "FunctionReference"] {
        if let Some(p) = find_prop(props, ref_name) {
            if let PropValue::Struct { fields, .. } = &p.value {
                if let Some(name) = find_prop_str(fields, "MemberName") {
                    return Some(name);
                }
            }
        }
    }
    None
}

fn filter_flags_for_summary(flags: &str) -> String {
    const NOISE: &[&str] = &["BlueprintCallable"];
    flags
        .split('|')
        .filter(|f| !NOISE.contains(&f.trim()))
        .collect::<Vec<_>>()
        .join("|")
}

/// Split ubergraph structured output into per-event sections and inline latent resumes.
fn emit_ubergraph_events(
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

    // Build a map of resume_offset → resume_block_index
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

    // Identify comment boxes covering multiple events — emit once as group header
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

        // Classify comments for this event section
        let (top_level_comments, inline_comments) = if !section.name.is_empty() {
            if let (Some(cbs), Some(&(ex, ey))) = (comments, event_positions.get(&section.name)) {
                // Event-wrapping comment boxes (contain the event node) → top-level
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
fn scan_structured_calls(
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

    // Helper to record a caller→callee edge
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

/// Strip `/*resume:0xHEX*/` annotations from a line for display.
fn strip_resume_annotation(line: &str) -> String {
    if let Some(start) = line.find(" /*resume:0x") {
        if let Some(end) = line[start..].find("*/") {
            return format!("{}{}", &line[..start], &line[start + end + 2..]);
        }
    }
    line.to_string()
}

/// Check if a function is a stub that just dispatches to the ubergraph.
/// Stubs contain only an ExecuteUbergraph_X(N) call, plus optional return/persistent-frame lines.
fn is_ubergraph_stub(props: &[Property], ug_name: &str) -> bool {
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
                let code = strip_offset_prefix(line).trim();
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
        assert_eq!(segments[0].0, ""); // unmatched — no label found
    }

    #[test]
    fn cross_segment_jump_past_end_not_rewritten() {
        // jump 0x2000 is past max offset (120) → find_target_idx_or_end resolves
        // this as jump-to-end, so resolve_cross_segment_jumps leaves it alone
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x2000"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x2000"); // unchanged — past-end is resolvable
                                                  // Sentinel still appended
        assert_eq!(stmts.last().unwrap().text, "return nop");
        assert_eq!(stmts.last().unwrap().mem_offset, 121);
    }

    #[test]
    fn unresolvable_jump_rewritten() {
        // jump 0x50 (=80) is before the segment start and >4 bytes from any
        // statement → find_target_idx would return None → rewritten to sentinel
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
        // if !(cond) jump 0x50 — target not resolvable → rewritten
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
        // jump 0x78 (=120) is within the segment → preserved
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
        // jump 0x75 (=117) is within ±4 of offset 120 → preserved as local
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x75"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x75"); // unchanged — fuzzy match
    }

    #[test]
    fn fuzzy_jump_beyond_4_bytes_rewritten() {
        // jump 0x73 (=115) is 5 bytes from offset 120, outside ±4 window
        // and >4 from offset 110 too → unresolvable → rewritten
        let mut stmts = vec![
            stmt(100, "some_call()"),
            stmt(110, "jump 0x73"),
            stmt(120, "return nop"),
        ];
        resolve_cross_segment_jumps(&mut stmts);
        assert_eq!(stmts[1].text, "jump 0x79"); // rewritten — outside ±4
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
