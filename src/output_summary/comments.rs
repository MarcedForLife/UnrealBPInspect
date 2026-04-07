//! EdGraph comment box/bubble parsing, spatial matching to bytecode nodes, classification.

use super::{CommentBox, NodeInfo, MAX_BUBBLE_DISTANCE_SQ};
use crate::helpers::indent_of;

/// A box comment covering more than this percentage of a function's nodes is treated
/// as a top-level description rather than an inline annotation.
const COVERAGE_THRESHOLD_PERCENT: usize = 80;

/// Find the closest identifiable nodes to a bubble comment.
fn nearest_nodes<'a>(
    comment: &CommentBox,
    nodes: &'a [NodeInfo],
    right_only: bool,
) -> Vec<&'a NodeInfo> {
    let mut candidates: Vec<(&NodeInfo, i64)> = nodes
        .iter()
        .filter(|n| !right_only || n.x >= comment.x)
        .map(|n| {
            let dx = (n.x - comment.x) as i64;
            let dy = (n.y - comment.y) as i64;
            (n, dx * dx + dy * dy)
        })
        .filter(|&(_, d)| d < MAX_BUBBLE_DISTANCE_SQ)
        .collect();
    candidates.sort_by_key(|&(n, d)| (d, n.y, n.x));
    candidates.truncate(5);
    candidates.into_iter().map(|(n, _)| n).collect()
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
/// Uses (Y, X) sort order; UE4 graphs branch vertically (true=up, false=down),
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
    let anchor_indent = indent_of(&bytecode_lines[anchor_line]);
    for i in (0..anchor_line).rev() {
        let line = &bytecode_lines[i];
        let trimmed = line.trim_start();
        let indent = indent_of(line);
        if indent < anchor_indent
            && (trimmed.starts_with("if (") || trimmed.starts_with("} else if ("))
        {
            return Some(i);
        }
    }
    None
}

pub(super) fn find_comment_line(
    comment: &CommentBox,
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> Option<usize> {
    let contained: Vec<&NodeInfo> = if comment.is_bubble {
        // Bubble comments sit on a specific node. The node itself may not have an
        // identifier (e.g. K2Node_IfThenElse), so find the closest identifiable nodes.
        // UE4 execution flows left-to-right, so prefer nodes to the right (downstream).
        // Two-pass: first try right-side only, fall back to all directions.
        let right = nearest_nodes(comment, nodes, true);
        if !right.is_empty() {
            right
        } else {
            nearest_nodes(comment, nodes, false)
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

    // For box comments, prefer execution nodes (CallFunction, VariableSet)
    // over pure nodes (VariableGet). Pure nodes produce expressions inlined
    // at multiple bytecode locations, so rank-based matching is unreliable
    // and can pull the comment to an unrelated outer line.
    let has_execution = !comment.is_bubble && contained.iter().any(|n| !n.is_pure);

    let mut min_line: Option<usize> = None;
    for node in &contained {
        if has_execution && node.is_pure {
            continue;
        }
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

pub(super) fn classify_comments<'a>(
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

        if total_nodes > 0
            && contained > 0
            && contained * 100 / total_nodes > COVERAGE_THRESHOLD_PERCENT
        {
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
