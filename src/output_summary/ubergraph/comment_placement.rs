//! Pin-classified and fallback comment placement within ubergraph sections.

use std::collections::{HashMap, HashSet};

use crate::types::NodePinData;

use super::super::comments::{
    build_node_index, build_ownership_index, classify_comment_by_pins, find_comment_line,
    find_comment_line_clustered, map_export_to_line, CommentPlacement,
};
use super::super::edgraph::EdGraphData;
use super::super::{CommentBox, NodeInfo, UbergraphSection};

use super::events::{resolve_event_position, resolve_section_name, section_for_line};

/// Maximum number of events a comment box can contain and still be treated as
/// an intentional multi-event group. Boxes containing more events are likely
/// organizational section dividers placed for visual layout, not semantic groupings.
const MAX_MULTI_EVENT_GROUP_SIZE: usize = 3;

/// Pre-computed ubergraph comment data shared across event sections.
pub(super) struct UbergraphCommentCtx<'a> {
    pub(super) small_group_idxs: HashSet<usize>,
    /// Inline comments matched against the full unsplit bytecode, then mapped
    /// to sections. Key is section name, value is (section-local line index, comment).
    pub(super) section_inline: HashMap<String, Vec<(usize, &'a CommentBox)>>,
    /// Event-wrapping comments per section (box comments containing the event node).
    pub(super) section_wrapping: HashMap<String, Vec<&'a CommentBox>>,
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
pub(super) fn build_ubergraph_comment_ctx<'a>(
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
