//! EdGraph data collection: comment boxes, node positions, event positions,
//! and EventGraph page merging.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::bytecode::names::normalize_lwc_name;
use crate::prop_query::{find_prop, find_prop_i32, find_prop_str, find_struct_field_str};
use crate::resolve::{resolve_index, short_class};
use crate::types::{ParsedAsset, PropValue, Property};

use super::{strip_node_func_prefix, CommentBox, NodeInfo, BRANCH_IDENTIFIER};

pub(super) struct EdGraphData {
    pub graph_comments: HashMap<String, Vec<CommentBox>>,
    pub graph_nodes: HashMap<String, Vec<NodeInfo>>,
    /// Event positions: maps event name to (x, y, graph_page).
    pub event_positions: HashMap<String, (i32, i32, String)>,
    /// K2Node_InputAction nodes store only InputActionName (e.g., "Jump"),
    /// not the full stub function name. Stored separately so
    /// resolve_event_position can pattern-match against InpActEvt_{name}_*.
    pub input_action_positions: HashMap<String, (i32, i32, String)>,
    /// EdGraph names that are EventGraph sub-pages (contain event-type nodes).
    /// The EventGraph is split into multiple pages (e.g. "BeginPlay",
    /// "EventTick", "Input") that must be merged for ubergraph comment matching.
    pub event_graph_pages: Vec<String>,
    /// Maps event name to the set of node export indices reachable via execution
    /// pin connections. Used to determine which event a node belongs to.
    pub event_node_ownership: HashMap<String, HashSet<usize>>,
    /// Positions for ALL EdGraph nodes per graph page. Outer key is page name,
    /// inner maps 1-based export index to (x, y). Used for containment checks
    /// in pin-based comment classification.
    pub all_node_positions: HashMap<String, HashMap<usize, (i32, i32)>>,
    /// Event name to 1-based export index of the event node.
    pub event_export_indices: HashMap<String, usize>,
}

fn node_pos(props: &[Property]) -> (i32, i32) {
    (
        find_prop_i32(props, "NodePosX").unwrap_or(0),
        find_prop_i32(props, "NodePosY").unwrap_or(0),
    )
}

/// Node classes whose reference property contains an identifier for comment matching.
const NODE_IDENTIFIER_REFS: &[(&str, &str)] = &[
    ("K2Node_CallFunction", "FunctionReference"),
    ("K2Node_CallArrayFunction", "FunctionReference"),
    ("K2Node_Message", "FunctionReference"),
    (
        "K2Node_CommutativeAssociativeBinaryOperator",
        "FunctionReference",
    ),
    ("K2Node_VariableGet", "VariableReference"),
    ("K2Node_VariableSet", "VariableReference"),
];

/// Collect comment boxes and bubble comments from a single graph node.
fn collect_graph_comments(
    node_class: &str,
    node_props: &[Property],
    graph_name: &str,
    export_index: usize,
    graph_comments: &mut HashMap<String, Vec<CommentBox>>,
) {
    // Comment nodes are full box comments with dimensions
    let is_comment = node_class == "EdGraphNode_Comment";
    // Non-comment nodes can have bubble comments (skip reroute knots,
    // their labels describe wire routing, not logic)
    let is_bubble = !is_comment
        && node_class != "K2Node_Knot"
        && find_prop(node_props, "bCommentBubbleVisible")
            .is_some_and(|p| matches!(p.value, PropValue::Bool(true)));

    if !is_comment && !is_bubble {
        return;
    }
    if let Some(text) = find_prop_str(node_props, "NodeComment") {
        let (x, y) = node_pos(node_props);
        let (width, height) = if is_comment {
            (
                find_prop_i32(node_props, "NodeWidth").unwrap_or(0),
                find_prop_i32(node_props, "NodeHeight").unwrap_or(0),
            )
        } else {
            (0, 0)
        };
        graph_comments
            .entry(graph_name.to_string())
            .or_default()
            .push(CommentBox {
                text,
                x,
                y,
                width,
                height,
                is_bubble,
                graph_page: graph_name.to_string(),
                owner_export: if is_bubble { export_index } else { 0 },
            });
    }
}

/// Collect node positions with identifiers for comment placement.
fn collect_graph_nodes(
    node_class: &str,
    node_props: &[Property],
    graph_name: &str,
    export_index: usize,
    graph_nodes: &mut HashMap<String, Vec<NodeInfo>>,
) {
    let identifier = if let Some(ref_prop) = NODE_IDENTIFIER_REFS
        .iter()
        .find(|(cls, _)| *cls == node_class)
        .map(|(_, prop)| *prop)
    {
        let Some(name) = find_struct_field_str(node_props, ref_prop, "MemberName") else {
            return;
        };
        // Normalize LWC names so UE5 node identifiers (e.g. Add_DoubleDouble)
        // match the normalized bytecode (Add_FloatFloat) for comment placement.
        let name = normalize_lwc_name(&name);
        if ref_prop == "FunctionReference" {
            strip_node_func_prefix(&name)
        } else {
            name
        }
    } else if node_class == "K2Node_IfThenElse" {
        BRANCH_IDENTIFIER.to_string()
    } else {
        return;
    };
    let is_pure = node_class == "K2Node_VariableGet"
        || node_class == "K2Node_CommutativeAssociativeBinaryOperator"
        || matches!(find_prop(node_props, "bIsPureFunc"), Some(p) if matches!(p.value, PropValue::Bool(true)));
    let is_variable_set = node_class == "K2Node_VariableSet";
    let (x, y) = node_pos(node_props);
    graph_nodes
        .entry(graph_name.to_string())
        .or_default()
        .push(NodeInfo {
            x,
            y,
            identifier,
            is_pure,
            is_variable_set,
            export_index,
            graph_page: graph_name.to_string(),
        });
}

fn get_event_name_opt(props: &[Property]) -> Option<String> {
    find_struct_field_str(props, "EventReference", "MemberName")
        .or_else(|| find_struct_field_str(props, "FunctionReference", "MemberName"))
}

/// Check if a node is an event-type node and collect its position if so.
/// Returns the event name when the node is an event (used for EventGraph page
/// tracking and pin-based BFS ownership).
fn collect_event_position(
    node_class: &str,
    node_props: &[Property],
    graph_name: &str,
    event_positions: &mut HashMap<String, (i32, i32, String)>,
    input_action_positions: &mut HashMap<String, (i32, i32, String)>,
) -> Option<String> {
    match node_class {
        "K2Node_Event" | "K2Node_CustomEvent" => {
            let event_name = if node_class == "K2Node_CustomEvent" {
                find_prop_str(node_props, "CustomFunctionName")
                    .or_else(|| get_event_name_opt(node_props))
            } else {
                get_event_name_opt(node_props)
            };
            if let Some(ref name) = event_name {
                let (x, y) = node_pos(node_props);
                event_positions.insert(name.clone(), (x, y, graph_name.to_string()));
            }
            event_name
        }
        "K2Node_InputAxisEvent" | "K2Node_ComponentBoundEvent" => {
            let fname = find_prop_str(node_props, "CustomFunctionName");
            if let Some(ref name) = fname {
                let (x, y) = node_pos(node_props);
                event_positions.insert(name.clone(), (x, y, graph_name.to_string()));
            }
            fname
        }
        "K2Node_InputAction" => {
            let action = find_prop_str(node_props, "InputActionName");
            if let Some(ref name) = action {
                let (x, y) = node_pos(node_props);
                input_action_positions.insert(name.clone(), (x, y, graph_name.to_string()));
            }
            action
        }
        _ => None,
    }
}

/// Extract object indices from a Nodes/AllNodes array property.
fn collect_node_indices(props: &[Property]) -> Vec<i32> {
    find_prop(props, "Nodes")
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
        .unwrap_or_default()
}

/// Build per-event node ownership by BFS through execution pin connections.
fn build_event_node_sets(
    asset: &ParsedAsset,
    event_export_indices: &HashMap<String, usize>,
) -> HashMap<String, HashSet<usize>> {
    if asset.pin_data.is_empty() || event_export_indices.is_empty() {
        return HashMap::new();
    }
    let mut ownership: HashMap<String, HashSet<usize>> = HashMap::new();
    for (event_name, &start_idx) in event_export_indices {
        let mut visited: HashSet<usize> = HashSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(start_idx);
        visited.insert(start_idx);
        while let Some(idx) = queue.pop_front() {
            let Some(pin_data) = asset.pin_data.get(&idx) else {
                continue;
            };
            for pin in &pin_data.pins {
                if !pin.is_exec_output() {
                    continue;
                }
                for &target_idx in &pin.linked_to {
                    if visited.insert(target_idx) {
                        queue.push_back(target_idx);
                    }
                }
            }
        }
        if visited.len() > 1 {
            ownership.insert(event_name.clone(), visited);
        }
    }
    ownership
}

/// Collect comment boxes, node positions, and event positions from EdGraph exports.
pub(super) fn collect_edgraph_data(asset: &ParsedAsset, export_names: &[String]) -> EdGraphData {
    let mut graph_comments: HashMap<String, Vec<CommentBox>> = HashMap::new();
    let mut graph_nodes: HashMap<String, Vec<NodeInfo>> = HashMap::new();
    let mut event_positions: HashMap<String, (i32, i32, String)> = HashMap::new();
    let mut input_action_positions: HashMap<String, (i32, i32, String)> = HashMap::new();
    let mut event_graph_pages: BTreeSet<String> = BTreeSet::new();
    let mut event_export_indices: HashMap<String, usize> = HashMap::new();
    let mut all_node_positions: HashMap<String, HashMap<usize, (i32, i32)>> = HashMap::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".EdGraph") {
            continue;
        }
        let graph_name = &hdr.object_name;

        for idx in &collect_node_indices(props) {
            if *idx <= 0 {
                continue;
            }
            let export_idx = (*idx - 1) as usize;
            let Some((node_hdr, node_props)) = asset.exports.get(export_idx) else {
                continue;
            };
            let node_class = resolve_index(&asset.imports, export_names, node_hdr.class_index);
            let short = short_class(&node_class);

            collect_graph_comments(
                &short,
                node_props,
                graph_name,
                export_idx + 1,
                &mut graph_comments,
            );
            if short != "EdGraphNode_Comment" {
                let (nx, ny) = node_pos(node_props);
                all_node_positions
                    .entry(graph_name.to_string())
                    .or_default()
                    .insert(export_idx + 1, (nx, ny));
                collect_graph_nodes(
                    &short,
                    node_props,
                    graph_name,
                    export_idx + 1,
                    &mut graph_nodes,
                );
            }

            if let Some(event_name) = collect_event_position(
                &short,
                node_props,
                graph_name,
                &mut event_positions,
                &mut input_action_positions,
            ) {
                event_graph_pages.insert(graph_name.clone());
                event_export_indices.insert(event_name, export_idx + 1);
            }
        }
    }

    let event_node_ownership = build_event_node_sets(asset, &event_export_indices);
    EdGraphData {
        graph_comments,
        graph_nodes,
        event_positions,
        input_action_positions,
        event_graph_pages: event_graph_pages.into_iter().collect(),
        event_node_ownership,
        all_node_positions,
        event_export_indices,
    }
}

/// Merge comments and nodes from all EventGraph pages, deduplicating entries
/// that appear on multiple pages (node references are shared across tabs).
///
/// For comments appearing on multiple pages, assigns graph_page to the page
/// where the comment box contains the most nodes. This ensures the comment
/// matches against the correct event's nodes for spatial filtering.
pub(super) fn merge_event_graph_data(
    pages: &[String],
    edgraph: &EdGraphData,
) -> (Vec<CommentBox>, Vec<NodeInfo>) {
    let mut comments: Vec<CommentBox> = Vec::new();
    let mut nodes: Vec<NodeInfo> = Vec::new();
    let mut seen_comments: HashMap<(i32, i32, String), usize> = HashMap::new(); // key -> index
    let mut seen_nodes: HashSet<(i32, i32, String)> = HashSet::new();
    for page in pages {
        if let Some(cbs) = edgraph.graph_comments.get(page) {
            for cb in cbs {
                let key = (cb.x, cb.y, cb.text.clone());
                if let Some(&idx) = seen_comments.get(&key) {
                    // Comment already seen on another page. Prefer the page where
                    // the comment contains the most identifiable nodes (using
                    // graph_nodes which correctly tracks per-page membership).
                    let existing = &comments[idx];
                    let existing_count = edgraph
                        .graph_nodes
                        .get(&existing.graph_page)
                        .map(|ns| {
                            ns.iter()
                                .filter(|n| existing.contains_point(n.x, n.y))
                                .count()
                        })
                        .unwrap_or(0);
                    let new_count = edgraph
                        .graph_nodes
                        .get(page)
                        .map(|ns| ns.iter().filter(|n| cb.contains_point(n.x, n.y)).count())
                        .unwrap_or(0);
                    if new_count > existing_count {
                        comments[idx].graph_page = page.clone();
                    }
                } else {
                    seen_comments.insert(key, comments.len());
                    comments.push(cb.clone());
                }
            }
        }
        if let Some(ns) = edgraph.graph_nodes.get(page) {
            for node in ns {
                if seen_nodes.insert((node.x, node.y, node.identifier.clone())) {
                    nodes.push(node.clone());
                }
            }
        }
    }
    (comments, nodes)
}
