//! EdGraph data collection: comment boxes, node positions, event positions,
//! and EventGraph page merging.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::resolve::{
    find_prop, find_prop_i32, find_prop_str, find_struct_field_str, resolve_index, short_class,
};
use crate::types::{ParsedAsset, PropValue, Property};

use super::{strip_node_func_prefix, CommentBox, NodeInfo};

pub(super) struct EdGraphData {
    pub graph_comments: HashMap<String, Vec<CommentBox>>,
    pub graph_nodes: HashMap<String, Vec<NodeInfo>>,
    pub event_positions: HashMap<String, (i32, i32)>,
    /// K2Node_InputAction nodes store only InputActionName (e.g., "Jump"),
    /// not the full stub function name. Stored separately so
    /// resolve_event_position can pattern-match against InpActEvt_{name}_*.
    pub input_action_positions: HashMap<String, (i32, i32)>,
    /// EdGraph names that are EventGraph sub-pages (contain event-type nodes).
    /// UE4/UE5 splits the EventGraph into multiple pages (e.g., "BeginPlay",
    /// "EventTick", "Input") that must be merged for ubergraph comment matching.
    pub event_graph_pages: Vec<String>,
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
            });
    }
}

/// Collect node positions with identifiers for comment placement.
fn collect_graph_nodes(
    node_class: &str,
    node_props: &[Property],
    graph_name: &str,
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
        if ref_prop == "FunctionReference" {
            strip_node_func_prefix(&name)
        } else {
            name
        }
    } else if node_class == "K2Node_IfThenElse" {
        "__branch__".to_string()
    } else {
        return;
    };
    let is_pure = node_class == "K2Node_VariableGet";
    let (x, y) = node_pos(node_props);
    graph_nodes
        .entry(graph_name.to_string())
        .or_default()
        .push(NodeInfo {
            x,
            y,
            identifier,
            is_pure,
        });
}

fn get_event_name_opt(props: &[Property]) -> Option<String> {
    find_struct_field_str(props, "EventReference", "MemberName")
        .or_else(|| find_struct_field_str(props, "FunctionReference", "MemberName"))
}

/// Check if a node is an event-type node and collect its position if so.
/// Returns true if the node is an event node (used to track EventGraph pages).
fn collect_event_position(
    node_class: &str,
    node_props: &[Property],
    event_positions: &mut HashMap<String, (i32, i32)>,
    input_action_positions: &mut HashMap<String, (i32, i32)>,
) -> bool {
    match node_class {
        "K2Node_Event" | "K2Node_CustomEvent" => {
            let event_name = if node_class == "K2Node_CustomEvent" {
                find_prop_str(node_props, "CustomFunctionName")
                    .or_else(|| get_event_name_opt(node_props))
            } else {
                get_event_name_opt(node_props)
            };
            if let Some(name) = event_name {
                event_positions.insert(name, node_pos(node_props));
            }
            true
        }
        "K2Node_InputAxisEvent" | "K2Node_ComponentBoundEvent" => {
            if let Some(fname) = find_prop_str(node_props, "CustomFunctionName") {
                event_positions.insert(fname, node_pos(node_props));
            }
            true
        }
        "K2Node_InputAction" => {
            if let Some(action) = find_prop_str(node_props, "InputActionName") {
                input_action_positions.insert(action, node_pos(node_props));
            }
            true
        }
        _ => false,
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

/// Collect comment boxes, node positions, and event positions from EdGraph exports.
pub(super) fn collect_edgraph_data(asset: &ParsedAsset, export_names: &[String]) -> EdGraphData {
    let mut graph_comments: HashMap<String, Vec<CommentBox>> = HashMap::new();
    let mut graph_nodes: HashMap<String, Vec<NodeInfo>> = HashMap::new();
    let mut event_positions: HashMap<String, (i32, i32)> = HashMap::new();
    let mut input_action_positions: HashMap<String, (i32, i32)> = HashMap::new();
    let mut event_graph_pages: BTreeSet<String> = BTreeSet::new();

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

            collect_graph_comments(&short, node_props, graph_name, &mut graph_comments);
            if short != "EdGraphNode_Comment" {
                collect_graph_nodes(&short, node_props, graph_name, &mut graph_nodes);
            }

            if collect_event_position(
                &short,
                node_props,
                &mut event_positions,
                &mut input_action_positions,
            ) {
                event_graph_pages.insert(graph_name.clone());
            }
        }
    }

    EdGraphData {
        graph_comments,
        graph_nodes,
        event_positions,
        input_action_positions,
        event_graph_pages: event_graph_pages.into_iter().collect(),
    }
}

/// Merge comments and nodes from all EventGraph pages, deduplicating entries
/// that appear on multiple pages (UE4/UE5 shares node references across tabs).
pub(super) fn merge_event_graph_data(
    pages: &[String],
    edgraph: &EdGraphData,
) -> (Vec<CommentBox>, Vec<NodeInfo>) {
    let mut comments: Vec<CommentBox> = Vec::new();
    let mut nodes: Vec<NodeInfo> = Vec::new();
    let mut seen_comments: HashSet<(i32, i32, String)> = HashSet::new();
    let mut seen_nodes: HashSet<(i32, i32, String)> = HashSet::new();
    for page in pages {
        if let Some(cbs) = edgraph.graph_comments.get(page) {
            for cb in cbs {
                if seen_comments.insert((cb.x, cb.y, cb.text.clone())) {
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
