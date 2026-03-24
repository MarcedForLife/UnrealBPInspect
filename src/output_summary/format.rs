//! Summary formatting: Blueprint header, component tree, variables, function signatures,
//! and pseudo-code bodies.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::BcStatement;
use crate::helpers::indent_of;
use crate::resolve::*;
use crate::types::*;

use super::comments::classify_comments;
use super::ubergraph::{
    build_ubergraph_structured, emit_ubergraph_events, is_ubergraph_stub, scan_structured_calls,
};
use super::{
    emit_comment, find_local_calls, section_sep, strip_node_func_prefix, strip_offset_prefix,
    CommentBox, NodeInfo,
};

const COMP_SKIP_PROPS: &[&str] = &[
    "StaticMeshImportVersion",
    "bVisualizeComponent",
    "CreationMethod",
];

struct SummaryCtx<'a> {
    imports: &'a [ImportEntry],
    export_names: &'a [String],
    comp_props: &'a HashMap<String, &'a [Property]>,
    cat_exports: &'a HashMap<String, (String, &'a [Property])>,
}

fn fmt_prop_list(
    buf: &mut String,
    indent: &str,
    props: &[Property],
    skip: &[&str],
    ctx: &SummaryCtx,
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
                    let val = prop_value_short(&prop.value, ctx.imports, ctx.export_names);
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
                                let val = prop_value_short(&f.value, ctx.imports, ctx.export_names);
                                Some(format!("{}: {}", f.name, val))
                            }
                        })
                        .collect();
                    if !summary.is_empty() {
                        writeln!(buf, "{}{}: {}", indent, prop.name, summary.join(", ")).unwrap();
                    }
                }
            }
            continue;
        }
        let val = prop_value_short(&prop.value, ctx.imports, ctx.export_names);
        writeln!(buf, "{}{}: {}", indent, prop.name, val).unwrap();
    }
}

fn fmt_comp_props(buf: &mut String, name: &str, class: &str, depth: usize, ctx: &SummaryCtx) {
    let indent = "  ".repeat(depth + 1);
    let prop_indent = "  ".repeat(depth + 2);
    writeln!(buf, "{}{} ({})", indent, name, class).unwrap();
    if let Some(props) = ctx.comp_props.get(name) {
        let skip = &[
            "ChildActorTemplate",
            COMP_SKIP_PROPS[0],
            COMP_SKIP_PROPS[1],
            COMP_SKIP_PROPS[2],
        ];
        fmt_prop_list(buf, &prop_indent, props, skip, ctx);
        // Handle ChildActorTemplate
        let child_actor_tpl =
            find_prop_object(props, "ChildActorTemplate", ctx.imports, ctx.export_names);
        if let Some(tpl_name) = child_actor_tpl {
            if let Some((tpl_class, tpl_props)) = ctx.cat_exports.get(&tpl_name) {
                writeln!(buf, "{}[template: {}]", prop_indent, tpl_class).unwrap();
                let tpl_indent = format!("{}  ", prop_indent);
                fmt_prop_list(buf, &tpl_indent, tpl_props, COMP_SKIP_PROPS, ctx);
            }
        }
    }
}

fn fmt_comp_tree(
    buf: &mut String,
    node_name: &str,
    depth: usize,
    scs_nodes: &HashMap<String, (String, String, Vec<String>)>,
    ctx: &SummaryCtx,
) {
    if let Some((comp_name, comp_class, children)) = scs_nodes.get(node_name) {
        fmt_comp_props(buf, comp_name, comp_class, depth, ctx);
        for child in children {
            fmt_comp_tree(buf, child, depth + 1, scs_nodes, ctx);
        }
    }
}

/// Find the Blueprint name and parent class, write the header line.
/// Returns `(bp_name, bp_parent)`.
fn format_header(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
) -> (String, String) {
    let mut bp_name = String::new();
    let mut bp_parent = String::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if class.ends_with(".Blueprint") {
            bp_name = hdr.object_name.clone();
            if let Some(p) = find_prop(props, "ParentClass") {
                if let PropValue::Object(idx) = &p.value {
                    bp_parent = resolve_index(&asset.imports, export_names, *idx);
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

    (bp_name, bp_parent)
}

/// Parse SCS_Node exports, build the component tree, format properties.
/// Returns the list of `(comp_name, comp_class)` pairs (needed by variable filtering).
fn format_component_tree(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
) -> Vec<(String, String)> {
    let mut scs_nodes: HashMap<String, (String, String, Vec<String>)> = HashMap::new();
    let mut components: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".SCS_Node") {
            continue;
        }
        let comp_name = find_prop_str(props, "InternalVariableName")
            .or_else(|| {
                find_prop_object(props, "ComponentTemplate", &asset.imports, export_names)
                    .map(|tpl| tpl.trim_end_matches("_GEN_VARIABLE").to_string())
            })
            .unwrap_or_else(|| hdr.object_name.clone());
        let comp_class = find_prop_object(props, "ComponentClass", &asset.imports, export_names)
            .map(|class| short_class(&class))
            .unwrap_or_else(|| "?".into());
        let children = find_prop_object_array(props, "ChildNodes", &asset.imports, export_names);
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
            let class = resolve_index(&asset.imports, export_names, hdr.class_index);
            cat_exports.insert(hdr.object_name.clone(), (short_class(&class), props));
        }
    }

    if !components.is_empty() {
        let ctx = SummaryCtx {
            imports: &asset.imports,
            export_names,
            comp_props: &comp_props,
            cat_exports: &cat_exports,
        };
        writeln!(buf, "Components:").unwrap();
        for root in &root_nodes {
            fmt_comp_tree(buf, root, 0, &scs_nodes, &ctx);
        }
        writeln!(buf).unwrap();
    }

    components
}

/// Collect member variables and defaults, write the variables section.
fn format_variables(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
    component_names: &[(String, String)],
) {
    let comp_names: Vec<&str> = component_names.iter().map(|(n, _)| n.as_str()).collect();

    let mut members: Vec<String> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".BlueprintGeneratedClass") {
            continue;
        }
        for decl in find_prop_str_items(props, "Members") {
            let var_name = decl.split(':').next().unwrap_or("");
            if comp_names.contains(&var_name) {
                continue;
            }
            if var_name == "UberGraphFrame" {
                continue;
            }
            members.push(decl.to_string());
        }
    }

    let mut defaults: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        if hdr.object_name.starts_with("Default__") && !props.is_empty() {
            for prop in props {
                if matches!(prop.name.as_str(), "ActorLabel" | "bCanProxyPhysics") {
                    continue;
                }
                let val_str = prop_value_short(&prop.value, &asset.imports, export_names);
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
}

struct EdGraphData {
    graph_comments: HashMap<String, Vec<CommentBox>>,
    graph_nodes: HashMap<String, Vec<NodeInfo>>,
    event_positions: HashMap<String, (i32, i32)>,
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
    (
        "K2Node_CommutativeAssociativeBinaryOperator",
        "FunctionReference",
    ),
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
    let (x, y) = node_pos(node_props);
    graph_nodes
        .entry(graph_name.to_string())
        .or_default()
        .push(NodeInfo { x, y, identifier });
}

/// Collect comment boxes, node positions, and event positions from EdGraph exports.
fn collect_edgraph_data(asset: &ParsedAsset, export_names: &[String]) -> EdGraphData {
    let mut graph_comments: HashMap<String, Vec<CommentBox>> = HashMap::new();
    let mut graph_nodes: HashMap<String, Vec<NodeInfo>> = HashMap::new();
    let mut event_positions: HashMap<String, (i32, i32)> = HashMap::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
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
            let node_class = resolve_index(&asset.imports, export_names, node_hdr.class_index);
            let short = short_class(&node_class);

            collect_graph_comments(&short, node_props, graph_name, &mut graph_comments);
            if short != "EdGraphNode_Comment" {
                collect_graph_nodes(&short, node_props, graph_name, &mut graph_nodes);
            }

            // Collect event positions for ubergraph splitting
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
                    event_positions.insert(name, node_pos(node_props));
                }
            }
        }
    }

    EdGraphData {
        graph_comments,
        graph_nodes,
        event_positions,
    }
}

/// Parse a stored bytecode line (`"XXXX: text"`) into a `BcStatement`.
fn parse_bytecode_line(line: &str) -> Option<BcStatement> {
    let hex_len = 4;
    let separator = ": ";
    let prefix_len = hex_len + separator.len();
    if line.len() <= prefix_len || line.as_bytes()[hex_len] != b':' {
        return None;
    }
    let offset = usize::from_str_radix(&line[..hex_len], 16).ok()?;
    Some(BcStatement {
        mem_offset: offset,
        text: line[prefix_len..].to_string(),
    })
}

/// Parse a single bytecode line for a call to the ubergraph entry point,
/// returning the offset argument if found.
fn parse_ubergraph_call(line: &str, call_prefix: &str) -> Option<usize> {
    let start = line.find(call_prefix)?;
    let after = &line[start + call_prefix.len()..];
    let end = after.find(')')?;
    after[..end].trim().parse::<usize>().ok()
}

/// Scan non-ubergraph function bytecode for calls to the ubergraph entry point,
/// returning a bytecode offset to event name mapping.
fn find_ubergraph_labels(
    asset: &ParsedAsset,
    export_names: &[String],
    ubergraph_name: &str,
) -> HashMap<usize, String> {
    let mut labels = HashMap::new();
    let call_prefix = format!("{}(", ubergraph_name);

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") || hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }
        for line in find_prop_str_items_any(props, &["BytecodeSummary", "Bytecode"]) {
            if let Some(offset) = parse_ubergraph_call(line, &call_prefix) {
                labels.insert(offset, hdr.object_name.clone());
            }
        }
    }
    labels
}

/// Build the call graph by scanning function bytecodes for cross-references.
///
/// Returns `(callees_map, callers_map)` where each maps a function name to the
/// list of local functions it calls (or is called by).
fn build_call_graph(
    asset: &ParsedAsset,
    export_names: &[String],
    local_functions: &HashSet<String>,
    ubergraph_name: Option<&str>,
    ubergraph_structured: Option<&[String]>,
) -> (HashMap<String, Vec<String>>, HashMap<String, Vec<String>>) {
    let mut callees_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut callers_map: HashMap<String, Vec<String>> = HashMap::new();

    // Scan non-ubergraph functions for calls to local functions
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }
        if ubergraph_name.is_some() && is_ubergraph_stub(props, ubergraph_name.unwrap_or("")) {
            continue;
        }

        let bc_lines = find_prop_str_items_any(props, &["Bytecode", "BytecodeSummary"]);
        if bc_lines.is_empty() {
            continue;
        }

        for line in bc_lines {
            let code = strip_offset_prefix(line);
            for callee in find_local_calls(code, local_functions) {
                if callee == hdr.object_name {
                    continue;
                }
                let entry = callees_map.entry(hdr.object_name.clone()).or_default();
                if !entry.contains(&callee) {
                    entry.push(callee.clone());
                }
                let entry = callers_map.entry(callee.clone()).or_default();
                if !entry.contains(&hdr.object_name) {
                    entry.push(hdr.object_name.clone());
                }
            }
        }
    }

    // Scan structured ubergraph output for local calls per event section
    if let Some(structured) = ubergraph_structured {
        scan_structured_calls(
            structured,
            local_functions,
            &mut callees_map,
            &mut callers_map,
        );
    }

    (callees_map, callers_map)
}

/// Format a parsed asset as a human-readable summary.
///
/// Produces: Blueprint name/parent, component tree, variables, function signatures
/// with structured pseudo-code bodies, and inline EdGraph comments. When `filters`
/// is non-empty, only functions matching a filter substring are shown.
pub fn format_summary(asset: &ParsedAsset, filters: &[String]) -> String {
    let mut buf = String::new();
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();

    let (_bp_name, _bp_parent) = format_header(&mut buf, asset, &export_names);
    let components = format_component_tree(&mut buf, asset, &export_names);
    format_variables(&mut buf, asset, &export_names, &components);

    // Ubergraph entry points
    let ubergraph_name: Option<String> = asset
        .exports
        .iter()
        .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))
        .map(|(hdr, _)| hdr.object_name.clone());
    let ubergraph_labels: HashMap<usize, String> = match ubergraph_name {
        Some(ref ug_name) => find_ubergraph_labels(asset, &export_names, ug_name),
        None => HashMap::new(),
    };

    let edgraph = collect_edgraph_data(asset, &export_names);

    // Build local function name set (includes ubergraph event names)
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
        for event_name in ubergraph_labels.values() {
            names.insert(event_name.clone());
        }
        names
    };

    // Pre-compute structured ubergraph output for call graph scanning
    let ubergraph_structured: Option<Vec<String>> = if !ubergraph_labels.is_empty() {
        asset
            .exports
            .iter()
            .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))
            .and_then(|(_, props)| {
                let stmts: Vec<BcStatement> = find_prop_str_items(props, "Bytecode")
                    .iter()
                    .filter_map(|line| parse_bytecode_line(line))
                    .collect();
                build_ubergraph_structured(stmts, &ubergraph_labels)
            })
    } else {
        None
    };

    let (mut callees_map, callers_map) = build_call_graph(
        asset,
        &export_names,
        &local_functions,
        ubergraph_name.as_deref(),
        ubergraph_structured.as_deref(),
    );

    // Emit call graph section
    if !callees_map.is_empty() {
        let mut entries: Vec<(&String, &mut Vec<String>)> = callees_map.iter_mut().collect();
        entries.sort_by(|(a, _), (b, _)| a.cmp(b));
        writeln!(buf, "Call graph:").unwrap();
        for (caller, callees) in &mut entries {
            callees.sort();
            writeln!(buf, "  {} \u{2192} {}", caller, callees.join(", ")).unwrap();
        }
        writeln!(buf).unwrap();
    }

    // Functions with signatures and bytecode
    let mut emitted_function_count = 0usize;
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
            .filter(|f| !f.is_empty())
            .map(|f| format!(" [{}]", f))
            .unwrap_or_default();

        // For ubergraph: use pre-computed structured output
        if hdr.object_name.starts_with("ExecuteUbergraph_") && !ubergraph_labels.is_empty() {
            if let Some(ref structured) = ubergraph_structured {
                if emitted_function_count == 0 {
                    writeln!(buf, "Functions:").unwrap();
                }
                section_sep(&mut buf, &mut emitted_function_count);
                let ug_comments = edgraph
                    .graph_comments
                    .get("EventGraph")
                    .map(|v| v.as_slice());
                let ug_nodes = edgraph.graph_nodes.get("EventGraph").map(|v| v.as_slice());
                emit_ubergraph_events(
                    &mut buf,
                    structured,
                    ug_comments,
                    ug_nodes,
                    &edgraph.event_positions,
                    &callers_map,
                );
                functions_with_bytecode.insert(hdr.object_name.clone());
            }
            continue;
        }

        if emitted_function_count == 0 {
            writeln!(buf, "Functions:").unwrap();
        }
        section_sep(&mut buf, &mut emitted_function_count);
        if let Some(callers) = callers_map.get(&hdr.object_name) {
            writeln!(buf, "  // called by: {}", callers.join(", ")).unwrap();
        }
        writeln!(buf, "  {}{}", sig, flags).unwrap();

        // Collect bytecode lines (BytecodeSummary is pre-stripped; Bytecode needs offset removal)
        let bc_lines: Vec<String> = {
            let summary = find_prop_str_items(props, "BytecodeSummary");
            if !summary.is_empty() {
                summary.iter().map(|s| s.to_string()).collect()
            } else {
                find_prop_str_items(props, "Bytecode")
                    .iter()
                    .map(|s| strip_offset_prefix(s).to_string())
                    .collect()
            }
        };

        // Classify comments as top-level vs inline using node positions
        let comments = edgraph.graph_comments.get(&hdr.object_name);
        let nodes = edgraph.graph_nodes.get(&hdr.object_name);
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
                    let ws_len = indent_of(line);
                    let indent = format!("    {}", &line[..ws_len]);
                    emit_comment(&mut buf, &inline[inline_idx].1.text, &indent);
                    inline_idx += 1;
                }
                writeln!(buf, "    {}", line).unwrap();
            }
            functions_with_bytecode.insert(hdr.object_name.clone());
        }
    }
    if emitted_function_count > 0 {
        writeln!(buf).unwrap();
    }

    buf
}
fn get_event_name_opt(props: &[Property]) -> Option<String> {
    // Try EventReference.MemberName first, then FunctionReference.MemberName
    find_struct_field_str(props, "EventReference", "MemberName")
        .or_else(|| find_struct_field_str(props, "FunctionReference", "MemberName"))
}

fn filter_flags_for_summary(flags: &str) -> String {
    const NOISE: &[&str] = &["BlueprintCallable"];
    flags
        .split('|')
        .filter(|f| !NOISE.contains(&f.trim()))
        .collect::<Vec<_>>()
        .join("|")
}
