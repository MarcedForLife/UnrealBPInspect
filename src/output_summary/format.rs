//! Summary formatting: Blueprint header, component tree, variables, function signatures,
//! and pseudo-code bodies.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::BcStatement;
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
                                    let val = prop_value_short(&f.value, imports, export_names);
                                    Some(format!("{}: {}", f.name, val))
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
                // Collect bubble comments from non-comment nodes (skip reroute knots --
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
                    build_ubergraph_structured(stmts, &ubergraph_labels)
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
                if emitted_function_count == 0 {
                    writeln!(buf, "Functions:").unwrap();
                }
                section_sep(&mut buf, &mut emitted_function_count);
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

        if emitted_function_count == 0 {
            writeln!(buf, "Functions:").unwrap();
        }
        section_sep(&mut buf, &mut emitted_function_count);
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
    if emitted_function_count > 0 {
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
