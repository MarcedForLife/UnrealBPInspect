//! Summary formatting: Blueprint header, component tree, variables, function signatures,
//! and pseudo-code bodies.

use std::collections::HashMap;
use std::fmt::Write;

use crate::bytecode::fold_long_lines;
use crate::helpers::indent_of;
use crate::resolve::{
    find_prop, find_prop_object, find_prop_object_array, find_prop_str, find_prop_str_items,
    prop_value_short, resolve_index, short_class,
};
use crate::types::{ImportEntry, ParsedAsset, PropValue, Property};

use super::call_graph::{
    build_call_graph, build_ubergraph_ctx, collect_local_functions, format_call_graph, UbergraphCtx,
};
use super::comments::classify_comments;
use super::edgraph::{collect_edgraph_data, merge_event_graph_data, EdGraphData};
use super::ubergraph::{emit_ubergraph_events, is_ubergraph_stub};
use super::{emit_comment, section_sep, strip_offset_prefix};

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

/// Emit a single function's bytecode with inline and top-level comments.
fn emit_function_body(
    buf: &mut String,
    func_name: &str,
    props: &[Property],
    edgraph: &EdGraphData,
    callers_map: &HashMap<String, Vec<String>>,
    sig: &str,
    flags: &str,
) {
    if let Some(callers) = callers_map.get(func_name) {
        writeln!(buf, "  // called by: {}", callers.join(", ")).unwrap();
    }
    writeln!(buf, "  {}{}", sig, flags).unwrap();

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

    let comments = edgraph.graph_comments.get(func_name);
    let nodes = edgraph.graph_nodes.get(func_name);
    let (top_level, inline) = if let Some(cbs) = comments {
        let node_slice = nodes.map(|v| v.as_slice()).unwrap_or(&[]);
        classify_comments(cbs, node_slice, &bc_lines)
    } else {
        (Vec::new(), Vec::new())
    };

    if !top_level.is_empty() {
        let mut sorted_top = top_level;
        sorted_top.sort_by(|a, b| a.x.cmp(&b.x).then(a.y.cmp(&b.y)).then(a.text.cmp(&b.text)));
        for cb in &sorted_top {
            emit_comment(buf, &cb.text, "    ");
        }
    }

    if bc_lines.is_empty() {
        return;
    }
    let mut inline_idx = 0;
    for (i, line) in bc_lines.iter().enumerate() {
        while inline_idx < inline.len() && inline[inline_idx].0 == i {
            let ws_len = indent_of(line);
            let indent = format!("    {}", &line[..ws_len]);
            emit_comment(buf, &inline[inline_idx].1.text, &indent);
            inline_idx += 1;
        }
        writeln!(buf, "    {}", line).unwrap();
    }
}

/// Emit the ubergraph (EventGraph) events with merged sub-page data.
fn emit_ubergraph_section(
    buf: &mut String,
    structured: &[String],
    edgraph: &EdGraphData,
    callers_map: &HashMap<String, Vec<String>>,
) {
    let (ug_comments, ug_nodes) = merge_event_graph_data(&edgraph.event_graph_pages, edgraph);
    let ug_comments_ref = if ug_comments.is_empty() {
        None
    } else {
        Some(ug_comments.as_slice())
    };
    let ug_nodes_ref = if ug_nodes.is_empty() {
        None
    } else {
        Some(ug_nodes.as_slice())
    };
    emit_ubergraph_events(
        buf,
        structured,
        ug_comments_ref,
        ug_nodes_ref,
        &edgraph.event_positions,
        &edgraph.input_action_positions,
        callers_map,
    );
}

/// Emit all function exports: ubergraph events and regular functions.
fn format_functions(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
    ubergraph_ctx: Option<&UbergraphCtx>,
    edgraph: &EdGraphData,
    callers_map: &HashMap<String, Vec<String>>,
) {
    let mut emitted_count = 0usize;
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if let Some(ctx) = ubergraph_ctx {
            if !hdr.object_name.starts_with("ExecuteUbergraph_")
                && is_ubergraph_stub(props, &ctx.name)
            {
                continue;
            }
        }

        let sig =
            find_prop_str(props, "Signature").unwrap_or_else(|| format!("{}()", hdr.object_name));
        let flags = find_prop_str(props, "FunctionFlags")
            .map(|f| filter_flags_for_summary(&f))
            .filter(|f| !f.is_empty())
            .map(|f| format!(" [{}]", f))
            .unwrap_or_default();

        if emitted_count == 0 {
            writeln!(buf, "Functions:").unwrap();
        }

        if let Some(ctx) = ubergraph_ctx {
            if hdr.object_name.starts_with("ExecuteUbergraph_") {
                section_sep(buf, &mut emitted_count);
                emit_ubergraph_section(buf, &ctx.structured, edgraph, callers_map);
                continue;
            }
        }

        section_sep(buf, &mut emitted_count);
        emit_function_body(
            buf,
            &hdr.object_name,
            props,
            edgraph,
            callers_map,
            &sig,
            &flags,
        );
    }
    if emitted_count > 0 {
        writeln!(buf).unwrap();
    }
}

fn filter_flags_for_summary(flags: &str) -> String {
    const NOISE: &[&str] = &["BlueprintCallable"];
    flags
        .split('|')
        .filter(|f| !NOISE.contains(&f.trim()))
        .collect::<Vec<_>>()
        .join("|")
}

pub fn format_summary(asset: &ParsedAsset) -> String {
    let mut buf = String::new();
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();

    let (_bp_name, _bp_parent) = format_header(&mut buf, asset, &export_names);
    let components = format_component_tree(&mut buf, asset, &export_names);
    format_variables(&mut buf, asset, &export_names, &components);

    let ubergraph_ctx = build_ubergraph_ctx(asset, &export_names);
    let edgraph = collect_edgraph_data(asset, &export_names);
    let local_functions = collect_local_functions(asset, &export_names, ubergraph_ctx.as_ref());

    let (mut callees_map, callers_map) = build_call_graph(
        asset,
        &export_names,
        &local_functions,
        ubergraph_ctx.as_ref().map(|c| c.name.as_str()),
        ubergraph_ctx.as_ref().map(|c| c.structured.as_slice()),
    );

    format_call_graph(&mut buf, &mut callees_map);
    format_functions(
        &mut buf,
        asset,
        &export_names,
        ubergraph_ctx.as_ref(),
        &edgraph,
        &callers_map,
    );

    let mut final_lines: Vec<String> = buf.split('\n').map(|l| l.to_string()).collect();
    fold_long_lines(&mut final_lines);
    final_lines.join("\n")
}
