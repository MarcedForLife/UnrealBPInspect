//! Summary formatting: Blueprint header, component tree, variables, function signatures,
//! and pseudo-code bodies.

use std::collections::HashMap;
use std::fmt::Write;

use crate::prop_query::{
    find_prop, find_prop_object, find_prop_object_array, find_prop_str, find_prop_str_items,
    prop_value_short,
};
use crate::resolve::{class_of, resolve_index, short_class};
use crate::types::{ImportEntry, ParsedAsset, PropValue, Property};

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
    let indent = " ".repeat(super::INDENT_WIDTH * (depth + 1));
    let prop_indent = " ".repeat(super::INDENT_WIDTH * (depth + 2));
    writeln!(buf, "{}{} ({})", indent, name, class).unwrap();
    if let Some(props) = ctx.comp_props.get(name) {
        let skip: Vec<&str> = std::iter::once("ChildActorTemplate")
            .chain(COMP_SKIP_PROPS.iter().copied())
            .collect();
        fmt_prop_list(buf, &prop_indent, props, &skip, ctx);
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
pub(crate) fn format_header(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
) -> (String, String) {
    let mut bp_name = String::new();
    let mut bp_parent = String::new();

    for (hdr, props) in &asset.exports {
        let class = class_of(&asset.imports, export_names, hdr);
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
pub(crate) fn format_component_tree(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
) -> Vec<(String, String)> {
    let mut scs_nodes: HashMap<String, (String, String, Vec<String>)> = HashMap::new();
    let mut components: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = class_of(&asset.imports, export_names, hdr);
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
            let class = class_of(&asset.imports, export_names, hdr);
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
pub(crate) fn format_variables(
    buf: &mut String,
    asset: &ParsedAsset,
    export_names: &[String],
    component_names: &[(String, String)],
) {
    let comp_names: Vec<&str> = component_names.iter().map(|(n, _)| n.as_str()).collect();

    let mut members: Vec<String> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = class_of(&asset.imports, export_names, hdr);
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
