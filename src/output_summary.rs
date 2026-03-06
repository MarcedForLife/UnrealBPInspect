use std::collections::{HashMap, HashSet};

use crate::types::*;
use crate::resolve::*;
use crate::bytecode::{BcStatement, reorder_flow_patterns, structure_bytecode};

pub fn print_summary(asset: &ParsedAsset, filters: &[String]) {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

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

    println!("Blueprint: {} (extends {})", bp_name, short_class(&bp_parent));
    println!();

    // Components from SCS_Node exports
    let mut scs_nodes: HashMap<String, (String, String, Vec<String>)> = HashMap::new();
    let mut components: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".SCS_Node") { continue; }
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
                PropValue::Object(idx) => Some(short_class(&resolve_index(&asset.imports, &export_names, *idx))),
                _ => None,
            })
            .unwrap_or_else(|| "?".into());
        let children = find_prop(props, "ChildNodes")
            .and_then(|p| match &p.value {
                PropValue::Array { items, .. } => Some(items.iter().filter_map(|i| match i {
                    PropValue::Object(idx) => Some(resolve_index(&asset.imports, &export_names, *idx)),
                    _ => None,
                }).collect()),
                _ => None,
            })
            .unwrap_or_default();
        components.push((comp_name.clone(), comp_class.clone()));
        scs_nodes.insert(hdr.object_name.clone(), (comp_name, comp_class, children));
    }

    let all_children: Vec<String> = scs_nodes.values()
        .flat_map(|(_, _, children)| children.iter().cloned())
        .collect();
    let root_nodes: Vec<String> = scs_nodes.keys()
        .filter(|k| !all_children.contains(k))
        .cloned()
        .collect();

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
        "StaticMeshImportVersion", "bVisualizeComponent",
        "CreationMethod",
    ];

    fn print_comp_props(
        name: &str, class: &str, depth: usize,
        comp_props: &HashMap<String, &[Property]>,
        cat_exports: &HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry], export_names: &[String],
    ) {
        let indent = "  ".repeat(depth + 1);
        let prop_indent = "  ".repeat(depth + 2);
        println!("{}{} ({})", indent, name, class);
        if let Some(props) = comp_props.get(name) {
            let mut child_actor_tpl: Option<String> = None;
            for prop in *props {
                if COMP_SKIP_PROPS.contains(&prop.name.as_str()) { continue; }
                if prop.name == "ChildActorTemplate" {
                    if let PropValue::Object(idx) = &prop.value {
                        let tpl_name = resolve_index(imports, export_names, *idx);
                        child_actor_tpl = Some(tpl_name);
                    }
                    continue;
                }
                if let PropValue::Struct { struct_type, fields } = &prop.value {
                    match struct_type.as_str() {
                        "Vector" | "Rotator" => {
                            let val = prop_value_short(&prop.value, imports, export_names);
                            println!("{}{}: {}", prop_indent, prop.name, val);
                        }
                        _ => {
                            let summary: Vec<String> = fields.iter().filter_map(|f| {
                                match &f.value {
                                    PropValue::Struct { .. } | PropValue::Array { .. } | PropValue::Map { .. } => None,
                                    _ => {
                                        let v = prop_value_short(&f.value, imports, export_names);
                                        Some(format!("{}: {}", f.name, v))
                                    }
                                }
                            }).collect();
                            if !summary.is_empty() {
                                println!("{}{}: {}", prop_indent, prop.name, summary.join(", "));
                            }
                        }
                    }
                    continue;
                }
                let val = prop_value_short(&prop.value, imports, export_names);
                println!("{}{}: {}", prop_indent, prop.name, val);
            }
            if let Some(tpl_name) = child_actor_tpl {
                if let Some((tpl_class, tpl_props)) = cat_exports.get(&tpl_name) {
                    println!("{}[template: {}]", prop_indent, tpl_class);
                    for prop in *tpl_props {
                        if let PropValue::Struct { struct_type, fields } = &prop.value {
                            match struct_type.as_str() {
                                "Vector" | "Rotator" => {
                                    let val = prop_value_short(&prop.value, imports, export_names);
                                    println!("{}  {}: {}", prop_indent, prop.name, val);
                                }
                                _ => {
                                    let summary: Vec<String> = fields.iter().filter_map(|f| {
                                        match &f.value {
                                            PropValue::Struct { .. } | PropValue::Array { .. } | PropValue::Map { .. } => None,
                                            _ => {
                                                let v = prop_value_short(&f.value, imports, export_names);
                                                Some(format!("{}: {}", f.name, v))
                                            }
                                        }
                                    }).collect();
                                    if !summary.is_empty() {
                                        println!("{}  {}: {}", prop_indent, prop.name, summary.join(", "));
                                    }
                                }
                            }
                            continue;
                        }
                        let val = prop_value_short(&prop.value, imports, export_names);
                        println!("{}  {}: {}", prop_indent, prop.name, val);
                    }
                }
            }
        }
    }

    fn print_comp_tree(
        node_name: &str, depth: usize,
        scs_nodes: &HashMap<String, (String, String, Vec<String>)>,
        comp_props: &HashMap<String, &[Property]>,
        cat_exports: &HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry], export_names: &[String],
    ) {
        if let Some((comp_name, comp_class, children)) = scs_nodes.get(node_name) {
            print_comp_props(comp_name, comp_class, depth, comp_props, cat_exports, imports, export_names);
            for child in children {
                print_comp_tree(child, depth + 1, scs_nodes, comp_props, cat_exports, imports, export_names);
            }
        }
    }

    if !components.is_empty() {
        println!("Components:");
        for root in &root_nodes {
            print_comp_tree(root, 0, &scs_nodes, &comp_props, &cat_exports, &asset.imports, &export_names);
        }
        println!();
    }

    // Member variables
    let mut members: Vec<String> = Vec::new();
    let component_names: Vec<&str> = components.iter().map(|(n, _)| n.as_str()).collect();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".BlueprintGeneratedClass") { continue; }
        if let Some(members_prop) = find_prop(props, "Members") {
            if let PropValue::Array { items, .. } = &members_prop.value {
                for item in items {
                    if let PropValue::Str(decl) = item {
                        let var_name = decl.split(':').next().unwrap_or("");
                        if component_names.contains(&var_name) { continue; }
                        if var_name == "UberGraphFrame" { continue; }
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
                if matches!(prop.name.as_str(), "ActorLabel" | "bCanProxyPhysics") { continue; }
                let val_str = prop_value_short(&prop.value, &asset.imports, &export_names);
                defaults.push((prop.name.clone(), val_str));
            }
        }
    }

    if !members.is_empty() {
        println!("Variables:");
        for decl in &members {
            let var_name = decl.split(':').next().unwrap_or("");
            if let Some((_, val)) = defaults.iter().find(|(n, _)| n == var_name) {
                println!("  {} = {}", decl, val);
            } else {
                println!("  {}", decl);
            }
        }
        println!();
    } else if !defaults.is_empty() {
        println!("Default values:");
        for (name, val) in &defaults {
            println!("  {} = {}", name, val);
        }
        println!();
    }

    // Ubergraph entry points
    let ubergraph_name: Option<String> = asset.exports.iter()
        .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))
        .map(|(hdr, _)| hdr.object_name.clone());
    let ubergraph_labels: HashMap<usize, String> = if let Some(ref ug_name) = ubergraph_name {
        let mut labels = HashMap::new();
        let call_prefix = format!("{}(", ug_name);
        for (hdr, props) in &asset.exports {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            if !class.ends_with(".Function") { continue; }
            if hdr.object_name.starts_with("ExecuteUbergraph_") { continue; }
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
                if !labels.is_empty() { break; }
            }
        }
        labels
    } else {
        HashMap::new()
    };

    // Functions with signatures and bytecode
    let mut has_functions = false;
    let mut functions_with_bytecode: HashSet<String> = HashSet::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".Function") { continue; }
        if !matches_filter(&hdr.object_name, filters) { continue; }

        // Skip stub dispatchers when ubergraph bytecode is present
        if ubergraph_name.is_some() && !hdr.object_name.starts_with("ExecuteUbergraph_") {
            if is_ubergraph_stub(props, ubergraph_name.as_deref().unwrap_or("")) {
                continue;
            }
        }

        let sig = find_prop_str(props, "Signature")
            .unwrap_or_else(|| format!("{}()", hdr.object_name));
        let flags = find_prop_str(props, "FunctionFlags")
            .map(|f| filter_flags_for_summary(&f))
            .and_then(|f| if f.is_empty() { None } else { Some(format!(" [{}]", f)) })
            .unwrap_or_default();

        if !has_functions {
            println!("Functions:");
            has_functions = true;
        }
        println!("  {}{}", sig, flags);

        if hdr.object_name.starts_with("ExecuteUbergraph_") && !ubergraph_labels.is_empty() {
            if let Some(bc_prop) = find_prop(props, "Bytecode") {
                if let PropValue::Array { items, .. } = &bc_prop.value {
                    let stmts: Vec<BcStatement> = items.iter().filter_map(|item| {
                        if let PropValue::Str(line) = item {
                            if line.len() > 6 && line.as_bytes()[4] == b':' {
                                let offset = usize::from_str_radix(&line[..4], 16).ok()?;
                                Some(BcStatement { mem_offset: offset, text: line[6..].to_string() })
                            } else { None }
                        } else { None }
                    }).collect();
                    let reordered = reorder_flow_patterns(&stmts);
                    let structured = structure_bytecode(&reordered, &ubergraph_labels);
                    for line in &structured {
                        println!("    {}", line);
                    }
                    if !stmts.is_empty() {
                        functions_with_bytecode.insert(hdr.object_name.clone());
                    }
                }
            }
        } else {
            let bc_prop_name = if find_prop(props, "BytecodeSummary").is_some() {
                "BytecodeSummary"
            } else {
                "Bytecode"
            };
            if let Some(bc_prop) = find_prop(props, bc_prop_name) {
                if let PropValue::Array { items, .. } = &bc_prop.value {
                    let has_bytecode = !items.is_empty();
                    for item in items {
                        if let PropValue::Str(line) = item {
                            if bc_prop_name == "Bytecode" {
                                let code = if line.len() > 6 && line.as_bytes()[4] == b':' {
                                    &line[6..]
                                } else {
                                    line
                                };
                                println!("    {}", code);
                            } else {
                                println!("    {}", line);
                            }
                        }
                    }
                    if has_bytecode {
                        functions_with_bytecode.insert(hdr.object_name.clone());
                    }
                }
            }
        }
    }
    if has_functions { println!(); }

    // Graphs
    let mut func_flags: HashMap<String, String> = HashMap::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if class.ends_with(".Function") {
            if let Some(flags) = find_prop_str(props, "FunctionFlags") {
                func_flags.insert(hdr.object_name.clone(), flags);
            }
        }
    }

    let has_ubergraph_bytecode = functions_with_bytecode.iter().any(|f| f.starts_with("ExecuteUbergraph_"));
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".EdGraph") { continue; }
        if !matches_filter(&hdr.object_name, filters) { continue; }
        if functions_with_bytecode.contains(&hdr.object_name) { continue; }
        if hdr.object_name == "EventGraph" && has_ubergraph_bytecode { continue; }
        let graph_name = &hdr.object_name;

        let node_indices: Vec<i32> = find_prop(props, "Nodes")
            .or_else(|| find_prop(props, "AllNodes"))
            .map(|p| match &p.value {
                PropValue::Array { items, .. } => items.iter().filter_map(|item| {
                    if let PropValue::Object(idx) = item { Some(*idx) } else { None }
                }).collect(),
                _ => Vec::new(),
            })
            .unwrap_or_default();

        if node_indices.is_empty() { continue; }

        let flags = func_flags.get(graph_name.as_str())
            .map(|f| filter_flags_for_summary(f))
            .and_then(|f| if f.is_empty() { None } else { Some(format!(" [{}]", f)) })
            .unwrap_or_default();
        println!("Graph: {}{}", graph_name, flags);

        let mut nodes: Vec<(i32, String)> = Vec::new();
        for idx in &node_indices {
            if *idx > 0 {
                let export_idx = (*idx - 1) as usize;
                if let Some((hdr, node_props)) = asset.exports.get(export_idx) {
                    let node_class = resolve_index(&asset.imports, &export_names, hdr.class_index);
                    let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                    let summary = summarise_node(&node_class, node_props, &asset.imports, &export_names);
                    nodes.push((x, summary));
                }
            }
        }
        nodes.sort_by_key(|(x, _)| *x);
        for (_, desc) in &nodes {
            println!("  {}", desc);
        }
        println!();
    }
}

fn summarise_node(class: &str, props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    let short = short_class(class);
    match short.as_str() {
        "K2Node_CallFunction" => {
            let func = get_member_ref(props, imports, export_names);
            let pure = find_prop(props, "bIsPureFunc").is_some_and(|p| matches!(p.value, PropValue::Bool(true)));
            if pure { format!("[pure] {}", func) } else { format!("Call {}", func) }
        }
        "K2Node_CommutativeAssociativeBinaryOperator" => {
            let func = get_member_ref(props, imports, export_names);
            format!("[pure] {}", func)
        }
        "K2Node_FunctionEntry" => {
            let name = get_member_name(props);
            format!("Entry: {}", name)
        }
        "K2Node_FunctionResult" => {
            let name = get_member_name(props);
            format!("Return: {}", name)
        }
        "K2Node_VariableGet" => {
            let var = get_var_ref(props, imports, export_names);
            format!("Get {}", var)
        }
        "K2Node_VariableSet" => {
            let var = get_var_ref(props, imports, export_names);
            format!("Set {}", var)
        }
        "K2Node_DynamicCast" => {
            let target = find_prop(props, "TargetType")
                .map(|p| match &p.value {
                    PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                    _ => "?".into(),
                })
                .unwrap_or_else(|| "?".into());
            format!("Cast to {}", target)
        }
        "K2Node_Event" => {
            let name = get_event_name(props);
            format!("Event: {}", name)
        }
        "K2Node_CustomEvent" => {
            let name = find_prop_str(props, "CustomFunctionName")
                .or_else(|| get_event_name_opt(props))
                .unwrap_or_else(|| "?".into());
            format!("Event: {}", name)
        }
        "K2Node_IfThenElse" => "Branch".into(),
        "K2Node_MacroInstance" => {
            let name = get_macro_name(props, imports, export_names);
            format!("Macro: {}", name)
        }
        _ => short.to_string(),
    }
}

fn get_member_ref(props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    find_prop(props, "FunctionReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => {
                let parent = find_prop(fields, "MemberParent")
                    .map(|mp| match &mp.value {
                        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                let name = find_prop_str(fields, "MemberName").unwrap_or_else(|| "?".into());
                if parent.is_empty() { Some(name) } else { Some(format!("{}::{}", parent, name)) }
            }
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}

fn get_member_name(props: &[Property]) -> String {
    find_prop(props, "FunctionReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => find_prop_str(fields, "MemberName"),
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}

fn get_event_name(props: &[Property]) -> String {
    get_event_name_opt(props).unwrap_or_else(|| "?".into())
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

fn get_macro_name(props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    // MacroGraphReference.MacroGraph — can be object ref or string path
    if let Some(p) = find_prop(props, "MacroGraphReference") {
        if let PropValue::Struct { fields, .. } = &p.value {
            if let Some(mg) = find_prop(fields, "MacroGraph") {
                match &mg.value {
                    PropValue::Object(idx) => {
                        return short_class(&resolve_index(imports, export_names, *idx));
                    }
                    PropValue::Str(path) | PropValue::Name(path) => {
                        return short_class(path);
                    }
                    _ => {}
                }
            }
        }
    }
    get_member_name(props)
}

fn filter_flags_for_summary(flags: &str) -> String {
    const NOISE: &[&str] = &["BlueprintCallable"];
    flags.split('|')
        .filter(|f| !NOISE.contains(&f.trim()))
        .collect::<Vec<_>>()
        .join("|")
}

/// Check if a function is a stub that just dispatches to the ubergraph.
/// Stubs contain only an ExecuteUbergraph_X(N) call, plus optional return/persistent-frame lines.
fn is_ubergraph_stub(props: &[Property], ug_name: &str) -> bool {
    let bc_prop = find_prop(props, "BytecodeSummary")
        .or_else(|| find_prop(props, "Bytecode"));
    let items = match bc_prop {
        Some(Property { value: PropValue::Array { items, .. }, .. }) => items,
        _ => return false,
    };
    let meaningful: Vec<&str> = items.iter().filter_map(|item| {
        if let PropValue::Str(line) = item {
            // Strip hex offset prefix (e.g. "0000: ")
            let code = if line.len() > 6 && line.as_bytes()[4] == b':' {
                line[6..].trim()
            } else {
                line.trim()
            };
            match code {
                "" | "return" | "return nop" => None,
                _ => Some(code),
            }
        } else {
            None
        }
    }).collect();
    if meaningful.is_empty() || meaningful.len() > 2 { return false; }
    meaningful.iter().any(|line| line.starts_with(&format!("{}(", ug_name)))
        && meaningful.iter().all(|line| {
            line.starts_with(&format!("{}(", ug_name))
                || line.contains("[persistent]")
        })
}

fn get_var_ref(props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    find_prop(props, "VariableReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => {
                let parent = find_prop(fields, "MemberParent")
                    .map(|mp| match &mp.value {
                        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                let name = find_prop_str(fields, "MemberName").unwrap_or_else(|| "?".into());
                let is_self = find_prop(fields, "bSelfContext")
                    .is_some_and(|p| matches!(p.value, PropValue::Bool(true)));
                if is_self { Some(format!("self.{}", name)) }
                else if parent.is_empty() { Some(name) }
                else { Some(format!("{}.{}", parent, name)) }
            }
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}
