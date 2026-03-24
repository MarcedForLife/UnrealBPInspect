//! JSON output mode (`--json`). Must always produce valid JSON.

use serde_json::{json, Value};

use crate::resolve::*;
use crate::types::*;

/// Convert a parsed asset to a JSON value. Filters restrict to matching export names.
pub fn to_json(asset: &ParsedAsset, filters: &[String]) -> Value {
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();

    let imports_json: Vec<Value> = asset
        .imports
        .iter()
        .enumerate()
        .map(|(i, imp)| {
            let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
            json!({
                "index": i,
                "name": imp.object_name,
                "path": full_path,
                "class_package": imp.class_package,
                "class_name": imp.class_name,
            })
        })
        .collect();

    let exports_json: Vec<Value> = asset
        .exports
        .iter()
        .enumerate()
        .filter(|(_, (hdr, _))| matches_filter(&hdr.object_name, filters))
        .map(|(i, (hdr, props))| export_to_json(i, hdr, props, &asset.imports, &export_names))
        .collect();

    let functions_json: Vec<Value> = asset
        .exports
        .iter()
        .enumerate()
        .filter(|(_, (hdr, _))| {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            class.ends_with(".Function") && matches_filter(&hdr.object_name, filters)
        })
        .map(|(i, (hdr, props))| function_to_json(i, hdr, props))
        .collect();

    json!({
        "imports": imports_json,
        "exports": exports_json,
        "functions": functions_json,
    })
}

/// Build JSON for a single export entry.
fn export_to_json(
    index: usize,
    hdr: &ExportHeader,
    props: &[Property],
    imports: &[ImportEntry],
    export_names: &[String],
) -> Value {
    let class = resolve_index(imports, export_names, hdr.class_index);
    let parent = resolve_index(imports, export_names, hdr.super_index);
    let mut exp = json!({
        "index": index + 1,
        "name": hdr.object_name,
        "class": class,
    });
    if parent != "None" {
        exp["parent"] = json!(parent);
    }
    if !props.is_empty() {
        exp["properties"] = Value::Array(
            props
                .iter()
                .map(|p| prop_to_json(p, imports, export_names))
                .collect(),
        );
    }
    exp
}

/// Build JSON for a single function export.
fn function_to_json(index: usize, hdr: &ExportHeader, props: &[Property]) -> Value {
    let sig = find_prop_str(props, "Signature").unwrap_or_else(|| format!("{}()", hdr.object_name));
    let flags = find_prop_str(props, "FunctionFlags").unwrap_or_default();
    let bytecode = find_prop(props, "BytecodeSummary")
        .or_else(|| find_prop(props, "Bytecode"))
        .and_then(|p| match &p.value {
            PropValue::Array { items, .. } => Some(
                items
                    .iter()
                    .filter_map(|item| match item {
                        PropValue::Str(s) => Some(json!(s)),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        })
        .unwrap_or_default();
    json!({
        "name": hdr.object_name,
        "signature": sig,
        "flags": flags,
        "bytecode": bytecode,
        "export_index": index + 1,
    })
}

fn value_to_json(value: &PropValue, imports: &[ImportEntry], export_names: &[String]) -> Value {
    match value {
        PropValue::Bool(v) => json!(v),
        PropValue::Int(v) => json!(v),
        PropValue::Int64(v) => json!(v),
        PropValue::Float(v) => json!(v),
        PropValue::Double(v) => json!(v),
        PropValue::Str(v) => json!(v),
        PropValue::Name(v) => json!(v),
        PropValue::Object(idx) => json!(resolve_index(imports, export_names, *idx)),
        PropValue::Enum { value, .. } => json!(value),
        PropValue::Byte { value, .. } => json!(value),
        PropValue::Struct {
            struct_type,
            fields,
        } => json!({
            "type": struct_type,
            "fields": fields.iter().map(|f| prop_to_json(f, imports, export_names)).collect::<Vec<_>>(),
        }),
        PropValue::Array { inner_type, items } => json!({
            "inner_type": inner_type,
            "items": items.iter().map(|item| value_to_json(item, imports, export_names)).collect::<Vec<_>>(),
        }),
        PropValue::Map {
            key_type,
            value_type,
            entries,
        } => json!({
            "key_type": key_type,
            "value_type": value_type,
            "entries": entries.iter().map(|(k, v)| json!({
                "key": value_to_json(k, imports, export_names),
                "value": value_to_json(v, imports, export_names),
            })).collect::<Vec<_>>(),
        }),
        PropValue::Text(v) => json!(v),
        PropValue::SoftObject(v) => json!(v),
        PropValue::Unknown { type_name, size } => json!({"unknown_type": type_name, "size": size}),
    }
}

fn prop_to_json(prop: &Property, imports: &[ImportEntry], export_names: &[String]) -> Value {
    json!({ "name": prop.name, "value": value_to_json(&prop.value, imports, export_names) })
}
