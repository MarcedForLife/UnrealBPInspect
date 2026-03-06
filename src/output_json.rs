use serde_json::{json, Value};

use crate::types::*;
use crate::resolve::*;

pub fn to_json(asset: &ParsedAsset, filters: &[String]) -> Value {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

    json!({
        "imports": asset.imports.iter().enumerate().map(|(i, imp)| {
            let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
            json!({
                "index": i,
                "name": imp.object_name,
                "path": full_path,
                "class_package": imp.class_package,
                "class_name": imp.class_name,
            })
        }).collect::<Vec<_>>(),
        "exports": asset.exports.iter().enumerate().filter(|(_, (hdr, _))| {
            matches_filter(&hdr.object_name, filters)
        }).map(|(i, (hdr, props))| {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            let parent = resolve_index(&asset.imports, &export_names, hdr.super_index);
            let mut exp = json!({
                "index": i + 1,
                "name": hdr.object_name,
                "class": class,
            });
            if parent != "None" {
                exp["parent"] = json!(parent);
            }
            if !props.is_empty() {
                exp["properties"] = Value::Array(
                    props.iter().map(|p| prop_to_json(p, &asset.imports, &export_names)).collect()
                );
            }
            exp
        }).collect::<Vec<_>>(),
    })
}

fn prop_to_json(prop: &Property, imports: &[ImportEntry], export_names: &[String]) -> Value {
    let val = match &prop.value {
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
        PropValue::Struct { struct_type, fields } => json!({
            "type": struct_type,
            "fields": fields.iter().map(|f| prop_to_json(f, imports, export_names)).collect::<Vec<_>>(),
        }),
        PropValue::Array { inner_type, items } => json!({
            "inner_type": inner_type,
            "items": items.iter().map(|item| {
                let child = Property { name: String::new(), value: item.clone() };
                prop_to_json(&child, imports, export_names)["value"].clone()
            }).collect::<Vec<_>>(),
        }),
        PropValue::Map { key_type, value_type, entries } => json!({
            "key_type": key_type,
            "value_type": value_type,
            "entries": entries.iter().map(|(k, v)| {
                let kp = Property { name: String::new(), value: k.clone() };
                let vp = Property { name: String::new(), value: v.clone() };
                json!({
                    "key": prop_to_json(&kp, imports, export_names)["value"],
                    "value": prop_to_json(&vp, imports, export_names)["value"],
                })
            }).collect::<Vec<_>>(),
        }),
        PropValue::Text(v) => json!(v),
        PropValue::SoftObject(v) => json!(v),
        PropValue::Unknown { type_name, size } => json!({"unknown_type": type_name, "size": size}),
    };
    json!({ "name": prop.name, "value": val })
}
