//! Full dump output mode (`--dump`).

use std::fmt::Write;

use crate::resolve::*;
use crate::types::*;

/// Format a parsed asset as a verbose text dump. Filters restrict to matching export names.
pub fn format_text(asset: &ParsedAsset, filters: &[String]) -> String {
    let mut buf = String::new();
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();

    writeln!(buf, "=== Blueprint Dump ===\n").unwrap();

    writeln!(buf, "--- Imports ({}) ---", asset.imports.len()).unwrap();
    for (i, imp) in asset.imports.iter().enumerate() {
        let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
        writeln!(
            buf,
            "  [{}] {} ({}::{})",
            i, full_path, imp.class_package, imp.class_name
        )
        .unwrap();
    }

    writeln!(buf, "\n--- Exports ({}) ---", asset.exports.len()).unwrap();
    for (i, (hdr, props)) in asset.exports.iter().enumerate() {
        if !matches_filter(&hdr.object_name, filters) {
            continue;
        }
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        let parent = resolve_index(&asset.imports, &export_names, hdr.super_index);
        if parent != "None" {
            writeln!(
                buf,
                "\n  [{}] {} (class: {}, parent: {})",
                i + 1,
                hdr.object_name,
                class,
                parent
            )
            .unwrap();
        } else {
            writeln!(
                buf,
                "\n  [{}] {} (class: {})",
                i + 1,
                hdr.object_name,
                class
            )
            .unwrap();
        }
        for prop in props {
            format_property(&mut buf, prop, &asset.imports, &export_names, 4);
        }
    }
    buf
}

pub fn print_text(asset: &ParsedAsset, filters: &[String]) {
    print!("{}", format_text(asset, filters));
}

fn format_property(
    buf: &mut String,
    prop: &Property,
    imports: &[ImportEntry],
    export_names: &[String],
    indent: usize,
) {
    let pad = " ".repeat(indent);
    match &prop.value {
        PropValue::Bool(v) => writeln!(buf, "{}{}: {}", pad, prop.name, v).unwrap(),
        PropValue::Int(v) => writeln!(buf, "{}{}: {}", pad, prop.name, v).unwrap(),
        PropValue::Int64(v) => writeln!(buf, "{}{}: {}", pad, prop.name, v).unwrap(),
        PropValue::Float(v) => writeln!(buf, "{}{}: {:.4}", pad, prop.name, v).unwrap(),
        PropValue::Double(v) => writeln!(buf, "{}{}: {:.4}", pad, prop.name, v).unwrap(),
        PropValue::Str(v) => writeln!(buf, "{}{}: \"{}\"", pad, prop.name, v).unwrap(),
        PropValue::Name(v) => writeln!(buf, "{}{}: {}", pad, prop.name, v).unwrap(),
        PropValue::Object(idx) => {
            let target = resolve_index(imports, export_names, *idx);
            writeln!(buf, "{}{}: -> {}", pad, prop.name, target).unwrap();
        }
        PropValue::Enum { enum_type, value } => {
            writeln!(buf, "{}{}: {} ({})", pad, prop.name, value, enum_type).unwrap();
        }
        PropValue::Byte { enum_name, value } => {
            if enum_name == "None" {
                writeln!(buf, "{}{}: {}", pad, prop.name, value).unwrap();
            } else {
                writeln!(buf, "{}{}: {} ({})", pad, prop.name, value, enum_name).unwrap();
            }
        }
        PropValue::Struct {
            struct_type,
            fields,
        } => {
            if fields.is_empty() {
                writeln!(buf, "{}{}: ({}) {{}}", pad, prop.name, struct_type).unwrap();
            } else {
                writeln!(buf, "{}{}: ({}) {{", pad, prop.name, struct_type).unwrap();
                for f in fields {
                    format_property(buf, f, imports, export_names, indent + 2);
                }
                writeln!(buf, "{}}}", pad).unwrap();
            }
        }
        PropValue::Array { inner_type, items } => {
            writeln!(
                buf,
                "{}{}: [{}; {} items]",
                pad,
                prop.name,
                inner_type,
                items.len()
            )
            .unwrap();
            for (j, item) in items.iter().enumerate() {
                let child = Property {
                    name: format!("[{}]", j),
                    value: item.clone(),
                };
                format_property(buf, &child, imports, export_names, indent + 2);
            }
        }
        PropValue::Map {
            key_type,
            value_type,
            entries,
        } => {
            writeln!(
                buf,
                "{}{}: {{{}->{}; {} entries}}",
                pad,
                prop.name,
                key_type,
                value_type,
                entries.len()
            )
            .unwrap();
            for (j, (k, v)) in entries.iter().enumerate() {
                let key_prop = Property {
                    name: format!("[{}].key", j),
                    value: k.clone(),
                };
                let val_prop = Property {
                    name: format!("[{}].val", j),
                    value: v.clone(),
                };
                format_property(buf, &key_prop, imports, export_names, indent + 2);
                format_property(buf, &val_prop, imports, export_names, indent + 2);
            }
        }
        PropValue::Text(v) => writeln!(buf, "{}{}: \"{}\"", pad, prop.name, v).unwrap(),
        PropValue::SoftObject(v) => writeln!(buf, "{}{}: ~{}", pad, prop.name, v).unwrap(),
        PropValue::Unknown { type_name, size } => {
            writeln!(buf, "{}{}: <{}, {} bytes>", pad, prop.name, type_name, size).unwrap();
        }
    }
}
