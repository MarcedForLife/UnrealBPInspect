//! Full dump output mode (`--dump`).

use std::fmt::Write;

use crate::resolve::{class_of, matches_filter, resolve_import_path, resolve_index};
use crate::types::*;

/// Read-only import/name tables threaded through the recursive value formatters.
struct TextDumpCtx<'a> {
    imports: &'a [ImportEntry],
    export_names: &'a [String],
}

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
        let class = class_of(&asset.imports, &export_names, hdr);
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
        let ctx = TextDumpCtx {
            imports: &asset.imports,
            export_names: &export_names,
        };
        for prop in props {
            format_value(&mut buf, &prop.name, &prop.value, &ctx, 4);
        }
    }
    buf
}
fn format_value(buf: &mut String, name: &str, value: &PropValue, ctx: &TextDumpCtx, indent: usize) {
    let pad = " ".repeat(indent);
    match value {
        PropValue::Bool(v) => writeln!(buf, "{}{}: {}", pad, name, v).unwrap(),
        PropValue::Int(v) => writeln!(buf, "{}{}: {}", pad, name, v).unwrap(),
        PropValue::Int64(v) => writeln!(buf, "{}{}: {}", pad, name, v).unwrap(),
        PropValue::Float(v) => writeln!(buf, "{}{}: {:.4}", pad, name, v).unwrap(),
        PropValue::Double(v) => writeln!(buf, "{}{}: {:.4}", pad, name, v).unwrap(),
        PropValue::Str(v) => writeln!(buf, "{}{}: \"{}\"", pad, name, v).unwrap(),
        PropValue::Name(v) => writeln!(buf, "{}{}: {}", pad, name, v).unwrap(),
        PropValue::Object(idx) => {
            let target = resolve_index(ctx.imports, ctx.export_names, *idx);
            writeln!(buf, "{}{}: -> {}", pad, name, target).unwrap();
        }
        PropValue::Enum { enum_name, value } => {
            writeln!(buf, "{}{}: {} ({})", pad, name, value, enum_name).unwrap();
        }
        PropValue::Byte { enum_name, value } => {
            if enum_name == "None" {
                writeln!(buf, "{}{}: {}", pad, name, value).unwrap();
            } else {
                writeln!(buf, "{}{}: {} ({})", pad, name, value, enum_name).unwrap();
            }
        }
        PropValue::Struct {
            struct_type,
            fields,
        } => format_struct(buf, name, struct_type, fields, ctx, indent),
        PropValue::Array { inner_type, items } => {
            format_array(buf, name, inner_type, items, ctx, indent)
        }
        PropValue::Map {
            key_type,
            value_type,
            entries,
        } => format_map(buf, name, key_type, value_type, entries, ctx, indent),
        PropValue::Text(v) => writeln!(buf, "{}{}: \"{}\"", pad, name, v).unwrap(),
        PropValue::SoftObject(v) => writeln!(buf, "{}{}: ~{}", pad, name, v).unwrap(),
        PropValue::Unknown { type_name, size } => {
            writeln!(buf, "{}{}: <{}, {} bytes>", pad, name, type_name, size).unwrap();
        }
    }
}

fn format_struct(
    buf: &mut String,
    name: &str,
    struct_type: &str,
    fields: &[Property],
    ctx: &TextDumpCtx,
    indent: usize,
) {
    let pad = " ".repeat(indent);
    if fields.is_empty() {
        writeln!(buf, "{}{}: ({}) {{}}", pad, name, struct_type).unwrap();
    } else {
        writeln!(buf, "{}{}: ({}) {{", pad, name, struct_type).unwrap();
        for f in fields {
            format_value(buf, &f.name, &f.value, ctx, indent + 2);
        }
        writeln!(buf, "{}}}", pad).unwrap();
    }
}

fn format_array(
    buf: &mut String,
    name: &str,
    inner_type: &str,
    items: &[PropValue],
    ctx: &TextDumpCtx,
    indent: usize,
) {
    let pad = " ".repeat(indent);
    writeln!(
        buf,
        "{}{}: [{}; {} items]",
        pad,
        name,
        inner_type,
        items.len()
    )
    .unwrap();
    for (j, item) in items.iter().enumerate() {
        format_value(buf, &format!("[{}]", j), item, ctx, indent + 2);
    }
}

fn format_map(
    buf: &mut String,
    name: &str,
    key_type: &str,
    value_type: &str,
    entries: &[(PropValue, PropValue)],
    ctx: &TextDumpCtx,
    indent: usize,
) {
    let pad = " ".repeat(indent);
    writeln!(
        buf,
        "{}{}: {{{}->{}; {} entries}}",
        pad,
        name,
        key_type,
        value_type,
        entries.len()
    )
    .unwrap();
    for (j, (k, v)) in entries.iter().enumerate() {
        format_value(buf, &format!("[{}].key", j), k, ctx, indent + 2);
        format_value(buf, &format!("[{}].val", j), v, ctx, indent + 2);
    }
}
