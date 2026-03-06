use crate::types::*;
use crate::resolve::*;

pub fn print_text(asset: &ParsedAsset, filters: &[String]) {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

    println!("=== Blueprint Dump ===\n");

    println!("--- Imports ({}) ---", asset.imports.len());
    for (i, imp) in asset.imports.iter().enumerate() {
        let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
        println!("  [{}] {} ({}::{})", i, full_path, imp.class_package, imp.class_name);
    }

    println!("\n--- Exports ({}) ---", asset.exports.len());
    for (i, (hdr, props)) in asset.exports.iter().enumerate() {
        if !matches_filter(&hdr.object_name, filters) { continue; }
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        let parent = resolve_index(&asset.imports, &export_names, hdr.super_index);
        if parent != "None" {
            println!("\n  [{}] {} (class: {}, parent: {})", i + 1, hdr.object_name, class, parent);
        } else {
            println!("\n  [{}] {} (class: {})", i + 1, hdr.object_name, class);
        }
        for prop in props {
            print_property(prop, &asset.imports, &export_names, 4);
        }
    }
}

fn print_property(prop: &Property, imports: &[ImportEntry], export_names: &[String], indent: usize) {
    let pad = " ".repeat(indent);
    match &prop.value {
        PropValue::Bool(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Int(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Int64(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Float(v) => println!("{}{}: {:.4}", pad, prop.name, v),
        PropValue::Double(v) => println!("{}{}: {:.4}", pad, prop.name, v),
        PropValue::Str(v) => println!("{}{}: \"{}\"", pad, prop.name, v),
        PropValue::Name(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Object(idx) => {
            let target = resolve_index(imports, export_names, *idx);
            println!("{}{}: -> {}", pad, prop.name, target);
        }
        PropValue::Enum { enum_type, value } => {
            println!("{}{}: {} ({})", pad, prop.name, value, enum_type);
        }
        PropValue::Byte { enum_name, value } => {
            if enum_name == "None" {
                println!("{}{}: {}", pad, prop.name, value);
            } else {
                println!("{}{}: {} ({})", pad, prop.name, value, enum_name);
            }
        }
        PropValue::Struct { struct_type, fields } => {
            if fields.is_empty() {
                println!("{}{}: ({}) {{}}", pad, prop.name, struct_type);
            } else {
                println!("{}{}: ({}) {{", pad, prop.name, struct_type);
                for f in fields {
                    print_property(f, imports, export_names, indent + 2);
                }
                println!("{}}}", pad);
            }
        }
        PropValue::Array { inner_type, items } => {
            println!("{}{}: [{}; {} items]", pad, prop.name, inner_type, items.len());
            for (j, item) in items.iter().enumerate() {
                let child = Property { name: format!("[{}]", j), value: item.clone() };
                print_property(&child, imports, export_names, indent + 2);
            }
        }
        PropValue::Map { key_type, value_type, entries } => {
            println!("{}{}: {{{}->{}; {} entries}}", pad, prop.name, key_type, value_type, entries.len());
            for (j, (k, v)) in entries.iter().enumerate() {
                let kp = Property { name: format!("[{}].key", j), value: k.clone() };
                let vp = Property { name: format!("[{}].val", j), value: v.clone() };
                print_property(&kp, imports, export_names, indent + 2);
                print_property(&vp, imports, export_names, indent + 2);
            }
        }
        PropValue::Text(v) => println!("{}{}: \"{}\"", pad, prop.name, v),
        PropValue::SoftObject(v) => println!("{}{}: ~{}", pad, prop.name, v),
        PropValue::Unknown { type_name, size } => {
            println!("{}{}: <{}, {} bytes>", pad, prop.name, type_name, size);
        }
    }
}
