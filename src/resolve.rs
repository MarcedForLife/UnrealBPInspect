use crate::types::*;

pub fn resolve_import_path(imports: &[ImportEntry], index: i32) -> String {
    if index >= 0 {
        return "?".to_string();
    }
    let idx = (-index - 1) as usize;
    let imp = match imports.get(idx) {
        Some(i) => i,
        None => return "?".to_string(),
    };
    if imp.outer_index == 0 {
        imp.object_name.clone()
    } else {
        let outer = resolve_import_path(imports, imp.outer_index);
        format!("{}.{}", outer, imp.object_name)
    }
}

pub fn resolve_index(imports: &[ImportEntry], export_names: &[String], index: i32) -> String {
    if index < 0 {
        resolve_import_path(imports, index)
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names.get(idx).cloned().unwrap_or_else(|| format!("Export({})", index))
    } else {
        "None".to_string()
    }
}

pub fn short_class(full: &str) -> String {
    full.rsplit('.').next().unwrap_or(full).to_string()
}

pub fn matches_filter(name: &str, filters: &[String]) -> bool {
    if filters.is_empty() { return true; }
    let lower = name.to_lowercase();
    filters.iter().any(|f| lower.contains(f))
}

pub fn find_prop<'a>(props: &'a [Property], name: &str) -> Option<&'a Property> {
    props.iter().find(|p| p.name == name)
}

pub fn find_prop_str(props: &[Property], name: &str) -> Option<String> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Str(s) => Some(s.clone()),
        PropValue::Name(s) => Some(s.clone()),
        _ => None,
    })
}

pub fn find_prop_i32(props: &[Property], name: &str) -> Option<i32> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Int(v) => Some(*v),
        _ => None,
    })
}

pub fn prop_value_short(val: &PropValue, imports: &[ImportEntry], export_names: &[String]) -> String {
    match val {
        PropValue::Bool(v) => v.to_string(),
        PropValue::Int(v) => v.to_string(),
        PropValue::Int64(v) => v.to_string(),
        PropValue::Float(v) => format!("{:.4}", v),
        PropValue::Double(v) => format!("{:.4}", v),
        PropValue::Str(v) => format!("\"{}\"", v),
        PropValue::Name(v) => v.clone(),
        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
        PropValue::Enum { value, .. } => value.clone(),
        PropValue::Byte { value, .. } => value.clone(),
        PropValue::Array { items, .. } => format!("[{} items]", items.len()),
        PropValue::Map { entries, .. } => format!("{{{} entries}}", entries.len()),
        PropValue::Struct { struct_type, fields } => {
            match struct_type.as_str() {
                "Vector" | "Rotator" => {
                    let parts: Vec<String> = fields.iter()
                        .map(|f| prop_value_short(&f.value, imports, export_names))
                        .collect();
                    format!("({})", parts.join(", "))
                }
                _ => format!("{} {{...}}", struct_type),
            }
        }
        _ => "...".into(),
    }
}

pub fn format_func_flags(flags: u32) -> String {
    let mut parts = Vec::new();
    if flags & 0x00000001 != 0 { parts.push("Final"); }
    if flags & 0x00000400 != 0 { parts.push("Native"); }
    if flags & 0x00000800 != 0 { parts.push("Event"); }
    if flags & 0x00002000 != 0 { parts.push("Static"); }
    if flags & 0x00004000 != 0 { parts.push("MulticastDelegate"); }
    if flags & 0x00020000 != 0 { parts.push("Public"); }
    if flags & 0x00040000 != 0 { parts.push("Private"); }
    if flags & 0x00080000 != 0 { parts.push("Protected"); }
    if flags & 0x00100000 != 0 { parts.push("Delegate"); }
    if flags & 0x00400000 != 0 { parts.push("HasOutParms"); }
    if flags & 0x01000000 != 0 { parts.push("BlueprintCallable"); }
    if flags & 0x02000000 != 0 { parts.push("BlueprintEvent"); }
    if flags & 0x04000000 != 0 { parts.push("BlueprintPure"); }
    if flags & 0x10000000 != 0 { parts.push("Const"); }
    if flags & 0x40000000 != 0 { parts.push("HasDefaults"); }
    if parts.is_empty() { format!("0x{:08x}", flags) } else { parts.join("|") }
}
