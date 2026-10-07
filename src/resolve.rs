//! Index resolution helpers.
//!
//! Package index convention: negative = import (1-based), positive = export (1-based), zero = null.

use crate::types::*;

/// Guard against circular outer_index references in the import table.
const MAX_IMPORT_DEPTH: usize = 32;

pub fn resolve_import_path(imports: &[ImportEntry], index: i32) -> String {
    resolve_import_path_inner(imports, index, 0)
}

fn resolve_import_path_inner(imports: &[ImportEntry], index: i32, depth: usize) -> String {
    if depth > MAX_IMPORT_DEPTH || index >= 0 {
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
        let outer = resolve_import_path_inner(imports, imp.outer_index, depth + 1);
        format!("{}.{}", outer, imp.object_name)
    }
}

pub fn resolve_index(imports: &[ImportEntry], export_names: &[String], index: i32) -> String {
    if index < 0 {
        resolve_import_path(imports, index)
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names
            .get(idx)
            .cloned()
            .unwrap_or_else(|| format!("Export({})", index))
    } else {
        "None".to_string()
    }
}

/// Resolve an export header's `class_index` to its full class path. Thin
/// wrapper over [`resolve_index`] for the common "what is this export's class"
/// lookup repeated across the output modes.
pub fn class_of(imports: &[ImportEntry], export_names: &[String], hdr: &ExportHeader) -> String {
    resolve_index(imports, export_names, hdr.class_index)
}

pub fn short_class(full: &str) -> String {
    full.rsplit('.').next().unwrap_or(full).to_string()
}

pub fn matches_filter(name: &str, filters: &[String]) -> bool {
    if filters.is_empty() {
        return true;
    }
    let lower = name.to_lowercase();
    filters.iter().any(|f| lower.contains(f))
}

// EFunctionFlags from Unreal's UObject/Script.h.
const FUNC_FLAG_NAMES: &[(u32, &str)] = &[
    (0x00000001, "Final"),
    (0x00000002, "RequiredAPI"),
    (0x00000004, "BlueprintAuthorityOnly"),
    (0x00000008, "BlueprintCosmetic"),
    (0x00000040, "Net"),
    (0x00000080, "NetReliable"),
    (0x00000100, "NetRequest"),
    (0x00000200, "Exec"),
    (0x00000400, "Native"),
    (0x00000800, "Event"),
    (0x00001000, "NetResponse"),
    (0x00002000, "Static"),
    (0x00004000, "NetMulticast"),
    (0x00008000, "UbergraphFunction"),
    (0x00010000, "MulticastDelegate"),
    (0x00020000, "Public"),
    (0x00040000, "Private"),
    (0x00080000, "Protected"),
    (0x00100000, "Delegate"),
    (0x00200000, "NetServer"),
    (0x00400000, "HasOutParms"),
    (0x00800000, "HasDefaults"),
    (0x01000000, "NetClient"),
    (0x02000000, "DLLImport"),
    (0x04000000, "BlueprintCallable"),
    (0x08000000, "BlueprintEvent"),
    (0x10000000, "BlueprintPure"),
    (0x20000000, "EditorOnly"),
    (0x40000000, "Const"),
    (0x80000000, "NetValidate"),
];

pub fn format_func_flags(flags: u32) -> String {
    let parts: Vec<&str> = FUNC_FLAG_NAMES
        .iter()
        .filter(|(mask, _)| flags & mask != 0)
        .map(|(_, name)| *name)
        .collect();
    if parts.is_empty() {
        format!("0x{:08x}", flags)
    } else {
        parts.join("|")
    }
}

/// Walk a node export's `outer_index` chain to the owning `EdGraph` export,
/// whose `object_name` is the graph-page name (a standalone function graph,
/// an ubergraph page like `EventGraph`, or a collapsed graph). Returns `None`
/// when the chain hits a null outer or exceeds the depth guard before
/// reaching an EdGraph ancestor (variables and function exports have none).
pub fn enclosing_graph_name(
    parsed: &ParsedAsset,
    export_names: &[String],
    node_one_based: usize,
) -> Option<String> {
    const MAX_OUTER_DEPTH: usize = 8;
    let mut current = node_one_based as i32;
    for _ in 0..MAX_OUTER_DEPTH {
        let (hdr, _) = parsed.exports.get((current - 1) as usize)?;
        let class = short_class(&resolve_index(
            &parsed.imports,
            export_names,
            hdr.class_index,
        ));
        if class == "EdGraph" {
            return Some(hdr.object_name.clone());
        }
        if hdr.outer_index <= 0 {
            return None;
        }
        current = hdr.outer_index;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_class_strips_to_last_segment() {
        for (full, expected) in [
            ("/Script/Engine.Actor", "Actor"),
            ("Actor", "Actor"), // no dot: unchanged
            ("/Script/Engine.SCS_Node", "SCS_Node"),
        ] {
            assert_eq!(short_class(full), expected, "short_class({full:?})");
        }
    }

    #[test]
    fn matches_filter_cases() {
        let cases: &[(&str, &[&str], bool)] = &[
            ("Anything", &[], true),                   // empty filter matches everything
            ("GetSteeringAngle", &["steering"], true), // case-insensitive substring
            ("GetSteeringAngle", &["foobar"], false),
        ];
        for (name, filters, expected) in cases {
            let filters: Vec<String> = filters.iter().map(|s| s.to_string()).collect();
            assert_eq!(
                matches_filter(name, &filters),
                *expected,
                "matches_filter({name:?}, {filters:?})"
            );
        }
    }

    #[test]
    fn format_func_flags_cases() {
        for (flags, expected) in [
            (0x04020000u32, "Public|BlueprintCallable"),
            (
                0x14420000,
                "Public|HasOutParms|BlueprintCallable|BlueprintPure",
            ),
            (0x40000000, "Const"),
            (0x00800000, "HasDefaults"),
            (0x00004000, "NetMulticast"),
            (0x00010000, "MulticastDelegate"),
            (0x03000000, "NetClient|DLLImport"),
            (0x08000000, "BlueprintEvent"),
            (0, "0x00000000"), // no flags: hex fallback
            (0x00000800, "Event"),
        ] {
            assert_eq!(format_func_flags(flags), expected, "flags=0x{flags:08x}");
        }
    }

    #[test]
    fn resolve_index_cases() {
        let names = vec!["Foo".to_string(), "Bar".to_string()];
        for (index, expected) in [(0, "None"), (1, "Foo"), (2, "Bar"), (5, "Export(5)")] {
            assert_eq!(resolve_index(&[], &names, index), expected, "index={index}");
        }
    }

    #[test]
    fn resolve_import_negative() {
        let imports = vec![ImportEntry {
            class_package: "pkg".into(),
            class_name: "cls".into(),
            object_name: "Root".into(),
            outer_index: 0,
        }];
        assert_eq!(resolve_import_path(&imports, -1), "Root");
    }

    #[test]
    fn resolve_import_positive() {
        assert_eq!(resolve_import_path(&[], 1), "?");
    }
}
