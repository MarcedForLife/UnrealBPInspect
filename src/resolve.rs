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

const FUNC_FLAG_NAMES: &[(u32, &str)] = &[
    (0x00000001, "Final"),
    (0x00000400, "Native"),
    (0x00000800, "Event"),
    (0x00002000, "Static"),
    (0x00004000, "MulticastDelegate"),
    (0x00020000, "Public"),
    (0x00040000, "Private"),
    (0x00080000, "Protected"),
    (0x00100000, "Delegate"),
    (0x00400000, "HasOutParms"),
    (0x01000000, "BlueprintCallable"),
    (0x02000000, "BlueprintEvent"),
    (0x04000000, "BlueprintPure"),
    (0x10000000, "Const"),
    (0x40000000, "HasDefaults"),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_class_with_dot() {
        assert_eq!(short_class("/Script/Engine.Actor"), "Actor");
    }

    #[test]
    fn short_class_no_dot() {
        assert_eq!(short_class("Actor"), "Actor");
    }

    #[test]
    fn short_class_multiple_dots() {
        assert_eq!(short_class("/Script/Engine.SCS_Node"), "SCS_Node");
    }

    #[test]
    fn matches_filter_empty() {
        assert!(matches_filter("Anything", &[]));
    }

    #[test]
    fn matches_filter_match() {
        assert!(matches_filter(
            "GetSteeringAngle",
            &["steering".to_string()]
        ));
    }

    #[test]
    fn matches_filter_no_match() {
        assert!(!matches_filter("GetSteeringAngle", &["foobar".to_string()]));
    }

    #[test]
    fn format_flags_public_pure() {
        assert_eq!(format_func_flags(0x04020000), "Public|BlueprintPure");
    }

    #[test]
    fn format_flags_zero() {
        assert_eq!(format_func_flags(0), "0x00000000");
    }

    #[test]
    fn format_flags_event() {
        assert_eq!(format_func_flags(0x00000800), "Event");
    }

    #[test]
    fn resolve_index_zero() {
        assert_eq!(resolve_index(&[], &[], 0), "None");
    }

    #[test]
    fn resolve_index_positive() {
        let names = vec!["Foo".to_string(), "Bar".to_string()];
        assert_eq!(resolve_index(&[], &names, 1), "Foo");
        assert_eq!(resolve_index(&[], &names, 2), "Bar");
    }

    #[test]
    fn resolve_index_out_of_bounds() {
        let names = vec!["Foo".to_string()];
        assert_eq!(resolve_index(&[], &names, 5), "Export(5)");
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
