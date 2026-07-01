//! Bytecode reference resolution: object indices to display names.

use crate::resolve::{resolve_import_path, short_class};
use crate::types::ImportEntry;

pub fn resolve_bc_obj(index: i32, imports: &[ImportEntry], export_names: &[String]) -> String {
    let name = if index < 0 {
        short_class(&resolve_import_path(imports, index))
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names
            .get(idx)
            .cloned()
            .unwrap_or_else(|| format!("export[{}]", index))
    } else {
        "null".to_string()
    };
    name.strip_prefix("Default__")
        .map(|s| s.to_string())
        .unwrap_or(name)
}
