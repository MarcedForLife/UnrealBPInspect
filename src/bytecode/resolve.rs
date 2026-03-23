//! Bytecode reference resolution: object indices and field paths to display names.

use super::names::clean_bc_name;
use super::readers::*;
use crate::binary::NameTable;
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

/// Read a UObject* reference from serialized bytecode (int32 FPackageIndex)
pub fn read_bc_obj_ref(
    bytecode: &[u8],
    pos: &mut usize,
    imports: &[ImportEntry],
    export_names: &[String],
    mem_adj: &mut i32,
) -> String {
    let index = read_bc_i32(bytecode, pos);
    // Object references are int32 (FPackageIndex) on disk but 8-byte pointers in memory
    *mem_adj += 4;
    resolve_bc_obj(index, imports, export_names)
}

/// Maximum FFieldPath depth. UE's field paths are typically 1-3 levels deep
/// (e.g. Struct.Member). 16 is generous enough for any real asset while catching
/// corrupt data that would read garbage FNames.
const MAX_FIELD_PATH_DEPTH: i32 = 16;

/// Read an FField* reference from serialized bytecode (FFieldPath format for UE4.25+).
/// Format: int32 PathNum + FName[PathNum] + int32 ResolvedOwner.
/// On disk this is variable-length (8 + N*8 bytes), but in memory it's a single 8-byte
/// pointer, so mem_adj tracks the cumulative size difference for code-offset mapping.
pub fn read_bc_field_path(
    bytecode: &[u8],
    pos: &mut usize,
    name_table: &NameTable,
    mem_adj: &mut i32,
) -> String {
    let path_num = read_bc_i32(bytecode, pos);
    if path_num <= 0 {
        let _owner = read_bc_i32(bytecode, pos);
        return "null".to_string();
    }
    let needed = path_num as usize * 8 + 4;
    if path_num > MAX_FIELD_PATH_DEPTH || *pos + needed > bytecode.len() {
        let _owner = read_bc_i32(bytecode, pos);
        return "???".to_string();
    }
    // disk: 4 + N*8 + 4 bytes (path_num + N FNames + owner), mem: 8 bytes (pointer)
    *mem_adj -= path_num * 8;
    let mut names = Vec::new();
    for _ in 0..path_num {
        names.push(clean_bc_name(&read_bc_fname(bytecode, pos, name_table)));
    }
    let _owner = read_bc_i32(bytecode, pos);
    names.join(".")
}

/// Read EX_Context/EX_ClassContext r-value info
/// Format: uint32 skip (in-memory) + FFieldPath r-value property (no size byte)
pub fn read_bc_context_rvalue(
    bytecode: &[u8],
    pos: &mut usize,
    name_table: &NameTable,
    mem_adj: &mut i32,
) {
    let _skip = read_bc_u32(bytecode, pos);
    let _rvalue = read_bc_field_path(bytecode, pos, name_table, mem_adj);
}

// Inline tests: read_bc_field_path is private and needs direct access to test
// edge cases (truncated data, too-many paths, negative indices).
#[cfg(test)]
mod tests {
    use super::*;

    fn make_name_table(names: &[&str]) -> NameTable {
        NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
    }

    fn put_i32(buf: &mut Vec<u8>, v: i32) {
        buf.extend_from_slice(&v.to_le_bytes());
    }

    fn put_fname(buf: &mut Vec<u8>, name_idx: i32) {
        put_i32(buf, name_idx); // name index
        put_i32(buf, 0); // instance number
    }

    #[test]
    fn field_path_normal() {
        let name_table = make_name_table(&["MyVar"]);
        let mut bytecode = Vec::new();
        put_i32(&mut bytecode, 1); // path_num = 1
        put_fname(&mut bytecode, 0); // FName index 0 = "MyVar"
        put_i32(&mut bytecode, 0); // owner
        let mut pos = 0;
        let mut mem_adj = 0i32;
        let result = read_bc_field_path(&bytecode, &mut pos, &name_table, &mut mem_adj);
        assert_eq!(result, "MyVar");
    }

    #[test]
    fn field_path_zero() {
        let name_table = make_name_table(&["X"]);
        let mut bytecode = Vec::new();
        put_i32(&mut bytecode, 0); // path_num = 0
        put_i32(&mut bytecode, 0); // owner
        let mut pos = 0;
        let mut mem_adj = 0i32;
        assert_eq!(
            read_bc_field_path(&bytecode, &mut pos, &name_table, &mut mem_adj),
            "null"
        );
    }

    #[test]
    fn field_path_negative() {
        let name_table = make_name_table(&["X"]);
        let mut bytecode = Vec::new();
        put_i32(&mut bytecode, -1); // path_num = -1
        put_i32(&mut bytecode, 0); // owner
        let mut pos = 0;
        let mut mem_adj = 0i32;
        assert_eq!(
            read_bc_field_path(&bytecode, &mut pos, &name_table, &mut mem_adj),
            "null"
        );
    }

    #[test]
    fn field_path_truncated() {
        let name_table = make_name_table(&["X"]);
        let mut bytecode = Vec::new();
        put_i32(&mut bytecode, 1); // path_num = 1
                                   // Need 1*8 + 4 = 12 more bytes, only provide 11
        bytecode.extend_from_slice(&[0u8; 11]);
        let mut pos = 0;
        let mut mem_adj = 0i32;
        assert_eq!(
            read_bc_field_path(&bytecode, &mut pos, &name_table, &mut mem_adj),
            "???"
        );
    }

    #[test]
    fn field_path_too_many() {
        let name_table = make_name_table(&["X"]);
        let mut bytecode = Vec::new();
        put_i32(&mut bytecode, 17); // path_num = 17 (exceeds limit of 16)
        put_i32(&mut bytecode, 0); // owner (read by error path)
        let mut pos = 0;
        let mut mem_adj = 0i32;
        assert_eq!(
            read_bc_field_path(&bytecode, &mut pos, &name_table, &mut mem_adj),
            "???"
        );
    }
}
