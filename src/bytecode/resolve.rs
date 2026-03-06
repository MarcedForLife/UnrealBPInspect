use crate::binary::NameTable;
use crate::types::ImportEntry;
use crate::resolve::{resolve_import_path, short_class};
use super::readers::*;
use super::names::clean_bc_name;

pub fn resolve_bc_obj(index: i32, imports: &[ImportEntry], export_names: &[String]) -> String {
    if index < 0 {
        short_class(&resolve_import_path(imports, index))
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names.get(idx).cloned().unwrap_or_else(|| format!("export[{}]", index))
    } else {
        "null".to_string()
    }
}

/// Read a UObject* reference from serialized bytecode (int32 FPackageIndex)
pub fn read_bc_obj_ref(bc: &[u8], pos: &mut usize, imports: &[ImportEntry], export_names: &[String], mem_adj: &mut i32) -> String {
    let index = read_bc_i32(bc, pos);
    *mem_adj += 4; // disk: 4 bytes (int32), mem: 8 bytes (pointer)
    resolve_bc_obj(index, imports, export_names)
}

/// Read an FField* reference from serialized bytecode (FFieldPath format for UE4.25+)
/// Format: int32 PathNum + FName[PathNum] + int32 ResolvedOwner
pub fn read_bc_field_path(bc: &[u8], pos: &mut usize, nt: &NameTable, mem_adj: &mut i32) -> String {
    let path_num = read_bc_i32(bc, pos);
    if path_num <= 0 {
        let _owner = read_bc_i32(bc, pos);
        return "null".to_string();
    }
    let needed = path_num as usize * 8 + 4;
    if path_num > 16 || *pos + needed > bc.len() + 8 {
        let _owner = read_bc_i32(bc, pos);
        return "???".to_string();
    }
    // disk: 8 + N*8 bytes (path_num + N FNames + owner), mem: 8 bytes (pointer)
    *mem_adj -= path_num * 8;
    let mut names = Vec::new();
    for _ in 0..path_num {
        names.push(clean_bc_name(&read_bc_fname(bc, pos, nt)));
    }
    let _owner = read_bc_i32(bc, pos);
    names.join(".")
}

/// Read EX_Context/EX_ClassContext r-value info
/// Format: uint32 skip (in-memory) + FFieldPath r-value property (no size byte)
pub fn read_bc_context_rvalue(bc: &[u8], pos: &mut usize, nt: &NameTable, mem_adj: &mut i32) {
    let _skip = read_bc_u32(bc, pos);
    let _rvalue = read_bc_field_path(bc, pos, nt, mem_adj);
}
