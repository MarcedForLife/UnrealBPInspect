//! Package-header reads: UE5 version + name table, and per-export
//! bytecode lookup.

use std::io::{Cursor, Seek, SeekFrom};

use crate::binary::{read_i32, read_u32};
use crate::binary::{NameTable, Reader};
use crate::types::ParsedAsset;

/// Read the UE5 version and name table from raw asset bytes.
///
/// Returns `None` if the bytes are too short or the header is malformed.
/// On success returns `(file_ver_ue5, NameTable)`.
#[cfg_attr(test, allow(dead_code))]
pub(crate) fn read_version_and_name_table(data: &[u8]) -> Option<(i32, NameTable)> {
    // Package header layout (abbreviated):
    //   u32 magic
    //   i32 legacy_ver
    //   [i32 ue3_ver if legacy_ver < LEGACY_VER_UE3_COMPAT and != -4]
    //   i32 file_ver
    //   [i32 file_ver_ue5 if legacy_ver <= LEGACY_VER_UE5_START]
    //   i32 licensee_ver
    //   i32 custom_ver_count; [20 * custom_ver_count bytes]
    //   i32 total_header_size
    //   FString folder_name
    //   u32 pkg_flags
    //   i32 name_count
    //   i32 name_offset
    //   ...
    // Mirrors `src/parser.rs::LEGACY_VER_UE3_COMPAT`. Legacy versions
    // strictly less than this (and not -4) include a separate UE3
    // compatibility version field. UE4.27 fixtures emit legacy=-7, which
    // is less than -3, so the UE3 version field is present.
    const LEGACY_VER_UE3_COMPAT: i32 = -3;
    const LEGACY_VER_UE5_START: i32 = -8;
    const VER_UE5_SOFT_OBJECT_PATH_LIST: i32 = 1007;
    const VER_UE4_LOCALIZATION_ID: i32 = 516;
    const VER_UE4_TEMPLATE_INDEX: i32 = 459;

    if data.len() < 12 {
        return None;
    }

    let mut reader: Reader = Cursor::new(data);

    let _magic = read_u32(&mut reader).ok()?;
    let legacy_ver = read_i32(&mut reader).ok()?;

    if legacy_ver < LEGACY_VER_UE3_COMPAT && legacy_ver != -4 {
        let _ = read_i32(&mut reader).ok()?; // ue3_ver
    }

    let file_ver = read_i32(&mut reader).ok()?;

    let file_ver_ue5 = if legacy_ver <= LEGACY_VER_UE5_START {
        read_i32(&mut reader).ok()?
    } else {
        0
    };

    let _ = read_i32(&mut reader).ok()?; // licensee_ver

    let custom_ver_count = read_i32(&mut reader).ok()?;
    reader
        .seek(SeekFrom::Current(custom_ver_count as i64 * 20))
        .ok()?;

    let _ = read_i32(&mut reader).ok()?; // total_header_size

    // FString folder_name: i32 length then bytes.
    let folder_len = read_i32(&mut reader).ok()?;
    if folder_len > 0 {
        reader.seek(SeekFrom::Current(folder_len as i64)).ok()?;
    } else if folder_len < 0 {
        // UTF-16: |len| code units * 2 bytes each.
        let utf16_len = folder_len.checked_neg()? as i64;
        reader.seek(SeekFrom::Current(utf16_len * 2)).ok()?;
    }

    let _ = read_u32(&mut reader).ok()?; // pkg_flags

    let name_count = read_i32(&mut reader).ok()?;
    let name_offset = read_i32(&mut reader).ok()?;

    // Skip optional UE5 / UE4 fields between name_offset and the name table.
    if file_ver_ue5 >= VER_UE5_SOFT_OBJECT_PATH_LIST {
        let _ = read_i32(&mut reader).ok()?; // soft_count
        let _ = read_i32(&mut reader).ok()?; // soft_offset
    }
    if file_ver >= VER_UE4_LOCALIZATION_ID {
        // FString localization id — skip the same way as folder_name.
        let loc_len = read_i32(&mut reader).ok()?;
        if loc_len > 0 {
            reader.seek(SeekFrom::Current(loc_len as i64)).ok()?;
        } else if loc_len < 0 {
            let utf16_len = loc_len.checked_neg()? as i64;
            reader.seek(SeekFrom::Current(utf16_len * 2)).ok()?;
        }
    }
    if file_ver >= VER_UE4_TEMPLATE_INDEX {
        let _ = read_i32(&mut reader).ok()?; // gc
        let _ = read_i32(&mut reader).ok()?; // go
    }

    let name_table = NameTable::read(&mut reader, name_count, name_offset).ok()?;

    Some((file_ver_ue5, name_table))
}

/// Look up the raw bytecode bytes for an export captured during
/// `parse_asset`'s prologue walk. Returns `None` for non-function exports
/// or any export whose serialized stream had no bytecode block.
///
/// Emits a warning to stderr when a function-class export with declared
/// parameters has no captured bytes; that's a regression signal because
/// every Blueprint function should round-trip through the prologue
/// reader. Callers can ignore the `None` return safely.
pub(super) fn lookup_export_bytecode(
    asset: &ParsedAsset,
    export_index: usize,
    name: &str,
) -> Option<Vec<u8>> {
    match asset.bytecode_by_export.get(&export_index) {
        Some((bytes, _mem_size)) => Some(bytes.clone()),
        None => {
            if asset.function_signatures.contains_key(name) {
                eprintln!("decode: no bytecode bytes for function-class export '{name}'");
            }
            None
        }
    }
}
