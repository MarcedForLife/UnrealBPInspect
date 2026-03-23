//! Asset parser. Reads a `.uasset` byte slice sequentially:
//! 1. Package header (magic, version, table offsets)
//! 2. Name table, import table, export table
//! 3. Per-export tagged properties and bytecode

use anyhow::{ensure, Context, Result};
use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::bytecode::{
    cleanup_structured_output, decode_bytecode, discard_unused_assignments, fold_summary_patterns,
    inline_constant_temps, inline_single_use_temps, reorder_convergence, reorder_flow_patterns,
    strip_orphaned_blocks, structure_bytecode,
};
use crate::ffield::*;
use crate::properties::read_properties;
use crate::resolve::*;
use crate::types::*;

/// UE4/UE5 package file magic number (first 4 bytes of every valid `.uasset`).
const PACKAGE_FILE_TAG: u32 = 0x9E2A83C1;

/// UE function flag: function is replicated over the network.
const FUNC_NET: u32 = 0x40;

/// Sanity cap on array/extension counts to catch corrupt data early.
const MAX_REASONABLE_COUNT: i32 = 1000;

/// Minimum legacy version that includes a separate UE3 compatibility version field.
const LEGACY_VER_UE3_COMPAT: i32 = -3;

/// Legacy version threshold that introduces the UE5 version field.
const LEGACY_VER_UE5_START: i32 = -8;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExportKind {
    Function,
    BlueprintGeneratedClass,
    OtherStruct, // Struct, ScriptStruct
    Other,
}

/// Shared immutable context for export-data parsing helpers.
struct ParseCtx<'a> {
    nt: &'a NameTable,
    imports: &'a [ImportEntry],
    export_names: &'a [String],
    debug: bool,
}

fn classify_export(class_name: &str) -> ExportKind {
    if class_name.ends_with(".Function") {
        ExportKind::Function
    } else if class_name.ends_with(".BlueprintGeneratedClass") {
        ExportKind::BlueprintGeneratedClass
    } else if class_name.ends_with(".Struct") || class_name.ends_with(".ScriptStruct") {
        ExportKind::OtherStruct
    } else {
        ExportKind::Other
    }
}

/// Parse a complete `.uasset` byte slice into a [`ParsedAsset`].
///
/// Individual export parse failures are logged (when `debug` is true)
/// and produce empty property lists.
pub fn parse_asset(data: &[u8], debug: bool) -> Result<ParsedAsset> {
    let file_size = data.len();
    let mut r = std::io::Cursor::new(data);

    // --- Package file summary ---
    let magic = read_u32(&mut r).context("truncated file: cannot read magic")?;
    ensure!(
        magic == PACKAGE_FILE_TAG,
        "not a valid .uasset file (magic: {:#X})",
        magic
    );
    let legacy_ver = read_i32(&mut r)?;
    if legacy_ver < LEGACY_VER_UE3_COMPAT && legacy_ver != -4 {
        let _ue3_ver = read_i32(&mut r)?;
    }
    let file_ver = read_i32(&mut r)?;
    let file_ver_ue5: i32 = if legacy_ver <= LEGACY_VER_UE5_START {
        read_i32(&mut r)?
    } else {
        0
    };
    let ver = AssetVersion {
        file_ver,
        file_ver_ue5,
    };
    let _licensee_ver = read_i32(&mut r)?;
    // Custom versions: each entry is 16-byte GUID + int32 version = 20 bytes
    let custom_ver_count = read_i32(&mut r)?;
    r.seek(SeekFrom::Current(custom_ver_count as i64 * 20))?;
    let _total_header_size = read_i32(&mut r)?;
    let _folder_name = read_fstring(&mut r)?;
    let _pkg_flags = read_u32(&mut r)?;
    let name_count = read_i32(&mut r)?;
    let name_offset = read_i32(&mut r)?;
    if file_ver_ue5 >= VER_UE5_SOFT_OBJECT_PATH_LIST {
        let _soft_count = read_i32(&mut r)?;
        let _soft_offset = read_i32(&mut r)?;
    }
    if file_ver >= VER_UE4_LOCALIZATION_ID {
        let _loc_id = read_fstring(&mut r)?;
    }
    if file_ver >= VER_UE4_TEMPLATE_INDEX {
        let _gc = read_i32(&mut r)?;
        let _go = read_i32(&mut r)?;
    }
    let export_count = read_i32(&mut r)?;
    let export_offset = read_i32(&mut r)?;
    let import_count = read_i32(&mut r)?;
    let import_offset = read_i32(&mut r)?;

    // --- Name table ---
    let nt =
        NameTable::read(&mut r, name_count, name_offset).context("failed to read name table")?;

    if debug {
        eprintln!(
            "Header: file_ver={} ue5_ver={} names={} imports={} exports={}",
            file_ver, file_ver_ue5, name_count, import_count, export_count
        );
    }

    // --- Import table ---
    r.seek(SeekFrom::Start(import_offset as u64))?;
    let mut imports = Vec::with_capacity(import_count as usize);
    for _ in 0..import_count {
        let class_package = nt.fname(&mut r)?;
        let class_name = nt.fname(&mut r)?;
        let outer_index = read_i32(&mut r)?;
        let object_name = nt.fname(&mut r)?;
        if file_ver >= VER_UE4_PACKAGE_NAME_IN_IMPORT {
            let _package_name = nt.fname(&mut r)?;
        }
        if file_ver_ue5 >= VER_UE5_OPTIONAL_RESOURCES {
            let _import_optional = read_i32(&mut r)?;
        }
        if debug {
            eprintln!(
                "  Import[{}]: {}::{} outer={} name={}",
                imports.len(),
                class_package,
                class_name,
                outer_index,
                object_name
            );
        }
        imports.push(ImportEntry {
            class_package,
            class_name,
            object_name,
            outer_index,
        });
    }

    // --- Export table ---
    r.seek(SeekFrom::Start(export_offset as u64))?;
    let mut export_headers = Vec::with_capacity(export_count as usize);
    for _ in 0..export_count {
        let class_index = read_i32(&mut r)?;
        let super_index = read_i32(&mut r)?;
        if file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _template = read_i32(&mut r)?;
        }
        let outer_index = read_i32(&mut r)?;
        let object_name = nt.fname(&mut r)?;
        let _object_flags = read_u32(&mut r)?;
        let serial_size = read_i64(&mut r)?;
        let serial_offset = read_i64(&mut r)?;
        let _forced = read_i32(&mut r)?;
        let _not_client = read_i32(&mut r)?;
        let _not_server = read_i32(&mut r)?;
        if file_ver_ue5 < VER_UE5_REMOVE_EXPORT_GUID {
            let _guid = read_guid(&mut r)?;
        }
        if file_ver_ue5 >= VER_UE5_TRACK_INHERITED {
            let _is_inherited = read_i32(&mut r)?;
        }
        let _pkg_flags = read_u32(&mut r)?;
        if file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _not_always = read_i32(&mut r)?;
        }
        if file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _is_asset = read_i32(&mut r)?;
        }
        if file_ver_ue5 >= VER_UE5_OPTIONAL_RESOURCES {
            let _gen_public_hash = read_i32(&mut r)?;
        }
        if file_ver >= VER_UE4_PACKAGE_NAME_IN_IMPORT {
            let _first_dep = read_i32(&mut r)?;
            let _s_before_s = read_i32(&mut r)?;
            let _c_before_s = read_i32(&mut r)?;
            let _s_before_c = read_i32(&mut r)?;
            let _c_before_c = read_i32(&mut r)?;
        }
        if file_ver_ue5 >= VER_UE5_SCRIPT_SERIALIZATION_OFFSET {
            let _script_start = read_i64(&mut r)?;
            let _script_end = read_i64(&mut r)?;
        }
        export_headers.push(ExportHeader {
            class_index,
            super_index,
            outer_index,
            object_name,
            serial_offset,
            serial_size,
        });
    }

    // --- Export data (properties) ---
    let export_names_pre: Vec<String> = export_headers
        .iter()
        .map(|h| h.object_name.clone())
        .collect();
    let pctx = ParseCtx {
        nt: &nt,
        imports: &imports,
        export_names: &export_names_pre,
        debug,
    };
    let mut exports = Vec::with_capacity(export_headers.len());
    for hdr in &export_headers {
        if hdr.serial_size <= 0
            || hdr.serial_offset < 0
            || (hdr.serial_offset + hdr.serial_size) > file_size as i64
        {
            exports.push((hdr.clone(), Vec::new()));
            continue;
        }

        let export_result: Result<Vec<Property>> = (|| {
            r.seek(SeekFrom::Start(hdr.serial_offset as u64))?;
            let end = hdr.serial_offset as u64 + hdr.serial_size as u64;
            let class_name = resolve_index(&imports, &export_names_pre, hdr.class_index);
            let kind = classify_export(&class_name);

            // UE5.2+: extension byte before tagged property stream.
            // UE source gates this on bIsUClass in SerializeVersionedTaggedProperties,
            // but uncooked assets emit it for all exports (verified empirically).
            if ver.has_complete_type_name() {
                skip_serialization_extension(&mut r, &nt)?;
            }

            if kind == ExportKind::Other {
                return Ok(read_properties(&mut r, &nt, end, ver));
            }

            let is_function = kind == ExportKind::Function;
            let props = read_properties(&mut r, &nt, end, ver);
            let after_props = r.position();

            let mut extra_props = props;

            // UStruct header: Next, Super, Children
            parse_ustruct_header(
                &mut r,
                &pctx,
                &mut extra_props,
                after_props,
                end,
                &hdr.object_name,
            )?;

            // FField children (parameters / member variables)
            let ffield_children = parse_ffield_children(&mut r, &pctx, end, &hdr.object_name)?;
            if is_function && !ffield_children.is_empty() {
                extra_props.push(Property {
                    name: "Signature".into(),
                    value: PropValue::Str(format_signature(&hdr.object_name, &ffield_children)),
                });
            }
            if !is_function && !ffield_children.is_empty() {
                extra_props.push(Property {
                    name: "Members".into(),
                    value: PropValue::Array {
                        inner_type: "StrProperty".into(),
                        items: ffield_children
                            .iter()
                            .map(|(name, ty, _)| PropValue::Str(format!("{}: {}", name, ty)))
                            .collect(),
                    },
                });
            }

            // Script bytecode
            parse_and_structure_bytecode(
                &mut r,
                &pctx,
                &mut extra_props,
                ver,
                end,
                &hdr.object_name,
            )?;

            // Function flags (after bytecode, only for Function exports)
            if is_function && r.position() + 4 <= end {
                let func_flags = read_u32(&mut r)?;
                if func_flags != 0 {
                    extra_props.push(Property {
                        name: "FunctionFlags".into(),
                        value: PropValue::Str(format_func_flags(func_flags)),
                    });
                }
                if func_flags & FUNC_NET != 0 && r.position() + 4 <= end {
                    let _rep_offset = read_i32(&mut r)?;
                }
            }

            Ok(extra_props)
        })();

        match export_result {
            Ok(props) => exports.push((hdr.clone(), props)),
            Err(e) => {
                if debug {
                    eprintln!("  {} parse error: {}", hdr.object_name, e);
                }
                exports.push((hdr.clone(), Vec::new()));
            }
        }
    }

    Ok(ParsedAsset { imports, exports })
}

// ---------------------------------------------------------------------------
// Extracted helpers for export data parsing
// ---------------------------------------------------------------------------

fn skip_serialization_extension(r: &mut Reader, nt: &NameTable) -> Result<()> {
    let ext = read_u8(r)?;
    if ext != 0 {
        let count = read_i32(r)?;
        anyhow::ensure!(
            (0..MAX_REASONABLE_COUNT).contains(&count),
            "invalid extension count {count}"
        );
        for _ in 0..count {
            nt.fname(r)?;
            nt.fname(r)?;
            read_guid(r)?;
        }
    }
    Ok(())
}

fn parse_ustruct_header(
    r: &mut Reader,
    pctx: &ParseCtx,
    props: &mut Vec<Property>,
    after_props: u64,
    end: u64,
    name: &str,
) -> Result<()> {
    let (imports, export_names, debug) = (pctx.imports, pctx.export_names, pctx.debug);
    if after_props + 12 > end {
        return Ok(());
    }
    let next = read_i32(r)?;
    let super_ref = read_i32(r)?;
    let children_count = read_i32(r)?;
    if children_count > 0 && children_count < MAX_REASONABLE_COUNT {
        r.seek(SeekFrom::Current(children_count as i64 * 4))?;
    }
    if debug {
        eprintln!(
            "  {} UStruct: after_props={} next={} super={} children={} pos={}",
            name,
            after_props,
            next,
            super_ref,
            children_count,
            r.position()
        );
    }
    if super_ref != 0 {
        let super_name = resolve_index(imports, export_names, super_ref);
        props.push(Property {
            name: "Super".into(),
            value: PropValue::Name(short_class(&super_name)),
        });
    }
    Ok(())
}

fn parse_ffield_children(
    r: &mut Reader,
    pctx: &ParseCtx,
    end: u64,
    name: &str,
) -> Result<Vec<(String, String, u64)>> {
    let (nt, imports, export_names, debug) = (pctx.nt, pctx.imports, pctx.export_names, pctx.debug);
    let mut children = Vec::new();
    if r.position() + 4 > end {
        return Ok(children);
    }
    let child_prop_count = read_i32(r)?;
    if debug && child_prop_count > 0 {
        eprintln!("  {} child properties: {}", name, child_prop_count);
    }
    let mut ci = 0;
    loop {
        if r.position() + 16 > end {
            break;
        }
        if ci >= child_prop_count {
            if !nt.peek_is_ffield_class(r)? {
                break;
            }
            if debug {
                eprintln!("  {} extra child property at {}", name, r.position());
            }
        }
        let field_class = nt.fname(r)?;
        let field_name = nt.fname(r)?;
        let _flags = read_u32(r)?;
        nt.skip_metadata(r)?;
        let _array_dim = read_i32(r)?;
        let _elem_size = read_i32(r)?;
        let prop_flags = read_i64(r)? as u64;
        let mut rep_bytes = [0u8; 2];
        r.read_exact(&mut rep_bytes)?;
        let _rep_notify_func = nt.fname(r)?;
        let _bp_rep_condition = read_u8(r)?;
        let type_name = resolve_ffield_type(&field_class, r, nt, imports, export_names, end)?;
        children.push((field_name.clone(), type_name, prop_flags));
        if debug {
            eprintln!(
                "    param: {} {} flags=0x{:x} @ {}",
                field_class,
                field_name,
                prop_flags,
                r.position()
            );
        }
        ci += 1;
    }
    Ok(children)
}

fn parse_and_structure_bytecode(
    r: &mut Reader,
    pctx: &ParseCtx,
    props: &mut Vec<Property>,
    ver: AssetVersion,
    end: u64,
    name: &str,
) -> Result<()> {
    let (nt, imports, export_names, debug) = (pctx.nt, pctx.imports, pctx.export_names, pctx.debug);
    if r.position() + 8 > end {
        return Ok(());
    }
    if debug {
        let spos = r.position();
        let peek_len = std::cmp::min(16, (end - spos) as usize);
        let mut peek = vec![0u8; peek_len];
        r.read_exact(&mut peek)?;
        r.seek(SeekFrom::Start(spos))?;
        let hex: Vec<String> = peek.iter().map(|b| format!("{:02x}", b)).collect();
        eprintln!(
            "  {} script @ {} (end={}) raw: {}",
            name,
            spos,
            end,
            hex.join(" ")
        );
    }
    let bytecode_size = read_i32(r)?;
    let storage_size = read_i32(r)?;
    if storage_size <= 0 || (r.position() + storage_size as u64) > end {
        return Ok(());
    }
    let mut bytecode_data = vec![0u8; storage_size as usize];
    r.read_exact(&mut bytecode_data)?;
    if debug {
        eprintln!(
            "  {} bytecode: {}B mem, {}B disk",
            name, bytecode_size, storage_size
        );
        let show = std::cmp::min(bytecode_data.len(), 64);
        let hex: Vec<String> = bytecode_data[..show]
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect();
        eprintln!("    hex: {}", hex.join(" "));
    }

    let (stmts, final_mem_adj) =
        decode_bytecode(&bytecode_data, nt, imports, export_names, ver.file_ver_ue5);
    if debug {
        let expected = bytecode_size - storage_size;
        let drift = final_mem_adj - expected;
        eprintln!(
            "  {} mem_adj: final={} expected={} drift={}",
            name, final_mem_adj, expected, drift
        );
    }
    if stmts.is_empty() {
        return Ok(());
    }

    props.push(Property {
        name: "Bytecode".into(),
        value: PropValue::Array {
            inner_type: "StrProperty".into(),
            items: stmts
                .iter()
                .map(|s| PropValue::Str(format!("{:04x}: {}", s.mem_offset, s.text)))
                .collect(),
        },
    });

    let mut reordered = reorder_flow_patterns(&stmts);
    reorder_convergence(&mut reordered);
    inline_constant_temps(&mut reordered);
    inline_single_use_temps(&mut reordered);
    discard_unused_assignments(&mut reordered);
    let mut structured = structure_bytecode(&reordered, &HashMap::new());
    cleanup_structured_output(&mut structured);
    fold_summary_patterns(&mut structured);
    strip_orphaned_blocks(&mut structured);
    if !structured.is_empty() {
        props.push(Property {
            name: "BytecodeSummary".into(),
            value: PropValue::Array {
                inner_type: "StrProperty".into(),
                items: structured.into_iter().map(PropValue::Str).collect(),
            },
        });
    }
    Ok(())
}
