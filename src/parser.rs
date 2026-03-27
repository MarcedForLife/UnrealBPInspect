//! Asset parser. Reads a `.uasset` byte slice sequentially:
//! 1. Package header (magic, version, table offsets)
//! 2. Name table, import table, export table
//! 3. Per-export tagged properties and bytecode

use anyhow::{ensure, Context, Result};
use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::bytecode::{
    cleanup_structured_output, collect_jump_targets, decode_bytecode, discard_unused_assignments,
    eliminate_constant_condition_branches, fold_summary_patterns, inline_constant_temps,
    inline_single_use_temps, reorder_convergence, reorder_flow_patterns, strip_orphaned_blocks,
    structure_bytecode,
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
    name_table: &'a NameTable,
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

/// Intermediate values from the package file summary.
struct PackageHeader {
    ver: AssetVersion,
    name_count: i32,
    name_offset: i32,
    export_count: i32,
    export_offset: i32,
    import_count: i32,
    import_offset: i32,
}

/// Read the package file summary (magic, versions, table offsets).
fn read_package_header(reader: &mut Reader) -> Result<PackageHeader> {
    let magic = read_u32(reader).context("truncated file: cannot read magic")?;
    ensure!(
        magic == PACKAGE_FILE_TAG,
        "not a valid .uasset file (magic: {:#X})",
        magic
    );
    let legacy_ver = read_i32(reader)?;
    // Version -4 is a known UE4 format variant that omits the UE3 compat field
    if legacy_ver < LEGACY_VER_UE3_COMPAT && legacy_ver != -4 {
        let _ue3_ver = read_i32(reader)?;
    }
    let file_ver = read_i32(reader)?;
    let file_ver_ue5: i32 = if legacy_ver <= LEGACY_VER_UE5_START {
        read_i32(reader)?
    } else {
        0
    };
    let _licensee_ver = read_i32(reader)?;
    // Custom versions: each entry is 16-byte GUID + int32 version = 20 bytes
    let custom_ver_count = read_i32(reader)?;
    reader.seek(SeekFrom::Current(custom_ver_count as i64 * 20))?;
    let _total_header_size = read_i32(reader)?;
    let _folder_name = read_fstring(reader)?;
    let _pkg_flags = read_u32(reader)?;
    let name_count = read_i32(reader)?;
    let name_offset = read_i32(reader)?;
    if file_ver_ue5 >= VER_UE5_SOFT_OBJECT_PATH_LIST {
        let _soft_count = read_i32(reader)?;
        let _soft_offset = read_i32(reader)?;
    }
    if file_ver >= VER_UE4_LOCALIZATION_ID {
        let _loc_id = read_fstring(reader)?;
    }
    if file_ver >= VER_UE4_TEMPLATE_INDEX {
        let _gc = read_i32(reader)?;
        let _go = read_i32(reader)?;
    }
    let export_count = read_i32(reader)?;
    let export_offset = read_i32(reader)?;
    let import_count = read_i32(reader)?;
    let import_offset = read_i32(reader)?;

    Ok(PackageHeader {
        ver: AssetVersion {
            file_ver,
            file_ver_ue5,
        },
        name_count,
        name_offset,
        export_count,
        export_offset,
        import_count,
        import_offset,
    })
}

/// Read the import table into a Vec of ImportEntry.
fn read_import_table(
    reader: &mut Reader,
    name_table: &NameTable,
    ver: AssetVersion,
    count: i32,
    offset: i32,
    debug: bool,
) -> Result<Vec<ImportEntry>> {
    reader.seek(SeekFrom::Start(offset as u64))?;
    let mut imports = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let class_package = name_table.fname(reader)?;
        let class_name = name_table.fname(reader)?;
        let outer_index = read_i32(reader)?;
        let object_name = name_table.fname(reader)?;
        if ver.file_ver >= VER_UE4_PACKAGE_NAME_IN_IMPORT {
            let _package_name = name_table.fname(reader)?;
        }
        if ver.file_ver_ue5 >= VER_UE5_OPTIONAL_RESOURCES {
            let _import_optional = read_i32(reader)?;
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
    Ok(imports)
}

/// Read the export table headers (metadata only, not serialized data).
fn read_export_headers(
    reader: &mut Reader,
    name_table: &NameTable,
    ver: AssetVersion,
    count: i32,
    offset: i32,
) -> Result<Vec<ExportHeader>> {
    reader.seek(SeekFrom::Start(offset as u64))?;
    let mut headers = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let class_index = read_i32(reader)?;
        let super_index = read_i32(reader)?;
        if ver.file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _template = read_i32(reader)?;
        }
        let outer_index = read_i32(reader)?;
        let object_name = name_table.fname(reader)?;
        let _object_flags = read_u32(reader)?;
        let serial_size = read_i64(reader)?;
        let serial_offset = read_i64(reader)?;
        let _forced = read_i32(reader)?;
        let _not_client = read_i32(reader)?;
        let _not_server = read_i32(reader)?;
        if ver.file_ver_ue5 < VER_UE5_REMOVE_EXPORT_GUID {
            let _guid = read_guid(reader)?;
        }
        if ver.file_ver_ue5 >= VER_UE5_TRACK_INHERITED {
            let _is_inherited = read_i32(reader)?;
        }
        let _pkg_flags = read_u32(reader)?;
        if ver.file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _not_always = read_i32(reader)?;
        }
        if ver.file_ver >= VER_UE4_TEMPLATE_INDEX {
            let _is_asset = read_i32(reader)?;
        }
        if ver.file_ver_ue5 >= VER_UE5_OPTIONAL_RESOURCES {
            let _gen_public_hash = read_i32(reader)?;
        }
        if ver.file_ver >= VER_UE4_PACKAGE_NAME_IN_IMPORT {
            let _first_dep = read_i32(reader)?;
            let _s_before_s = read_i32(reader)?;
            let _c_before_s = read_i32(reader)?;
            let _s_before_c = read_i32(reader)?;
            let _c_before_c = read_i32(reader)?;
        }
        if ver.file_ver_ue5 >= VER_UE5_SCRIPT_SERIALIZATION_OFFSET {
            let _script_start = read_i64(reader)?;
            let _script_end = read_i64(reader)?;
        }
        headers.push(ExportHeader {
            class_index,
            super_index,
            outer_index,
            object_name,
            serial_offset,
            serial_size,
        });
    }
    Ok(headers)
}

/// Parse a complete `.uasset` byte slice into a [`ParsedAsset`].
///
/// Individual export parse failures are logged (when `debug` is true)
/// and produce empty property lists.
pub fn parse_asset(data: &[u8], debug: bool) -> Result<ParsedAsset> {
    let file_size = data.len();
    let mut reader = std::io::Cursor::new(data);

    let hdr = read_package_header(&mut reader)?;
    let ver = hdr.ver;
    let name_table = NameTable::read(&mut reader, hdr.name_count, hdr.name_offset)
        .context("failed to read name table")?;

    if debug {
        eprintln!(
            "Header: file_ver={} ue5_ver={} names={} imports={} exports={}",
            ver.file_ver, ver.file_ver_ue5, hdr.name_count, hdr.import_count, hdr.export_count
        );
    }

    let imports = read_import_table(
        &mut reader,
        &name_table,
        ver,
        hdr.import_count,
        hdr.import_offset,
        debug,
    )?;
    let export_headers = read_export_headers(
        &mut reader,
        &name_table,
        ver,
        hdr.export_count,
        hdr.export_offset,
    )?;

    // Export data (properties)
    let export_names_pre: Vec<String> = export_headers
        .iter()
        .map(|h| h.object_name.clone())
        .collect();
    let pctx = ParseCtx {
        name_table: &name_table,
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
            reader.seek(SeekFrom::Start(hdr.serial_offset as u64))?;
            let end = hdr.serial_offset as u64 + hdr.serial_size as u64;
            let class_name = resolve_index(&imports, &export_names_pre, hdr.class_index);
            let kind = classify_export(&class_name);

            // UE5.2+: extension byte before tagged property stream.
            // UE source gates this on bIsUClass in SerializeVersionedTaggedProperties,
            // but uncooked assets emit it for all exports (verified empirically).
            if ver.has_complete_type_name() {
                skip_serialization_extension(&mut reader, &name_table)?;
            }

            if kind == ExportKind::Other {
                return Ok(read_properties(&mut reader, &name_table, end, ver));
            }

            let is_function = kind == ExportKind::Function;
            let props = read_properties(&mut reader, &name_table, end, ver);
            let props_end_pos = reader.position();

            let mut extra_props = props;

            // UStruct header: Next, Super, Children
            parse_ustruct_header(
                &mut reader,
                &pctx,
                &mut extra_props,
                props_end_pos,
                end,
                &hdr.object_name,
            )?;

            // FField children (parameters / member variables)
            let ffield_children = parse_ffield_children(&mut reader, &pctx, end, &hdr.object_name)?;
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
                &mut reader,
                &pctx,
                &mut extra_props,
                ver,
                end,
                &hdr.object_name,
            )?;

            // Function flags (after bytecode, only for Function exports)
            if is_function && reader.position() + 4 <= end {
                let func_flags = read_u32(&mut reader)?;
                if func_flags != 0 {
                    extra_props.push(Property {
                        name: "FunctionFlags".into(),
                        value: PropValue::Str(format_func_flags(func_flags)),
                    });
                }
                if func_flags & FUNC_NET != 0 && reader.position() + 4 <= end {
                    let _rep_offset = read_i32(&mut reader)?;
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

fn skip_serialization_extension(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    let ext = read_u8(reader)?;
    if ext != 0 {
        let count = read_i32(reader)?;
        anyhow::ensure!(
            (0..MAX_REASONABLE_COUNT).contains(&count),
            "invalid extension count {count}"
        );
        for _ in 0..count {
            name_table.fname(reader)?;
            name_table.fname(reader)?;
            read_guid(reader)?;
        }
    }
    Ok(())
}

fn parse_ustruct_header(
    reader: &mut Reader,
    pctx: &ParseCtx,
    props: &mut Vec<Property>,
    props_end_pos: u64,
    end: u64,
    name: &str,
) -> Result<()> {
    if props_end_pos + 12 > end {
        return Ok(());
    }
    let next = read_i32(reader)?;
    let super_ref = read_i32(reader)?;
    let children_count = read_i32(reader)?;
    if children_count > 0 && children_count < MAX_REASONABLE_COUNT {
        reader.seek(SeekFrom::Current(children_count as i64 * 4))?;
    }
    if pctx.debug {
        eprintln!(
            "  {} UStruct: after_props={} next={} super={} children={} pos={}",
            name,
            props_end_pos,
            next,
            super_ref,
            children_count,
            reader.position()
        );
    }
    if super_ref != 0 {
        let super_name = resolve_index(pctx.imports, pctx.export_names, super_ref);
        props.push(Property {
            name: "Super".into(),
            value: PropValue::Name(short_class(&super_name)),
        });
    }
    Ok(())
}

fn read_one_ffield_child(
    reader: &mut Reader,
    pctx: &ParseCtx,
    end: u64,
) -> Result<(String, String, u64)> {
    let field_class = pctx.name_table.fname(reader)?;
    let field_name = pctx.name_table.fname(reader)?;
    let _flags = read_u32(reader)?;
    pctx.name_table.skip_metadata(reader)?;
    let _array_dim = read_i32(reader)?;
    let _elem_size = read_i32(reader)?;
    let prop_flags = read_i64(reader)? as u64;
    let mut rep_bytes = [0u8; 2];
    reader.read_exact(&mut rep_bytes)?;
    let _rep_notify_func = pctx.name_table.fname(reader)?;
    let _bp_rep_condition = read_u8(reader)?;
    let type_name = resolve_ffield_type(
        &field_class,
        reader,
        pctx.name_table,
        pctx.imports,
        pctx.export_names,
        end,
    )?;
    if pctx.debug {
        eprintln!(
            "    param: {} {} flags=0x{:x} @ {}",
            field_class,
            field_name,
            prop_flags,
            reader.position()
        );
    }
    Ok((field_name, type_name, prop_flags))
}

fn parse_ffield_children(
    reader: &mut Reader,
    pctx: &ParseCtx,
    end: u64,
    name: &str,
) -> Result<Vec<(String, String, u64)>> {
    let mut children = Vec::new();
    if reader.position() + 4 > end {
        return Ok(children);
    }
    let child_prop_count = read_i32(reader)?;
    if pctx.debug && child_prop_count > 0 {
        eprintln!("  {} child properties: {}", name, child_prop_count);
    }
    // Phase 1: read declared children
    for _ in 0..child_prop_count {
        if reader.position() + 16 > end {
            break;
        }
        children.push(read_one_ffield_child(reader, pctx, end)?);
    }
    // Phase 2: some UE versions emit more children than declared
    while reader.position() + 16 <= end {
        if !pctx.name_table.peek_is_ffield_class(reader)? {
            break;
        }
        if pctx.debug {
            eprintln!("  {} extra child property at {}", name, reader.position());
        }
        children.push(read_one_ffield_child(reader, pctx, end)?);
    }
    Ok(children)
}

fn parse_and_structure_bytecode(
    reader: &mut Reader,
    pctx: &ParseCtx,
    props: &mut Vec<Property>,
    ver: AssetVersion,
    end: u64,
    name: &str,
) -> Result<()> {
    if reader.position() + 8 > end {
        return Ok(());
    }
    if pctx.debug {
        debug_peek_script(reader, name, end)?;
    }

    // Read raw bytecode from the export data
    let bytecode_size = read_i32(reader)?;
    let storage_size = read_i32(reader)?;
    if storage_size <= 0 || (reader.position() + storage_size as u64) > end {
        return Ok(());
    }
    let mut bytecode_data = vec![0u8; storage_size as usize];
    reader.read_exact(&mut bytecode_data)?;
    if pctx.debug {
        debug_bytecode_hex(&bytecode_data, name, bytecode_size, storage_size);
    }

    // Decode opcodes into flat statement list
    let (stmts, final_mem_adj) = decode_bytecode(
        &bytecode_data,
        pctx.name_table,
        pctx.imports,
        pctx.export_names,
        ver.file_ver_ue5,
    );
    if pctx.debug {
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

    // Store raw decoded bytecode
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

    // Run the structuring pipeline: reorder, inline, structure, cleanup
    let structured = structure_statements(&stmts);
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

/// Run the inline/structure/cleanup pipeline on pre-processed statements.
pub fn structure_and_cleanup(stmts: &[crate::bytecode::BcStatement]) -> Vec<String> {
    let mut structured = structure_bytecode(stmts, &HashMap::new());
    cleanup_structured_output(&mut structured);
    fold_summary_patterns(&mut structured);
    // Re-run after pattern folding: temp inlining can create new constant-condition
    // branches (e.g., inlining `Temp_bool = true` into `if (!Temp_bool) return`).
    eliminate_constant_condition_branches(&mut structured);
    strip_orphaned_blocks(&mut structured);
    structured
}

/// Run the full statement structuring pipeline: flow reordering, temp inlining,
/// if/else reconstruction, expression cleanup, and pattern folding.
fn structure_statements(stmts: &[crate::bytecode::BcStatement]) -> Vec<String> {
    let mut reordered = reorder_flow_patterns(stmts);
    reorder_convergence(&mut reordered);
    let jump_targets = collect_jump_targets(&reordered);
    inline_constant_temps(&mut reordered, &jump_targets);
    inline_single_use_temps(&mut reordered);
    discard_unused_assignments(&mut reordered);
    structure_and_cleanup(&reordered)
}

fn debug_peek_script(reader: &mut Reader, name: &str, end: u64) -> Result<()> {
    let spos = reader.position();
    let peek_len = std::cmp::min(16, (end - spos) as usize);
    let mut peek = vec![0u8; peek_len];
    reader.read_exact(&mut peek)?;
    reader.seek(SeekFrom::Start(spos))?;
    let hex: Vec<String> = peek.iter().map(|b| format!("{:02x}", b)).collect();
    eprintln!(
        "  {} script @ {} (end={}) raw: {}",
        name,
        spos,
        end,
        hex.join(" ")
    );
    Ok(())
}

fn debug_bytecode_hex(bytecode_data: &[u8], name: &str, bytecode_size: i32, storage_size: i32) {
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
