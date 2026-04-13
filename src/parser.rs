//! Asset parser. Reads a `.uasset` byte slice sequentially:
//! 1. Package header (magic, version, table offsets)
//! 2. Name table, import table, export table
//! 3. Per-export tagged properties and bytecode

use anyhow::{ensure, Context, Result};
use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::bytecode::{
    apply_indentation, cleanup_structured_output, collect_jump_targets, decode_bytecode,
    discard_unused_assignments, discard_unused_assignments_text,
    eliminate_constant_condition_branches, fold_cascade_across_sequences, fold_summary_patterns,
    fold_switch_enum_cascade, inline_constant_temps, inline_constant_temps_text,
    inline_single_use_temps, rename_loop_temp_vars, reorder_convergence, reorder_flow_patterns,
    split_by_sequence_markers, strip_inlined_break_calls, strip_latch_boilerplate,
    strip_orphaned_blocks, strip_unmatched_braces, structure_bytecode,
};
use crate::ffield::*;
use crate::properties::read_properties;
use crate::resolve::*;
use crate::types::*;

/// Package file magic number (first 4 bytes of every valid `.uasset`).
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
    let mut pin_data_map: std::collections::HashMap<usize, NodePinData> =
        std::collections::HashMap::new();
    for (ei, hdr) in export_headers.iter().enumerate() {
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
                let props = read_properties(&mut reader, &name_table, end, ver);
                let short = short_class(&class_name);
                if short.starts_with("K2Node_") || short == "EdGraphNode_Comment" {
                    // K2Node subclasses serialize additional data between the
                    // tagged property stream and the pin array. Scan forward
                    // from the current position looking for the pin data
                    // signature: deprecated_count(0) + reasonable pin_count.
                    let pins = scan_for_pins(&mut reader, &name_table, end, ver);
                    if let Some(ref pins) = pins {
                        pin_data_map.insert(ei + 1, NodePinData { pins: pins.clone() });
                    }
                }
                return Ok(props);
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

    if debug && !pin_data_map.is_empty() {
        let total_links: usize = pin_data_map
            .values()
            .flat_map(|pd| &pd.pins)
            .map(|pin| pin.linked_to.len())
            .sum();
        eprintln!(
            "  Pins: {} nodes parsed, {} total links",
            pin_data_map.len(),
            total_links
        );
    }
    Ok(ParsedAsset {
        imports,
        exports,
        pin_data: pin_data_map,
    })
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
    // Temp inlining runs post-structure so that structure detection has the
    // full statement array with intact mem_offsets for jump target resolution.
    inline_constant_temps_text(&mut structured);
    discard_unused_assignments_text(&mut structured);
    fold_summary_patterns(&mut structured);
    // Remove Break* calls left orphaned by fold_break_patterns: when out params
    // were inlined by an earlier pass, fold_break_patterns skips the call but
    // the accessor-form arguments make the call dead code.
    strip_inlined_break_calls(&mut structured);
    // Re-run after pattern folding: temp inlining can create new constant-condition
    // branches (e.g., inlining `Temp_bool = true` into `if (!Temp_bool) return`).
    eliminate_constant_condition_branches(&mut structured);
    strip_orphaned_blocks(&mut structured);
    rename_loop_temp_vars(&mut structured);
    fold_switch_enum_cascade(&mut structured);
    // Re-run cleanup: switch folding can expose dead code from pin-boundary
    // sentinels that were hidden inside the cascade's brace nesting.
    cleanup_structured_output(&mut structured);
    apply_indentation(&mut structured);
    // Strip bare "// on loop complete:" markers (used internally by dedup_completion_paths
    // but redundant in output since the closing brace already shows the loop ended).
    // Annotated variants like "// on loop complete: (same as pre-loop setup)" are kept.
    structured.retain(|line| line.trim() != "// on loop complete:");
    structured
}

/// Run the full statement structuring pipeline: flow reordering, temp inlining,
/// if/else reconstruction, expression cleanup, and pattern folding.
///
/// When the function has Sequence pins, splits by `// sequence [N]:` markers
/// and structures each body independently. This prevents switch cascades and
/// other control flow from spanning across sequence boundaries.
fn structure_statements(stmts: &[crate::bytecode::BcStatement]) -> Vec<String> {
    let mut cleaned = stmts.to_vec();
    strip_latch_boilerplate(&mut cleaned);
    let mut reordered = reorder_flow_patterns(&cleaned);
    reorder_convergence(&mut reordered);
    let jump_targets = collect_jump_targets(&reordered);
    inline_constant_temps(&mut reordered, &jump_targets);
    inline_single_use_temps(&mut reordered);
    discard_unused_assignments(&mut reordered);

    let sub_segments = split_by_sequence_markers(&reordered);

    // When a switch-enum cascade in the prefix targets sequence pin bodies,
    // fold it into switch/case text with each case body structured
    // independently. This prevents the cascade scaffold from being separated
    // from its targets by sequence splitting.
    if sub_segments.len() > 1 {
        let first_marker_idx = reordered
            .iter()
            .position(|s| s.text.starts_with("// sequence ["))
            .unwrap_or(0);
        if first_marker_idx > 0 {
            if let Some(mut lines) =
                fold_cascade_across_sequences(&reordered, first_marker_idx, structure_and_cleanup)
            {
                // Re-apply indentation on the combined output so the
                // switch/case wrapper and case bodies are properly nested.
                apply_indentation(&mut lines);
                return lines;
            }
        }
    }
    if sub_segments.len() <= 1 {
        return structure_and_cleanup(&reordered);
    }

    // Structure each pin independently (proper if/else blocks per pin),
    // but defer pattern folding to the combined output so cross-pin
    // variable references are preserved.
    let mut all_lines = Vec::new();
    for (marker, body) in &sub_segments {
        if let Some(marker_text) = marker {
            all_lines.push(marker_text.clone());
        }
        if !body.is_empty() {
            let mut structured = structure_bytecode(body, &HashMap::new());
            cleanup_structured_output(&mut structured);
            all_lines.extend(structured);
        }
    }
    inline_constant_temps_text(&mut all_lines);
    discard_unused_assignments_text(&mut all_lines);
    fold_summary_patterns(&mut all_lines);
    eliminate_constant_condition_branches(&mut all_lines);
    strip_orphaned_blocks(&mut all_lines);
    rename_loop_temp_vars(&mut all_lines);
    fold_switch_enum_cascade(&mut all_lines);
    // Re-run cleanup: switch folding can expose dead code from pin-boundary
    // sentinels that were hidden inside the cascade's brace nesting.
    cleanup_structured_output(&mut all_lines);
    // Strip unmatched braces last, after all passes that might create them.
    strip_unmatched_braces(&mut all_lines);
    apply_indentation(&mut all_lines);
    all_lines
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

// Pin parsing for EdGraph nodes.

use crate::types::{EdGraphPin, NodePinData};

/// Sanity cap on pin count per node (most nodes have < 50 pins).
const MAX_PIN_COUNT: i32 = 500;

/// Sanity cap on LinkedTo entries per pin (most pins have 0-3 links).
const MAX_LINKED_COUNT: i32 = 200;

/// Sanity cap on SubPins per pin.
const MAX_SUBPIN_COUNT: i32 = 50;

/// Maximum SubPin nesting depth to prevent stack overflow on corrupt data.
const MAX_SUBPIN_DEPTH: usize = 10;

/// Scan forward from the current reader position to find pin data.
///
/// K2Node subclasses serialize class-specific data between the tagged
/// property stream and the pin array. We scan at 4-byte (i32) alignment
/// looking for the pin signature: deprecated_count(i32=0) followed by a
/// reasonable pin_count(i32 in 1..MAX_PIN_COUNT), then attempt to parse
/// pins at each candidate. Tries both UE5 and UE4 formats for UE5 assets.
fn scan_for_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
) -> Option<Vec<EdGraphPin>> {
    let scan_start = reader.position();
    let scan_limit = end.saturating_sub(8);

    // First try at the current position (no scan needed if properties consumed correctly)
    let direct = try_pins_at(reader, name_table, end, ver, scan_start);
    if direct.is_some() {
        return direct;
    }

    // Scan at i32 alignment for the deprecated_count=0 + pin_count signature
    let mut pos = scan_start;
    while pos <= scan_limit {
        reader.seek(SeekFrom::Start(pos)).ok()?;

        let deprecated = read_i32(reader).ok()?;
        if deprecated != 0 {
            pos += 4;
            continue;
        }

        let pin_count_val = read_i32(reader).ok()?;
        if !(1..=MAX_PIN_COUNT).contains(&pin_count_val) {
            pos += 4;
            continue;
        }

        let result = try_pins_at(reader, name_table, end, ver, pos);
        if result.is_some() {
            return result;
        }

        pos += 4;
    }

    None
}

/// Try parsing pins at a specific position, with UE5/UE4 format negotiation.
fn try_pins_at(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
    pos: u64,
) -> Option<Vec<EdGraphPin>> {
    if ver.file_ver_ue5 > 0 {
        reader.seek(SeekFrom::Start(pos)).ok()?;
        let ue5_result = try_parse_pins(reader, name_table, end, true);
        reader.seek(SeekFrom::Start(pos)).ok()?;
        let ue4_result = try_parse_pins(reader, name_table, end, false);
        match (ue5_result, ue4_result) {
            (Some(a), Some(b)) => Some(if a.len() >= b.len() { a } else { b }),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    } else {
        reader.seek(SeekFrom::Start(pos)).ok()?;
        try_parse_pins(reader, name_table, end, false)
    }
}

/// Parse EdGraph pin data from a node export's post-property stream.
///
/// Returns a Vec of pins with per-pin LinkedTo connections.
/// Based on UE4.27 `UEdGraphPin::Serialize` format.
fn try_parse_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
) -> Option<Vec<EdGraphPin>> {
    let result: Result<Vec<EdGraphPin>> = (|| {
        let remaining = end.saturating_sub(reader.position());
        if remaining < 8 {
            return Ok(Vec::new());
        }

        // UEdGraphNode::Serialize writes deprecated pins (always 0) then new pin count
        let deprecated_count = read_i32(reader)?;
        let pin_count = read_i32(reader)?;
        if deprecated_count != 0 {
            anyhow::bail!("deprecated_pin_count={deprecated_count}");
        }
        if !(0..=MAX_PIN_COUNT).contains(&pin_count) {
            anyhow::bail!("pin_count={pin_count}");
        }

        let mut pins = Vec::new();
        for _ in 0..pin_count {
            match read_one_pin(reader, name_table, end, ue5, 0) {
                Ok(pin_group) => pins.extend(pin_group),
                Err(_) => break,
            }
        }

        Ok(pins)
    })();

    match result {
        Ok(pins) if !pins.is_empty() => Some(pins),
        Err(err) => {
            eprintln!("  pin err: {err}");
            None
        }
        _ => None,
    }
}

/// Read a single pin from the owning node's pin array.
///
/// UE4.27 format: SerializePin writes (bNullPtr, OwningNode, PinId),
/// then UEdGraphPin::Serialize writes the full pin data starting with
/// (OwningNode, PinId) again, followed by name, type, defaults, LinkedTo, etc.
///
/// `depth` tracks SubPin recursion to prevent stack overflow on corrupt data.
#[allow(clippy::only_used_in_recursion)] // end is threaded for future bounds checks
fn read_one_pin(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
    depth: usize,
) -> Result<Vec<EdGraphPin>> {
    // SerializePin wrapper: bNullPtr(i32) + OwningNode(i32) + PinGuid(FGuid)
    let is_null = read_i32(reader)?;
    if is_null != 0 {
        anyhow::bail!("null pin");
    }
    let _wrapper_owner = read_i32(reader)?;
    let _wrapper_guid = read_guid(reader)?;

    // UEdGraphPin::Serialize: OwningNode + PinId (repeated from wrapper)
    let _owning_node = read_i32(reader)?;
    let _pin_id = read_guid(reader)?;
    let pin_name = name_table.fname(reader)?;

    skip_ftext(reader, name_table)?; // PinFriendlyName

    // UE5: SourceIndex (i32) added after PinFriendlyName
    if ue5 {
        let _source_index = read_i32(reader)?;
    }

    let _tooltip = read_fstring(reader)?; // PinToolTip
    let direction = read_u8(reader)?; // Direction
    let type_name = read_pin_type(reader, name_table, ue5)?; // FEdGraphPinType

    // Default values
    let _default_value = read_fstring(reader)?;
    let _autogen_default = read_fstring(reader)?;
    let _default_object = read_i32(reader)?;
    skip_ftext(reader, name_table)?; // DefaultTextValue

    // LinkedTo array: count + (bNull(i32) + OwningNode(i32) + PinGuid(FGuid)) per entry
    let linked_count = read_i32(reader)?;
    ensure!(
        (0..MAX_LINKED_COUNT).contains(&linked_count),
        "linked_count={linked_count}"
    );
    let mut linked_to: Vec<usize> = Vec::new();
    for _ in 0..linked_count {
        let link_null = read_i32(reader)?;
        if link_null == 0 {
            let owner_idx = read_i32(reader)?;
            let _pin_guid = read_guid(reader)?;
            if owner_idx > 0 {
                let idx = owner_idx as usize;
                if !linked_to.contains(&idx) {
                    linked_to.push(idx);
                }
            }
        }
    }

    // SubPins array (recursive, depth-limited). Sub-pins on split structs
    // contain field-specific names and connections used for comment placement.
    let sub_count = read_i32(reader)?;
    ensure!(
        (0..MAX_SUBPIN_COUNT).contains(&sub_count),
        "sub_count={sub_count}"
    );
    ensure!(
        depth < MAX_SUBPIN_DEPTH,
        "SubPin nesting too deep ({depth})"
    );
    let mut sub_pins: Vec<EdGraphPin> = Vec::new();
    for _ in 0..sub_count {
        let sub_null = read_i32(reader)?;
        if sub_null == 0 {
            let _sub_owner = read_i32(reader)?;
            let _sub_guid = read_guid(reader)?;
            sub_pins.extend(read_one_pin(reader, name_table, end, ue5, depth + 1)?);
        }
    }

    // ParentPin + ReferencePassThroughConnection
    read_pin_ref(reader)?;
    read_pin_ref(reader)?;

    // Editor-only: PersistentGuid(16) + bitfield(4)
    let _persistent_guid = read_guid(reader)?;
    let _bitfield = read_u32(reader)?;

    let mut result = vec![EdGraphPin {
        name: pin_name,
        pin_type: type_name,
        direction,
        linked_to,
    }];
    result.extend(sub_pins);
    Ok(result)
}

/// Read a nullable pin reference (bNullPtr + optional OwningNode + PinGuid).
fn read_pin_ref(reader: &mut Reader) -> Result<()> {
    let is_null = read_i32(reader)?; // bool as i32
    if is_null == 0 {
        let _owner = read_i32(reader)?;
        let _guid = read_guid(reader)?;
    }
    Ok(())
}

/// Read FEdGraphPinType (UE4.27 format).
/// Returns the pin category name (e.g., "exec", "bool", "object").
fn read_pin_type(reader: &mut Reader, name_table: &NameTable, ue5: bool) -> Result<String> {
    let category = name_table.fname(reader)?;
    let _subcategory = name_table.fname(reader)?;
    let _subcategory_object = read_i32(reader)?; // TWeakObjectPtr as package index

    // ContainerType (EPinContainerType: u8, None=0, Array=1, Set=2, Map=3)
    let container_type = read_u8(reader)?;
    if container_type == 3 {
        // Map value type: FEdGraphTerminalType
        read_terminal_type(reader, name_table)?;
    }

    // bIsReference and bIsWeakPointer (bools serialized as i32)
    let _is_reference = read_i32(reader)?;
    let _is_weak_pointer = read_i32(reader)?;

    // FSimpleMemberReference (for delegate pins)
    let _member_parent = read_i32(reader)?; // UObject*
    let _member_name = name_table.fname(reader)?;
    let _member_guid = read_guid(reader)?;

    // bIsConst (bool as i32)
    let _is_const = read_i32(reader)?;

    // bIsUObjectWrapper (bool as i32)
    let _is_uobject_wrapper = read_i32(reader)?;

    // UE5: bSerializeAsSinglePrecisionFloat (bool as i32, editor-only)
    if ue5 {
        let _single_precision = read_i32(reader)?;
    }

    Ok(category)
}

/// Read FEdGraphTerminalType.
fn read_terminal_type(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    let _category = name_table.fname(reader)?;
    let _subcategory = name_table.fname(reader)?;
    let _subcategory_object = read_i32(reader)?;
    let _is_const = read_i32(reader)?; // bool as i32
    let _is_weak = read_i32(reader)?; // bool as i32
    let _is_uobject_wrapper = read_i32(reader)?; // bool as i32
    Ok(())
}

/// Skip an FText in the binary stream.
///
/// UE4 FText format: i32 Flags, i8 HistoryType, then type-specific content.
/// For None (-1): bool bHasCultureInvariantString + optional FString.
/// For Base (0): FString Namespace + FString Key + FString SourceString.
fn skip_ftext(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    let _flags = read_i32(reader)?;
    let history_type = {
        let val = read_u8(reader)?;
        val as i8
    };
    match history_type {
        -1 => {
            // None: bool bHasCultureInvariantString + optional FString
            let has_invariant = read_i32(reader)?; // bool as i32
            if has_invariant != 0 {
                let _invariant = read_fstring(reader)?;
            }
        }
        0 => {
            // Base: namespace + key + source string
            let _ns = read_fstring(reader)?;
            let _key = read_fstring(reader)?;
            let _src = read_fstring(reader)?;
        }
        1 | 2 => {
            // NamedFormat / OrderedFormat: pattern FText + arguments array.
            // Each argument: FString key + FText value.
            skip_ftext(reader, name_table)?;
            let arg_count = read_i32(reader)?;
            for _ in 0..arg_count {
                let _arg_name = read_fstring(reader)?;
                skip_ftext(reader, name_table)?;
            }
        }
        11 => {
            // StringTableEntry: table_id (FName) + key (FString)
            let _table = name_table.fname(reader)?;
            let _key = read_fstring(reader)?;
        }
        _ => anyhow::bail!("unhandled FText history_type={history_type}"),
    }
    Ok(())
}
