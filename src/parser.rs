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

pub fn parse_asset(data: &[u8], debug: bool) -> Result<ParsedAsset> {
    let file_size = data.len();
    let mut c = std::io::Cursor::new(data);

    // --- Package file summary ---
    let magic = read_u32(&mut c).context("truncated file: cannot read magic")?;
    ensure!(
        magic == 0x9E2A83C1, // UE4 package signature (PACKAGE_FILE_TAG)
        "not a valid .uasset file (magic: {:#X})",
        magic
    );
    let legacy_ver = read_i32(&mut c)?;
    if legacy_ver < -3 && legacy_ver != -4 {
        let _ue3_ver = read_i32(&mut c)?;
    }
    let file_ver = read_i32(&mut c)?;
    let file_ver_ue5: i32 = if legacy_ver <= -8 {
        read_i32(&mut c)?
    } else {
        0
    };
    let ver = AssetVersion {
        file_ver,
        file_ver_ue5,
    };
    let _licensee_ver = read_i32(&mut c)?;
    // Custom versions: each entry is 16-byte GUID + int32 version = 20 bytes
    let custom_ver_count = read_i32(&mut c)?;
    c.seek(SeekFrom::Current(custom_ver_count as i64 * 20))?;
    let _total_header_size = read_i32(&mut c)?;
    let _folder_name = read_fstring(&mut c)?;
    let _pkg_flags = read_u32(&mut c)?;
    let name_count = read_i32(&mut c)?;
    let name_offset = read_i32(&mut c)?;
    if file_ver_ue5 >= 1007 {
        // ADD_SOFTOBJECTPATH_LIST
        let _soft_count = read_i32(&mut c)?;
        let _soft_offset = read_i32(&mut c)?;
    }
    if file_ver >= 516 {
        let _loc_id = read_fstring(&mut c)?;
    }
    if file_ver >= 459 {
        let _gc = read_i32(&mut c)?;
        let _go = read_i32(&mut c)?;
    }
    let export_count = read_i32(&mut c)?;
    let export_offset = read_i32(&mut c)?;
    let import_count = read_i32(&mut c)?;
    let import_offset = read_i32(&mut c)?;

    // --- Name table ---
    let nt =
        NameTable::read(&mut c, name_count, name_offset).context("failed to read name table")?;

    if debug {
        eprintln!(
            "Header: file_ver={} ue5_ver={} names={} imports={} exports={}",
            file_ver, file_ver_ue5, name_count, import_count, export_count
        );
    }

    // --- Import table ---
    c.seek(SeekFrom::Start(import_offset as u64))?;
    let mut imports = Vec::with_capacity(import_count as usize);
    for _ in 0..import_count {
        let class_package = nt.fname(&mut c)?;
        let class_name = nt.fname(&mut c)?;
        let outer_index = read_i32(&mut c)?;
        let object_name = nt.fname(&mut c)?;
        if file_ver >= 518 {
            let _package_name = nt.fname(&mut c)?;
        }
        if file_ver_ue5 >= 1003 {
            // OPTIONAL_RESOURCES
            let _import_optional = read_i32(&mut c)?;
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
    c.seek(SeekFrom::Start(export_offset as u64))?;
    let mut export_headers = Vec::with_capacity(export_count as usize);
    for _ in 0..export_count {
        let class_index = read_i32(&mut c)?;
        let super_index = read_i32(&mut c)?;
        if file_ver >= 459 {
            let _template = read_i32(&mut c)?;
        }
        let outer_index = read_i32(&mut c)?;
        let object_name = nt.fname(&mut c)?;
        let _object_flags = read_u32(&mut c)?;
        let serial_size = read_i64(&mut c)?;
        let serial_offset = read_i64(&mut c)?;
        let _forced = read_i32(&mut c)?;
        let _not_client = read_i32(&mut c)?;
        let _not_server = read_i32(&mut c)?;
        if file_ver_ue5 < 1005 {
            // PackageGuid removed at REMOVE_OBJECT_EXPORT_PACKAGE_GUID
            let _guid = read_guid(&mut c)?;
        }
        if file_ver_ue5 >= 1006 {
            // TRACK_OBJECT_EXPORT_IS_INHERITED
            let _is_inherited = read_i32(&mut c)?;
        }
        let _pkg_flags = read_u32(&mut c)?;
        if file_ver >= 459 {
            let _not_always = read_i32(&mut c)?;
        }
        if file_ver >= 459 {
            let _is_asset = read_i32(&mut c)?;
        }
        if file_ver_ue5 >= 1003 {
            // OPTIONAL_RESOURCES
            let _gen_public_hash = read_i32(&mut c)?;
        }
        if file_ver >= 518 {
            let _first_dep = read_i32(&mut c)?;
            let _s_before_s = read_i32(&mut c)?;
            let _c_before_s = read_i32(&mut c)?;
            let _s_before_c = read_i32(&mut c)?;
            let _c_before_c = read_i32(&mut c)?;
        }
        if file_ver_ue5 >= 1010 {
            // SCRIPT_SERIALIZATION_OFFSET
            let _script_start = read_i64(&mut c)?;
            let _script_end = read_i64(&mut c)?;
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
            c.seek(SeekFrom::Start(hdr.serial_offset as u64))?;
            let end = hdr.serial_offset as u64 + hdr.serial_size as u64;
            let class_name = resolve_index(&imports, &export_names_pre, hdr.class_index);

            let is_struct = class_name.ends_with(".Function")
                || class_name.ends_with(".Struct")
                || class_name.ends_with(".BlueprintGeneratedClass")
                || class_name.ends_with(".ScriptStruct");
            if !is_struct {
                return Ok(read_properties(&mut c, &nt, end, ver));
            }

            let is_function = class_name.ends_with(".Function");
            let props = read_properties(&mut c, &nt, end, ver);
            let after_props = c.position();

            let mut extra_props = props;
            if after_props + 12 <= end {
                let _next = read_i32(&mut c)?;
                let super_ref = read_i32(&mut c)?;
                // UStruct::Children: array of export indices for child UField objects.
                // Separate from FField child properties below — these reference sub-structs
                // and functions, not the parameters/member variables parsed via FField.
                let children_count = read_i32(&mut c)?;
                if children_count > 0 && children_count < 1000 {
                    c.seek(SeekFrom::Current(children_count as i64 * 4))?;
                }
                if debug {
                    eprintln!(
                        "  {} UStruct: after_props={} next={} super={} children={} pos={}",
                        hdr.object_name,
                        after_props,
                        _next,
                        super_ref,
                        children_count,
                        c.position()
                    );
                }
                if super_ref != 0 {
                    let super_name = resolve_index(&imports, &export_names_pre, super_ref);
                    extra_props.push(Property {
                        name: "Super".into(),
                        value: PropValue::Name(short_class(&super_name)),
                    });
                }
            }

            // UStruct::ChildProperties (FField children)
            let mut ffield_children: Vec<(String, String, u64)> = Vec::new();
            if c.position() + 4 <= end {
                let child_prop_count = read_i32(&mut c)?;
                if debug && child_prop_count > 0 {
                    eprintln!(
                        "  {} child properties: {}",
                        hdr.object_name, child_prop_count
                    );
                }
                let mut ci = 0;
                loop {
                    if c.position() + 16 > end {
                        break;
                    }
                    // After reading the counted children, check for uncounted extras.
                    // Some UE4 assets serialize more FField children than the count
                    // indicates. Peek at the next FName: if it resolves to a known
                    // FField class (ends with "Property"), there's an extra child.
                    if ci >= child_prop_count {
                        if !nt.peek_is_ffield_class(&mut c)? {
                            break;
                        }
                        if debug {
                            eprintln!(
                                "  {} extra child property at {}",
                                hdr.object_name,
                                c.position()
                            );
                        }
                    }
                    let field_class = nt.fname(&mut c)?;
                    let field_name = nt.fname(&mut c)?;
                    let _flags = read_u32(&mut c)?;
                    nt.skip_metadata(&mut c)?;
                    let _array_dim = read_i32(&mut c)?;
                    let _elem_size = read_i32(&mut c)?;
                    let prop_flags = read_i64(&mut c)? as u64;
                    let mut rep_bytes = [0u8; 2];
                    c.read_exact(&mut rep_bytes)?;
                    let _rep_notify_func = nt.fname(&mut c)?;
                    let _bp_rep_condition = read_u8(&mut c)?;
                    let type_name = resolve_ffield_type(
                        &field_class,
                        &mut c,
                        &nt,
                        &imports,
                        &export_names_pre,
                        end,
                    )?;
                    ffield_children.push((field_name.clone(), type_name, prop_flags));
                    if debug {
                        eprintln!(
                            "    param: {} {} flags=0x{:x} @ {}",
                            field_class,
                            field_name,
                            prop_flags,
                            c.position()
                        );
                    }
                    ci += 1;
                }
            }

            if is_function && !ffield_children.is_empty() {
                let sig = format_signature(&hdr.object_name, &ffield_children);
                extra_props.push(Property {
                    name: "Signature".into(),
                    value: PropValue::Str(sig),
                });
            }

            if !is_function && !ffield_children.is_empty() {
                let members: Vec<PropValue> = ffield_children
                    .iter()
                    .map(|(name, type_name, _flags)| {
                        PropValue::Str(format!("{}: {}", name, type_name))
                    })
                    .collect();
                extra_props.push(Property {
                    name: "Members".into(),
                    value: PropValue::Array {
                        inner_type: "StrProperty".into(),
                        items: members,
                    },
                });
            }

            // Script bytecode
            let mut bytecode_data: Vec<u8> = Vec::new();
            let mut bytecode_size: i32 = 0;
            let mut storage_size: i32 = 0;
            if c.position() + 8 <= end {
                if debug {
                    let spos = c.position();
                    let peek_len = std::cmp::min(16, (end - spos) as usize);
                    let mut peek = vec![0u8; peek_len];
                    c.read_exact(&mut peek)?;
                    c.seek(SeekFrom::Start(spos))?;
                    let hex: Vec<String> = peek.iter().map(|b| format!("{:02x}", b)).collect();
                    eprintln!(
                        "  {} script @ {} (end={}) raw: {}",
                        hdr.object_name,
                        spos,
                        end,
                        hex.join(" ")
                    );
                }
                bytecode_size = read_i32(&mut c)?;
                storage_size = read_i32(&mut c)?;
                if storage_size > 0 && (c.position() + storage_size as u64) <= end {
                    bytecode_data = vec![0u8; storage_size as usize];
                    c.read_exact(&mut bytecode_data)?;
                    if debug {
                        eprintln!(
                            "  {} bytecode: {}B mem, {}B disk",
                            hdr.object_name, bytecode_size, storage_size
                        );
                        let show = std::cmp::min(bytecode_data.len(), 64);
                        let hex: Vec<String> = bytecode_data[..show]
                            .iter()
                            .map(|b| format!("{:02x}", b))
                            .collect();
                        eprintln!("    hex: {}", hex.join(" "));
                    }
                }
            }

            if !bytecode_data.is_empty() {
                let (stmts, final_mem_adj) = decode_bytecode(
                    &bytecode_data,
                    &nt,
                    &imports,
                    &export_names_pre,
                    ver.file_ver_ue5,
                );
                if debug {
                    // Drift validation: bytecodeSize is in-memory size, storageSize is on-disk.
                    // The difference should equal cumulative mem_adj (all +4/-N adjustments for
                    // FName, obj-ref, and FFieldPath size differences). Non-zero drift indicates
                    // a missed or incorrect mem_adj in the decoder.
                    let expected = bytecode_size - storage_size;
                    let drift = final_mem_adj - expected;
                    eprintln!(
                        "  {} mem_adj: final={} expected={} drift={}",
                        hdr.object_name, final_mem_adj, expected, drift
                    );
                }
                if !stmts.is_empty() {
                    extra_props.push(Property {
                        name: "Bytecode".into(),
                        value: PropValue::Array {
                            inner_type: "StrProperty".into(),
                            items: stmts
                                .iter()
                                .map(|s| {
                                    PropValue::Str(format!("{:04x}: {}", s.mem_offset, s.text))
                                })
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
                        extra_props.push(Property {
                            name: "BytecodeSummary".into(),
                            value: PropValue::Array {
                                inner_type: "StrProperty".into(),
                                items: structured.into_iter().map(PropValue::Str).collect(),
                            },
                        });
                    }
                }
            }

            if is_function && c.position() + 4 <= end {
                let func_flags = read_u32(&mut c)?;
                if func_flags != 0 {
                    extra_props.push(Property {
                        name: "FunctionFlags".into(),
                        value: PropValue::Str(format_func_flags(func_flags)),
                    });
                }
                if func_flags & 0x40 != 0 && c.position() + 2 <= end {
                    let _rep_offset = read_i32(&mut c)?;
                }
            }
            Ok(extra_props)
        })();

        exports.push((hdr.clone(), export_result.unwrap_or_default()));
    }

    Ok(ParsedAsset { imports, exports })
}
