//! Asset parser. Reads a `.uasset` byte slice sequentially:
//! 1. Package header (magic, version, table offsets)
//! 2. Name table, import table, export table
//! 3. Per-export tagged properties and bytecode

use anyhow::{ensure, Context, Result};
use std::collections::{BTreeMap, HashMap};
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::bytecode::names::K2NODE_PREFIX;
use crate::ffield::*;
use crate::pins::scan_for_pins;
use crate::properties::read_properties;
use crate::resolve::{class_of, format_func_flags, resolve_index, short_class};
use crate::types::*;

/// Package file magic number (first 4 bytes of every valid `.uasset`).
const PACKAGE_FILE_TAG: u32 = 0x9E2A83C1;

/// Package-level `EPackageFlags` bits that mark a cooked package. Cooked
/// assets split the header (`.uasset`) from the serialized data (`.uexp`)
/// and strip editor-only fields, so the editor/uncooked layout this parser
/// assumes (e.g. the +4 `WITH_CASE_PRESERVING_NAME` bytecode FName memory
/// adjustment) does not hold. Either bit set means the package is cooked:
/// `PKG_Cooked` (0x00000200) and `PKG_FilterEditorOnly` (0x80000000).
const PKG_COOKED: u32 = 0x0000_0200;
const PKG_FILTER_EDITOR_ONLY: u32 = 0x8000_0000;
const PKG_COOKED_MASK: u32 = PKG_COOKED | PKG_FILTER_EDITOR_ONLY;

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
    let pkg_flags = read_u32(reader)?;
    ensure!(
        pkg_flags & PKG_COOKED_MASK == 0,
        "cooked asset is not supported (PackageFlags {:#010X}): \
         this tool only parses uncooked editor .uasset files; cooked assets \
         split the header and .uexp data and strip editor-only fields",
        pkg_flags
    );
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
    let parsed_exports = parse_exports(&mut reader, &export_headers, &pctx, ver, file_size);

    if debug && !parsed_exports.pin_data.is_empty() {
        let total_links: usize = parsed_exports
            .pin_data
            .values()
            .flat_map(|pd| &pd.pins)
            .map(|pin| pin.linked_to.len())
            .sum();
        eprintln!(
            "  Pins: {} nodes parsed, {} total links",
            parsed_exports.pin_data.len(),
            total_links
        );
    }
    Ok(ParsedAsset {
        imports,
        exports: parsed_exports.exports,
        pin_data: parsed_exports.pin_data,
        function_signatures: parsed_exports.function_signatures,
        bytecode_by_export: parsed_exports.bytecode_by_export,
    })
}

/// Per-export parse products collected while walking the serialized export
/// data: the export headers paired with their tagged-property streams, the
/// EdGraph pin data per K2Node, the function call signatures, and the raw
/// captured bytecode keyed by 1-based export index.
struct ParsedExports {
    exports: Vec<(ExportHeader, Vec<Property>)>,
    pin_data: HashMap<usize, NodePinData>,
    function_signatures: BTreeMap<String, FunctionSignature>,
    bytecode_by_export: BTreeMap<usize, (Vec<u8>, u32)>,
}

/// What a single export's serialized walk yields: its property stream plus the
/// optional products that only some export kinds produce (the function call
/// signature for Function exports, captured script bytecode, EdGraph pin data
/// for K2Node/comment exports). The caller keys the optional products by
/// 1-based export index.
struct ExportProducts {
    props: Vec<Property>,
    signature: Option<FunctionSignature>,
    bytecode: Option<(Vec<u8>, u32)>,
    pin_data: Option<NodePinData>,
}

/// Read one export's serialized data: extension skip, tagged properties,
/// UStruct header, FField children, script bytecode, and function flags.
///
/// `pin_scan_hint` threads the rolling pin-scan offset hint across exports, the
/// caller carries it from one export to the next.
fn parse_one_export(
    reader: &mut Reader,
    hdr: &ExportHeader,
    pctx: &ParseCtx,
    ver: AssetVersion,
    pin_scan_hint: &mut Option<u64>,
) -> Result<ExportProducts> {
    reader.seek(SeekFrom::Start(hdr.serial_offset as u64))?;
    let end = hdr.serial_offset as u64 + hdr.serial_size as u64;
    let class_name = class_of(pctx.imports, pctx.export_names, hdr);
    let kind = classify_export(&class_name);

    // UE5.2+: extension byte before tagged property stream.
    // UE source gates this on bIsUClass in SerializeVersionedTaggedProperties,
    // but uncooked assets emit it for all exports (verified empirically).
    if ver.has_complete_type_name() {
        skip_serialization_extension(reader, pctx.name_table)?;
    }

    if kind == ExportKind::Other {
        let props = read_properties(reader, pctx.name_table, end, ver);
        let short = short_class(&class_name);
        let mut pin_data = None;
        if short.starts_with(K2NODE_PREFIX) || short == "EdGraphNode_Comment" {
            // K2Node subclasses serialize additional data between the
            // tagged property stream and the pin array. Scan forward
            // from the current position looking for the pin data
            // signature: deprecated_count(0) + reasonable pin_count.
            let (pins, new_hint) = scan_for_pins(reader, pctx.name_table, end, ver, *pin_scan_hint);
            *pin_scan_hint = new_hint;
            if let Some(pins) = pins {
                pin_data = Some(NodePinData { pins });
            }
        }
        return Ok(ExportProducts {
            props,
            signature: None,
            bytecode: None,
            pin_data,
        });
    }

    let is_function = kind == ExportKind::Function;
    let props = read_properties(reader, pctx.name_table, end, ver);
    let props_end_pos = reader.position();

    let mut extra_props = props;

    // UStruct header: Next, Super, Children
    parse_ustruct_header(
        reader,
        pctx,
        &mut extra_props,
        props_end_pos,
        end,
        &hdr.object_name,
    )?;

    // FField children (parameters / member variables)
    let ffield_children = parse_ffield_children(reader, pctx, end, &hdr.object_name)?;
    let mut signature = None;
    if is_function && !ffield_children.is_empty() {
        extra_props.push(Property {
            name: "Signature".into(),
            value: PropValue::Str(format_signature(&hdr.object_name, &ffield_children)),
        });
        signature = Some(build_function_signature(&ffield_children));
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
    let bytecode = capture_bytecode(reader, pctx, end, &hdr.object_name)?;

    // Function flags (after bytecode, only for Function exports)
    if is_function && reader.position() + 4 <= end {
        let func_flags = read_u32(reader)?;
        if func_flags != 0 {
            extra_props.push(Property {
                name: "FunctionFlags".into(),
                value: PropValue::Str(format_func_flags(func_flags)),
            });
        }
        if func_flags & FUNC_NET != 0 && reader.position() + 4 <= end {
            let _rep_offset = read_i32(reader)?;
        }
    }

    Ok(ExportProducts {
        props: extra_props,
        signature,
        bytecode,
        pin_data: None,
    })
}

/// Walk every export's serialized data, reading its tagged properties,
/// UStruct header, FField children, and script bytecode.
///
/// Out-of-range or empty exports get an empty property vector. Property
/// stream parse errors are recorded (logged when `pctx.debug`) and leave
/// that export with an empty vector rather than aborting the whole asset.
fn parse_exports(
    reader: &mut Reader,
    export_headers: &[ExportHeader],
    pctx: &ParseCtx,
    ver: AssetVersion,
    file_size: usize,
) -> ParsedExports {
    let mut exports = Vec::with_capacity(export_headers.len());
    let mut pin_data_map: HashMap<usize, NodePinData> = HashMap::new();
    let mut function_signatures: BTreeMap<String, FunctionSignature> = BTreeMap::new();
    let mut bytecode_by_export: BTreeMap<usize, (Vec<u8>, u32)> = BTreeMap::new();
    let mut pin_scan_hint: Option<u64> = None;
    for (ei, hdr) in export_headers.iter().enumerate() {
        if hdr.serial_size <= 0
            || hdr.serial_offset < 0
            || (hdr.serial_offset + hdr.serial_size) > file_size as i64
        {
            exports.push((hdr.clone(), Vec::new()));
            continue;
        }

        match parse_one_export(reader, hdr, pctx, ver, &mut pin_scan_hint) {
            Ok(products) => {
                exports.push((hdr.clone(), products.props));
                if let Some(sig) = products.signature {
                    function_signatures.insert(hdr.object_name.clone(), sig);
                }
                if let Some(bytecode) = products.bytecode {
                    bytecode_by_export.insert(ei + 1, bytecode);
                }
                if let Some(pin_data) = products.pin_data {
                    pin_data_map.insert(ei + 1, pin_data);
                }
            }
            Err(e) => {
                if pctx.debug {
                    eprintln!("  {} parse error: {}", hdr.object_name, e);
                }
                exports.push((hdr.clone(), Vec::new()));
            }
        }
    }

    ParsedExports {
        exports,
        pin_data: pin_data_map,
        function_signatures,
        bytecode_by_export,
    }
}

/// Build a `FunctionSignature` from raw FField child triples. The return
/// type is the slot whose flags carry `CPF_RETURN_PARM`, the input list is
/// every entry with `CPF_PARM`. Member variables (no `CPF_PARM`) are
/// skipped, the signature is for the function call ABI.
fn build_function_signature(children: &[(String, String, u64)]) -> FunctionSignature {
    let mut params = Vec::new();
    let mut return_type = None;
    for (name, type_name, flags) in children {
        if flags & CPF_RETURN_PARM != 0 {
            return_type = Some(type_name.clone());
        } else if flags & CPF_PARM != 0 {
            params.push(ParamInfo {
                name: name.clone(),
                type_name: type_name.clone(),
                flags: *flags,
            });
        }
    }
    FunctionSignature {
        params,
        return_type,
    }
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
    // Read declared children
    for _ in 0..child_prop_count {
        if reader.position() + 16 > end {
            break;
        }
        children.push(read_one_ffield_child(reader, pctx, end)?);
    }
    // Read undeclared trailing children: some UE versions emit more children than declared
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

/// Capture the raw script bytecode block at the current reader position.
///
/// Returns the `(disk_bytes, mem_size)` pair so callers can hand the raw
/// bytes to the decoder without having to re-locate the block. Decoding
/// and structuring happen later in the pipeline; this only advances the
/// reader past the block and captures the bytes. Returns `None` when there's
/// no bytecode block (header truncated or `storage_size <= 0`).
fn capture_bytecode(
    reader: &mut Reader,
    pctx: &ParseCtx,
    end: u64,
    name: &str,
) -> Result<Option<(Vec<u8>, u32)>> {
    if reader.position() + 8 > end {
        return Ok(None);
    }
    if pctx.debug {
        debug_peek_script(reader, name, end)?;
    }

    let bytecode_size = read_i32(reader)?;
    let storage_size = read_i32(reader)?;
    if storage_size <= 0 || (reader.position() + storage_size as u64) > end {
        return Ok(None);
    }
    let mut bytecode_data = vec![0u8; storage_size as usize];
    reader.read_exact(&mut bytecode_data)?;
    if pctx.debug {
        debug_bytecode_hex(&bytecode_data, name, bytecode_size, storage_size);
    }

    Ok(Some((bytecode_data, bytecode_size.max(0) as u32)))
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn helm_fixture_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("samples")
            .join("ue_4.27")
            .join("Helm_BP.uasset")
    }

    /// Walk the package summary exactly as [`read_package_header`] does, up
    /// to (but not consuming) the `PackageFlags` u32, and return its byte
    /// offset. Derived rather than hardcoded because the `folder_name`
    /// FString preceding it has a variable length.
    fn package_flags_offset(data: &[u8]) -> u64 {
        let mut reader = std::io::Cursor::new(data);
        let _magic = read_u32(&mut reader).unwrap();
        let legacy_ver = read_i32(&mut reader).unwrap();
        if legacy_ver < LEGACY_VER_UE3_COMPAT && legacy_ver != -4 {
            let _ue3_ver = read_i32(&mut reader).unwrap();
        }
        let _file_ver = read_i32(&mut reader).unwrap();
        if legacy_ver <= LEGACY_VER_UE5_START {
            let _file_ver_ue5 = read_i32(&mut reader).unwrap();
        }
        let _licensee_ver = read_i32(&mut reader).unwrap();
        let custom_ver_count = read_i32(&mut reader).unwrap();
        reader
            .seek(SeekFrom::Current(custom_ver_count as i64 * 20))
            .unwrap();
        let _total_header_size = read_i32(&mut reader).unwrap();
        let _folder_name = read_fstring(&mut reader).unwrap();
        reader.position()
    }

    #[test]
    fn uncooked_fixture_parses() {
        let data = std::fs::read(helm_fixture_path()).expect("read Helm_BP fixture");
        parse_asset(&data, false).expect("uncooked fixture should parse");
    }

    #[test]
    fn cooked_flag_is_rejected() {
        let mut data = std::fs::read(helm_fixture_path()).expect("read Helm_BP fixture");
        let offset = package_flags_offset(&data) as usize;

        // Sanity: the unmodified fixture has no cooked bit set.
        let original = u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap());
        assert_eq!(
            original & PKG_COOKED_MASK,
            0,
            "test fixture unexpectedly already marked cooked"
        );

        // Flip the PKG_FilterEditorOnly bit to simulate a cooked package.
        let cooked = original | PKG_FILTER_EDITOR_ONLY;
        data[offset..offset + 4].copy_from_slice(&cooked.to_le_bytes());

        let temp_path = std::env::temp_dir().join("bp_inspect_cooked_helm_test.uasset");
        std::fs::write(&temp_path, &data).expect("write temp cooked fixture");
        let cooked_data = std::fs::read(&temp_path).expect("read temp cooked fixture");
        let _ = std::fs::remove_file(&temp_path);

        let err = match parse_asset(&cooked_data, false) {
            Ok(_) => panic!("cooked asset should be rejected"),
            Err(error) => error.to_string(),
        };
        assert!(
            err.contains("cooked asset is not supported"),
            "expected cooked-asset rejection message, got: {err}"
        );
    }
}
