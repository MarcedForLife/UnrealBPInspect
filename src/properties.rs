//! Tagged property deserializer for UE4 and UE5 exports.
//!
//! UE4 uses `FPropertyTag` (explicit Type/StructName/EnumName fields).
//! UE5.2+ (version >= 1012) uses `FPropertyTypeName` (recursive type descriptor, flags byte).

use anyhow::{ensure, Context, Result};
use sha2::{Digest, Sha256};
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::property_type::{PropertyType, PROPERTY_CLASS_SUFFIX};
use crate::types::*;

/// Immutable context for property reading.
struct PropCtx<'a> {
    name_table: &'a NameTable,
    soft_object_paths: &'a [String],
    ver: AssetVersion,
}

// UE5.2+ FPropertyTypeName: recursive type descriptor
struct PropertyTypeInfo {
    type_name: String,
    inners: Vec<PropertyTypeInfo>,
}

impl PropertyTypeInfo {
    fn inner_name(&self, index: usize) -> String {
        self.inners
            .get(index)
            .map(|i| i.type_name.clone())
            .unwrap_or_default()
    }
}

fn read_property_type_name(reader: &mut Reader, ctx: &PropCtx) -> Result<PropertyTypeInfo> {
    read_property_type_name_depth(reader, ctx, 0)
}

fn read_property_type_name_depth(
    reader: &mut Reader,
    ctx: &PropCtx,
    depth: u32,
) -> Result<PropertyTypeInfo> {
    anyhow::ensure!(depth < 8, "FPropertyTypeName recursion too deep");
    let type_name = ctx.name_table.fname(reader)?;
    let inner_count = read_i32(reader)?;
    anyhow::ensure!(
        (0..=4).contains(&inner_count),
        "FPropertyTypeName inner count {} out of range",
        inner_count
    );
    let mut inners = Vec::new();
    for _ in 0..inner_count {
        inners.push(read_property_type_name_depth(reader, ctx, depth + 1)?);
    }
    Ok(PropertyTypeInfo { type_name, inners })
}

// UE5.2+ property tag flags byte (replaces ArrayIndex + HasPropertyGuid)
const TAG_HAS_ARRAY_INDEX: u8 = 0x01;
const TAG_HAS_PROPERTY_GUID: u8 = 0x02;
const TAG_HAS_PROPERTY_EXTENSIONS: u8 = 0x04;
const TAG_BOOL_TRUE: u8 = 0x10;

// Shared metadata, populated differently by UE4 (from tag fields) and UE5 (from PropertyTypeInfo)
#[derive(Default)]
struct PropertyMeta {
    /// Struct type for this value or its array elements/map values.
    struct_type: String,
    /// EnumProperty/ByteProperty: the enum's full path
    enum_name: String,
    /// ArrayProperty/SetProperty: the element type name
    inner_type: String,
    /// MapProperty: the key type name
    key_type: String,
    /// MapProperty: the value type name
    value_type: String,
}

fn format_delegate_binding(reader: &mut Reader, name_table: &NameTable) -> Result<String> {
    let obj = read_i32(reader)?;
    let func = name_table.fname(reader)?;
    Ok(if obj != 0 {
        format!("{}::{}", obj, func)
    } else {
        func
    })
}

/// Append tagged properties, preserving the successfully read prefix on failure.
/// Returns whether a None terminator was read, rather than reaching the boundary.
pub fn read_properties(
    reader: &mut Reader,
    name_table: &NameTable,
    soft_object_paths: &[String],
    end_offset: u64,
    ver: AssetVersion,
    props: &mut Vec<Property>,
) -> Result<bool> {
    let ctx = PropCtx {
        name_table,
        soft_object_paths,
        ver,
    };
    if ver.has_complete_type_name() {
        return read_properties_ue5(reader, &ctx, end_offset, props);
    }
    loop {
        if reader.position() == end_offset {
            return Ok(false);
        }
        ensure!(
            reader.position() + 8 <= end_offset,
            "truncated property name"
        );
        let (prop_name, is_none) = ctx.name_table.fname_is_none(reader)?;
        if is_none {
            return Ok(true);
        }
        ensure!(
            reader.position() + 16 <= end_offset,
            "truncated tag for {prop_name}"
        );
        let type_name = ctx.name_table.fname(reader)?;
        ensure!(
            type_name.ends_with(PROPERTY_CLASS_SUFFIX),
            "invalid property type {type_name} for {prop_name}"
        );
        let size = read_i32(reader)?;
        let _array_index = read_i32(reader)?;
        ensure!(size >= 0, "negative property size for {prop_name}");
        let value = read_property_value_ue4(reader, &ctx, &type_name, size)
            .with_context(|| format!("cannot read property {prop_name}"))?;
        ensure!(
            reader.position() <= end_offset,
            "property {prop_name} exceeds its containing stream"
        );
        props.push(Property {
            name: prop_name,
            value,
        });
    }
}

// UE4 tag preamble: type-specific fields, PropertyGuid, then shared reader
fn read_property_value_ue4(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    size: i32,
) -> Result<PropValue> {
    let file_ver = ctx.ver.file_ver;
    let property_type = PropertyType::from_fname(type_name);

    // BoolProperty has a unique UE4 layout: value byte before PropertyGuid
    if property_type == PropertyType::Bool {
        let val = read_u8(reader)? != 0;
        if file_ver >= VER_UE4_PROPERTY_GUID {
            let has_guid = read_u8(reader)?;
            if has_guid != 0 {
                let _guid = read_guid(reader)?;
            }
        }
        return Ok(PropValue::Bool(val));
    }

    // Build metadata from tag-specific fields
    let mut meta = PropertyMeta::default();
    match property_type {
        PropertyType::Struct => {
            meta.struct_type = ctx.name_table.fname(reader)?;
            let _struct_guid = read_guid(reader)?;
        }
        PropertyType::Array => meta.inner_type = ctx.name_table.fname(reader)?,
        PropertyType::Set => meta.inner_type = ctx.name_table.fname(reader)?,
        PropertyType::Map => {
            meta.key_type = ctx.name_table.fname(reader)?;
            meta.value_type = ctx.name_table.fname(reader)?;
        }
        PropertyType::Enum => meta.enum_name = ctx.name_table.fname(reader)?,
        PropertyType::Byte => meta.enum_name = ctx.name_table.fname(reader)?,
        _ => {}
    }
    skip_property_guid(reader, file_ver)?;

    // The cursor is now past all tag-specific fields; value data is next.
    let value_data_end = reader.position() + size as u64;
    ensure!(
        value_data_end <= reader.get_ref().len() as u64,
        "property payload exceeds available data"
    );

    let value = read_value_with_meta(reader, ctx, type_name, size, &meta, value_data_end)?;
    ensure!(
        reader.position() <= value_data_end,
        "property exceeds its declared size"
    );

    // Ensure cursor is at the correct position after the value
    match property_type {
        PropertyType::Struct | PropertyType::Array | PropertyType::Map | PropertyType::Set => {
            reader.seek(SeekFrom::Start(value_data_end))?;
        }
        _ => {}
    }
    Ok(value)
}

fn skip_property_guid(reader: &mut Reader, file_ver: i32) -> Result<()> {
    if file_ver >= VER_UE4_PROPERTY_GUID {
        let has_guid = read_u8(reader)?;
        if has_guid != 0 {
            let _guid = read_guid(reader)?;
        }
    }
    Ok(())
}

// UE5.2+ tagged property reader
fn read_properties_ue5(
    reader: &mut Reader,
    ctx: &PropCtx,
    end_offset: u64,
    props: &mut Vec<Property>,
) -> Result<bool> {
    loop {
        if reader.position() == end_offset {
            return Ok(false);
        }
        ensure!(
            reader.position() + 8 <= end_offset,
            "truncated property name"
        );
        let (prop_name, is_none) = ctx.name_table.fname_is_none(reader)?;
        if is_none {
            return Ok(true);
        }
        let type_info = read_property_type_name(reader, ctx)?;
        ensure!(
            type_info.type_name.ends_with(PROPERTY_CLASS_SUFFIX),
            "invalid property type {} for {prop_name}",
            type_info.type_name
        );
        let size = read_i32(reader)?;
        let flags = read_u8(reader)?;
        if flags & TAG_HAS_ARRAY_INDEX != 0 {
            read_i32(reader)?;
        }
        if flags & TAG_HAS_PROPERTY_GUID != 0 {
            read_guid(reader)?;
        }
        if flags & TAG_HAS_PROPERTY_EXTENSIONS != 0 {
            let extension = read_u8(reader)?;
            if extension & 0x02 != 0 {
                read_u8(reader)?;
                read_u8(reader)?;
            }
        }
        ensure!(size >= 0, "negative property size for {prop_name}");
        let value_end = reader.position() + size as u64;
        ensure!(
            value_end <= end_offset,
            "property {prop_name} exceeds its containing stream"
        );
        let value = read_property_value_ue5(reader, ctx, &type_info, size, flags)
            .with_context(|| format!("cannot read property {prop_name}"))?;
        ensure!(
            reader.position() <= value_end,
            "property {prop_name} exceeds its declared size"
        );
        reader.seek(SeekFrom::Start(value_end))?;
        props.push(Property {
            name: prop_name,
            value,
        });
    }
}

fn read_property_value_ue5(
    reader: &mut Reader,
    ctx: &PropCtx,
    ti: &PropertyTypeInfo,
    size: i32,
    flags: u8,
) -> Result<PropValue> {
    // BoolProperty: value encoded in flags, no payload
    if PropertyType::from_fname(&ti.type_name) == PropertyType::Bool {
        return Ok(PropValue::Bool(flags & TAG_BOOL_TRUE != 0));
    }

    let meta = PropertyMeta {
        struct_type: match PropertyType::from_fname(&ti.type_name) {
            PropertyType::Array | PropertyType::Set => ti
                .inners
                .first()
                .map(|inner| inner.inner_name(0))
                .unwrap_or_default(),
            PropertyType::Map => ti
                .inners
                .get(1)
                .map(|inner| inner.inner_name(0))
                .unwrap_or_default(),
            _ => ti.inner_name(0),
        },
        enum_name: ti.inner_name(0),
        inner_type: ti.inner_name(0),
        key_type: ti.inner_name(0),
        value_type: ti.inner_name(1),
    };
    let value_data_end = reader.position() + size as u64;
    read_value_with_meta(reader, ctx, &ti.type_name, size, &meta, value_data_end)
}

// Primitive value reader: integers, floats, names, objects, strings
fn read_primitive_value(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
) -> Result<Option<PropValue>> {
    match PropertyType::from_fname(type_name) {
        PropertyType::Int | PropertyType::Int32 | PropertyType::UInt32 => {
            Ok(Some(PropValue::Int(read_i32(reader)?)))
        }
        PropertyType::Int8 => Ok(Some(PropValue::Int(read_u8(reader)? as i8 as i32))),
        PropertyType::Int16 | PropertyType::UInt16 => {
            let mut b = [0u8; 2];
            reader.read_exact(&mut b)?;
            Ok(Some(PropValue::Int(i16::from_le_bytes(b) as i32)))
        }
        PropertyType::Int64 | PropertyType::UInt64 => Ok(Some(PropValue::Int64(read_i64(reader)?))),
        PropertyType::Float => Ok(Some(PropValue::Float(read_f32(reader)?))),
        PropertyType::Double => Ok(Some(PropValue::Double(read_f64(reader)?))),
        PropertyType::Name => Ok(Some(PropValue::Name(ctx.name_table.fname(reader)?))),
        PropertyType::Object => Ok(Some(PropValue::Object(read_i32(reader)?))),
        PropertyType::SoftObject => read_soft_object_value(reader, ctx)
            .map(PropValue::SoftObject)
            .map(Some),
        PropertyType::Str => Ok(Some(PropValue::Str(read_fstring(reader)?))),
        _ => Ok(None),
    }
}

fn read_name_reference(reader: &mut Reader, name_table: &NameTable) -> Result<String> {
    let start = reader.position();
    let index = read_i32(reader)?;
    let number = read_i32(reader)?;
    ensure!(
        index >= 0 && number >= 0 && name_table.get(index) != "?",
        "invalid name reference"
    );
    reader.set_position(start);
    name_table.fname(reader)
}

fn read_soft_path_string(reader: &mut Reader) -> Result<String> {
    let length = read_i32(reader)?;
    if length == 0 {
        return Ok(String::new());
    }
    let byte_count = u64::from(length.unsigned_abs()) * if length < 0 { 2 } else { 1 };
    let start = reader.position();
    let end = start
        .checked_add(byte_count)
        .context("soft object subpath length overflow")?;
    let payload = reader
        .get_ref()
        .get(start as usize..usize::try_from(end)?)
        .context("soft object subpath exceeds available data")?;
    let value = if length > 0 {
        ensure!(
            payload.last() == Some(&0),
            "soft object subpath has no terminator"
        );
        String::from_utf8(payload[..payload.len() - 1].to_vec())
            .context("invalid UTF-8 soft object subpath")?
    } else {
        ensure!(
            payload.ends_with(&[0, 0]),
            "soft object subpath has no terminator"
        );
        let characters: Vec<u16> = payload[..payload.len() - 2]
            .as_chunks::<2>()
            .0
            .iter()
            .map(|bytes| u16::from_le_bytes([bytes[0], bytes[1]]))
            .collect();
        String::from_utf16(&characters).context("invalid UTF-16 soft object subpath")?
    };
    reader.set_position(end);
    Ok(value)
}

fn read_soft_object_value(reader: &mut Reader, ctx: &PropCtx) -> Result<String> {
    if ctx.soft_object_paths.is_empty() {
        return read_soft_object_path(reader, ctx.name_table, ctx.ver);
    }
    let index = read_i32(reader)?;
    ctx.soft_object_paths
        .get(usize::try_from(index).context("negative soft object path index")?)
        .cloned()
        .with_context(|| format!("soft object path index {index} exceeds package table"))
}

pub(crate) fn read_soft_object_path(
    reader: &mut Reader,
    name_table: &NameTable,
    version: AssetVersion,
) -> Result<String> {
    // UE4's ADDED_SOFT_OBJECT_PATH changed FString to FName plus subpath at 514.
    if version.file_ver < 514 {
        return read_soft_path_string(reader);
    }
    let first_name = read_name_reference(reader, name_table)?;
    // FSOFTOBJECTPATH_REMOVE_ASSET_PATH_FNAMES introduced FTopLevelAssetPath at 1007.
    let mut path = if version.file_ver_ue5 >= 1007 {
        let asset_name = read_name_reference(reader, name_table)?;
        if first_name == "None" && asset_name == "None" {
            String::new()
        } else {
            format!("{first_name}.{asset_name}")
        }
    } else if first_name == "None" {
        String::new()
    } else {
        first_name
    };
    let subpath = read_soft_path_string(reader)?;
    if !subpath.is_empty() {
        path.push(':');
        path.push_str(&subpath);
    }
    Ok(path)
}

// Shared value reader, used after metadata extraction from either tag format
fn read_value_with_meta(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    size: i32,
    meta: &PropertyMeta,
    value_data_end: u64,
) -> Result<PropValue> {
    let value_start = reader.position();
    if let Some(val) = read_primitive_value(reader, ctx, type_name)? {
        if PropertyType::from_fname(type_name) == PropertyType::SoftObject {
            ensure!(
                reader.position() <= value_data_end,
                "soft object path exceeds its declared size"
            );
            if reader.position() < value_data_end {
                return read_unknown_value(reader, type_name, value_start, value_data_end);
            }
        }
        return Ok(val);
    }
    match PropertyType::from_fname(type_name) {
        PropertyType::Text => read_text_property(reader, size).map(PropValue::Text),

        PropertyType::Enum => {
            let value = ctx.name_table.fname(reader)?;
            Ok(PropValue::Enum {
                enum_name: meta.enum_name.clone(),
                value,
            })
        }
        PropertyType::Byte => {
            if size == 1 {
                Ok(PropValue::Byte {
                    enum_name: meta.enum_name.clone(),
                    value: read_u8(reader)?.to_string(),
                })
            } else {
                Ok(PropValue::Byte {
                    enum_name: meta.enum_name.clone(),
                    value: ctx.name_table.fname(reader)?,
                })
            }
        }

        PropertyType::Struct => read_struct_property(reader, ctx, meta, size, value_data_end),

        PropertyType::Array | PropertyType::Set => {
            if PropertyType::from_fname(type_name) == PropertyType::Set {
                let removed_count = read_i32(reader)?;
                ensure!(
                    reader.position() <= value_data_end,
                    "set removal count exceeds its declared size"
                );
                ensure!(removed_count >= 0, "negative set removal count");
                if removed_count != 0 {
                    return read_unknown_value(
                        reader,
                        &format!("{type_name}<{}>", meta.inner_type),
                        value_start,
                        value_data_end,
                    );
                }
            }
            let count = read_i32(reader)?;
            ensure!(count >= 0, "negative collection count");
            let items = if PropertyType::from_fname(type_name) == PropertyType::Array
                && PropertyType::from_fname(&meta.inner_type) == PropertyType::Struct
            {
                let Some(items) =
                    read_struct_array(reader, ctx, &meta.struct_type, count, value_data_end)?
                else {
                    return read_unknown_value(
                        reader,
                        &format!("{type_name}<{}>", meta.inner_type),
                        value_start,
                        value_data_end,
                    );
                };
                items
            } else {
                read_array_items(reader, ctx, &meta.inner_type, count, value_data_end)?
            };
            ensure!(
                reader.position() <= value_data_end,
                "collection exceeds its declared size"
            );
            if reader.position() < value_data_end
                || items.len() != count as usize
                || items
                    .iter()
                    .any(|item| matches!(item, PropValue::Unknown { .. }))
            {
                return read_unknown_value(
                    reader,
                    &format!("{type_name}<{}>", meta.inner_type),
                    value_start,
                    value_data_end,
                );
            }
            Ok(PropValue::Array {
                inner_type: meta.inner_type.clone(),
                items,
            })
        }

        PropertyType::Map => read_map_value(reader, ctx, type_name, meta, value_data_end),

        PropertyType::Delegate => {
            format_delegate_binding(reader, ctx.name_table).map(PropValue::Str)
        }

        PropertyType::MulticastDelegate
        | PropertyType::MulticastInlineDelegate
        | PropertyType::MulticastSparseDelegate => {
            let count = read_i32(reader)?;
            let mut bindings = Vec::new();
            for _ in 0..count {
                bindings.push(PropValue::Str(format_delegate_binding(
                    reader,
                    ctx.name_table,
                )?));
            }
            Ok(PropValue::Array {
                inner_type: "DelegateProperty".into(),
                items: bindings,
            })
        }

        _ => read_unknown_value(reader, type_name, value_start, value_data_end),
    }
}

fn read_struct_property(
    reader: &mut Reader,
    ctx: &PropCtx,
    meta: &PropertyMeta,
    size: i32,
    value_data_end: u64,
) -> Result<PropValue> {
    let value_start = reader.position();
    if meta.struct_type == "SoftObjectPath" {
        let path = read_soft_object_value(reader, ctx)?;
        ensure!(
            reader.position() <= value_data_end,
            "soft object path exceeds its declared size"
        );
        if reader.position() != value_data_end {
            return read_unknown_value(reader, &meta.struct_type, value_start, value_data_end);
        }
        return Ok(PropValue::SoftObject(path));
    }
    if meta.struct_type == "EdGraphPinType" {
        let payload = reader
            .get_ref()
            .get(value_start as usize..value_data_end as usize)
            .context("pin type payload exceeds available data")?;
        let mut bounded = std::io::Cursor::new(payload);
        if let Ok(fields) = read_edgraph_pin_type(&mut bounded, ctx.name_table, ctx.ver.is_lwc()) {
            if bounded.position() == payload.len() as u64 {
                reader.set_position(value_data_end);
                return Ok(PropValue::Struct {
                    struct_type: meta.struct_type.clone(),
                    fields,
                });
            }
        }
        return read_unknown_value(reader, &meta.struct_type, value_start, value_data_end);
    }
    let struct_end = reader.position() + size as u64;
    let fields = read_struct_value(reader, ctx, &meta.struct_type, size, struct_end)?;
    ensure!(
        reader.position() <= struct_end,
        "struct exceeds its declared size"
    );
    if reader.position() < struct_end {
        return read_unknown_value(reader, &meta.struct_type, value_start, struct_end);
    }
    reader.seek(SeekFrom::Start(struct_end))?;
    Ok(PropValue::Struct {
        struct_type: meta.struct_type.clone(),
        fields,
    })
}

fn read_map_value(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    meta: &PropertyMeta,
    value_data_end: u64,
) -> Result<PropValue> {
    let value_start = reader.position();
    let descriptor = format!("{type_name}<{}, {}>", meta.key_type, meta.value_type);
    let removed_count = read_i32(reader)?;
    ensure!(
        reader.position() <= value_data_end,
        "map removal count exceeds its declared size"
    );
    ensure!(removed_count >= 0, "negative map removal count");
    if removed_count != 0 {
        return read_unknown_value(reader, &descriptor, value_start, value_data_end);
    }
    let count = read_i32(reader)?;
    ensure!(count >= 0, "negative map count");
    let mut entries = Vec::new();
    for _ in 0..count {
        ensure!(
            reader.position() < value_data_end,
            "map has fewer entries than declared"
        );
        let key = read_typed_value(reader, ctx, &meta.key_type, "", value_data_end)?;
        ensure!(
            reader.position() <= value_data_end,
            "map key exceeds its declared size"
        );
        let opaque_key = matches!(key, PropValue::Unknown { .. });
        if opaque_key {
            // Without element boundaries, preserve the complete map.
            return read_unknown_value(reader, &descriptor, value_start, value_data_end);
        }
        let val = read_typed_value(
            reader,
            ctx,
            &meta.value_type,
            &meta.struct_type,
            value_data_end,
        )?;
        ensure!(
            reader.position() <= value_data_end,
            "map value exceeds its declared size"
        );
        if matches!(val, PropValue::Unknown { .. }) {
            return read_unknown_value(reader, &descriptor, value_start, value_data_end);
        }
        entries.push((key, val));
    }
    ensure!(
        reader.position() <= value_data_end,
        "map exceeds its declared size"
    );
    if reader.position() < value_data_end {
        return read_unknown_value(reader, &descriptor, value_start, value_data_end);
    }
    Ok(PropValue::Map {
        key_type: meta.key_type.clone(),
        value_type: meta.value_type.clone(),
        entries,
    })
}

fn read_unknown_value(
    reader: &mut Reader,
    type_name: &str,
    start_offset: u64,
    end_offset: u64,
) -> Result<PropValue> {
    let start = usize::try_from(start_offset)?;
    let end = usize::try_from(end_offset)?;
    let payload = reader
        .get_ref()
        .get(start..end)
        .context("opaque property payload exceeds available data")?;
    let size = i32::try_from(payload.len())?;
    let payload_sha256 = Sha256::digest(payload)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    reader.seek(SeekFrom::Start(end_offset))?;
    Ok(PropValue::Unknown {
        type_name: type_name.to_owned(),
        size,
        payload_sha256,
    })
}

fn has_property_tag(reader: &Reader, ctx: &PropCtx) -> bool {
    let mut probe = reader.clone();
    let Ok((_, is_none)) = ctx.name_table.fname_is_none(&mut probe) else {
        return false;
    };
    if is_none {
        return true;
    }
    let type_name = if ctx.ver.has_complete_type_name() {
        read_property_type_name(&mut probe, ctx).map(|info| info.type_name)
    } else {
        ctx.name_table.fname(&mut probe)
    };
    type_name.is_ok_and(|name| name.ends_with(PROPERTY_CLASS_SUFFIX))
}

fn read_typed_value(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    struct_type: &str,
    end_offset: u64,
) -> Result<PropValue> {
    if let Some(val) = read_primitive_value(reader, ctx, type_name)? {
        return Ok(val);
    }
    match PropertyType::from_fname(type_name) {
        PropertyType::Bool => Ok(PropValue::Bool(read_u8(reader)? != 0)),
        PropertyType::Byte => Ok(PropValue::Int(read_u8(reader)? as i32)),
        PropertyType::Enum => Ok(PropValue::Name(ctx.name_table.fname(reader)?)),
        PropertyType::Struct => {
            if struct_type == "SoftObjectPath" {
                return read_soft_object_value(reader, ctx).map(PropValue::SoftObject);
            }
            if !matches!(
                struct_type,
                "IntPoint" | "Vector" | "Rotator" | "Vector2D" | "LinearColor" | "Guid"
            ) && !has_property_tag(reader, ctx)
            {
                return read_unknown_value(reader, struct_type, reader.position(), end_offset);
            }
            let fields = read_struct_value(reader, ctx, struct_type, 0, end_offset)?;
            Ok(PropValue::Struct {
                struct_type: struct_type.into(),
                fields,
            })
        }
        _ => read_unknown_value(reader, type_name, reader.position(), end_offset),
    }
}

fn read_text_property(reader: &mut Reader, size: i32) -> Result<String> {
    if size <= 0 {
        return Ok(String::new());
    }
    let mut buf = vec![0u8; size as usize];
    reader.read_exact(&mut buf)?;
    let text = String::from_utf8_lossy(&buf);
    let readable: String = text
        .chars()
        .filter(|c| c.is_ascii_graphic() || *c == ' ')
        .collect();
    Ok(if readable.is_empty() {
        "<text>".to_string()
    } else {
        readable
    })
}

fn read_native_bool(reader: &mut Reader) -> Result<PropValue> {
    let value = read_i32(reader)?;
    ensure!(matches!(value, 0 | 1), "invalid native boolean {value}");
    Ok(PropValue::Bool(value != 0))
}

pub(crate) fn read_edgraph_pin_type(
    reader: &mut Reader,
    name_table: &NameTable,
    ue5: bool,
) -> Result<Vec<Property>> {
    let mut fields = Vec::new();
    for name in ["PinCategory", "PinSubCategory"] {
        fields.push(Property {
            name: name.into(),
            value: PropValue::Name(read_name_reference(reader, name_table)?),
        });
    }
    fields.push(Property {
        name: "PinSubCategoryObject".into(),
        value: PropValue::Object(read_i32(reader)?),
    });
    let container_type = read_u8(reader)?;
    let container_name = ["None", "Array", "Set", "Map"]
        .get(container_type as usize)
        .context("invalid pin container type")?;
    fields.push(Property {
        name: "ContainerType".into(),
        value: PropValue::Enum {
            enum_name: "EPinContainerType".into(),
            value: (*container_name).into(),
        },
    });
    if container_type == 3 {
        let mut terminal_fields = Vec::new();
        for name in ["TerminalCategory", "TerminalSubCategory"] {
            terminal_fields.push(Property {
                name: name.into(),
                value: PropValue::Name(read_name_reference(reader, name_table)?),
            });
        }
        terminal_fields.push(Property {
            name: "TerminalSubCategoryObject".into(),
            value: PropValue::Object(read_i32(reader)?),
        });
        for name in [
            "bTerminalIsConst",
            "bTerminalIsWeakPointer",
            "bTerminalIsUObjectWrapper",
        ] {
            terminal_fields.push(Property {
                name: name.into(),
                value: read_native_bool(reader)?,
            });
        }
        fields.push(Property {
            name: "PinValueType".into(),
            value: PropValue::Struct {
                struct_type: "EdGraphTerminalType".into(),
                fields: terminal_fields,
            },
        });
    }
    for name in ["bIsReference", "bIsWeakPointer"] {
        fields.push(Property {
            name: name.into(),
            value: read_native_bool(reader)?,
        });
    }
    let member_parent = PropValue::Object(read_i32(reader)?);
    let member_name = PropValue::Name(read_name_reference(reader, name_table)?);
    let member_guid = PropValue::Str(format!("{:02x?}", read_guid(reader)?));
    fields.push(Property {
        name: "PinSubCategoryMemberReference".into(),
        value: PropValue::Struct {
            struct_type: "SimpleMemberReference".into(),
            fields: vec![
                Property {
                    name: "MemberParent".into(),
                    value: member_parent,
                },
                Property {
                    name: "MemberName".into(),
                    value: member_name,
                },
                Property {
                    name: "MemberGuid".into(),
                    value: member_guid,
                },
            ],
        },
    });
    for name in ["bIsConst", "bIsUObjectWrapper"] {
        fields.push(Property {
            name: name.into(),
            value: read_native_bool(reader)?,
        });
    }
    if ue5 {
        fields.push(Property {
            name: "bSerializeAsSinglePrecisionFloat".into(),
            value: read_native_bool(reader)?,
        });
    }
    Ok(fields)
}

fn read_lwc_components(reader: &mut Reader, lwc: bool, names: &[&str]) -> Result<Vec<Property>> {
    let mut props = Vec::new();
    for name in names {
        let value = if lwc {
            PropValue::Double(read_f64(reader)?)
        } else {
            PropValue::Float(read_f32(reader)?)
        };
        props.push(Property {
            name: name.to_string(),
            value,
        });
    }
    Ok(props)
}

fn read_struct_value(
    reader: &mut Reader,
    ctx: &PropCtx,
    struct_type: &str,
    _size: i32,
    end_offset: u64,
) -> Result<Vec<Property>> {
    let lwc = ctx.ver.is_lwc();
    match struct_type {
        "IntPoint" => ["X", "Y"]
            .into_iter()
            .map(|name| {
                Ok(Property {
                    name: name.into(),
                    value: PropValue::Int(read_i32(reader)?),
                })
            })
            .collect(),
        "Vector" => read_lwc_components(reader, lwc, &["X", "Y", "Z"]),
        "Rotator" => read_lwc_components(reader, lwc, &["Pitch", "Yaw", "Roll"]),
        "Vector2D" => read_lwc_components(reader, lwc, &["X", "Y"]),
        "LinearColor" => {
            let red = read_f32(reader)?;
            let green = read_f32(reader)?;
            let blue = read_f32(reader)?;
            let alpha = read_f32(reader)?;
            Ok(vec![
                Property {
                    name: "R".into(),
                    value: PropValue::Float(red),
                },
                Property {
                    name: "G".into(),
                    value: PropValue::Float(green),
                },
                Property {
                    name: "B".into(),
                    value: PropValue::Float(blue),
                },
                Property {
                    name: "A".into(),
                    value: PropValue::Float(alpha),
                },
            ])
        }
        "Guid" => {
            let guid = read_guid(reader)?;
            Ok(vec![Property {
                name: "Guid".into(),
                value: PropValue::Str(format!("{:02x?}", guid)),
            }])
        }
        _ => {
            let mut fields = Vec::new();
            read_properties(
                reader,
                ctx.name_table,
                ctx.soft_object_paths,
                end_offset,
                ctx.ver,
                &mut fields,
            )?;
            Ok(fields)
        }
    }
}

/// Legacy arrays have one inner tag for the entire sequence, not one per item.
fn read_struct_array(
    reader: &mut Reader,
    ctx: &PropCtx,
    struct_type: &str,
    count: i32,
    end_offset: u64,
) -> Result<Option<Vec<PropValue>>> {
    let mut struct_type = struct_type.to_owned();
    if !ctx.ver.has_complete_type_name() {
        if reader.position() == end_offset && count == 0 {
            return Ok(Some(Vec::new()));
        }
        if !has_property_tag(reader, ctx) {
            return Ok(None);
        }
        let (_, is_none) = ctx.name_table.fname_is_none(reader)?;
        if is_none || ctx.name_table.fname(reader)? != "StructProperty" {
            return Ok(None);
        }
        let payload_size = read_i64(reader)?;
        ensure!(payload_size >= 0, "negative struct array payload size");
        struct_type = ctx.name_table.fname(reader)?;
        read_guid(reader)?;
        skip_property_guid(reader, ctx.ver.file_ver)?;
        ensure!(
            reader.position() <= end_offset,
            "struct array tag exceeds its declared size"
        );
        if payload_size as u64 != end_offset - reader.position() {
            return Ok(None);
        }
    }
    let mut items = Vec::new();
    for _ in 0..count {
        if reader.position() >= end_offset {
            return Ok(None);
        }
        let fields = match struct_type.as_str() {
            "IntPoint" | "Vector" | "Rotator" | "Vector2D" | "LinearColor" | "Guid" => {
                read_struct_value(reader, ctx, &struct_type, 0, end_offset)?
            }
            _ => {
                if !has_property_tag(reader, ctx) {
                    return Ok(None);
                }
                let mut fields = Vec::new();
                if !read_properties(
                    reader,
                    ctx.name_table,
                    ctx.soft_object_paths,
                    end_offset,
                    ctx.ver,
                    &mut fields,
                )? {
                    return Ok(None);
                }
                fields
            }
        };
        ensure!(
            reader.position() <= end_offset,
            "struct array item exceeds its declared size"
        );
        items.push(PropValue::Struct {
            struct_type: struct_type.clone(),
            fields,
        });
    }
    Ok(Some(items))
}

fn read_array_items(
    reader: &mut Reader,
    ctx: &PropCtx,
    inner_type: &str,
    count: i32,
    end_offset: u64,
) -> Result<Vec<PropValue>> {
    let mut items = Vec::new();
    for _ in 0..count {
        if reader.position() >= end_offset {
            ensure!(
                PropertyType::from_fname(inner_type) == PropertyType::Struct,
                "array has fewer items than declared"
            );
            break;
        }
        let item = read_typed_value(reader, ctx, inner_type, "", end_offset)?;
        if matches!(&item, PropValue::Unknown { .. }) {
            reader.seek(SeekFrom::Start(end_offset))?;
            items.push(item);
            break;
        }
        items.push(item);
    }
    Ok(items)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn synthetic_name(bytes: &mut Vec<u8>, index: i32) {
        bytes.extend(index.to_le_bytes());
        bytes.extend(0i32.to_le_bytes());
    }

    fn synthetic_inner_tag(payload: &[u8], struct_type: i32) -> Vec<u8> {
        let mut bytes = Vec::new();
        synthetic_name(&mut bytes, 1);
        synthetic_name(&mut bytes, 2);
        bytes.extend((payload.len() as i64).to_le_bytes());
        synthetic_name(&mut bytes, struct_type);
        bytes.extend([0; 16]);
        bytes.push(0);
        bytes.extend(payload);
        bytes
    }

    #[test]
    fn struct_array_inner_tag_describes_every_native_element() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "Entries".into(),
            "StructProperty".into(),
            "IntPoint".into(),
        ]);
        for file_ver_ue5 in [0, 1012] {
            let context = PropCtx {
                name_table: &name_table,
                soft_object_paths: &[],
                ver: AssetVersion {
                    file_ver: 522,
                    file_ver_ue5,
                },
            };
            for count in [0i32, 2] {
                let coordinates: Vec<u8> = [i32::MIN, 31, 47, i32::MAX]
                    .into_iter()
                    .take(count as usize * 2)
                    .flat_map(i32::to_le_bytes)
                    .collect();
                let mut payload = count.to_le_bytes().to_vec();
                payload.extend(if file_ver_ue5 == 0 {
                    synthetic_inner_tag(&coordinates, 3)
                } else {
                    coordinates
                });
                let mut reader = std::io::Cursor::new(payload.as_slice());
                let meta = PropertyMeta {
                    inner_type: "StructProperty".into(),
                    struct_type: "IntPoint".into(),
                    ..Default::default()
                };
                let value = read_value_with_meta(
                    &mut reader,
                    &context,
                    "ArrayProperty",
                    payload.len() as i32,
                    &meta,
                    payload.len() as u64,
                )
                .unwrap();
                let PropValue::Array { items, .. } = value else {
                    panic!("expected complete array");
                };
                assert_eq!(items.len(), count as usize);
                if count > 0 {
                    let PropValue::Struct {
                        struct_type,
                        fields,
                    } = &items[1]
                    else {
                        unreachable!()
                    };
                    assert_eq!(struct_type, "IntPoint");
                    assert!(matches!(fields[0].value, PropValue::Int(47)));
                    assert!(matches!(fields[1].value, PropValue::Int(i32::MAX)));
                }
                assert_eq!(reader.position(), payload.len() as u64);
            }
        }
    }

    #[test]
    fn tagged_struct_array_retains_element_boundaries_and_type() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "Entries".into(),
            "StructProperty".into(),
            "Settings".into(),
            "Value".into(),
            "IntProperty".into(),
        ]);
        for file_ver_ue5 in [0, 1012] {
            let context = PropCtx {
                name_table: &name_table,
                soft_object_paths: &[],
                ver: AssetVersion {
                    file_ver: 522,
                    file_ver_ue5,
                },
            };
            let mut elements = Vec::new();
            for value in [11i32, 22] {
                synthetic_name(&mut elements, 4);
                synthetic_name(&mut elements, 5);
                if file_ver_ue5 != 0 {
                    elements.extend(0i32.to_le_bytes());
                }
                elements.extend(4i32.to_le_bytes());
                if file_ver_ue5 == 0 {
                    elements.extend(0i32.to_le_bytes());
                }
                elements.push(0);
                elements.extend(value.to_le_bytes());
                synthetic_name(&mut elements, 0);
            }
            let mut payload = 2i32.to_le_bytes().to_vec();
            payload.extend(if file_ver_ue5 == 0 {
                synthetic_inner_tag(&elements, 3)
            } else {
                elements
            });
            let meta = PropertyMeta {
                inner_type: "StructProperty".into(),
                struct_type: "Settings".into(),
                ..Default::default()
            };
            let mut reader = std::io::Cursor::new(payload.as_slice());
            let value = read_value_with_meta(
                &mut reader,
                &context,
                "ArrayProperty",
                payload.len() as i32,
                &meta,
                payload.len() as u64,
            )
            .unwrap();
            let PropValue::Array { items, .. } = value else {
                panic!("expected complete array");
            };
            assert_eq!(items.len(), 2);
            for (item, expected) in items.iter().zip([11, 22]) {
                let PropValue::Struct {
                    struct_type,
                    fields,
                } = item
                else {
                    unreachable!()
                };
                assert_eq!(struct_type, "Settings");
                assert_eq!(fields.len(), 1);
                assert!(matches!(fields[0].value, PropValue::Int(value) if value == expected));
            }
        }
    }

    #[test]
    fn complete_type_names_preserve_native_map_value_identity() {
        let name_table = NameTable::from_names(vec!["None".into(), "Key".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 1012,
            },
        };
        let type_info = PropertyTypeInfo {
            type_name: "MapProperty".into(),
            inners: vec![
                PropertyTypeInfo {
                    type_name: "NameProperty".into(),
                    inners: vec![],
                },
                PropertyTypeInfo {
                    type_name: "StructProperty".into(),
                    inners: vec![PropertyTypeInfo {
                        type_name: "Guid".into(),
                        inners: vec![],
                    }],
                },
            ],
        };
        let mut payload = [0i32, 1]
            .into_iter()
            .flat_map(i32::to_le_bytes)
            .collect::<Vec<_>>();
        synthetic_name(&mut payload, 1);
        payload.extend(0u8..16);
        let mut reader = std::io::Cursor::new(payload.as_slice());
        let value =
            read_property_value_ue5(&mut reader, &context, &type_info, payload.len() as i32, 0)
                .unwrap();
        let PropValue::Map { entries, .. } = value else {
            panic!("expected native map");
        };
        assert_eq!(entries.len(), 1);
        assert!(matches!(&entries[0].0, PropValue::Name(name) if name == "Key"));
        assert!(
            matches!(&entries[0].1, PropValue::Struct { struct_type, fields } if struct_type == "Guid" && fields.len() == 1)
        );
        assert_eq!(reader.position(), payload.len() as u64);
    }

    #[test]
    fn unsupported_native_map_type_keeps_the_complete_payload_hash() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 1012,
            },
        };
        let meta = PropertyMeta {
            key_type: "IntProperty".into(),
            value_type: "StructProperty".into(),
            struct_type: "UnsupportedNative".into(),
            ..Default::default()
        };
        let mut payload: Vec<u8> = [0i32, 1, 42]
            .into_iter()
            .flat_map(i32::to_le_bytes)
            .collect();
        payload.extend([0xff; 16]);
        let mut reader = std::io::Cursor::new(payload.as_slice());
        let value = read_value_with_meta(
            &mut reader,
            &context,
            "MapProperty",
            payload.len() as i32,
            &meta,
            payload.len() as u64,
        )
        .unwrap();
        let PropValue::Unknown {
            size,
            payload_sha256,
            ..
        } = value
        else {
            panic!("native unknown map cannot be represented as tagged fields");
        };
        assert_eq!(size as usize, payload.len());
        let expected: String = Sha256::digest(&payload)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(payload_sha256, expected);
    }

    #[test]
    fn int_point_is_signed_and_truncation_is_an_error() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let payload: Vec<u8> = [i32::MIN, i32::MAX]
            .into_iter()
            .flat_map(i32::to_le_bytes)
            .collect();
        let meta = PropertyMeta {
            struct_type: "IntPoint".into(),
            ..Default::default()
        };
        let mut reader = std::io::Cursor::new(payload.as_slice());
        let value =
            read_value_with_meta(&mut reader, &context, "StructProperty", 8, &meta, 8).unwrap();
        let PropValue::Struct { fields, .. } = value else {
            unreachable!()
        };
        assert!(matches!(fields[0].value, PropValue::Int(i32::MIN)));
        assert!(matches!(fields[1].value, PropValue::Int(i32::MAX)));
        let mut reader = std::io::Cursor::new(&payload[..7]);
        assert!(
            read_value_with_meta(&mut reader, &context, "StructProperty", 7, &meta, 7).is_err()
        );
    }

    #[test]
    fn native_pin_type_preserves_container_members_flags_and_unknown_layouts() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "object".into(),
            "float".into(),
            "Handler".into(),
        ]);
        for file_ver_ue5 in [0, 1012] {
            let context = PropCtx {
                name_table: &name_table,
                soft_object_paths: &[],
                ver: AssetVersion {
                    file_ver: 522,
                    file_ver_ue5,
                },
            };
            let mut payload = Vec::new();
            synthetic_name(&mut payload, 1);
            synthetic_name(&mut payload, 0);
            payload.extend((-3i32).to_le_bytes());
            payload.push(3); // Map.
            synthetic_name(&mut payload, 2);
            synthetic_name(&mut payload, 0);
            for value in [-4i32, 1, 0, 1, 1, 0, -5] {
                payload.extend(value.to_le_bytes());
            }
            synthetic_name(&mut payload, 3);
            payload.extend(0u8..16);
            payload.extend([1i32, 0].into_iter().flat_map(i32::to_le_bytes));
            if file_ver_ue5 != 0 {
                payload.extend(1i32.to_le_bytes());
            }
            let meta = PropertyMeta {
                struct_type: "EdGraphPinType".into(),
                ..Default::default()
            };
            let mut reader = std::io::Cursor::new(payload.as_slice());
            let value = read_value_with_meta(
                &mut reader,
                &context,
                "StructProperty",
                payload.len() as i32,
                &meta,
                payload.len() as u64,
            )
            .unwrap();
            let PropValue::Struct { fields, .. } = value else {
                panic!("expected complete pin type");
            };
            assert!(fields.iter().any(|field| field.name == "PinValueType"
                && matches!(&field.value, PropValue::Struct { fields, .. } if fields.len() == 6)));
            assert!(fields.iter().any(|field| field.name == "bIsReference"
                && matches!(field.value, PropValue::Bool(true))));
            assert_eq!(
                fields
                    .iter()
                    .any(|field| field.name == "bSerializeAsSinglePrecisionFloat"),
                file_ver_ue5 != 0
            );
            payload.push(1); // Unknown extension cannot disappear.
            let mut reader = std::io::Cursor::new(payload.as_slice());
            assert!(matches!(
                read_value_with_meta(
                    &mut reader,
                    &context,
                    "StructProperty",
                    payload.len() as i32,
                    &meta,
                    payload.len() as u64
                )
                .unwrap(),
                PropValue::Unknown { .. }
            ));
        }
    }

    #[test]
    fn inline_soft_objects_preserve_asset_and_subobject_in_every_supported_layout() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "/Game/Test.Asset".into(),
            "/Game/Test".into(),
            "Asset".into(),
        ]);
        for (file_ver, file_ver_ue5) in [(513, 0), (522, 0), (522, 1006), (522, 1007), (522, 1012)]
        {
            let context = PropCtx {
                name_table: &name_table,
                soft_object_paths: &[],
                ver: AssetVersion {
                    file_ver,
                    file_ver_ue5,
                },
            };
            for subpath in ["", "Component.Nested"] {
                let expected = format!(
                    "/Game/Test.Asset{}",
                    if subpath.is_empty() {
                        String::new()
                    } else {
                        format!(":{subpath}")
                    }
                );
                let mut payload = Vec::new();
                if file_ver < 514 {
                    payload.extend((expected.len() as i32 + 1).to_le_bytes());
                    payload.extend(expected.as_bytes());
                    payload.push(0);
                } else {
                    if file_ver_ue5 >= 1007 {
                        synthetic_name(&mut payload, 2);
                        synthetic_name(&mut payload, 3);
                    } else {
                        synthetic_name(&mut payload, 1);
                    }
                    payload.extend((subpath.len() as i32 + 1).to_le_bytes());
                    payload.extend(subpath.as_bytes());
                    payload.push(0);
                }
                let mut reader = std::io::Cursor::new(payload.as_slice());
                let value =
                    read_primitive_value(&mut reader, &context, "SoftObjectProperty").unwrap();
                assert!(matches!(value, Some(PropValue::SoftObject(value)) if value == expected));
                assert_eq!(reader.position(), payload.len() as u64);
                let mut reader = std::io::Cursor::new(payload.as_slice());
                let meta = PropertyMeta {
                    struct_type: "SoftObjectPath".into(),
                    ..Default::default()
                };
                let value = read_value_with_meta(
                    &mut reader,
                    &context,
                    "StructProperty",
                    payload.len() as i32,
                    &meta,
                    payload.len() as u64,
                )
                .unwrap();
                assert!(matches!(value, PropValue::SoftObject(value) if value == expected));
            }
        }
    }

    #[test]
    fn inline_soft_objects_reject_invalid_names_and_truncated_subpaths() {
        let name_table = NameTable::from_names(vec!["None".into(), "/Game/Test.Asset".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        for name_index in [-1, 1, 999] {
            let mut payload = Vec::new();
            synthetic_name(&mut payload, name_index);
            payload.extend(i32::MAX.to_le_bytes());
            let mut reader = std::io::Cursor::new(payload.as_slice());
            assert!(read_primitive_value(&mut reader, &context, "SoftObjectProperty").is_err());
        }
    }

    #[test]
    fn soft_path_strings_reject_lossy_or_unterminated_encodings() {
        for (length, payload) in [
            (2i32, vec![b'a', b'b']),
            (2, vec![0xff, 0]),
            (-2, vec![b'a', 0, b'b', 0]),
            (-2, vec![0, 0xd8, 0, 0]),
            (-2, vec![0, 0xdc, 0, 0]),
        ] {
            let bytes = [length.to_le_bytes().to_vec(), payload].concat();
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            assert!(read_soft_path_string(&mut reader).is_err());
        }
        let expected = "Component.\u{1f680}";
        let characters: Vec<u16> = expected.encode_utf16().chain([0]).collect();
        let mut bytes = (-(characters.len() as i32)).to_le_bytes().to_vec();
        bytes.extend(characters.into_iter().flat_map(u16::to_le_bytes));
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        assert_eq!(read_soft_path_string(&mut reader).unwrap(), expected);
        assert_eq!(reader.position(), bytes.len() as u64);
    }

    #[test]
    fn indexed_soft_paths_share_resolution_and_reject_invalid_indices() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let soft_object_paths = vec![String::new(), "/Game/Test.Asset:Root.Child".into()];
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &soft_object_paths,
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 1008,
            },
        };
        for index in [-1i32, 0, 1, 2, i32::MAX] {
            for type_name in ["SoftObjectProperty", "StructProperty"] {
                let bytes = index.to_le_bytes();
                let mut reader = std::io::Cursor::new(bytes.as_slice());
                let meta = PropertyMeta {
                    struct_type: "SoftObjectPath".into(),
                    ..Default::default()
                };
                let result = read_value_with_meta(&mut reader, &context, type_name, 4, &meta, 4);
                if let Some(expected) = soft_object_paths.get(index as usize) {
                    assert!(
                        matches!(result.unwrap(), PropValue::SoftObject(value) if value == *expected)
                    );
                } else {
                    assert!(result.is_err());
                }
            }
        }
    }

    #[test]
    fn invalid_native_pin_names_keep_distinct_payload_hashes() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let meta = PropertyMeta {
            struct_type: "EdGraphPinType".into(),
            ..Default::default()
        };
        let mut hashes = Vec::new();
        for (index, number) in [(1i32, 0i32), (2, 0), (0, -1)] {
            let mut bytes = vec![0; 65];
            bytes[..4].copy_from_slice(&index.to_le_bytes());
            bytes[4..8].copy_from_slice(&number.to_le_bytes());
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let value =
                read_value_with_meta(&mut reader, &context, "StructProperty", 65, &meta, 65)
                    .unwrap();
            let PropValue::Unknown { payload_sha256, .. } = value else {
                panic!("invalid name must stay opaque");
            };
            assert!(!hashes.contains(&payload_sha256));
            hashes.push(payload_sha256);
        }
    }

    #[test]
    fn malformed_tag_preserves_preceding_properties() {
        let name_table =
            NameTable::from_names(vec!["None".into(), "Value".into(), "IntProperty".into()]);
        for version in [
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 1012,
            },
        ] {
            let mut bytes = Vec::new();
            for value in [1i32, 0, 2, 0] {
                bytes.extend(value.to_le_bytes());
            }
            if version.has_complete_type_name() {
                bytes.extend(0i32.to_le_bytes());
            }
            bytes.extend(4i32.to_le_bytes());
            if !version.has_complete_type_name() {
                bytes.extend(0i32.to_le_bytes());
            }
            bytes.push(0);
            bytes.extend(42i32.to_le_bytes());
            bytes.extend(1i32.to_le_bytes());
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let mut properties = Vec::new();
            let error = read_properties(
                &mut reader,
                &name_table,
                &[],
                bytes.len() as u64,
                version,
                &mut properties,
            )
            .unwrap_err();
            assert!(error.to_string().contains("truncated property name"));
            assert_eq!(properties.len(), 1);
            assert!(matches!(properties[0].value, PropValue::Int(42)));
        }
    }

    #[test]
    fn scalar_collections_reject_missing_declared_items() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let bytes = 42i32.to_le_bytes();
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        assert!(read_array_items(&mut reader, &context, "IntProperty", 2, 4).is_err());
        let bytes: Vec<u8> = [0i32, 2, 42, 43]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let meta = PropertyMeta {
            key_type: "IntProperty".into(),
            value_type: "IntProperty".into(),
            ..Default::default()
        };
        assert!(read_value_with_meta(
            &mut reader,
            &context,
            "MapProperty",
            bytes.len() as i32,
            &meta,
            bytes.len() as u64
        )
        .is_err());
    }

    #[test]
    fn native_map_is_explicitly_unknown_instead_of_one_partial_entry() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let bytes: Vec<u8> = [0i32, 2, 42, 99, 99, 99, 99, 43, 99, 99, 99, 99]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let meta = PropertyMeta {
            key_type: "IntProperty".into(),
            value_type: "StructProperty".into(),
            ..Default::default()
        };
        let value = read_value_with_meta(
            &mut reader,
            &context,
            "MapProperty",
            bytes.len() as i32,
            &meta,
            bytes.len() as u64,
        )
        .unwrap();
        assert!(matches!(value, PropValue::Unknown { .. }));
        assert_eq!(reader.position(), bytes.len() as u64);
    }

    #[test]
    fn undersized_scalar_payload_is_an_error() {
        let name_table =
            NameTable::from_names(vec!["None".into(), "Value".into(), "IntProperty".into()]);
        let version = AssetVersion {
            file_ver: 522,
            file_ver_ue5: 0,
        };
        let mut bytes = Vec::new();
        for value in [1i32, 0, 2, 0, 0, 0] {
            bytes.extend(value.to_le_bytes());
        }
        bytes.push(0);
        bytes.extend(42i32.to_le_bytes());
        bytes.extend([0; 8]);
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let mut properties = Vec::new();
        assert!(read_properties(
            &mut reader,
            &name_table,
            &[],
            bytes.len() as u64,
            version,
            &mut properties
        )
        .is_err());
        assert!(properties.is_empty());
    }

    #[test]
    fn opaque_hash_covers_only_the_bounded_payload() {
        let bytes = b"leftabcright";
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        reader.set_position(4);
        let value = read_unknown_value(&mut reader, "OpaqueProperty", 4, 7).unwrap();
        let PropValue::Unknown {
            size,
            payload_sha256,
            ..
        } = value
        else {
            unreachable!()
        };
        assert_eq!(size, 3);
        assert_eq!(
            payload_sha256,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(reader.position(), 7);
        assert!(read_unknown_value(&mut reader, "OpaqueProperty", 4, 99).is_err());
        assert!(read_unknown_value(&mut reader, "OpaqueProperty", 7, 4).is_err());
    }

    fn opaque_collection(type_name: &str, payload: &[u8], meta: &PropertyMeta) -> PropValue {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let mut reader = std::io::Cursor::new(payload);
        let value = read_value_with_meta(
            &mut reader,
            &context,
            type_name,
            payload.len() as i32,
            meta,
            payload.len() as u64,
        )
        .unwrap();
        assert_eq!(reader.position(), payload.len() as u64);
        value
    }

    #[test]
    fn unsupported_collection_elements_preserve_the_entire_payload_and_types() {
        for (type_name, prefix) in [
            ("ArrayProperty", vec![2i32]),
            ("SetProperty", vec![0, 2]),
            ("MapProperty", vec![0, 2]),
        ] {
            let mut payload: Vec<u8> = prefix
                .iter()
                .flat_map(|value| value.to_le_bytes())
                .collect();
            payload.extend_from_slice(b"opaque bytes for two elements");
            let mut hashes = Vec::new();
            for inner in ["OpaqueFirstProperty", "OpaqueSecondProperty"] {
                let meta = PropertyMeta {
                    inner_type: inner.into(),
                    key_type: inner.into(),
                    value_type: "IntProperty".into(),
                    ..Default::default()
                };
                let value = opaque_collection(type_name, &payload, &meta);
                let PropValue::Unknown {
                    type_name: descriptor,
                    size,
                    payload_sha256,
                } = value
                else {
                    panic!("unsupported elements must not pretend to be parsed");
                };
                assert_eq!(size, payload.len() as i32);
                assert!(descriptor.contains(inner));
                assert_eq!(payload_sha256.len(), 64);
                hashes.push(payload_sha256);
            }
            assert_eq!(
                hashes[0], hashes[1],
                "type metadata is separate from payload bytes"
            );
            let meta = PropertyMeta {
                inner_type: "OpaqueFirstProperty".into(),
                key_type: "OpaqueFirstProperty".into(),
                value_type: "IntProperty".into(),
                ..Default::default()
            };
            *payload.last_mut().unwrap() ^= 1;
            let PropValue::Unknown { payload_sha256, .. } =
                opaque_collection(type_name, &payload, &meta)
            else {
                unreachable!()
            };
            assert_ne!(hashes[0], payload_sha256);
        }
    }

    #[test]
    fn unsupported_pin_type_layout_retains_its_type_and_payload_hash() {
        let struct_type = "EdGraphPinType";
        let meta = PropertyMeta {
            struct_type: struct_type.into(),
            ..Default::default()
        };
        let value = opaque_collection("StructProperty", b"abc", &meta);
        let PropValue::Unknown {
            type_name,
            size,
            payload_sha256,
        } = value
        else {
            unreachable!()
        };
        assert_eq!(type_name, struct_type);
        assert_eq!(size, 3);
        assert_eq!(
            payload_sha256,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn nested_unknown_properties_hash_their_payload_in_both_tag_formats() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "Payload".into(),
            "OpaqueProperty".into(),
        ]);
        for file_ver_ue5 in [0, 1012] {
            let context = PropCtx {
                name_table: &name_table,
                soft_object_paths: &[],
                ver: AssetVersion {
                    file_ver: 522,
                    file_ver_ue5,
                },
            };
            let mut bytes = Vec::new();
            for value in [1i32, 0, 2, 0] {
                bytes.extend(value.to_le_bytes());
            }
            if context.ver.has_complete_type_name() {
                bytes.extend(0i32.to_le_bytes());
            }
            bytes.extend(3i32.to_le_bytes());
            if !context.ver.has_complete_type_name() {
                bytes.extend(0i32.to_le_bytes());
            }
            bytes.push(0);
            bytes.extend_from_slice(b"abc");
            bytes.extend([0; 8]);
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let meta = PropertyMeta {
                struct_type: "Container".into(),
                ..Default::default()
            };
            let value = read_value_with_meta(
                &mut reader,
                &context,
                "StructProperty",
                bytes.len() as i32,
                &meta,
                bytes.len() as u64,
            )
            .unwrap();
            let PropValue::Struct { fields, .. } = value else {
                unreachable!()
            };
            assert_eq!(fields.len(), 1);
            let PropValue::Unknown {
                size,
                payload_sha256,
                ..
            } = &fields[0].value
            else {
                unreachable!()
            };
            assert_eq!(*size, 3);
            assert_eq!(
                payload_sha256,
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
            );
        }
    }

    #[test]
    fn unread_native_bytes_cannot_disappear_behind_an_empty_tagged_value() {
        let map_bytes: Vec<u8> = [0i32, 1, 7, 0, 0, 99]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let meta = PropertyMeta {
            key_type: "IntProperty".into(),
            value_type: "StructProperty".into(),
            ..Default::default()
        };
        let map = opaque_collection("MapProperty", &map_bytes, &meta);
        assert!(matches!(map, PropValue::Unknown { size, .. } if size == map_bytes.len() as i32));
        let struct_bytes: Vec<u8> = [0i32, 0, 99]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let meta = PropertyMeta {
            struct_type: "Container".into(),
            ..Default::default()
        };
        let structure = opaque_collection("StructProperty", &struct_bytes, &meta);
        assert!(
            matches!(structure, PropValue::Unknown { size, .. } if size == struct_bytes.len() as i32)
        );
    }

    #[test]
    fn opaque_map_fallback_does_not_hide_a_key_crossing_the_payload_boundary() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let bytes: Vec<u8> = [0i32, 1, 7, 99]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let meta = PropertyMeta {
            key_type: "IntProperty".into(),
            value_type: "StructProperty".into(),
            ..Default::default()
        };
        assert!(read_value_with_meta(&mut reader, &context, "MapProperty", 10, &meta, 10).is_err());
    }

    #[test]
    fn incomplete_struct_array_hash_includes_the_declared_element_count() {
        let name_table = NameTable::from_names(vec![
            "None".into(),
            "Entries".into(),
            "StructProperty".into(),
            "Guid".into(),
        ]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let meta = PropertyMeta {
            inner_type: "StructProperty".into(),
            ..Default::default()
        };
        let mut hashes = Vec::new();
        for count in [1i32, 22, 23] {
            let mut payload = count.to_le_bytes().to_vec();
            for word in [1i32, 0, 2, 0, 16, 0, 3, 0] {
                payload.extend(word.to_le_bytes());
            }
            payload.extend([0; 16]); // Native struct GUID.
            payload.push(0); // No property GUID.
            payload.extend(0u8..16); // One native Guid payload.
            let mut reader = std::io::Cursor::new(payload.as_slice());
            let value = read_value_with_meta(
                &mut reader,
                &context,
                "ArrayProperty",
                payload.len() as i32,
                &meta,
                payload.len() as u64,
            )
            .unwrap();
            if count == 1 {
                assert!(matches!(value, PropValue::Array { items, .. } if items.len() == 1));
            } else {
                let PropValue::Unknown {
                    size,
                    payload_sha256,
                    type_name,
                } = value
                else {
                    panic!("one wrapper cannot establish all declared element boundaries");
                };
                assert_eq!(size, payload.len() as i32);
                assert_eq!(type_name, "ArrayProperty<StructProperty>");
                hashes.push(payload_sha256);
            }
            assert_eq!(reader.position(), payload.len() as u64);
        }
        assert_ne!(
            hashes[0], hashes[1],
            "same-size count-only edits must change the complete payload hash"
        );
    }

    #[test]
    fn unsupported_removal_prefixes_preserve_complete_map_and_set_hashes() {
        let meta = PropertyMeta {
            inner_type: "IntProperty".into(),
            key_type: "IntProperty".into(),
            value_type: "IntProperty".into(),
            ..Default::default()
        };
        for type_name in ["MapProperty", "SetProperty"] {
            let empty = [0u8; 8];
            assert!(!matches!(
                opaque_collection(type_name, &empty, &meta),
                PropValue::Unknown { .. }
            ));
            let mut hashes = Vec::new();
            for removed_count in [1i32, 2] {
                let payload: Vec<u8> = [removed_count, 0]
                    .iter()
                    .flat_map(|word| word.to_le_bytes())
                    .collect();
                let value = opaque_collection(type_name, &payload, &meta);
                let PropValue::Unknown {
                    size,
                    payload_sha256,
                    type_name: descriptor,
                } = value
                else {
                    panic!(
                        "undecoded removal entries cannot be represented as an empty collection"
                    );
                };
                assert_eq!(size, payload.len() as i32);
                assert!(descriptor.starts_with(type_name));
                hashes.push(payload_sha256);
            }
            assert_ne!(hashes[0], hashes[1]);
        }
    }

    #[test]
    fn removal_counts_must_fit_their_payload_and_be_nonnegative() {
        let name_table = NameTable::from_names(vec!["None".into()]);
        let context = PropCtx {
            name_table: &name_table,
            soft_object_paths: &[],
            ver: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
        };
        let meta = PropertyMeta {
            inner_type: "IntProperty".into(),
            key_type: "IntProperty".into(),
            value_type: "IntProperty".into(),
            ..Default::default()
        };
        for type_name in ["MapProperty", "SetProperty"] {
            for (removed_count, payload_end) in [(-1i32, 8), (1, 2)] {
                let payload: Vec<u8> = [removed_count, 0]
                    .iter()
                    .flat_map(|word| word.to_le_bytes())
                    .collect();
                let mut reader = std::io::Cursor::new(payload.as_slice());
                assert!(read_value_with_meta(
                    &mut reader,
                    &context,
                    type_name,
                    payload_end as i32,
                    &meta,
                    payload_end
                )
                .is_err());
            }
        }
    }
}
