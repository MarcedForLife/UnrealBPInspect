//! Tagged property deserializer for UE4 and UE5 exports.
//!
//! UE4 uses `FPropertyTag` (explicit Type/StructName/EnumName fields).
//! UE5.2+ (version >= 1012) uses `FPropertyTypeName` (recursive type descriptor, flags byte).

use anyhow::Result;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::types::*;

/// Immutable context for property reading.
struct PropCtx<'a> {
    name_table: &'a NameTable,
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
    /// StructProperty: the struct's type name (e.g. "Vector", "Transform")
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

/// Headroom for property size validation against remaining data.
/// The cursor may be slightly past the size measurement point after reading tag-specific fields.
const SIZE_VALIDATION_HEADROOM: u64 = 256;

/// Read tagged properties from an export's serialized data stream.
///
/// Returns a `Vec<Property>`; on malformed data the stream is terminated early and
/// already-read properties are returned (best-effort parsing).
pub fn read_properties(
    reader: &mut Reader,
    name_table: &NameTable,
    end_offset: u64,
    ver: AssetVersion,
) -> Vec<Property> {
    let ctx = PropCtx { name_table, ver };
    if ver.has_complete_type_name() {
        return read_properties_ue5(reader, &ctx, end_offset);
    }
    let mut props = Vec::new();
    loop {
        if reader.position() + 8 > end_offset {
            break;
        }
        let pos_before = reader.position();
        let Ok((prop_name, is_none)) = ctx.name_table.fname_is_none(reader) else {
            break;
        };
        if is_none {
            break;
        }
        if reader.position() + 16 > end_offset {
            let _ = reader.seek(SeekFrom::Start(pos_before));
            break;
        }
        let Ok(type_name) = ctx.name_table.fname(reader) else {
            break;
        };

        if !type_name.ends_with("Property") {
            let _ = reader.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(reader) else { break };
        let Ok(_array_index) = read_i32(reader) else {
            break;
        };

        if size < 0 || size as u64 > end_offset - reader.position() + SIZE_VALIDATION_HEADROOM {
            let _ = reader.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(value) = read_property_value_ue4(reader, &ctx, &type_name, size) else {
            break;
        };
        props.push(Property {
            name: prop_name,
            value,
        });
    }
    props
}

// UE4 tag preamble: type-specific fields, PropertyGuid, then shared reader
fn read_property_value_ue4(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    size: i32,
) -> Result<PropValue> {
    let file_ver = ctx.ver.file_ver;

    // BoolProperty has a unique UE4 layout: value byte before PropertyGuid
    if type_name == "BoolProperty" {
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
    match type_name {
        "StructProperty" => {
            meta.struct_type = ctx.name_table.fname(reader)?;
            let _struct_guid = read_guid(reader)?;
        }
        "ArrayProperty" => meta.inner_type = ctx.name_table.fname(reader)?,
        "SetProperty" => meta.inner_type = ctx.name_table.fname(reader)?,
        "MapProperty" => {
            meta.key_type = ctx.name_table.fname(reader)?;
            meta.value_type = ctx.name_table.fname(reader)?;
        }
        "EnumProperty" => meta.enum_name = ctx.name_table.fname(reader)?,
        "ByteProperty" => meta.enum_name = ctx.name_table.fname(reader)?,
        _ => {}
    }
    skip_property_guid(reader, file_ver)?;

    // The cursor is now past all tag-specific fields; value data is next.
    let value_data_end = reader.position() + size as u64;

    let value = read_value_with_meta(reader, ctx, type_name, size, &meta, value_data_end)?;

    // Ensure cursor is at the correct position after the value
    match type_name {
        "StructProperty" | "ArrayProperty" | "MapProperty" | "SetProperty" => {
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
fn read_properties_ue5(reader: &mut Reader, ctx: &PropCtx, end_offset: u64) -> Vec<Property> {
    let mut props = Vec::new();
    loop {
        if reader.position() + 8 > end_offset {
            break;
        }
        let pos_before = reader.position();
        let Ok((prop_name, is_none)) = ctx.name_table.fname_is_none(reader) else {
            break;
        };
        if is_none {
            break;
        }

        let Ok(type_info) = read_property_type_name(reader, ctx) else {
            break;
        };
        if !type_info.type_name.ends_with("Property") {
            let _ = reader.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(reader) else { break };
        let Ok(flags) = read_u8(reader) else { break };

        if flags & TAG_HAS_ARRAY_INDEX != 0 {
            let Ok(_) = read_i32(reader) else { break };
        }
        if flags & TAG_HAS_PROPERTY_GUID != 0 {
            let Ok(_) = read_guid(reader) else { break };
        }
        if flags & TAG_HAS_PROPERTY_EXTENSIONS != 0 {
            let Ok(ext) = read_u8(reader) else { break };
            // EPropertyTagExtensionType::OverridableSerializationInformation (2 extra bytes)
            if ext & 0x02 != 0 {
                let Ok(_operation) = read_u8(reader) else {
                    break;
                };
                let Ok(_condition) = read_u8(reader) else {
                    break;
                };
            }
        }

        if size < 0
            || size as u64 > end_offset.saturating_sub(reader.position()) + SIZE_VALIDATION_HEADROOM
        {
            let _ = reader.seek(SeekFrom::Start(pos_before));
            break;
        }

        let value_start = reader.position();
        let Ok(value) = read_property_value_ue5(reader, ctx, &type_info, size, flags) else {
            break;
        };
        // Ensure we consumed exactly `size` bytes of value data
        let _ = reader.seek(SeekFrom::Start(value_start + size as u64));

        props.push(Property {
            name: prop_name,
            value,
        });
    }
    props
}

fn read_property_value_ue5(
    reader: &mut Reader,
    ctx: &PropCtx,
    ti: &PropertyTypeInfo,
    size: i32,
    flags: u8,
) -> Result<PropValue> {
    // BoolProperty: value encoded in flags, no payload
    if ti.type_name == "BoolProperty" {
        return Ok(PropValue::Bool(flags & TAG_BOOL_TRUE != 0));
    }

    let meta = PropertyMeta {
        struct_type: ti.inner_name(0),
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
    name_table: &NameTable,
    type_name: &str,
) -> Result<Option<PropValue>> {
    match type_name {
        "IntProperty" | "Int32Property" | "UInt32Property" => {
            Ok(Some(PropValue::Int(read_i32(reader)?)))
        }
        "Int8Property" => Ok(Some(PropValue::Int(read_u8(reader)? as i8 as i32))),
        "Int16Property" | "UInt16Property" => {
            let mut b = [0u8; 2];
            reader.read_exact(&mut b)?;
            Ok(Some(PropValue::Int(i16::from_le_bytes(b) as i32)))
        }
        "Int64Property" | "UInt64Property" => Ok(Some(PropValue::Int64(read_i64(reader)?))),
        "FloatProperty" => Ok(Some(PropValue::Float(read_f32(reader)?))),
        "DoubleProperty" => Ok(Some(PropValue::Double(read_f64(reader)?))),
        "NameProperty" => Ok(Some(PropValue::Name(name_table.fname(reader)?))),
        "ObjectProperty" => Ok(Some(PropValue::Object(read_i32(reader)?))),
        "SoftObjectProperty" => {
            let path = read_fstring(reader)?;
            let _sub = read_fstring(reader)?;
            Ok(Some(PropValue::SoftObject(path)))
        }
        "StrProperty" => Ok(Some(PropValue::Str(read_fstring(reader)?))),
        _ => Ok(None),
    }
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
    if let Some(val) = read_primitive_value(reader, ctx.name_table, type_name)? {
        return Ok(val);
    }
    match type_name {
        "TextProperty" => read_text_property(reader, size).map(PropValue::Text),

        "EnumProperty" => {
            let value = ctx.name_table.fname(reader)?;
            Ok(PropValue::Enum {
                enum_name: meta.enum_name.clone(),
                value,
            })
        }
        "ByteProperty" => {
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

        "StructProperty" => {
            let struct_end = reader.position() + size as u64;
            let fields = read_struct_value(reader, ctx, &meta.struct_type, size, struct_end)?;
            reader.seek(SeekFrom::Start(struct_end))?;
            Ok(PropValue::Struct {
                struct_type: meta.struct_type.clone(),
                fields,
            })
        }

        "ArrayProperty" => {
            let count = read_i32(reader)?;
            let items = read_array_items(reader, ctx, &meta.inner_type, count, value_data_end)?;
            Ok(PropValue::Array {
                inner_type: meta.inner_type.clone(),
                items,
            })
        }

        "MapProperty" => {
            let _num_keys_to_remove = read_i32(reader)?;
            let count = read_i32(reader)?;
            let mut entries = Vec::new();
            for _ in 0..count {
                if reader.position() >= value_data_end {
                    break;
                }
                let key = read_typed_value(reader, ctx, &meta.key_type, value_data_end)?;
                let val = read_typed_value(reader, ctx, &meta.value_type, value_data_end)?;
                entries.push((key, val));
            }
            Ok(PropValue::Map {
                key_type: meta.key_type.clone(),
                value_type: meta.value_type.clone(),
                entries,
            })
        }

        "SetProperty" => {
            let _num_to_remove = read_i32(reader)?;
            let count = read_i32(reader)?;
            let items = read_array_items(reader, ctx, &meta.inner_type, count, value_data_end)?;
            Ok(PropValue::Array {
                inner_type: meta.inner_type.clone(),
                items,
            })
        }

        "DelegateProperty" => format_delegate_binding(reader, ctx.name_table).map(PropValue::Str),

        "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => {
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

        _ => {
            reader.seek(SeekFrom::Current(size as i64))?;
            Ok(PropValue::Unknown {
                type_name: type_name.to_string(),
                size,
            })
        }
    }
}

fn read_typed_value(
    reader: &mut Reader,
    ctx: &PropCtx,
    type_name: &str,
    end_offset: u64,
) -> Result<PropValue> {
    if let Some(val) = read_primitive_value(reader, ctx.name_table, type_name)? {
        return Ok(val);
    }
    match type_name {
        "BoolProperty" => Ok(PropValue::Bool(read_u8(reader)? != 0)),
        "ByteProperty" => Ok(PropValue::Int(read_u8(reader)? as i32)),
        "EnumProperty" => Ok(PropValue::Name(ctx.name_table.fname(reader)?)),
        "StructProperty" => {
            let fields = read_properties(reader, ctx.name_table, end_offset, ctx.ver);
            Ok(PropValue::Struct {
                struct_type: String::new(),
                fields,
            })
        }
        _ => Ok(PropValue::Unknown {
            type_name: type_name.to_string(),
            size: 0,
        }),
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
        _ => Ok(read_properties(reader, ctx.name_table, end_offset, ctx.ver)),
    }
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
            break;
        }
        let item = read_typed_value(reader, ctx, inner_type, end_offset)?;
        if matches!(&item, PropValue::Unknown { .. }) {
            reader.seek(SeekFrom::Start(end_offset))?;
            items.push(item);
            break;
        }
        items.push(item);
    }
    Ok(items)
}
