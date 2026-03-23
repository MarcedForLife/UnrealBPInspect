//! Tagged property deserializer for UE4 and UE5 exports.
//!
//! UE4 uses `FPropertyTag` (explicit Type/StructName/EnumName fields).
//! UE5.2+ (version >= 1012) uses `FPropertyTypeName` (recursive type descriptor, flags byte).

use anyhow::Result;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::types::*;

// ---------------------------------------------------------------------------
// UE5.2+ FPropertyTypeName: recursive type descriptor replacing the old
// Type FName + type-specific tag fields (StructName, EnumName, InnerType …).
// Binary format: FName mainType(8) + i32 innerCount(4) + [inner × TypeName].
// ---------------------------------------------------------------------------
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

fn read_property_type_name(r: &mut Reader, nt: &NameTable) -> Result<PropertyTypeInfo> {
    read_property_type_name_depth(r, nt, 0)
}

fn read_property_type_name_depth(
    r: &mut Reader,
    nt: &NameTable,
    depth: u32,
) -> Result<PropertyTypeInfo> {
    anyhow::ensure!(depth < 8, "FPropertyTypeName recursion too deep");
    let type_name = nt.fname(r)?;
    let inner_count = read_i32(r)?;
    anyhow::ensure!(
        (0..=4).contains(&inner_count),
        "FPropertyTypeName inner count {} out of range",
        inner_count
    );
    let mut inners = Vec::new();
    for _ in 0..inner_count {
        inners.push(read_property_type_name_depth(r, nt, depth + 1)?);
    }
    Ok(PropertyTypeInfo { type_name, inners })
}

// UE5.2+ property tag flags byte (replaces ArrayIndex + HasPropertyGuid)
const TAG_HAS_ARRAY_INDEX: u8 = 0x01;
const TAG_HAS_PROPERTY_GUID: u8 = 0x02;
const TAG_HAS_PROPERTY_EXTENSIONS: u8 = 0x04;
const TAG_BOOL_TRUE: u8 = 0x10;

// ---------------------------------------------------------------------------
// Shared metadata for property value reading, populated differently by
// UE4 (from tag fields) and UE5 (from PropertyTypeInfo).
// ---------------------------------------------------------------------------
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

fn format_delegate_binding(r: &mut Reader, nt: &NameTable) -> Result<String> {
    let obj = read_i32(r)?;
    let func = nt.fname(r)?;
    Ok(if obj != 0 {
        format!("{}::{}", obj, func)
    } else {
        func
    })
}

/// Size validation headroom. Property sizes are checked against remaining data, but
/// the tag preamble (type-specific fields, GUID) is consumed before the size field is
/// validated, so the cursor may be slightly past where the size was measured from.
/// This headroom prevents false termination on valid properties near the end of an export.
const SIZE_VALIDATION_HEADROOM: u64 = 256;

/// Read tagged properties from an export's serialized data stream.
///
/// Returns a `Vec<Property>`; on malformed data the stream is terminated early and
/// already-read properties are returned (best-effort parsing).
pub fn read_properties(
    r: &mut Reader,
    nt: &NameTable,
    end_offset: u64,
    ver: AssetVersion,
) -> Vec<Property> {
    if ver.has_complete_type_name() {
        return read_properties_ue5(r, nt, end_offset, ver);
    }
    let mut props = Vec::new();
    loop {
        if r.position() + 8 > end_offset {
            break;
        }
        let pos_before = r.position();
        let Ok((prop_name, is_none)) = nt.fname_is_none(r) else {
            break;
        };
        if is_none {
            break;
        }
        if r.position() + 16 > end_offset {
            let _ = r.seek(SeekFrom::Start(pos_before));
            break;
        }
        let Ok(type_name) = nt.fname(r) else { break };

        if !type_name.ends_with("Property") {
            let _ = r.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(r) else { break };
        let Ok(_array_index) = read_i32(r) else { break };

        if size < 0 || size as u64 > end_offset - r.position() + SIZE_VALIDATION_HEADROOM {
            let _ = r.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(value) = read_property_value_ue4(r, nt, &type_name, size, ver) else {
            break;
        };
        props.push(Property {
            name: prop_name,
            value,
        });
    }
    props
}

// ---------------------------------------------------------------------------
// UE4 tag preamble reader: reads type-specific fields from the binary tag,
// builds PropertyMeta, skips PropertyGuid, then delegates to shared reader.
// ---------------------------------------------------------------------------
fn read_property_value_ue4(
    r: &mut Reader,
    nt: &NameTable,
    type_name: &str,
    size: i32,
    ver: AssetVersion,
) -> Result<PropValue> {
    let file_ver = ver.file_ver;

    // BoolProperty has a unique UE4 layout: value byte before PropertyGuid
    if type_name == "BoolProperty" {
        let val = read_u8(r)? != 0;
        if file_ver >= VER_UE4_PROPERTY_GUID {
            let has_guid = read_u8(r)?;
            if has_guid != 0 {
                let _guid = read_guid(r)?;
            }
        }
        return Ok(PropValue::Bool(val));
    }

    // Build metadata from tag-specific fields
    let mut meta = PropertyMeta::default();
    match type_name {
        "StructProperty" => {
            meta.struct_type = nt.fname(r)?;
            let _struct_guid = read_guid(r)?;
        }
        "ArrayProperty" => meta.inner_type = nt.fname(r)?,
        "SetProperty" => meta.inner_type = nt.fname(r)?,
        "MapProperty" => {
            meta.key_type = nt.fname(r)?;
            meta.value_type = nt.fname(r)?;
        }
        "EnumProperty" => meta.enum_name = nt.fname(r)?,
        "ByteProperty" => meta.enum_name = nt.fname(r)?,
        _ => {}
    }
    skip_property_guid(r, file_ver)?;

    // The cursor is now past all tag-specific fields; value data is next.
    let value_data_end = r.position() + size as u64;

    let value = read_value_with_meta(r, nt, type_name, size, &meta, value_data_end, ver)?;

    // Ensure cursor is at the correct position after the value
    match type_name {
        "StructProperty" | "ArrayProperty" | "MapProperty" | "SetProperty" => {
            r.seek(SeekFrom::Start(value_data_end))?;
        }
        _ => {}
    }
    Ok(value)
}

fn skip_property_guid(r: &mut Reader, file_ver: i32) -> Result<()> {
    if file_ver >= VER_UE4_PROPERTY_GUID {
        let has_guid = read_u8(r)?;
        if has_guid != 0 {
            let _guid = read_guid(r)?;
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// UE5.2+ tagged property reader
// ---------------------------------------------------------------------------
fn read_properties_ue5(
    r: &mut Reader,
    nt: &NameTable,
    end_offset: u64,
    ver: AssetVersion,
) -> Vec<Property> {
    let mut props = Vec::new();
    loop {
        if r.position() + 8 > end_offset {
            break;
        }
        let pos_before = r.position();
        let Ok((prop_name, is_none)) = nt.fname_is_none(r) else {
            break;
        };
        if is_none {
            break;
        }

        let Ok(type_info) = read_property_type_name(r, nt) else {
            break;
        };
        if !type_info.type_name.ends_with("Property") {
            let _ = r.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(r) else { break };
        let Ok(flags) = read_u8(r) else { break };

        if flags & TAG_HAS_ARRAY_INDEX != 0 {
            let Ok(_) = read_i32(r) else { break };
        }
        if flags & TAG_HAS_PROPERTY_GUID != 0 {
            let Ok(_) = read_guid(r) else { break };
        }
        if flags & TAG_HAS_PROPERTY_EXTENSIONS != 0 {
            let Ok(ext) = read_u8(r) else { break };
            // EPropertyTagExtensionType::OverridableSerializationInformation (2 extra bytes)
            if ext & 0x02 != 0 {
                let Ok(_operation) = read_u8(r) else { break };
                let Ok(_condition) = read_u8(r) else { break };
            }
        }

        if size < 0
            || size as u64 > end_offset.saturating_sub(r.position()) + SIZE_VALIDATION_HEADROOM
        {
            let _ = r.seek(SeekFrom::Start(pos_before));
            break;
        }

        let value_start = r.position();
        let Ok(value) = read_property_value_ue5(r, nt, &type_info, size, flags, ver) else {
            break;
        };
        // Ensure we consumed exactly `size` bytes of value data
        let _ = r.seek(SeekFrom::Start(value_start + size as u64));

        props.push(Property {
            name: prop_name,
            value,
        });
    }
    props
}

fn read_property_value_ue5(
    r: &mut Reader,
    nt: &NameTable,
    ti: &PropertyTypeInfo,
    size: i32,
    flags: u8,
    ver: AssetVersion,
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
    let value_data_end = r.position() + size as u64;
    read_value_with_meta(r, nt, &ti.type_name, size, &meta, value_data_end, ver)
}

// ---------------------------------------------------------------------------
// Primitive value reader: handles types shared between read_value_with_meta
// and read_typed_value (integers, floats, names, objects, strings).
// Returns None for types that need context-specific handling.
// ---------------------------------------------------------------------------
fn read_primitive_value(
    r: &mut Reader,
    nt: &NameTable,
    type_name: &str,
) -> Result<Option<PropValue>> {
    match type_name {
        "IntProperty" | "Int32Property" | "UInt32Property" => {
            Ok(Some(PropValue::Int(read_i32(r)?)))
        }
        "Int8Property" => Ok(Some(PropValue::Int(read_u8(r)? as i8 as i32))),
        "Int16Property" | "UInt16Property" => {
            let mut b = [0u8; 2];
            r.read_exact(&mut b)?;
            Ok(Some(PropValue::Int(i16::from_le_bytes(b) as i32)))
        }
        "Int64Property" | "UInt64Property" => Ok(Some(PropValue::Int64(read_i64(r)?))),
        "FloatProperty" => Ok(Some(PropValue::Float(read_f32(r)?))),
        "DoubleProperty" => Ok(Some(PropValue::Double(read_f64(r)?))),
        "NameProperty" => Ok(Some(PropValue::Name(nt.fname(r)?))),
        "ObjectProperty" => Ok(Some(PropValue::Object(read_i32(r)?))),
        "SoftObjectProperty" => {
            let path = read_fstring(r)?;
            let _sub = read_fstring(r)?;
            Ok(Some(PropValue::SoftObject(path)))
        }
        "StrProperty" => Ok(Some(PropValue::Str(read_fstring(r)?))),
        _ => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// Shared value reader, used by both UE4 and UE5 paths after metadata
// has been extracted from their respective tag formats.
// ---------------------------------------------------------------------------
#[allow(clippy::too_many_arguments)]
fn read_value_with_meta(
    r: &mut Reader,
    nt: &NameTable,
    type_name: &str,
    size: i32,
    meta: &PropertyMeta,
    value_data_end: u64,
    ver: AssetVersion,
) -> Result<PropValue> {
    if let Some(val) = read_primitive_value(r, nt, type_name)? {
        return Ok(val);
    }
    match type_name {
        "TextProperty" => read_text_property(r, size).map(PropValue::Text),

        "EnumProperty" => {
            let value = nt.fname(r)?;
            Ok(PropValue::Enum {
                enum_type: meta.enum_name.clone(),
                value,
            })
        }
        "ByteProperty" => {
            if size == 1 {
                Ok(PropValue::Byte {
                    enum_name: meta.enum_name.clone(),
                    value: read_u8(r)?.to_string(),
                })
            } else {
                Ok(PropValue::Byte {
                    enum_name: meta.enum_name.clone(),
                    value: nt.fname(r)?,
                })
            }
        }

        "StructProperty" => {
            let struct_end = r.position() + size as u64;
            let fields = read_struct_value(r, nt, &meta.struct_type, size, struct_end, ver)?;
            r.seek(SeekFrom::Start(struct_end))?;
            Ok(PropValue::Struct {
                struct_type: meta.struct_type.clone(),
                fields,
            })
        }

        "ArrayProperty" => {
            let count = read_i32(r)?;
            let items = read_array_items(r, nt, &meta.inner_type, count, value_data_end, ver)?;
            Ok(PropValue::Array {
                inner_type: meta.inner_type.clone(),
                items,
            })
        }

        "MapProperty" => {
            let _num_keys_to_remove = read_i32(r)?;
            let count = read_i32(r)?;
            let mut entries = Vec::new();
            for _ in 0..count {
                if r.position() >= value_data_end {
                    break;
                }
                let k = read_typed_value(r, nt, &meta.key_type, value_data_end, ver)?;
                let v = read_typed_value(r, nt, &meta.value_type, value_data_end, ver)?;
                entries.push((k, v));
            }
            Ok(PropValue::Map {
                key_type: meta.key_type.clone(),
                value_type: meta.value_type.clone(),
                entries,
            })
        }

        "SetProperty" => {
            let _num_to_remove = read_i32(r)?;
            let count = read_i32(r)?;
            let items = read_array_items(r, nt, &meta.inner_type, count, value_data_end, ver)?;
            Ok(PropValue::Array {
                inner_type: meta.inner_type.clone(),
                items,
            })
        }

        "DelegateProperty" => format_delegate_binding(r, nt).map(PropValue::Str),

        "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => {
            let count = read_i32(r)?;
            let mut bindings = Vec::new();
            for _ in 0..count {
                bindings.push(PropValue::Str(format_delegate_binding(r, nt)?));
            }
            Ok(PropValue::Array {
                inner_type: "DelegateProperty".into(),
                items: bindings,
            })
        }

        _ => {
            r.seek(SeekFrom::Current(size as i64))?;
            Ok(PropValue::Unknown {
                type_name: type_name.to_string(),
                size,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn read_typed_value(
    r: &mut Reader,
    nt: &NameTable,
    type_name: &str,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<PropValue> {
    if let Some(val) = read_primitive_value(r, nt, type_name)? {
        return Ok(val);
    }
    match type_name {
        "BoolProperty" => Ok(PropValue::Bool(read_u8(r)? != 0)),
        "ByteProperty" => Ok(PropValue::Int(read_u8(r)? as i32)),
        "EnumProperty" => Ok(PropValue::Name(nt.fname(r)?)),
        "StructProperty" => {
            let fields = read_properties(r, nt, end_offset, ver);
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

fn read_text_property(r: &mut Reader, size: i32) -> Result<String> {
    if size <= 0 {
        return Ok(String::new());
    }
    let mut buf = vec![0u8; size as usize];
    r.read_exact(&mut buf)?;
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

fn read_lwc_components(r: &mut Reader, lwc: bool, names: &[&str]) -> Result<Vec<Property>> {
    let mut props = Vec::new();
    for name in names {
        let value = if lwc {
            PropValue::Double(read_f64(r)?)
        } else {
            PropValue::Float(read_f32(r)?)
        };
        props.push(Property {
            name: name.to_string(),
            value,
        });
    }
    Ok(props)
}

fn read_struct_value(
    r: &mut Reader,
    nt: &NameTable,
    struct_type: &str,
    _size: i32,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<Vec<Property>> {
    let lwc = ver.is_lwc();
    match struct_type {
        "Vector" => read_lwc_components(r, lwc, &["X", "Y", "Z"]),
        "Rotator" => read_lwc_components(r, lwc, &["Pitch", "Yaw", "Roll"]),
        "Vector2D" => read_lwc_components(r, lwc, &["X", "Y"]),
        "LinearColor" => {
            let red = read_f32(r)?;
            let g = read_f32(r)?;
            let b = read_f32(r)?;
            let a = read_f32(r)?;
            Ok(vec![
                Property {
                    name: "R".into(),
                    value: PropValue::Float(red),
                },
                Property {
                    name: "G".into(),
                    value: PropValue::Float(g),
                },
                Property {
                    name: "B".into(),
                    value: PropValue::Float(b),
                },
                Property {
                    name: "A".into(),
                    value: PropValue::Float(a),
                },
            ])
        }
        "Guid" => {
            let g = read_guid(r)?;
            Ok(vec![Property {
                name: "Guid".into(),
                value: PropValue::Str(format!("{:02x?}", g)),
            }])
        }
        _ => Ok(read_properties(r, nt, end_offset, ver)),
    }
}

fn read_array_items(
    r: &mut Reader,
    nt: &NameTable,
    inner_type: &str,
    count: i32,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<Vec<PropValue>> {
    let mut items = Vec::new();
    for _ in 0..count {
        if r.position() >= end_offset {
            break;
        }
        let item = read_typed_value(r, nt, inner_type, end_offset, ver)?;
        if matches!(&item, PropValue::Unknown { .. }) {
            r.seek(SeekFrom::Start(end_offset))?;
            items.push(item);
            break;
        }
        items.push(item);
    }
    Ok(items)
}
