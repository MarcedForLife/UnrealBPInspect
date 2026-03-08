use anyhow::Result;
use std::io::{Read, Seek, SeekFrom};

use crate::binary::*;
use crate::types::*;

pub fn read_properties(
    c: &mut R,
    nt: &NameTable,
    end_offset: u64,
    ver: AssetVersion,
) -> Vec<Property> {
    let mut props = Vec::new();
    loop {
        if c.position() + 8 > end_offset {
            break;
        }
        let pos_before = c.position();
        let Ok((prop_name, is_none)) = nt.fname_is_none(c) else {
            break;
        };
        if is_none {
            break;
        }
        if c.position() + 16 > end_offset {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }
        let Ok(type_name) = nt.fname(c) else { break };

        if !type_name.ends_with("Property") {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(c) else { break };
        let Ok(_array_index) = read_i32(c) else { break };

        if size < 0 || size as u64 > end_offset - c.position() + 256 {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(value) = read_property_value(c, nt, &type_name, size, end_offset, ver) else {
            break;
        };
        props.push(Property {
            name: prop_name,
            value,
        });
    }
    props
}

fn read_property_value(
    c: &mut R,
    nt: &NameTable,
    type_name: &str,
    size: i32,
    _end_offset: u64,
    ver: AssetVersion,
) -> Result<PropValue> {
    let file_ver = ver.file_ver;
    let data_start = c.position();

    match type_name {
        "BoolProperty" => {
            let val = read_u8(c)? != 0;
            if file_ver >= 503 {
                let has_guid = read_u8(c)?;
                if has_guid != 0 {
                    let _guid = read_guid(c)?;
                }
            }
            Ok(PropValue::Bool(val))
        }
        "IntProperty" | "Int32Property" | "UInt32Property" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Int(read_i32(c)?))
        }
        "Int8Property" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Int(read_u8(c)? as i8 as i32))
        }
        "Int16Property" | "UInt16Property" => {
            skip_property_guid(c, file_ver)?;
            let mut b = [0u8; 2];
            c.read_exact(&mut b)?;
            Ok(PropValue::Int(i16::from_le_bytes(b) as i32))
        }
        "Int64Property" | "UInt64Property" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Int64(read_i64(c)?))
        }
        "FloatProperty" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Float(read_f32(c)?))
        }
        "DoubleProperty" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Double(read_f64(c)?))
        }
        "StrProperty" | "TextProperty" => {
            skip_property_guid(c, file_ver)?;
            if type_name == "TextProperty" {
                let text = read_text_property(c, size)?;
                Ok(PropValue::Text(text))
            } else {
                Ok(PropValue::Str(read_fstring(c)?))
            }
        }
        "NameProperty" => {
            skip_property_guid(c, file_ver)?;
            Ok(PropValue::Name(nt.fname(c)?))
        }
        "ObjectProperty" | "SoftObjectProperty" => {
            skip_property_guid(c, file_ver)?;
            if type_name == "SoftObjectProperty" {
                let path = read_fstring(c)?;
                let _sub = read_fstring(c)?;
                Ok(PropValue::SoftObject(path))
            } else {
                Ok(PropValue::Object(read_i32(c)?))
            }
        }
        "EnumProperty" => {
            let enum_name = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            let value = nt.fname(c)?;
            Ok(PropValue::Enum {
                enum_type: enum_name,
                value,
            })
        }
        "ByteProperty" => {
            let enum_name = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            if size == 1 {
                let val = read_u8(c)?;
                Ok(PropValue::Byte {
                    enum_name,
                    value: val.to_string(),
                })
            } else {
                let value = nt.fname(c)?;
                Ok(PropValue::Byte { enum_name, value })
            }
        }
        "StructProperty" => {
            let struct_type = nt.fname(c)?;
            let _struct_guid = read_guid(c)?;
            skip_property_guid(c, file_ver)?;
            let struct_end = c.position() + size as u64;
            let fields = read_struct_value(c, nt, &struct_type, size, struct_end, ver)?;
            c.seek(SeekFrom::Start(struct_end))?;
            Ok(PropValue::Struct {
                struct_type,
                fields,
            })
        }
        "ArrayProperty" => {
            let inner_type = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            let count = read_i32(c)?;
            let array_data_end = data_start + tag_overhead(type_name, file_ver) + size as u64;
            let items = read_array_items(c, nt, &inner_type, count, array_data_end, ver)?;
            c.seek(SeekFrom::Start(array_data_end))?;
            Ok(PropValue::Array { inner_type, items })
        }
        "MapProperty" => {
            let key_type = nt.fname(c)?;
            let value_type = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            let map_data_end = data_start + tag_overhead(type_name, file_ver) + size as u64;
            let _num_keys_to_remove = read_i32(c)?;
            let count = read_i32(c)?;
            let mut entries = Vec::new();
            for _ in 0..count {
                if c.position() >= map_data_end {
                    break;
                }
                let k = read_typed_value(c, nt, &key_type, map_data_end, ver)?;
                let v = read_typed_value(c, nt, &value_type, map_data_end, ver)?;
                entries.push((k, v));
            }
            c.seek(SeekFrom::Start(map_data_end))?;
            Ok(PropValue::Map {
                key_type,
                value_type,
                entries,
            })
        }
        "SetProperty" => {
            let inner_type = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            let set_data_end = data_start + tag_overhead(type_name, file_ver) + size as u64;
            let _num_to_remove = read_i32(c)?;
            let count = read_i32(c)?;
            let items = read_array_items(c, nt, &inner_type, count, set_data_end, ver)?;
            c.seek(SeekFrom::Start(set_data_end))?;
            Ok(PropValue::Array { inner_type, items })
        }
        "DelegateProperty" => {
            skip_property_guid(c, file_ver)?;
            let obj = read_i32(c)?;
            let func = nt.fname(c)?;
            let desc = if obj != 0 {
                format!("{}::{}", obj, func)
            } else {
                func
            };
            Ok(PropValue::Str(desc))
        }
        "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => {
            skip_property_guid(c, file_ver)?;
            let count = read_i32(c)?;
            let mut bindings = Vec::new();
            for _ in 0..count {
                let obj = read_i32(c)?;
                let func = nt.fname(c)?;
                let desc = if obj != 0 {
                    format!("{}::{}", obj, func)
                } else {
                    func
                };
                bindings.push(PropValue::Str(desc));
            }
            Ok(PropValue::Array {
                inner_type: "DelegateProperty".into(),
                items: bindings,
            })
        }
        _ => {
            skip_property_guid(c, file_ver)?;
            c.seek(SeekFrom::Current(size as i64))?;
            Ok(PropValue::Unknown {
                type_name: type_name.to_string(),
                size,
            })
        }
    }
}

fn skip_property_guid(c: &mut R, file_ver: i32) -> Result<()> {
    if file_ver >= 503 {
        let has_guid = read_u8(c)?;
        if has_guid != 0 {
            let _guid = read_guid(c)?;
        }
    }
    Ok(())
}

fn read_typed_value(
    c: &mut R,
    nt: &NameTable,
    type_name: &str,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<PropValue> {
    match type_name {
        "IntProperty" | "Int32Property" | "UInt32Property" => Ok(PropValue::Int(read_i32(c)?)),
        "Int8Property" => Ok(PropValue::Int(read_u8(c)? as i8 as i32)),
        "Int16Property" | "UInt16Property" => {
            let mut b = [0u8; 2];
            c.read_exact(&mut b)?;
            Ok(PropValue::Int(i16::from_le_bytes(b) as i32))
        }
        "Int64Property" | "UInt64Property" => Ok(PropValue::Int64(read_i64(c)?)),
        "FloatProperty" => Ok(PropValue::Float(read_f32(c)?)),
        "DoubleProperty" => Ok(PropValue::Double(read_f64(c)?)),
        "BoolProperty" => Ok(PropValue::Bool(read_u8(c)? != 0)),
        "ByteProperty" => Ok(PropValue::Int(read_u8(c)? as i32)),
        "NameProperty" | "EnumProperty" => Ok(PropValue::Name(nt.fname(c)?)),
        "StrProperty" => Ok(PropValue::Str(read_fstring(c)?)),
        "ObjectProperty" => Ok(PropValue::Object(read_i32(c)?)),
        "SoftObjectProperty" => {
            let path = read_fstring(c)?;
            let _sub = read_fstring(c)?;
            Ok(PropValue::SoftObject(path))
        }
        "StructProperty" => {
            let fields = read_properties(c, nt, end_offset, ver);
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

/// Bytes between the tag's Size field and the start of actual data.
/// Each FName = 8 bytes, GUID = 16 bytes, guid_byte = HasPropertyGuid flag (v503+),
/// extra int32s for element counts (Array=4, Set/Map=8 for remove+count).
fn tag_overhead(_type_name: &str, file_ver: i32) -> u64 {
    let guid_byte: u64 = if file_ver >= 503 { 1 } else { 0 };
    match _type_name {
        "ArrayProperty" => 8 + guid_byte + 4, // InnerType FName + guid + Size
        "SetProperty" => 8 + guid_byte + 8,   // InnerType FName + guid + remove + count
        "MapProperty" => 16 + guid_byte + 8,  // Key+Value FNames + guid + remove + count
        "EnumProperty" => 8 + guid_byte,      // EnumName FName + guid
        "ByteProperty" => 8 + guid_byte,      // EnumName FName + guid
        "StructProperty" => 8 + 16 + guid_byte, // StructName FName + GUID + guid
        _ => guid_byte,
    }
}

fn read_text_property(c: &mut R, size: i32) -> Result<String> {
    if size <= 0 {
        return Ok(String::new());
    }
    let mut buf = vec![0u8; size as usize];
    c.read_exact(&mut buf)?;
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

fn read_lwc_components(c: &mut R, lwc: bool, names: &[&str]) -> Result<Vec<Property>> {
    let mut props = Vec::new();
    for name in names {
        let value = if lwc {
            PropValue::Double(read_f64(c)?)
        } else {
            PropValue::Float(read_f32(c)?)
        };
        props.push(Property {
            name: name.to_string(),
            value,
        });
    }
    Ok(props)
}

fn read_struct_value(
    c: &mut R,
    nt: &NameTable,
    struct_type: &str,
    _size: i32,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<Vec<Property>> {
    let lwc = ver.file_ver_ue5 >= 1004; // LARGE_WORLD_COORDINATES
    match struct_type {
        "Vector" => read_lwc_components(c, lwc, &["X", "Y", "Z"]),
        "Rotator" => read_lwc_components(c, lwc, &["Pitch", "Yaw", "Roll"]),
        "Vector2D" => read_lwc_components(c, lwc, &["X", "Y"]),
        "LinearColor" => {
            let r = read_f32(c)?;
            let g = read_f32(c)?;
            let b = read_f32(c)?;
            let a = read_f32(c)?;
            Ok(vec![
                Property {
                    name: "R".into(),
                    value: PropValue::Float(r),
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
            let g = read_guid(c)?;
            Ok(vec![Property {
                name: "Guid".into(),
                value: PropValue::Str(format!("{:02x?}", g)),
            }])
        }
        _ => Ok(read_properties(c, nt, end_offset, ver)),
    }
}

fn read_array_items(
    c: &mut R,
    nt: &NameTable,
    inner_type: &str,
    count: i32,
    end_offset: u64,
    ver: AssetVersion,
) -> Result<Vec<PropValue>> {
    let mut items = Vec::new();
    for _ in 0..count {
        if c.position() >= end_offset {
            break;
        }
        let item = read_typed_value(c, nt, inner_type, end_offset, ver)?;
        // Unknown type in array context: consume remaining bytes
        if matches!(&item, PropValue::Unknown { .. }) {
            c.seek(SeekFrom::Start(end_offset))?;
            items.push(item);
            break;
        }
        items.push(item);
    }
    Ok(items)
}
