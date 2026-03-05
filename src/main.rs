use std::io::{Cursor, Read, Seek, SeekFrom};
use std::path::PathBuf;

use anyhow::{ensure, Context, Result};
use clap::Parser as ClapParser;
use serde_json::{json, Value};

// --- CLI ---

#[derive(ClapParser)]
#[command(name = "bp-inspect", about = "Extract Blueprint graph data from .uasset files", version)]
struct Cli {
    /// Path to the .uasset file
    path: PathBuf,

    /// Output as JSON
    #[arg(long)]
    json: bool,

    /// Summary: concise logical structure (class, components, graphs)
    #[arg(long)]
    summary: bool,

    /// Filter exports by name (substring match, comma-separated)
    #[arg(long, short)]
    filter: Option<String>,

    /// Debug: dump raw table data
    #[arg(long)]
    debug: bool,
}

// --- Binary reading helpers ---

type R<'a> = Cursor<&'a [u8]>;

fn read_i32(c: &mut R) -> Result<i32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(i32::from_le_bytes(b))
}

fn read_u32(c: &mut R) -> Result<u32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(u32::from_le_bytes(b))
}

fn read_i64(c: &mut R) -> Result<i64> {
    let mut b = [0u8; 8];
    c.read_exact(&mut b)?;
    Ok(i64::from_le_bytes(b))
}

fn read_u8(c: &mut R) -> Result<u8> {
    let mut b = [0u8; 1];
    c.read_exact(&mut b)?;
    Ok(b[0])
}

fn read_f32(c: &mut R) -> Result<f32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(f32::from_le_bytes(b))
}

fn read_f64(c: &mut R) -> Result<f64> {
    let mut b = [0u8; 8];
    c.read_exact(&mut b)?;
    Ok(f64::from_le_bytes(b))
}

fn read_guid(c: &mut R) -> Result<[u8; 16]> {
    let mut g = [0u8; 16];
    c.read_exact(&mut g)?;
    Ok(g)
}

fn read_fstring(c: &mut R) -> Result<String> {
    let len = read_i32(c)?;
    if len == 0 {
        return Ok(String::new());
    }
    if len > 0 {
        let mut s = vec![0u8; len as usize];
        c.read_exact(&mut s)?;
        Ok(String::from_utf8_lossy(&s).trim_end_matches('\0').to_string())
    } else {
        let count = (-len) as usize;
        let mut s = vec![0u8; count * 2];
        c.read_exact(&mut s)?;
        let utf16: Vec<u16> = s.chunks_exact(2).map(|c| u16::from_le_bytes([c[0], c[1]])).collect();
        Ok(String::from_utf16_lossy(&utf16).trim_end_matches('\0').to_string())
    }
}

// --- Name table ---

struct NameTable {
    names: Vec<String>,
}

impl NameTable {
    fn read(c: &mut R, count: i32, offset: i32) -> Result<Self> {
        c.seek(SeekFrom::Start(offset as u64))?;
        let mut names = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let name = read_fstring(c)?;
            let _hash = read_u32(c)?;
            names.push(name);
        }
        Ok(NameTable { names })
    }

    fn get(&self, index: i32) -> &str {
        self.names.get(index as usize).map(|s| s.as_str()).unwrap_or("?")
    }

    fn fname(&self, c: &mut R) -> Result<String> {
        let index = read_i32(c)?;
        let number = read_i32(c)?;
        let base = self.get(index);
        if number > 0 {
            Ok(format!("{}_{}", base, number - 1))
        } else {
            Ok(base.to_string())
        }
    }

    fn fname_is_none(&self, c: &mut R) -> Result<(String, bool)> {
        let index = read_i32(c)?;
        let number = read_i32(c)?;
        let base = self.get(index);
        let is_none = base == "None" && number == 0;
        let name = if number > 0 {
            format!("{}_{}", base, number - 1)
        } else {
            base.to_string()
        };
        Ok((name, is_none))
    }
}

// --- Import/Export table entries ---

#[derive(Debug)]
#[allow(dead_code)]
struct ImportEntry {
    class_package: String,
    class_name: String,
    object_name: String,
    outer_index: i32,
}

#[derive(Debug)]
struct ExportHeader {
    class_index: i32,
    super_index: i32,
    outer_index: i32,
    object_name: String,
    serial_offset: i64,
    serial_size: i64,
}

// --- Property values ---

#[derive(Debug)]
enum PropValue {
    Bool(bool),
    Int(i32),
    Int64(i64),
    Float(f32),
    Double(f64),
    Str(String),
    Name(String),
    Object(i32),
    Enum { enum_type: String, value: String },
    Struct { struct_type: String, fields: Vec<Property> },
    Array { inner_type: String, items: Vec<PropValue> },
    Map { key_type: String, value_type: String, entries: Vec<(PropValue, PropValue)> },
    Text(String),
    SoftObject(String),
    Byte { enum_name: String, value: String },
    Unknown { type_name: String, size: i32 },
}

#[derive(Debug)]
struct Property {
    name: String,
    value: PropValue,
}

// --- Tagged property parser ---

fn read_properties(c: &mut R, nt: &NameTable, end_offset: u64, file_ver: i32) -> Vec<Property> {
    let mut props = Vec::new();
    loop {
        if c.position() + 8 > end_offset {
            break;
        }
        let pos_before = c.position();
        let Ok((prop_name, is_none)) = nt.fname_is_none(c) else { break };
        if is_none {
            break;
        }
        // Sanity check: need at least 16 more bytes for type_name + size + array_index
        if c.position() + 16 > end_offset {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }
        let Ok(type_name) = nt.fname(c) else { break };

        // Valid UE tagged property types always end in "Property"
        if !type_name.ends_with("Property") {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(size) = read_i32(c) else { break };
        let Ok(_array_index) = read_i32(c) else { break };

        // Sanity: reject nonsensical sizes
        if size < 0 || size as u64 > end_offset - c.position() + 256 {
            let _ = c.seek(SeekFrom::Start(pos_before));
            break;
        }

        let Ok(value) = read_property_value(c, nt, &type_name, size, end_offset, file_ver) else { break };
        props.push(Property { name: prop_name, value });
    }
    props
}

fn read_property_value(
    c: &mut R,
    nt: &NameTable,
    type_name: &str,
    size: i32,
    _end_offset: u64,
    file_ver: i32,
) -> Result<PropValue> {
    let data_start = c.position();

    match type_name {
        "BoolProperty" => {
            let val = read_u8(c)? != 0;
            // HasPropertyGuid
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
            Ok(PropValue::Enum { enum_type: enum_name, value })
        }
        "ByteProperty" => {
            let enum_name = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            if size == 1 {
                let val = read_u8(c)?;
                Ok(PropValue::Byte { enum_name, value: val.to_string() })
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
            let fields = read_struct_value(c, nt, &struct_type, size, struct_end, file_ver)?;
            c.seek(SeekFrom::Start(struct_end))?;
            Ok(PropValue::Struct { struct_type, fields })
        }
        "ArrayProperty" => {
            let inner_type = nt.fname(c)?;
            skip_property_guid(c, file_ver)?;
            let count = read_i32(c)?;
            let array_data_end = data_start + tag_overhead(type_name, file_ver) + size as u64;
            let items = read_array_items(c, nt, &inner_type, count, array_data_end, file_ver)?;
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
                if c.position() >= map_data_end { break; }
                let k = read_map_item(c, nt, &key_type, map_data_end, file_ver)?;
                let v = read_map_item(c, nt, &value_type, map_data_end, file_ver)?;
                entries.push((k, v));
            }
            c.seek(SeekFrom::Start(map_data_end))?;
            Ok(PropValue::Map { key_type, value_type, entries })
        }
        _ => {
            skip_property_guid(c, file_ver)?;
            c.seek(SeekFrom::Current(size as i64))?;
            Ok(PropValue::Unknown { type_name: type_name.to_string(), size })
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

fn read_map_item(c: &mut R, nt: &NameTable, type_name: &str, end_offset: u64, file_ver: i32) -> Result<PropValue> {
    match type_name {
        "IntProperty" | "Int32Property" => Ok(PropValue::Int(read_i32(c)?)),
        "Int64Property" | "UInt64Property" => Ok(PropValue::Int64(read_i64(c)?)),
        "FloatProperty" => Ok(PropValue::Float(read_f32(c)?)),
        "BoolProperty" => Ok(PropValue::Bool(read_u8(c)? != 0)),
        "NameProperty" => Ok(PropValue::Name(nt.fname(c)?)),
        "StrProperty" => Ok(PropValue::Str(read_fstring(c)?)),
        "ObjectProperty" => Ok(PropValue::Object(read_i32(c)?)),
        "EnumProperty" => Ok(PropValue::Name(nt.fname(c)?)),
        "StructProperty" => {
            let fields = read_properties(c, nt, end_offset, file_ver);
            Ok(PropValue::Struct { struct_type: String::new(), fields })
        }
        _ => Ok(PropValue::Unknown { type_name: type_name.to_string(), size: 0 }),
    }
}

fn tag_overhead(_type_name: &str, file_ver: i32) -> u64 {
    // Bytes between data_start and the actual property value data
    // For ArrayProperty: inner_type FName (8) + property guid check (1) + count (4) = 13
    // This is approximate; we mainly use end offset to bound reads
    let guid_byte: u64 = if file_ver >= 503 { 1 } else { 0 };
    match _type_name {
        "ArrayProperty" => 8 + guid_byte + 4,
        "MapProperty" => 16 + guid_byte + 8, // key FName + value FName + guid + num_to_remove + count
        "EnumProperty" => 8 + guid_byte,
        "ByteProperty" => 8 + guid_byte,
        "StructProperty" => 8 + 16 + guid_byte,
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
    let readable: String = text.chars().filter(|c| c.is_ascii_graphic() || *c == ' ').collect();
    Ok(if readable.is_empty() { "<text>".to_string() } else { readable })
}

fn read_struct_value(
    c: &mut R,
    nt: &NameTable,
    struct_type: &str,
    _size: i32,
    end_offset: u64,
    file_ver: i32,
) -> Result<Vec<Property>> {
    match struct_type {
        "Vector" => {
            let x = read_f32(c)?;
            let y = read_f32(c)?;
            let z = read_f32(c)?;
            Ok(vec![
                Property { name: "X".into(), value: PropValue::Float(x) },
                Property { name: "Y".into(), value: PropValue::Float(y) },
                Property { name: "Z".into(), value: PropValue::Float(z) },
            ])
        }
        "Rotator" => {
            let p = read_f32(c)?;
            let y = read_f32(c)?;
            let r = read_f32(c)?;
            Ok(vec![
                Property { name: "Pitch".into(), value: PropValue::Float(p) },
                Property { name: "Yaw".into(), value: PropValue::Float(y) },
                Property { name: "Roll".into(), value: PropValue::Float(r) },
            ])
        }
        "Vector2D" => {
            let x = read_f32(c)?;
            let y = read_f32(c)?;
            Ok(vec![
                Property { name: "X".into(), value: PropValue::Float(x) },
                Property { name: "Y".into(), value: PropValue::Float(y) },
            ])
        }
        "LinearColor" => {
            let r = read_f32(c)?;
            let g = read_f32(c)?;
            let b = read_f32(c)?;
            let a = read_f32(c)?;
            Ok(vec![
                Property { name: "R".into(), value: PropValue::Float(r) },
                Property { name: "G".into(), value: PropValue::Float(g) },
                Property { name: "B".into(), value: PropValue::Float(b) },
                Property { name: "A".into(), value: PropValue::Float(a) },
            ])
        }
        "Guid" => {
            let g = read_guid(c)?;
            Ok(vec![Property {
                name: "Guid".into(),
                value: PropValue::Str(format!("{:02x?}", g)),
            }])
        }
        _ => {
            Ok(read_properties(c, nt, end_offset, file_ver))
        }
    }
}

fn read_array_items(
    c: &mut R,
    nt: &NameTable,
    inner_type: &str,
    count: i32,
    end_offset: u64,
    file_ver: i32,
) -> Result<Vec<PropValue>> {
    let mut items = Vec::new();
    for _ in 0..count {
        if c.position() >= end_offset {
            break;
        }
        let item = match inner_type {
            "IntProperty" | "Int32Property" => PropValue::Int(read_i32(c)?),
            "FloatProperty" => PropValue::Float(read_f32(c)?),
            "NameProperty" => PropValue::Name(nt.fname(c)?),
            "ObjectProperty" => PropValue::Object(read_i32(c)?),
            "StrProperty" => PropValue::Str(read_fstring(c)?),
            "SoftObjectProperty" => {
                let path = read_fstring(c)?;
                let _sub = read_fstring(c)?;
                PropValue::SoftObject(path)
            }
            "StructProperty" => {
                let fields = read_properties(c, nt, end_offset, file_ver);
                PropValue::Struct { struct_type: "".into(), fields }
            }
            _ => {
                let remaining = (end_offset - c.position()) as i32;
                c.seek(SeekFrom::Start(end_offset))?;
                PropValue::Unknown { type_name: inner_type.to_string(), size: remaining }
            }
        };
        items.push(item);
    }
    Ok(items)
}

// --- Skip FField child (for ArrayProperty/MapProperty inner types) ---

fn skip_ffield_child(c: &mut R, nt: &NameTable, end: u64) -> Result<()> {
    if c.position() + 8 > end { return Ok(()); }
    let field_class = nt.fname(c)?;
    if field_class == "None" { return Ok(()); }
    let _field_name = nt.fname(c)?;
    let _flags = read_u32(c)?;
    let has_meta = read_i32(c)?;
    if has_meta != 0 {
        let meta_count = read_i32(c)?;
        for _ in 0..meta_count {
            let _meta_key = nt.fname(c)?;
            let meta_val_len = read_i32(c)?;
            if meta_val_len > 0 {
                c.seek(SeekFrom::Current(meta_val_len as i64))?;
            }
        }
    }
    let _array_dim = read_i32(c)?;
    let _elem_size = read_i32(c)?;
    let _prop_flags = read_i64(c)?;
    let mut rep_bytes = [0u8; 2];
    c.read_exact(&mut rep_bytes)?;
    let _rep_func = nt.fname(c)?;
    let _bp_rep = read_u8(c)?;
    match field_class.as_str() {
        "ObjectProperty" | "WeakObjectProperty" | "ClassProperty"
        | "SoftObjectProperty" | "SoftClassProperty" | "InterfaceProperty" => {
            let _ref = read_i32(c)?;
        }
        "StructProperty" => { let _ref = read_i32(c)?; }
        "ByteProperty" | "EnumProperty" => { let _ref = read_i32(c)?; }
        "BoolProperty" => { for _ in 0..6 { read_u8(c)?; } }
        "ArrayProperty" | "SetProperty" => { skip_ffield_child(c, nt, end)?; }
        "MapProperty" => { skip_ffield_child(c, nt, end)?; skip_ffield_child(c, nt, end)?; }
        "DelegateProperty" | "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty" => { let _ref = read_i32(c)?; }
        _ => {}
    }
    Ok(())
}

// --- FField type resolution (for function signatures) ---

fn resolve_ffield_type(
    field_class: &str, c: &mut R, nt: &NameTable,
    imports: &[ImportEntry], export_names: &[String], end: u64,
) -> Result<String> {
    match field_class {
        "FloatProperty" => Ok("float".into()),
        "DoubleProperty" => Ok("double".into()),
        "IntProperty" | "Int32Property" | "UInt32Property" => Ok("int".into()),
        "Int64Property" | "UInt64Property" => Ok("int64".into()),
        "Int16Property" | "UInt16Property" => Ok("int16".into()),
        "Int8Property" => Ok("int8".into()),
        "BoolProperty" => {
            for _ in 0..6 { read_u8(c)?; }
            Ok("bool".into())
        }
        "StrProperty" => Ok("FString".into()),
        "NameProperty" => Ok("FName".into()),
        "TextProperty" => Ok("FText".into()),
        "ObjectProperty" | "WeakObjectProperty" | "LazyObjectProperty"
        | "SoftObjectProperty" | "InterfaceProperty" => {
            let class_ref = read_i32(c)?;
            if class_ref != 0 {
                Ok(format!("{}*", short_class(&resolve_index(imports, export_names, class_ref))))
            } else {
                Ok("UObject*".into())
            }
        }
        "ClassProperty" | "SoftClassProperty" => {
            let _prop_class = read_i32(c)?;
            let _meta_class = read_i32(c)?;
            Ok("UClass*".into())
        }
        "StructProperty" => {
            let struct_ref = read_i32(c)?;
            Ok(short_class(&resolve_index(imports, export_names, struct_ref)))
        }
        "ByteProperty" | "EnumProperty" => {
            let enum_ref = read_i32(c)?;
            if enum_ref != 0 {
                Ok(short_class(&resolve_index(imports, export_names, enum_ref)))
            } else {
                Ok("byte".into())
            }
        }
        "ArrayProperty" | "SetProperty" => {
            skip_ffield_child(c, nt, end)?;
            Ok(if field_class == "SetProperty" { "TSet<>".into() } else { "TArray<>".into() })
        }
        "MapProperty" => {
            skip_ffield_child(c, nt, end)?;
            skip_ffield_child(c, nt, end)?;
            Ok("TMap<>".into())
        }
        "DelegateProperty" | "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty" | "MulticastSparseDelegateProperty" => {
            let _sig = read_i32(c)?;
            Ok("Delegate".into())
        }
        _ => Ok(field_class.strip_suffix("Property").unwrap_or(field_class).to_string()),
    }
}

fn format_signature(func_name: &str, params: &[(String, String, u64)]) -> String {
    const CPF_PARM: u64 = 0x80;
    const CPF_OUT_PARM: u64 = 0x100;
    const CPF_RETURN_PARM: u64 = 0x200;

    let mut inputs = Vec::new();
    let mut ret_type = None;

    for (name, type_name, flags) in params {
        if *flags & CPF_RETURN_PARM != 0 {
            ret_type = Some(type_name.clone());
        } else if *flags & CPF_PARM != 0 {
            if *flags & CPF_OUT_PARM != 0 {
                inputs.push(format!("out {}: {}", name, type_name));
            } else {
                inputs.push(format!("{}: {}", name, type_name));
            }
        }
        // Internal locals (no CPF_Parm) are not part of the signature
    }

    let sig = format!("{}({})", func_name, inputs.join(", "));
    match ret_type {
        Some(t) => format!("{} -> {}", sig, t),
        None => sig,
    }
}

// --- Bytecode name cleanup ---

fn clean_bc_name(name: &str) -> String {
    // Shorten verbose Blueprint-generated local variable names
    // CallFunc_Multiply_FloatFloat_ReturnValue → $Multiply_FloatFloat
    // K2Node_DynamicCast_AsWinch_Constraint_BP → $Cast_AsWinch_Constraint_BP
    // K2Node_DynamicCast_bSuccess → $Cast_bSuccess
    if let Some(rest) = name.strip_prefix("CallFunc_") {
        // Strip trailing _ReturnValue
        let rest = rest.strip_suffix("_ReturnValue").unwrap_or(rest);
        return format!("${}", rest);
    }
    if let Some(rest) = name.strip_prefix("K2Node_DynamicCast_") {
        return format!("$Cast_{}", rest);
    }
    if let Some(rest) = name.strip_prefix("K2Node_") {
        return format!("${}", rest);
    }
    name.to_string()
}

// --- Kismet bytecode decoder ---

fn read_bc_u8(bc: &[u8], pos: &mut usize) -> u8 {
    if *pos >= bc.len() { *pos = bc.len(); return 0; }
    let v = bc[*pos];
    *pos += 1;
    v
}

fn read_bc_i32(bc: &[u8], pos: &mut usize) -> i32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0; }
    let v = i32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

fn read_bc_u32(bc: &[u8], pos: &mut usize) -> u32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0; }
    let v = u32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

fn read_bc_i64(bc: &[u8], pos: &mut usize) -> i64 {
    if *pos + 8 > bc.len() { *pos = bc.len(); return 0; }
    let v = i64::from_le_bytes([
        bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3],
        bc[*pos+4], bc[*pos+5], bc[*pos+6], bc[*pos+7],
    ]);
    *pos += 8;
    v
}

fn read_bc_f32(bc: &[u8], pos: &mut usize) -> f32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0.0; }
    let v = f32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

fn read_bc_fname(bc: &[u8], pos: &mut usize, nt: &NameTable) -> String {
    let index = read_bc_i32(bc, pos);
    let number = read_bc_i32(bc, pos);
    let base = nt.get(index);
    if number > 0 { format!("{}_{}", base, number - 1) } else { base.to_string() }
}

fn read_bc_string(bc: &[u8], pos: &mut usize) -> String {
    let mut s = Vec::new();
    while *pos < bc.len() {
        let b = bc[*pos];
        *pos += 1;
        if b == 0 { break; }
        s.push(b);
    }
    String::from_utf8_lossy(&s).to_string()
}

fn resolve_bc_obj(index: i32, imports: &[ImportEntry], export_names: &[String]) -> String {
    if index < 0 {
        short_class(&resolve_import_path(imports, index))
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names.get(idx).cloned().unwrap_or_else(|| format!("export[{}]", index))
    } else {
        "null".to_string()
    }
}

/// Read a UObject* reference from serialized bytecode (int32 FPackageIndex)
fn read_bc_obj_ref(bc: &[u8], pos: &mut usize, imports: &[ImportEntry], export_names: &[String]) -> String {
    let index = read_bc_i32(bc, pos);
    resolve_bc_obj(index, imports, export_names)
}

/// Read an FField* reference from serialized bytecode (FFieldPath format for UE4.25+)
/// Format: int32 PathNum + FName[PathNum] + int32 ResolvedOwner
fn read_bc_field_path(bc: &[u8], pos: &mut usize, nt: &NameTable) -> String {
    let path_num = read_bc_i32(bc, pos);
    if path_num <= 0 {
        let _owner = read_bc_i32(bc, pos);
        return "null".to_string();
    }
    // Sanity check: each FName is 8 bytes + 4 bytes owner at end
    let needed = path_num as usize * 8 + 4;
    if path_num > 16 || *pos + needed > bc.len() + 8 {
        // Garbage path_num — skip owner and bail
        let _owner = read_bc_i32(bc, pos);
        return "???".to_string();
    }
    let mut names = Vec::new();
    for _ in 0..path_num {
        names.push(clean_bc_name(&read_bc_fname(bc, pos, nt)));
    }
    let _owner = read_bc_i32(bc, pos);
    names.join(".")
}

/// Read EX_Context/EX_ClassContext r-value info
/// Format: uint32 skip (in-memory) + FFieldPath r-value property (no size byte)
fn read_bc_context_rvalue(bc: &[u8], pos: &mut usize, nt: &NameTable) {
    let _skip = read_bc_u32(bc, pos);
    let _rvalue = read_bc_field_path(bc, pos, nt);
}

/// Decode a single Kismet expression, returning a string representation.
/// Returns None if at end of script or unknown opcode.
fn decode_expr(bc: &[u8], pos: &mut usize, nt: &NameTable,
               imports: &[ImportEntry], export_names: &[String]) -> Option<String> {
    if *pos >= bc.len() { return None; }
    let opcode = read_bc_u8(bc, pos);
    match opcode {
        0x00 => { // EX_LocalVariable
            let prop = read_bc_field_path(bc, pos, nt);
            Some(prop)
        }
        0x01 => { // EX_InstanceVariable
            let prop = read_bc_field_path(bc, pos, nt);
            Some(format!("self.{}", prop))
        }
        0x02 => { // EX_DefaultVariable
            let prop = read_bc_field_path(bc, pos, nt);
            Some(format!("default.{}", prop))
        }
        0x04 => { // EX_Return
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("return {}", expr))
        }
        0x06 => { // EX_Jump
            let offset = read_bc_u32(bc, pos);
            Some(format!("jump 0x{:x}", offset))
        }
        0x07 => { // EX_JumpIfNot
            let offset = read_bc_u32(bc, pos);
            let cond = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("if !({}) jump 0x{:x}", cond, offset))
        }
        0x0B => Some("nop".into()), // EX_Nothing
        0x0F => { // EX_Let
            let _prop = read_bc_field_path(bc, pos, nt); // type info, redundant with variable
            let var = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x12 => { // EX_ClassContext
            let obj = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}.{}", obj, expr))
        }
        0x13 => { // EX_MetaCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("cast<{}>({})", class, expr))
        }
        0x14 => { // EX_LetBool
            let var = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x15 => Some("end_param".into()), // EX_EndParmValue
        0x16 => None, // EX_EndFunctionParms — handled by function call decoders
        0x17 => Some("self".into()), // EX_Self
        0x18 => { // EX_Skip
            let _skip = read_bc_u32(bc, pos);
            decode_expr(bc, pos, nt, imports, export_names)
        }
        0x19 => { // EX_Context
            let obj = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}.{}", obj, expr))
        }
        0x1A => { // EX_Context_FailSilent
            let obj = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}?.{}", obj, expr))
        }
        0x1B => { // EX_VirtualFunction
            let name = read_bc_fname(bc, pos, nt);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}({})", name, args.join(", ")))
        }
        0x1C => { // EX_FinalFunction
            let func = read_bc_obj_ref(bc, pos, imports, export_names);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x1D => Some(format!("{}", read_bc_i32(bc, pos))),    // EX_IntConst
        0x1E => Some(format!("{:.4}", read_bc_f32(bc, pos))), // EX_FloatConst
        0x1F => Some(format!("\"{}\"", read_bc_string(bc, pos))), // EX_StringConst
        0x20 => { // EX_ObjectConst
            let obj = read_bc_obj_ref(bc, pos, imports, export_names);
            Some(obj)
        }
        0x21 => { // EX_NameConst
            let name = read_bc_fname(bc, pos, nt);
            Some(format!("'{}'", name))
        }
        0x22 => { // EX_RotationConst
            let p = read_bc_f32(bc, pos);
            let y = read_bc_f32(bc, pos);
            let r = read_bc_f32(bc, pos);
            Some(format!("Rot({:.1},{:.1},{:.1})", p, y, r))
        }
        0x23 => { // EX_VectorConst
            let x = read_bc_f32(bc, pos);
            let y = read_bc_f32(bc, pos);
            let z = read_bc_f32(bc, pos);
            Some(format!("Vec({:.1},{:.1},{:.1})", x, y, z))
        }
        0x24 => Some(format!("{}", read_bc_u8(bc, pos))), // EX_ByteConst
        0x25 => Some("0".into()),    // EX_IntZero
        0x26 => Some("1".into()),    // EX_IntOne
        0x27 => Some("true".into()), // EX_True
        0x28 => Some("false".into()),// EX_False
        0x29 => { // EX_TextConst
            let text_type = read_bc_u8(bc, pos);
            match text_type {
                0xFF => Some("\"\"".into()),
                0 => { // LOCTEXT
                    let _ns = read_bc_string(bc, pos);
                    let _key = read_bc_string(bc, pos);
                    let val = read_bc_string(bc, pos);
                    Some(format!("\"{}\"", val))
                }
                _ => Some(format!("text(type={})", text_type))
            }
        }
        0x2A => Some("null".into()),  // EX_NoObject
        0x2C => Some(format!("{}", read_bc_u8(bc, pos))), // EX_IntConstByte
        0x2E => { // EX_DynamicCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("cast<{}>({})", class, expr))
        }
        0x34 => { // EX_UnicodeStringConst
            let mut s = Vec::new();
            while *pos + 1 < bc.len() {
                let lo = bc[*pos]; let hi = bc[*pos + 1];
                *pos += 2;
                if lo == 0 && hi == 0 { break; }
                s.push(u16::from_le_bytes([lo, hi]));
            }
            Some(format!("\"{}\"", String::from_utf16_lossy(&s)))
        }
        0x35 => Some(format!("{}L", read_bc_i64(bc, pos))), // EX_Int64Const
        0x38 => { // EX_PrimitiveCast
            let cast_type = read_bc_u8(bc, pos);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("cast_{}({})", cast_type, expr))
        }
        0x41 => { // EX_StructMemberContext
            let prop = read_bc_field_path(bc, pos, nt);
            let struct_expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{}.{}", struct_expr, prop))
        }
        0x44 => { // EX_LocalVirtualFunction
            let name = read_bc_fname(bc, pos, nt);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}({})", name, args.join(", ")))
        }
        0x45 => { // EX_LocalFinalFunction
            let func = read_bc_fname(bc, pos, nt);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x48 => { // EX_LocalOutVariable
            let prop = read_bc_field_path(bc, pos, nt);
            Some(format!("out {}", prop))
        }
        0x4C => { // EX_PushExecutionFlow
            let offset = read_bc_u32(bc, pos);
            Some(format!("push_flow 0x{:x}", offset))
        }
        0x4D => Some("pop_flow".into()), // EX_PopExecutionFlow
        0x4F => { // EX_PopExecutionFlowIfNot
            let cond = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("pop_flow_if_not({})", cond))
        }
        0x50 => Some("breakpoint".into()), // EX_Breakpoint
        0x51 => { // EX_InterfaceContext
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("iface({})", expr))
        }
        0x52 => { // EX_ObjToInterfaceCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names);
            let expr = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("icast<{}>({})", class, expr))
        }
        0x53 => None, // EX_EndOfScript
        0x5A => Some("wire_trace".into()), // EX_WireTracepoint
        0x5B => { // EX_SkipOffsetConst
            let offset = read_bc_u32(bc, pos);
            Some(format!("skip_offset(0x{:x})", offset))
        }
        0x5C => { // EX_AddMulticastDelegate
            let delegate = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let func = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{} += {}", delegate, func))
        }
        0x5E => Some("tracepoint".into()), // EX_Tracepoint
        0x5F => { // EX_LetObj
            let var = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x60 => { // EX_LetWeakObjPtr
            let var = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("{} = weak({})", var, val))
        }
        0x61 => { // EX_BindDelegate
            let name = read_bc_fname(bc, pos, nt);
            let delegate = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            let obj = decode_expr(bc, pos, nt, imports, export_names).unwrap_or_default();
            Some(format!("bind({}, {}, {})", name, delegate, obj))
        }
        0x63 => { // EX_CallMulticastDelegate
            let func = read_bc_obj_ref(bc, pos, imports, export_names);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}.Broadcast({})", func, args.join(", ")))
        }
        0x68 => { // EX_CallMath
            let func = read_bc_obj_ref(bc, pos, imports, export_names);
            let args = decode_func_args(bc, pos, nt, imports, export_names);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x6A => { // EX_InstrumentationEvent
            let _event_type = read_bc_u8(bc, pos);
            Some("instrumentation".into())
        }
        _ => {
            // Unknown opcode — can't continue safely
            Some(format!("???(0x{:02x})", opcode))
        }
    }
}

fn decode_func_args(bc: &[u8], pos: &mut usize, nt: &NameTable,
                    imports: &[ImportEntry], export_names: &[String]) -> Vec<String> {
    let mut args = Vec::new();
    loop {
        if *pos >= bc.len() { break; }
        if bc[*pos] == 0x16 { // EX_EndFunctionParms
            *pos += 1;
            break;
        }
        if let Some(expr) = decode_expr(bc, pos, nt, imports, export_names) {
            args.push(expr);
        } else {
            break;
        }
    }
    args
}

fn decode_bytecode(bc: &[u8], nt: &NameTable,
                   imports: &[ImportEntry], export_names: &[String]) -> Vec<String> {
    let mut pos = 0;
    let mut stmts = Vec::new();
    while pos < bc.len() {
        let start = pos;
        match decode_expr(bc, &mut pos, nt, imports, export_names) {
            Some(s) => {
                // Filter out noise (tracepoints, nops)
                match s.as_str() {
                    "nop" | "wire_trace" | "tracepoint" | "instrumentation" => continue,
                    _ => stmts.push(format!("{:04x}: {}", start, s)),
                }
            }
            None => break, // EndOfScript or end of data
        }
        // Safety: if we haven't advanced, break to avoid infinite loop
        if pos == start { break; }
    }
    stmts
}

// --- Resolve package indices to names ---

fn resolve_import_path(imports: &[ImportEntry], index: i32) -> String {
    if index >= 0 {
        return "?".to_string();
    }
    let idx = (-index - 1) as usize;
    let imp = match imports.get(idx) {
        Some(i) => i,
        None => return "?".to_string(),
    };
    if imp.outer_index == 0 {
        // Top-level package
        imp.object_name.clone()
    } else {
        let outer = resolve_import_path(imports, imp.outer_index);
        format!("{}.{}", outer, imp.object_name)
    }
}

fn resolve_index(imports: &[ImportEntry], export_names: &[String], index: i32) -> String {
    if index < 0 {
        resolve_import_path(imports, index)
    } else if index > 0 {
        let idx = (index - 1) as usize;
        export_names.get(idx).cloned().unwrap_or_else(|| format!("Export({})", index))
    } else {
        "None".to_string()
    }
}

// --- Parse the full asset ---

struct ParsedAsset {
    imports: Vec<ImportEntry>,
    exports: Vec<(ExportHeader, Vec<Property>)>,
}

fn parse_asset(data: &[u8], debug: bool) -> Result<ParsedAsset> {
    let file_size = data.len();
    let mut c = Cursor::new(data);

    // --- Package file summary ---
    let magic = read_u32(&mut c).context("truncated file: cannot read magic")?;
    ensure!(magic == 0x9E2A83C1, "not a valid .uasset file (magic: {:#X})", magic);
    let legacy_ver = read_i32(&mut c)?;
    if legacy_ver < -3 && legacy_ver != -4 {
        let _ue3_ver = read_i32(&mut c)?;
    }
    let file_ver = read_i32(&mut c)?;
    let _licensee_ver = read_i32(&mut c)?;
    let custom_ver_count = read_i32(&mut c)?;
    c.seek(SeekFrom::Current(custom_ver_count as i64 * 20))?;
    let _total_header_size = read_i32(&mut c)?;
    let _folder_name = read_fstring(&mut c)?;
    let _pkg_flags = read_u32(&mut c)?;
    let name_count = read_i32(&mut c)?;
    let name_offset = read_i32(&mut c)?;
    if file_ver >= 516 { let _loc_id = read_fstring(&mut c)?; }
    if file_ver >= 459 { let _gc = read_i32(&mut c)?; let _go = read_i32(&mut c)?; }
    let export_count = read_i32(&mut c)?;
    let export_offset = read_i32(&mut c)?;
    let import_count = read_i32(&mut c)?;
    let import_offset = read_i32(&mut c)?;

    // --- Name table ---
    let nt = NameTable::read(&mut c, name_count, name_offset)
        .context("failed to read name table")?;

    if debug {
        eprintln!("Header: file_ver={} names={} imports={} exports={}", file_ver, name_count, import_count, export_count);
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
        if debug {
            eprintln!("  Import[{}]: {}::{} outer={} name={}",
                imports.len(), class_package, class_name, outer_index, object_name);
        }
        imports.push(ImportEntry { class_package, class_name, object_name, outer_index });
    }

    // --- Export table ---
    c.seek(SeekFrom::Start(export_offset as u64))?;
    let mut export_headers = Vec::with_capacity(export_count as usize);
    for _ in 0..export_count {
        let class_index = read_i32(&mut c)?;
        let super_index = read_i32(&mut c)?;
        if file_ver >= 459 { let _template = read_i32(&mut c)?; }
        let outer_index = read_i32(&mut c)?;
        let object_name = nt.fname(&mut c)?;
        let _object_flags = read_u32(&mut c)?;
        let serial_size = read_i64(&mut c)?;
        let serial_offset = read_i64(&mut c)?;
        let _forced = read_i32(&mut c)?;
        let _not_client = read_i32(&mut c)?;
        let _not_server = read_i32(&mut c)?;
        let _guid = read_guid(&mut c)?;
        let _pkg_flags = read_u32(&mut c)?;
        if file_ver >= 459 { let _not_always = read_i32(&mut c)?; }
        if file_ver >= 459 { let _is_asset = read_i32(&mut c)?; }
        if file_ver >= 518 {
            let _first_dep = read_i32(&mut c)?;
            let _s_before_s = read_i32(&mut c)?;
            let _c_before_s = read_i32(&mut c)?;
            let _s_before_c = read_i32(&mut c)?;
            let _c_before_c = read_i32(&mut c)?;
        }
        export_headers.push(ExportHeader {
            class_index, super_index, outer_index, object_name,
            serial_offset, serial_size,
        });
    }

    // --- Export data (properties) ---
    let export_names_pre: Vec<String> = export_headers.iter().map(|h| h.object_name.clone()).collect();
    let mut exports = Vec::with_capacity(export_headers.len());
    for hdr in &export_headers {
        if hdr.serial_size <= 0 || hdr.serial_offset < 0 || (hdr.serial_offset + hdr.serial_size) > file_size as i64 {
            exports.push((hdr.clone_header(), Vec::new()));
            continue;
        }

        // Per-export parsing: errors here skip the export rather than aborting
        let export_result: Result<Vec<Property>> = (|| {
            c.seek(SeekFrom::Start(hdr.serial_offset as u64))?;
            let end = hdr.serial_offset as u64 + hdr.serial_size as u64;
            let class_name = resolve_index(&imports, &export_names_pre, hdr.class_index);

            let is_struct = class_name.ends_with(".Function") || class_name.ends_with(".Struct")
                || class_name.ends_with(".BlueprintGeneratedClass")
                || class_name.ends_with(".ScriptStruct");
            if !is_struct {
                return Ok(read_properties(&mut c, &nt, end, file_ver));
            }

            let is_function = class_name.ends_with(".Function");
            let props = read_properties(&mut c, &nt, end, file_ver);
            let after_props = c.position();

            let mut extra_props = props;
            if after_props + 12 <= end {
                let _next = read_i32(&mut c)?;
                let super_ref = read_i32(&mut c)?;
                let children_count = read_i32(&mut c)?;
                if children_count > 0 && children_count < 1000 {
                    c.seek(SeekFrom::Current(children_count as i64 * 4))?;
                }
                if debug {
                    eprintln!("  {} UStruct: after_props={} next={} super={} children={} pos={}",
                        hdr.object_name, after_props, _next, super_ref, children_count, c.position());
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
                    eprintln!("  {} child properties: {}", hdr.object_name, child_prop_count);
                }
                for _ci in 0..child_prop_count {
                    if c.position() + 16 > end { break; }
                    let field_class = nt.fname(&mut c)?;
                    let field_name = nt.fname(&mut c)?;
                    let _flags = read_u32(&mut c)?;
                    let has_meta = read_i32(&mut c)?;
                    if has_meta != 0 {
                        let meta_count = read_i32(&mut c)?;
                        for _ in 0..meta_count {
                            let _meta_key = nt.fname(&mut c)?;
                            let meta_val_len = read_i32(&mut c)?;
                            if meta_val_len > 0 {
                                c.seek(SeekFrom::Current(meta_val_len as i64))?;
                            }
                        }
                    }
                    let _array_dim = read_i32(&mut c)?;
                    let _elem_size = read_i32(&mut c)?;
                    let prop_flags = read_i64(&mut c)? as u64;
                    let mut rep_bytes = [0u8; 2];
                    c.read_exact(&mut rep_bytes)?;
                    let _rep_notify_func = nt.fname(&mut c)?;
                    let _bp_rep_condition = read_u8(&mut c)?;
                    let type_name = resolve_ffield_type(
                        &field_class, &mut c, &nt, &imports, &export_names_pre, end,
                    )?;
                    ffield_children.push((field_name.clone(), type_name, prop_flags));
                    if debug {
                        eprintln!("    param: {} {} flags=0x{:x} @ {}",
                            field_class, field_name, prop_flags, c.position());
                    }
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
                let members: Vec<PropValue> = ffield_children.iter()
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
            if c.position() + 8 <= end {
                if debug {
                    let spos = c.position();
                    let peek_len = std::cmp::min(16, (end - spos) as usize);
                    let mut peek = vec![0u8; peek_len];
                    c.read_exact(&mut peek)?;
                    c.seek(SeekFrom::Start(spos))?;
                    let hex: Vec<String> = peek.iter().map(|b| format!("{:02x}", b)).collect();
                    eprintln!("  {} script @ {} (end={}) raw: {}", hdr.object_name, spos, end, hex.join(" "));
                }
                let bytecode_size = read_i32(&mut c)?;
                let storage_size = read_i32(&mut c)?;
                if storage_size > 0 && (c.position() + storage_size as u64) <= end {
                    bytecode_data = vec![0u8; storage_size as usize];
                    c.read_exact(&mut bytecode_data)?;
                    if debug {
                        eprintln!("  {} bytecode: {}B mem, {}B disk",
                            hdr.object_name, bytecode_size, storage_size);
                        let show = std::cmp::min(bytecode_data.len(), 64);
                        let hex: Vec<String> = bytecode_data[..show].iter().map(|b| format!("{:02x}", b)).collect();
                        eprintln!("    hex: {}", hex.join(" "));
                    }
                }
            }

            if !bytecode_data.is_empty() {
                let decoded = decode_bytecode(&bytecode_data, &nt, &imports, &export_names_pre);
                if !decoded.is_empty() {
                    extra_props.push(Property {
                        name: "Bytecode".into(),
                        value: PropValue::Array {
                            inner_type: "StrProperty".into(),
                            items: decoded.into_iter().map(PropValue::Str).collect(),
                        },
                    });
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

        exports.push((hdr.clone_header(), export_result.unwrap_or_default()));
    }

    Ok(ParsedAsset { imports, exports })
}

impl ExportHeader {
    fn clone_header(&self) -> ExportHeader {
        ExportHeader {
            class_index: self.class_index,
            super_index: self.super_index,
            outer_index: self.outer_index,
            object_name: self.object_name.clone(),
            serial_offset: self.serial_offset,
            serial_size: self.serial_size,
        }
    }
}

// --- Output: Text ---

fn matches_filter(name: &str, filters: &[String]) -> bool {
    if filters.is_empty() { return true; }
    let lower = name.to_lowercase();
    filters.iter().any(|f| lower.contains(f))
}

fn print_text(asset: &ParsedAsset, filters: &[String]) {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

    println!("=== Blueprint Dump ===\n");

    println!("--- Imports ({}) ---", asset.imports.len());
    for (i, imp) in asset.imports.iter().enumerate() {
        let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
        println!("  [{}] {} ({}::{})", i, full_path, imp.class_package, imp.class_name);
    }

    println!("\n--- Exports ({}) ---", asset.exports.len());
    for (i, (hdr, props)) in asset.exports.iter().enumerate() {
        if !matches_filter(&hdr.object_name, filters) { continue; }
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        let parent = resolve_index(&asset.imports, &export_names, hdr.super_index);
        if parent != "None" {
            println!("\n  [{}] {} (class: {}, parent: {})", i + 1, hdr.object_name, class, parent);
        } else {
            println!("\n  [{}] {} (class: {})", i + 1, hdr.object_name, class);
        }
        for prop in props {
            print_property(prop, &asset.imports, &export_names, 4);
        }
    }
}

fn print_property(prop: &Property, imports: &[ImportEntry], export_names: &[String], indent: usize) {
    let pad = " ".repeat(indent);
    match &prop.value {
        PropValue::Bool(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Int(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Int64(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Float(v) => println!("{}{}: {:.4}", pad, prop.name, v),
        PropValue::Double(v) => println!("{}{}: {:.4}", pad, prop.name, v),
        PropValue::Str(v) => println!("{}{}: \"{}\"", pad, prop.name, v),
        PropValue::Name(v) => println!("{}{}: {}", pad, prop.name, v),
        PropValue::Object(idx) => {
            let target = resolve_index(imports, export_names, *idx);
            println!("{}{}: -> {}", pad, prop.name, target);
        }
        PropValue::Enum { enum_type, value } => {
            println!("{}{}: {} ({})", pad, prop.name, value, enum_type);
        }
        PropValue::Byte { enum_name, value } => {
            if enum_name == "None" {
                println!("{}{}: {}", pad, prop.name, value);
            } else {
                println!("{}{}: {} ({})", pad, prop.name, value, enum_name);
            }
        }
        PropValue::Struct { struct_type, fields } => {
            if fields.is_empty() {
                println!("{}{}: ({}) {{}}", pad, prop.name, struct_type);
            } else {
                println!("{}{}: ({}) {{", pad, prop.name, struct_type);
                for f in fields {
                    print_property(f, imports, export_names, indent + 2);
                }
                println!("{}}}", pad);
            }
        }
        PropValue::Array { inner_type, items } => {
            println!("{}{}: [{}; {} items]", pad, prop.name, inner_type, items.len());
            for (j, item) in items.iter().enumerate() {
                let child = Property { name: format!("[{}]", j), value: clone_value(item) };
                print_property(&child, imports, export_names, indent + 2);
            }
        }
        PropValue::Map { key_type, value_type, entries } => {
            println!("{}{}: {{{}->{}; {} entries}}", pad, prop.name, key_type, value_type, entries.len());
            for (j, (k, v)) in entries.iter().enumerate() {
                let kp = Property { name: format!("[{}].key", j), value: clone_value(k) };
                let vp = Property { name: format!("[{}].val", j), value: clone_value(v) };
                print_property(&kp, imports, export_names, indent + 2);
                print_property(&vp, imports, export_names, indent + 2);
            }
        }
        PropValue::Text(v) => println!("{}{}: \"{}\"", pad, prop.name, v),
        PropValue::SoftObject(v) => println!("{}{}: ~{}", pad, prop.name, v),
        PropValue::Unknown { type_name, size } => {
            println!("{}{}: <{}, {} bytes>", pad, prop.name, type_name, size);
        }
    }
}

fn clone_value(v: &PropValue) -> PropValue {
    match v {
        PropValue::Bool(b) => PropValue::Bool(*b),
        PropValue::Int(i) => PropValue::Int(*i),
        PropValue::Int64(i) => PropValue::Int64(*i),
        PropValue::Float(f) => PropValue::Float(*f),
        PropValue::Double(d) => PropValue::Double(*d),
        PropValue::Str(s) => PropValue::Str(s.clone()),
        PropValue::Name(n) => PropValue::Name(n.clone()),
        PropValue::Object(i) => PropValue::Object(*i),
        PropValue::Enum { enum_type, value } => PropValue::Enum { enum_type: enum_type.clone(), value: value.clone() },
        PropValue::Byte { enum_name, value } => PropValue::Byte { enum_name: enum_name.clone(), value: value.clone() },
        PropValue::Struct { struct_type, fields } => PropValue::Struct {
            struct_type: struct_type.clone(),
            fields: fields.iter().map(|p| Property { name: p.name.clone(), value: clone_value(&p.value) }).collect(),
        },
        PropValue::Array { inner_type, items } => PropValue::Array {
            inner_type: inner_type.clone(),
            items: items.iter().map(clone_value).collect(),
        },
        PropValue::Map { key_type, value_type, entries } => PropValue::Map {
            key_type: key_type.clone(),
            value_type: value_type.clone(),
            entries: entries.iter().map(|(k, v)| (clone_value(k), clone_value(v))).collect(),
        },
        PropValue::Text(t) => PropValue::Text(t.clone()),
        PropValue::SoftObject(s) => PropValue::SoftObject(s.clone()),
        PropValue::Unknown { type_name, size } => PropValue::Unknown { type_name: type_name.clone(), size: *size },
    }
}

// --- Output: JSON ---

fn to_json(asset: &ParsedAsset, filters: &[String]) -> Value {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

    json!({
        "imports": asset.imports.iter().enumerate().map(|(i, imp)| {
            let full_path = resolve_import_path(&asset.imports, -(i as i32 + 1));
            json!({
                "index": i,
                "name": imp.object_name,
                "path": full_path,
                "class_package": imp.class_package,
                "class_name": imp.class_name,
            })
        }).collect::<Vec<_>>(),
        "exports": asset.exports.iter().enumerate().filter(|(_, (hdr, _))| {
            matches_filter(&hdr.object_name, filters)
        }).map(|(i, (hdr, props))| {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            let parent = resolve_index(&asset.imports, &export_names, hdr.super_index);
            let mut exp = json!({
                "index": i + 1,
                "name": hdr.object_name,
                "class": class,
            });
            if parent != "None" {
                exp["parent"] = json!(parent);
            }
            if !props.is_empty() {
                exp["properties"] = Value::Array(
                    props.iter().map(|p| prop_to_json(p, &asset.imports, &export_names)).collect()
                );
            }
            exp
        }).collect::<Vec<_>>(),
    })
}

fn prop_to_json(prop: &Property, imports: &[ImportEntry], export_names: &[String]) -> Value {
    let val = match &prop.value {
        PropValue::Bool(v) => json!(v),
        PropValue::Int(v) => json!(v),
        PropValue::Int64(v) => json!(v),
        PropValue::Float(v) => json!(v),
        PropValue::Double(v) => json!(v),
        PropValue::Str(v) => json!(v),
        PropValue::Name(v) => json!(v),
        PropValue::Object(idx) => json!(resolve_index(imports, export_names, *idx)),
        PropValue::Enum { value, .. } => json!(value),
        PropValue::Byte { value, .. } => json!(value),
        PropValue::Struct { struct_type, fields } => json!({
            "type": struct_type,
            "fields": fields.iter().map(|f| prop_to_json(f, imports, export_names)).collect::<Vec<_>>(),
        }),
        PropValue::Array { inner_type, items } => json!({
            "inner_type": inner_type,
            "items": items.iter().map(|item| {
                let child = Property { name: String::new(), value: clone_value(item) };
                prop_to_json(&child, imports, export_names)["value"].clone()
            }).collect::<Vec<_>>(),
        }),
        PropValue::Map { key_type, value_type, entries } => json!({
            "key_type": key_type,
            "value_type": value_type,
            "entries": entries.iter().map(|(k, v)| {
                let kp = Property { name: String::new(), value: clone_value(k) };
                let vp = Property { name: String::new(), value: clone_value(v) };
                json!({
                    "key": prop_to_json(&kp, imports, export_names)["value"],
                    "value": prop_to_json(&vp, imports, export_names)["value"],
                })
            }).collect::<Vec<_>>(),
        }),
        PropValue::Text(v) => json!(v),
        PropValue::SoftObject(v) => json!(v),
        PropValue::Unknown { type_name, size } => json!({"unknown_type": type_name, "size": size}),
    };
    json!({ "name": prop.name, "value": val })
}

// --- Output: Summary ---

fn print_summary(asset: &ParsedAsset, filters: &[String]) {
    let export_names: Vec<String> = asset.exports.iter().map(|(h, _)| h.object_name.clone()).collect();

    // Find the Blueprint and generated class exports
    let mut bp_name = String::new();
    let mut bp_parent = String::new();

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if class.ends_with(".Blueprint") {
            bp_name = hdr.object_name.clone();
            if let Some(p) = find_prop(props, "ParentClass") {
                if let PropValue::Object(idx) = &p.value {
                    bp_parent = resolve_index(&asset.imports, &export_names, *idx);
                    // Strip Default__ prefix and class suffix for readability
                    if let Some(stripped) = bp_parent.strip_suffix("'") {
                        bp_parent = stripped.to_string();
                    }
                    bp_parent = bp_parent.replace("Default__", "");
                }
            }
            break;
        }
    }

    println!("Blueprint: {} (extends {})", bp_name, short_class(&bp_parent));
    println!();

    // Components from SCS_Node exports — build tree structure
    // scs_node_name -> (comp_name, comp_class, child_scs_node_names)
    let mut scs_nodes: std::collections::HashMap<String, (String, String, Vec<String>)> = std::collections::HashMap::new();
    let mut components: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".SCS_Node") { continue; }
        let comp_name = find_prop_str(props, "InternalVariableName")
            .or_else(|| {
                find_prop(props, "ComponentTemplate").and_then(|p| match &p.value {
                    PropValue::Object(idx) => {
                        let tpl = resolve_index(&asset.imports, &export_names, *idx);
                        Some(tpl.trim_end_matches("_GEN_VARIABLE").to_string())
                    }
                    _ => None,
                })
            })
            .unwrap_or_else(|| hdr.object_name.clone());
        let comp_class = find_prop(props, "ComponentClass")
            .and_then(|p| match &p.value {
                PropValue::Object(idx) => Some(short_class(&resolve_index(&asset.imports, &export_names, *idx))),
                _ => None,
            })
            .unwrap_or_else(|| "?".into());
        let children = find_prop(props, "ChildNodes")
            .and_then(|p| match &p.value {
                PropValue::Array { items, .. } => Some(items.iter().filter_map(|i| match i {
                    PropValue::Object(idx) => Some(resolve_index(&asset.imports, &export_names, *idx)),
                    _ => None,
                }).collect()),
                _ => None,
            })
            .unwrap_or_default();
        components.push((comp_name.clone(), comp_class.clone()));
        scs_nodes.insert(hdr.object_name.clone(), (comp_name, comp_class, children));
    }

    // Find root nodes (not referenced as children by any other node)
    let all_children: Vec<String> = scs_nodes.values()
        .flat_map(|(_, _, children)| children.iter().cloned())
        .collect();
    let root_nodes: Vec<String> = scs_nodes.keys()
        .filter(|k| !all_children.contains(k))
        .cloned()
        .collect();

    // Build lookup of component sub-object properties (*_GEN_VARIABLE exports)
    let mut comp_props: std::collections::HashMap<String, &[Property]> = std::collections::HashMap::new();
    for (hdr, props) in &asset.exports {
        if let Some(comp_name) = hdr.object_name.strip_suffix("_GEN_VARIABLE") {
            comp_props.insert(comp_name.to_string(), props);
        }
    }

    // Build lookup for child actor template exports
    let mut cat_exports: std::collections::HashMap<String, (String, &[Property])> = std::collections::HashMap::new();
    for (hdr, props) in &asset.exports {
        if hdr.object_name.contains("_CAT") {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            cat_exports.insert(hdr.object_name.clone(), (short_class(&class), props));
        }
    }

    // Properties to skip in component summaries (pure noise)
    const COMP_SKIP_PROPS: &[&str] = &[
        "StaticMeshImportVersion", "bVisualizeComponent",
        "CreationMethod",
    ];

    // Print a component and its properties at the given indent depth
    fn print_comp_props(
        name: &str, class: &str, depth: usize,
        comp_props: &std::collections::HashMap<String, &[Property]>,
        cat_exports: &std::collections::HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry], export_names: &[String],
    ) {
        let indent = "  ".repeat(depth + 1);
        let prop_indent = "  ".repeat(depth + 2);
        println!("{}{} ({})", indent, name, class);
        if let Some(props) = comp_props.get(name) {
            let mut child_actor_tpl: Option<String> = None;
            for prop in *props {
                if COMP_SKIP_PROPS.contains(&prop.name.as_str()) { continue; }
                // Capture child actor template name for later expansion
                if prop.name == "ChildActorTemplate" {
                    if let PropValue::Object(idx) = &prop.value {
                        let tpl_name = resolve_index(imports, export_names, *idx);
                        child_actor_tpl = Some(tpl_name);
                    }
                    continue;
                }
                // For structs: inline Vector/Rotator, summarise others by top-level fields
                if let PropValue::Struct { struct_type, fields } = &prop.value {
                    match struct_type.as_str() {
                        "Vector" | "Rotator" => {
                            let val = prop_value_short(&prop.value, imports, export_names);
                            println!("{}{}: {}", prop_indent, prop.name, val);
                        }
                        _ => {
                            let summary: Vec<String> = fields.iter().filter_map(|f| {
                                match &f.value {
                                    PropValue::Struct { .. } | PropValue::Array { .. } | PropValue::Map { .. } => None,
                                    _ => {
                                        let v = prop_value_short(&f.value, imports, export_names);
                                        Some(format!("{}: {}", f.name, v))
                                    }
                                }
                            }).collect();
                            if !summary.is_empty() {
                                println!("{}{}: {}", prop_indent, prop.name, summary.join(", "));
                            }
                        }
                    }
                    continue;
                }
                let val = prop_value_short(&prop.value, imports, export_names);
                println!("{}{}: {}", prop_indent, prop.name, val);
            }
            // Show child actor template properties if present
            if let Some(tpl_name) = child_actor_tpl {
                if let Some((tpl_class, tpl_props)) = cat_exports.get(&tpl_name) {
                    println!("{}[template: {}]", prop_indent, tpl_class);
                    for prop in *tpl_props {
                        if let PropValue::Struct { struct_type, fields } = &prop.value {
                            match struct_type.as_str() {
                                "Vector" | "Rotator" => {
                                    let val = prop_value_short(&prop.value, imports, export_names);
                                    println!("{}  {}: {}", prop_indent, prop.name, val);
                                }
                                _ => {
                                    let summary: Vec<String> = fields.iter().filter_map(|f| {
                                        match &f.value {
                                            PropValue::Struct { .. } | PropValue::Array { .. } | PropValue::Map { .. } => None,
                                            _ => {
                                                let v = prop_value_short(&f.value, imports, export_names);
                                                Some(format!("{}: {}", f.name, v))
                                            }
                                        }
                                    }).collect();
                                    if !summary.is_empty() {
                                        println!("{}  {}: {}", prop_indent, prop.name, summary.join(", "));
                                    }
                                }
                            }
                            continue;
                        }
                        let val = prop_value_short(&prop.value, imports, export_names);
                        println!("{}  {}: {}", prop_indent, prop.name, val);
                    }
                }
            }
        }
    }

    // Recursive tree printer
    fn print_comp_tree(
        node_name: &str, depth: usize,
        scs_nodes: &std::collections::HashMap<String, (String, String, Vec<String>)>,
        comp_props: &std::collections::HashMap<String, &[Property]>,
        cat_exports: &std::collections::HashMap<String, (String, &[Property])>,
        imports: &[ImportEntry], export_names: &[String],
    ) {
        if let Some((comp_name, comp_class, children)) = scs_nodes.get(node_name) {
            print_comp_props(comp_name, comp_class, depth, comp_props, cat_exports, imports, export_names);
            for child in children {
                print_comp_tree(child, depth + 1, scs_nodes, comp_props, cat_exports, imports, export_names);
            }
        }
    }

    if !components.is_empty() {
        println!("Components:");
        for root in &root_nodes {
            print_comp_tree(root, 0, &scs_nodes, &comp_props, &cat_exports, &asset.imports, &export_names);
        }
        println!();
    }

    // Member variables from BlueprintGeneratedClass FField children
    let mut members: Vec<String> = Vec::new();
    let component_names: Vec<&str> = components.iter().map(|(n, _)| n.as_str()).collect();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".BlueprintGeneratedClass") { continue; }
        if let Some(members_prop) = find_prop(props, "Members") {
            if let PropValue::Array { items, .. } = &members_prop.value {
                for item in items {
                    if let PropValue::Str(decl) = item {
                        // Skip component variables (already shown in Components section)
                        let var_name = decl.split(':').next().unwrap_or("");
                        if component_names.contains(&var_name) { continue; }
                        members.push(decl.clone());
                    }
                }
            }
        }
    }

    // Default values from the CDO (Default__*_C export)
    let mut defaults: Vec<(String, String)> = Vec::new();
    for (hdr, props) in &asset.exports {
        if hdr.object_name.starts_with("Default__") && !props.is_empty() {
            for prop in props {
                // Skip internal engine properties
                if matches!(prop.name.as_str(), "ActorLabel" | "bCanProxyPhysics") { continue; }
                let val_str = prop_value_short(&prop.value, &asset.imports, &export_names);
                defaults.push((prop.name.clone(), val_str));
            }
        }
    }

    // Print variables section: declaration with default if available
    if !members.is_empty() {
        println!("Variables:");
        for decl in &members {
            let var_name = decl.split(':').next().unwrap_or("");
            if let Some((_, val)) = defaults.iter().find(|(n, _)| n == var_name) {
                println!("  {} = {}", decl, val);
            } else {
                println!("  {}", decl);
            }
        }
        println!();
    } else if !defaults.is_empty() {
        // Fallback: show defaults even without member declarations
        println!("Default values:");
        for (name, val) in &defaults {
            println!("  {} = {}", name, val);
        }
        println!();
    }

    // Functions with signatures and bytecode
    let mut has_functions = false;
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".Function") { continue; }
        if !matches_filter(&hdr.object_name, filters) { continue; }

        // Get signature or fall back to bare name
        let sig = find_prop_str(props, "Signature")
            .unwrap_or_else(|| format!("{}()", hdr.object_name));
        let flags = find_prop_str(props, "FunctionFlags")
            .map(|f| format!(" [{}]", f))
            .unwrap_or_default();

        if !has_functions {
            println!("Functions:");
            has_functions = true;
        }
        println!("  {}{}", sig, flags);

        // Show bytecode pseudo-code
        if let Some(bc_prop) = find_prop(props, "Bytecode") {
            if let PropValue::Array { items, .. } = &bc_prop.value {
                for item in items {
                    if let PropValue::Str(line) = item {
                        // Strip hex offset prefix (e.g. "0004: ")
                        let code = if line.len() > 6 && line.as_bytes()[4] == b':' {
                            &line[6..]
                        } else {
                            line
                        };
                        println!("    {}", code);
                    }
                }
            }
        }
    }
    if has_functions { println!(); }

    // Function flags for graph headers
    let mut func_flags: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if class.ends_with(".Function") {
            if let Some(flags) = find_prop_str(props, "FunctionFlags") {
                func_flags.insert(hdr.object_name.clone(), flags);
            }
        }
    }

    // Graphs (visual node layout)
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".EdGraph") { continue; }
        if !matches_filter(&hdr.object_name, filters) { continue; }
        let graph_name = &hdr.object_name;

        // Collect node export indices from the Nodes array
        let node_indices: Vec<i32> = find_prop(props, "Nodes")
            .or_else(|| find_prop(props, "AllNodes"))
            .map(|p| match &p.value {
                PropValue::Array { items, .. } => items.iter().filter_map(|item| {
                    if let PropValue::Object(idx) = item { Some(*idx) } else { None }
                }).collect(),
                _ => Vec::new(),
            })
            .unwrap_or_default();

        if node_indices.is_empty() { continue; }

        let flags = func_flags.get(graph_name.as_str()).map(|f| format!(" [{}]", f)).unwrap_or_default();
        println!("Graph: {}{}", graph_name, flags);

        // Collect node details and sort by X position
        let mut nodes: Vec<(i32, String)> = Vec::new();
        for idx in &node_indices {
            if *idx > 0 {
                let export_idx = (*idx - 1) as usize;
                if let Some((hdr, node_props)) = asset.exports.get(export_idx) {
                    let node_class = resolve_index(&asset.imports, &export_names, hdr.class_index);
                    let x = find_prop_i32(node_props, "NodePosX").unwrap_or(0);
                    let summary = summarise_node(&node_class, node_props, &asset.imports, &export_names);
                    nodes.push((x, summary));
                }
            }
        }
        nodes.sort_by_key(|(x, _)| *x);
        for (_, desc) in &nodes {
            println!("  {}", desc);
        }
        println!();
    }
}

fn format_func_flags(flags: u32) -> String {
    let mut parts = Vec::new();
    if flags & 0x00000001 != 0 { parts.push("Final"); }
    if flags & 0x00000400 != 0 { parts.push("Native"); }
    if flags & 0x00000800 != 0 { parts.push("Event"); }
    if flags & 0x00002000 != 0 { parts.push("Static"); }
    if flags & 0x00004000 != 0 { parts.push("MulticastDelegate"); }
    if flags & 0x00020000 != 0 { parts.push("Public"); }
    if flags & 0x00040000 != 0 { parts.push("Private"); }
    if flags & 0x00080000 != 0 { parts.push("Protected"); }
    if flags & 0x00100000 != 0 { parts.push("Delegate"); }
    if flags & 0x00400000 != 0 { parts.push("HasOutParms"); }
    if flags & 0x01000000 != 0 { parts.push("BlueprintCallable"); }
    if flags & 0x02000000 != 0 { parts.push("BlueprintEvent"); }
    if flags & 0x04000000 != 0 { parts.push("BlueprintPure"); }
    if flags & 0x10000000 != 0 { parts.push("Const"); }
    if flags & 0x40000000 != 0 { parts.push("HasDefaults"); }
    if parts.is_empty() { format!("0x{:08x}", flags) } else { parts.join("|") }
}

fn short_class(full: &str) -> String {
    full.rsplit('.').next().unwrap_or(full).to_string()
}

fn find_prop<'a>(props: &'a [Property], name: &str) -> Option<&'a Property> {
    props.iter().find(|p| p.name == name)
}

fn find_prop_str(props: &[Property], name: &str) -> Option<String> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Str(s) => Some(s.clone()),
        PropValue::Name(s) => Some(s.clone()),
        _ => None,
    })
}

fn find_prop_i32(props: &[Property], name: &str) -> Option<i32> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Int(v) => Some(*v),
        _ => None,
    })
}

fn prop_value_short(val: &PropValue, imports: &[ImportEntry], export_names: &[String]) -> String {
    match val {
        PropValue::Bool(v) => v.to_string(),
        PropValue::Int(v) => v.to_string(),
        PropValue::Int64(v) => v.to_string(),
        PropValue::Float(v) => format!("{:.4}", v),
        PropValue::Double(v) => format!("{:.4}", v),
        PropValue::Str(v) => format!("\"{}\"", v),
        PropValue::Name(v) => v.clone(),
        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
        PropValue::Enum { value, .. } => value.clone(),
        PropValue::Byte { value, .. } => value.clone(),
        PropValue::Array { items, .. } => format!("[{} items]", items.len()),
        PropValue::Map { entries, .. } => format!("{{{} entries}}", entries.len()),
        PropValue::Struct { struct_type, fields } => {
            match struct_type.as_str() {
                "Vector" | "Rotator" => {
                    let parts: Vec<String> = fields.iter()
                        .map(|f| prop_value_short(&f.value, imports, export_names))
                        .collect();
                    format!("({})", parts.join(", "))
                }
                _ => format!("{} {{...}}", struct_type),
            }
        }
        _ => "...".into(),
    }
}

fn summarise_node(class: &str, props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    let short = short_class(class);
    match short.as_str() {
        "K2Node_CallFunction" => {
            let func = get_member_ref(props, imports, export_names);
            let pure = find_prop(props, "bIsPureFunc").is_some_and(|p| matches!(p.value, PropValue::Bool(true)));
            if pure { format!("[pure] {}", func) } else { format!("Call {}", func) }
        }
        "K2Node_CommutativeAssociativeBinaryOperator" => {
            let func = get_member_ref(props, imports, export_names);
            format!("[pure] {}", func)
        }
        "K2Node_FunctionEntry" => {
            let name = get_member_name(props);
            format!("Entry: {}", name)
        }
        "K2Node_FunctionResult" => {
            let name = get_member_name(props);
            format!("Return: {}", name)
        }
        "K2Node_VariableGet" => {
            let var = get_var_ref(props, imports, export_names);
            format!("Get {}", var)
        }
        "K2Node_VariableSet" => {
            let var = get_var_ref(props, imports, export_names);
            format!("Set {}", var)
        }
        "K2Node_DynamicCast" => {
            let target = find_prop(props, "TargetType")
                .map(|p| match &p.value {
                    PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                    _ => "?".into(),
                })
                .unwrap_or_else(|| "?".into());
            format!("Cast to {}", target)
        }
        "K2Node_Event" | "K2Node_CustomEvent" => {
            let name = get_member_name(props);
            format!("Event: {}", name)
        }
        "K2Node_IfThenElse" => "Branch".into(),
        "K2Node_MacroInstance" => {
            let name = get_member_name(props);
            format!("Macro: {}", name)
        }
        _ => short.to_string(),
    }
}

fn get_member_ref(props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    find_prop(props, "FunctionReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => {
                let parent = find_prop(fields, "MemberParent")
                    .map(|mp| match &mp.value {
                        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                let name = find_prop_str(fields, "MemberName").unwrap_or_else(|| "?".into());
                if parent.is_empty() { Some(name) } else { Some(format!("{}::{}", parent, name)) }
            }
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}

fn get_member_name(props: &[Property]) -> String {
    find_prop(props, "FunctionReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => find_prop_str(fields, "MemberName"),
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}

fn get_var_ref(props: &[Property], imports: &[ImportEntry], export_names: &[String]) -> String {
    find_prop(props, "VariableReference")
        .and_then(|p| match &p.value {
            PropValue::Struct { fields, .. } => {
                let parent = find_prop(fields, "MemberParent")
                    .map(|mp| match &mp.value {
                        PropValue::Object(idx) => short_class(&resolve_index(imports, export_names, *idx)),
                        _ => String::new(),
                    })
                    .unwrap_or_default();
                let name = find_prop_str(fields, "MemberName").unwrap_or_else(|| "?".into());
                let is_self = find_prop(fields, "bSelfContext")
                    .is_some_and(|p| matches!(p.value, PropValue::Bool(true)));
                if is_self { Some(format!("self.{}", name)) }
                else if parent.is_empty() { Some(name) }
                else { Some(format!("{}.{}", parent, name)) }
            }
            _ => None,
        })
        .unwrap_or_else(|| "?".into())
}

// --- Main ---

fn main() {
    let cli = Cli::parse();

    let data = std::fs::read(&cli.path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {}", cli.path.display(), e);
        std::process::exit(1);
    });

    let asset = match parse_asset(&data, cli.debug) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Failed to parse {}: {}", cli.path.display(), e);
            std::process::exit(1);
        }
    };

    let filters: Vec<String> = cli.filter
        .map(|f| f.split(',').map(|s| s.trim().to_lowercase()).collect())
        .unwrap_or_default();

    if cli.json {
        println!("{}", serde_json::to_string_pretty(&to_json(&asset, &filters)).unwrap());
    } else if cli.summary {
        print_summary(&asset, &filters);
    } else {
        print_text(&asset, &filters);
    }
}
