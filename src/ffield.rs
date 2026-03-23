//! FField child property parsing, type resolution, and function signatures.
//!
//! Resolves FField children into function signatures, e.g. `MyFunc(X: float, Y: Vector) -> bool`.

use anyhow::Result;
use std::io::Read;

use crate::binary::*;
use crate::resolve::*;
use crate::types::*;

pub fn skip_ffield_child(reader: &mut Reader, name_table: &NameTable, end: u64) -> Result<()> {
    if reader.position() + 8 > end {
        return Ok(());
    }
    let field_class = name_table.fname(reader)?;
    if field_class == "None" {
        return Ok(());
    }
    let _field_name = name_table.fname(reader)?;
    let _flags = read_u32(reader)?;
    name_table.skip_metadata(reader)?;
    let _array_dim = read_i32(reader)?;
    let _elem_size = read_i32(reader)?;
    let _prop_flags = read_i64(reader)?;
    let mut rep_bytes = [0u8; 2];
    reader.read_exact(&mut rep_bytes)?;
    let _rep_func = name_table.fname(reader)?;
    let _bp_rep = read_u8(reader)?;
    match field_class.as_str() {
        "ObjectProperty" | "WeakObjectProperty" | "SoftObjectProperty" | "InterfaceProperty" => {
            let _ref = read_i32(reader)?;
        }
        "ClassProperty" | "SoftClassProperty" => {
            let _prop_class = read_i32(reader)?;
            let _meta_class = read_i32(reader)?;
        }
        "StructProperty" => {
            let _ref = read_i32(reader)?;
        }
        "ByteProperty" | "EnumProperty" => {
            let _ref = read_i32(reader)?;
        }
        "BoolProperty" => {
            // 6 bytes: FieldSize(1) + ByteOffset(1) + ByteMask(1) + FieldMask(1) + NativeBool(1) + Value(1)
            for _ in 0..6 {
                read_u8(reader)?;
            }
        }
        "ArrayProperty" | "SetProperty" => {
            skip_ffield_child(reader, name_table, end)?;
        }
        "MapProperty" => {
            skip_ffield_child(reader, name_table, end)?;
            skip_ffield_child(reader, name_table, end)?;
        }
        "DelegateProperty" | "MulticastDelegateProperty" | "MulticastInlineDelegateProperty" => {
            let _ref = read_i32(reader)?;
        }
        _ => {}
    }
    Ok(())
}

pub fn resolve_ffield_type(
    field_class: &str,
    reader: &mut Reader,
    name_table: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    end: u64,
) -> Result<String> {
    match field_class {
        // UE5 LWC promotes float -> double internally, but we display as "float"
        // for consistency with UE4 and the Blueprint editor. Actual values are
        // parsed at full f64 precision regardless.
        "FloatProperty" | "DoubleProperty" => Ok("float".into()),
        "IntProperty" | "Int32Property" | "UInt32Property" => Ok("int".into()),
        "Int64Property" | "UInt64Property" => Ok("int64".into()),
        "Int16Property" | "UInt16Property" => Ok("int16".into()),
        "Int8Property" => Ok("int8".into()),
        "BoolProperty" => {
            // 6 bytes: FieldSize, ByteOffset, ByteMask, FieldMask, NativeBool, Value
            for _ in 0..6 {
                read_u8(reader)?;
            }
            Ok("bool".into())
        }
        "StrProperty" => Ok("FString".into()),
        "NameProperty" => Ok("FName".into()),
        "TextProperty" => Ok("FText".into()),
        "ObjectProperty" | "WeakObjectProperty" | "LazyObjectProperty" | "SoftObjectProperty"
        | "InterfaceProperty" => {
            let class_ref = read_i32(reader)?;
            if class_ref != 0 {
                Ok(format!(
                    "{}*",
                    short_class(&resolve_index(imports, export_names, class_ref))
                ))
            } else {
                Ok("UObject*".into())
            }
        }
        "ClassProperty" | "SoftClassProperty" => {
            let _prop_class = read_i32(reader)?;
            let _meta_class = read_i32(reader)?;
            Ok("UClass*".into())
        }
        "StructProperty" => {
            let struct_ref = read_i32(reader)?;
            Ok(short_class(&resolve_index(
                imports,
                export_names,
                struct_ref,
            )))
        }
        "ByteProperty" | "EnumProperty" => {
            let enum_ref = read_i32(reader)?;
            if enum_ref != 0 {
                Ok(short_class(&resolve_index(imports, export_names, enum_ref)))
            } else {
                Ok("byte".into())
            }
        }
        "ArrayProperty" | "SetProperty" => {
            skip_ffield_child(reader, name_table, end)?;
            Ok(if field_class == "SetProperty" {
                "TSet<>".into()
            } else {
                "TArray<>".into()
            })
        }
        "MapProperty" => {
            skip_ffield_child(reader, name_table, end)?;
            skip_ffield_child(reader, name_table, end)?;
            Ok("TMap<>".into())
        }
        "DelegateProperty"
        | "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => {
            let _sig = read_i32(reader)?;
            Ok("Delegate".into())
        }
        _ => Ok(field_class
            .strip_suffix("Property")
            .unwrap_or(field_class)
            .to_string()),
    }
}

// UE property flags used to classify function parameters
const CPF_PARM: u64 = 0x80;
const CPF_OUT_PARM: u64 = 0x100;
const CPF_RETURN_PARM: u64 = 0x200;

pub fn format_signature(func_name: &str, params: &[(String, String, u64)]) -> String {
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
    }

    let sig = format!("{}({})", func_name, inputs.join(", "));
    match ret_type {
        Some(t) => format!("{} -> {}", sig, t),
        None => sig,
    }
}
