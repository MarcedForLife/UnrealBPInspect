use anyhow::Result;
use std::io::Read;

use crate::binary::*;
use crate::resolve::*;
use crate::types::*;

pub fn skip_ffield_child(c: &mut R, nt: &NameTable, end: u64) -> Result<()> {
    if c.position() + 8 > end {
        return Ok(());
    }
    let field_class = nt.fname(c)?;
    if field_class == "None" {
        return Ok(());
    }
    let _field_name = nt.fname(c)?;
    let _flags = read_u32(c)?;
    let has_meta = read_i32(c)?;
    if has_meta != 0 {
        let meta_count = read_i32(c)?;
        for _ in 0..meta_count {
            let _meta_key = nt.fname(c)?;
            let _meta_val = read_fstring(c)?;
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
        "ObjectProperty" | "WeakObjectProperty" | "ClassProperty" | "SoftObjectProperty"
        | "SoftClassProperty" | "InterfaceProperty" => {
            let _ref = read_i32(c)?;
        }
        "StructProperty" => {
            let _ref = read_i32(c)?;
        }
        "ByteProperty" | "EnumProperty" => {
            let _ref = read_i32(c)?;
        }
        "BoolProperty" => {
            // 6 bytes: FieldSize(1) + ByteOffset(1) + ByteMask(1) + FieldMask(1) + NativeBool(1) + Value(1)
            for _ in 0..6 {
                read_u8(c)?;
            }
        }
        "ArrayProperty" | "SetProperty" => {
            skip_ffield_child(c, nt, end)?;
        }
        "MapProperty" => {
            skip_ffield_child(c, nt, end)?;
            skip_ffield_child(c, nt, end)?;
        }
        "DelegateProperty" | "MulticastDelegateProperty" | "MulticastInlineDelegateProperty" => {
            let _ref = read_i32(c)?;
        }
        _ => {}
    }
    Ok(())
}

pub fn resolve_ffield_type(
    field_class: &str,
    c: &mut R,
    nt: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    end: u64,
) -> Result<String> {
    match field_class {
        "FloatProperty" => Ok("float".into()),
        "DoubleProperty" => Ok("double".into()),
        "IntProperty" | "Int32Property" | "UInt32Property" => Ok("int".into()),
        "Int64Property" | "UInt64Property" => Ok("int64".into()),
        "Int16Property" | "UInt16Property" => Ok("int16".into()),
        "Int8Property" => Ok("int8".into()),
        "BoolProperty" => {
            // 6 bytes: FieldSize, ByteOffset, ByteMask, FieldMask, NativeBool, Value
            for _ in 0..6 {
                read_u8(c)?;
            }
            Ok("bool".into())
        }
        "StrProperty" => Ok("FString".into()),
        "NameProperty" => Ok("FName".into()),
        "TextProperty" => Ok("FText".into()),
        "ObjectProperty" | "WeakObjectProperty" | "LazyObjectProperty" | "SoftObjectProperty"
        | "InterfaceProperty" => {
            let class_ref = read_i32(c)?;
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
            let _prop_class = read_i32(c)?;
            let _meta_class = read_i32(c)?;
            Ok("UClass*".into())
        }
        "StructProperty" => {
            let struct_ref = read_i32(c)?;
            Ok(short_class(&resolve_index(
                imports,
                export_names,
                struct_ref,
            )))
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
            Ok(if field_class == "SetProperty" {
                "TSet<>".into()
            } else {
                "TArray<>".into()
            })
        }
        "MapProperty" => {
            skip_ffield_child(c, nt, end)?;
            skip_ffield_child(c, nt, end)?;
            Ok("TMap<>".into())
        }
        "DelegateProperty"
        | "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => {
            let _sig = read_i32(c)?;
            Ok("Delegate".into())
        }
        _ => Ok(field_class
            .strip_suffix("Property")
            .unwrap_or(field_class)
            .to_string()),
    }
}

pub fn format_signature(func_name: &str, params: &[(String, String, u64)]) -> String {
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
    }

    let sig = format!("{}({})", func_name, inputs.join(", "));
    match ret_type {
        Some(t) => format!("{} -> {}", sig, t),
        None => sig,
    }
}
