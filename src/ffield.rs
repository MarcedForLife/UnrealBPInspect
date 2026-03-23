//! FField child property parsing, type resolution, and function signatures.
//!
//! Resolves FField children into function signatures, e.g. `MyFunc(X: float, Y: Vector) -> bool`.

use anyhow::Result;
use std::io::Read;

use crate::binary::*;
use crate::resolve::*;
use crate::types::*;

/// Extra data layout that follows the common FProperty header for each field class.
/// Used by both `skip_ffield_child` and `resolve_ffield_type` so the field class
/// groupings are defined once.
enum FieldExtra {
    /// No extra bytes (simple scalar types like Float, Int, Str, Name, Text).
    None,
    /// Single package index: object/interface ref, struct ref, enum ref, delegate sig.
    OneRef,
    /// Two package indices: property class + meta class.
    TwoRefs,
    /// 6 bytes: FieldSize, ByteOffset, ByteMask, FieldMask, NativeBool, Value.
    Bool,
    /// One recursive FField child (ArrayProperty, SetProperty).
    OneChild,
    /// Two recursive FField children (MapProperty key + value).
    TwoChildren,
}

fn field_extra(class: &str) -> FieldExtra {
    match class {
        "ObjectProperty"
        | "WeakObjectProperty"
        | "LazyObjectProperty"
        | "SoftObjectProperty"
        | "InterfaceProperty"
        | "StructProperty"
        | "ByteProperty"
        | "EnumProperty"
        | "DelegateProperty"
        | "MulticastDelegateProperty"
        | "MulticastInlineDelegateProperty"
        | "MulticastSparseDelegateProperty" => FieldExtra::OneRef,
        "ClassProperty" | "SoftClassProperty" => FieldExtra::TwoRefs,
        "BoolProperty" => FieldExtra::Bool,
        "ArrayProperty" | "SetProperty" => FieldExtra::OneChild,
        "MapProperty" => FieldExtra::TwoChildren,
        _ => FieldExtra::None,
    }
}

/// Skip past one serialized FField child without extracting type information.
fn skip_ffield_extra(
    class: &str,
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
) -> Result<()> {
    match field_extra(class) {
        FieldExtra::None => {}
        FieldExtra::OneRef => {
            read_i32(reader)?;
        }
        FieldExtra::TwoRefs => {
            read_i32(reader)?;
            read_i32(reader)?;
        }
        FieldExtra::Bool => {
            for _ in 0..6 {
                read_u8(reader)?;
            }
        }
        FieldExtra::OneChild => {
            skip_ffield_child(reader, name_table, end)?;
        }
        FieldExtra::TwoChildren => {
            skip_ffield_child(reader, name_table, end)?;
            skip_ffield_child(reader, name_table, end)?;
        }
    }
    Ok(())
}

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
    skip_ffield_extra(&field_class, reader, name_table, end)
}

pub fn resolve_ffield_type(
    field_class: &str,
    reader: &mut Reader,
    name_table: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    end: u64,
) -> Result<String> {
    // Simple types: no extra bytes to read, just return the display name.
    let simple = match field_class {
        // UE5 LWC promotes float -> double internally, but we display as "float"
        // for consistency with UE4 and the Blueprint editor. Actual values are
        // parsed at full f64 precision regardless.
        "FloatProperty" | "DoubleProperty" => Some("float"),
        "IntProperty" | "Int32Property" | "UInt32Property" => Some("int"),
        "Int64Property" | "UInt64Property" => Some("int64"),
        "Int16Property" | "UInt16Property" => Some("int16"),
        "Int8Property" => Some("int8"),
        "StrProperty" => Some("FString"),
        "NameProperty" => Some("FName"),
        "TextProperty" => Some("FText"),
        _ => None,
    };
    if let Some(name) = simple {
        return Ok(name.into());
    }

    // Types that need extra bytes read. Use field_extra() for the read layout,
    // then interpret the values per field class.
    match field_extra(field_class) {
        FieldExtra::Bool => {
            for _ in 0..6 {
                read_u8(reader)?;
            }
            Ok("bool".into())
        }
        FieldExtra::TwoRefs => {
            read_i32(reader)?;
            read_i32(reader)?;
            Ok("UClass*".into())
        }
        FieldExtra::OneRef => {
            let ref_idx = read_i32(reader)?;
            match field_class {
                "ObjectProperty" | "WeakObjectProperty" | "LazyObjectProperty"
                | "SoftObjectProperty" | "InterfaceProperty" => {
                    if ref_idx != 0 {
                        Ok(format!(
                            "{}*",
                            short_class(&resolve_index(imports, export_names, ref_idx))
                        ))
                    } else {
                        Ok("UObject*".into())
                    }
                }
                "StructProperty" => Ok(short_class(&resolve_index(imports, export_names, ref_idx))),
                "ByteProperty" | "EnumProperty" => {
                    if ref_idx != 0 {
                        Ok(short_class(&resolve_index(imports, export_names, ref_idx)))
                    } else {
                        Ok("byte".into())
                    }
                }
                // Delegate variants
                _ => Ok("Delegate".into()),
            }
        }
        FieldExtra::OneChild => {
            skip_ffield_child(reader, name_table, end)?;
            Ok(if field_class == "SetProperty" {
                "TSet<>".into()
            } else {
                "TArray<>".into()
            })
        }
        FieldExtra::TwoChildren => {
            skip_ffield_child(reader, name_table, end)?;
            skip_ffield_child(reader, name_table, end)?;
            Ok("TMap<>".into())
        }
        FieldExtra::None => Ok(field_class
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
