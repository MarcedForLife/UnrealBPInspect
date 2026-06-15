//! FField child property parsing, type resolution, and function signatures.
//!
//! Resolves FField children into function signatures, e.g. `MyFunc(X: float, Y: Vector) -> bool`.

use anyhow::Result;
use std::io::Read;

use crate::binary::*;
use crate::property_type::{PropertyType, PROPERTY_CLASS_SUFFIX};
use crate::resolve::{resolve_index, short_class};
use crate::types::*;

/// Extra data layout after the common FProperty header, shared across skip and resolve functions.
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
    use PropertyType::*;
    match PropertyType::from_fname(class) {
        Object
        | WeakObject
        | LazyObject
        | SoftObject
        | Interface
        | Struct
        | Byte
        | Enum
        | Delegate
        | MulticastDelegate
        | MulticastInlineDelegate
        | MulticastSparseDelegate => FieldExtra::OneRef,
        Class | SoftClass => FieldExtra::TwoRefs,
        Bool => FieldExtra::Bool,
        Array | Set => FieldExtra::OneChild,
        Map => FieldExtra::TwoChildren,
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

/// Resolve a `OneRef` field's already-read reference index to a display type.
/// Handles object/weak/lazy/soft-object/interface (`T*`, `UObject*` when null),
/// struct (`T`), byte/enum (`T`, `byte` when null), and delegate variants.
fn resolve_one_ref_type(
    property_type: PropertyType,
    ref_idx: i32,
    imports: &[ImportEntry],
    export_names: &[String],
) -> String {
    match property_type {
        PropertyType::Object
        | PropertyType::WeakObject
        | PropertyType::LazyObject
        | PropertyType::SoftObject
        | PropertyType::Interface => {
            if ref_idx != 0 {
                format!(
                    "{}*",
                    short_class(&resolve_index(imports, export_names, ref_idx))
                )
            } else {
                "UObject*".into()
            }
        }
        PropertyType::Struct => short_class(&resolve_index(imports, export_names, ref_idx)),
        PropertyType::Byte | PropertyType::Enum => {
            if ref_idx != 0 {
                short_class(&resolve_index(imports, export_names, ref_idx))
            } else {
                "byte".into()
            }
        }
        // Delegate variants
        _ => "Delegate".into(),
    }
}

pub fn resolve_ffield_type(
    field_class: &str,
    reader: &mut Reader,
    name_table: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    end: u64,
) -> Result<String> {
    let property_type = PropertyType::from_fname(field_class);

    // Simple types: no extra bytes to read, just return the display name.
    let simple = match property_type {
        // UE5 LWC (Large World Coordinates) promotes float -> double internally,
        // but we display as "float" for consistency with UE4 and the Blueprint
        // editor. Actual values are parsed at full f64 precision regardless.
        PropertyType::Float | PropertyType::Double => Some("float"),
        PropertyType::Int | PropertyType::Int32 | PropertyType::UInt32 => Some("int"),
        PropertyType::Int64 | PropertyType::UInt64 => Some("int64"),
        PropertyType::Int16 | PropertyType::UInt16 => Some("int16"),
        PropertyType::Int8 => Some("int8"),
        PropertyType::Str => Some("FString"),
        PropertyType::Name => Some("FName"),
        PropertyType::Text => Some("FText"),
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
            Ok(resolve_one_ref_type(
                property_type,
                ref_idx,
                imports,
                export_names,
            ))
        }
        FieldExtra::OneChild => {
            skip_ffield_child(reader, name_table, end)?;
            Ok(if property_type == PropertyType::Set {
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
        FieldExtra::None => Ok(property_type
            .as_str()
            .strip_suffix(PROPERTY_CLASS_SUFFIX)
            .unwrap_or(field_class)
            .to_string()),
    }
}

// UE property flags used to classify function parameters
pub(crate) const CPF_PARM: u64 = 0x80;
const CPF_OUT_PARM: u64 = 0x100;
pub(crate) const CPF_RETURN_PARM: u64 = 0x200;

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
