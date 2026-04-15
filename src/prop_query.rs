//! Property lookup helpers for traversing parsed export properties.
//!
//! Provides typed accessors for extracting values from `Vec<Property>`,
//! including string, integer, object reference, and array variants.

use crate::resolve::{resolve_index, short_class};
use crate::types::*;

pub fn find_prop<'a>(props: &'a [Property], name: &str) -> Option<&'a Property> {
    props.iter().find(|p| p.name == name)
}

pub fn find_prop_str(props: &[Property], name: &str) -> Option<String> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Str(s) | PropValue::Name(s) | PropValue::Text(s) => Some(s.clone()),
        _ => None,
    })
}

/// Extract a string field from a nested Struct property.
pub fn find_struct_field_str(props: &[Property], struct_name: &str, field: &str) -> Option<String> {
    find_prop(props, struct_name).and_then(|p| match &p.value {
        PropValue::Struct { fields, .. } => find_prop_str(fields, field),
        _ => None,
    })
}

pub fn find_prop_i32(props: &[Property], name: &str) -> Option<i32> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Int(v) => Some(*v),
        _ => None,
    })
}

/// Extract an Object property as a resolved index string.
pub fn find_prop_object(
    props: &[Property],
    name: &str,
    imports: &[ImportEntry],
    export_names: &[String],
) -> Option<String> {
    find_prop(props, name).and_then(|p| match &p.value {
        PropValue::Object(idx) => Some(resolve_index(imports, export_names, *idx)),
        _ => None,
    })
}

/// Extract an Array of Object properties as resolved index strings.
pub fn find_prop_object_array(
    props: &[Property],
    name: &str,
    imports: &[ImportEntry],
    export_names: &[String],
) -> Vec<String> {
    find_prop(props, name)
        .and_then(|p| match &p.value {
            PropValue::Array { items, .. } => Some(
                items
                    .iter()
                    .filter_map(|i| match i {
                        PropValue::Object(idx) => Some(resolve_index(imports, export_names, *idx)),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

/// Get the string items from an Array property (Str, Name, and Text variants).
pub fn find_prop_str_items<'a>(props: &'a [Property], name: &str) -> Vec<&'a str> {
    find_prop(props, name)
        .and_then(|p| match &p.value {
            PropValue::Array { items, .. } => Some(
                items
                    .iter()
                    .filter_map(|item| match item {
                        PropValue::Str(s) | PropValue::Name(s) | PropValue::Text(s) => {
                            Some(s.as_str())
                        }
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        })
        .unwrap_or_default()
}

/// Get string items from the first matching property name (tries each in order).
pub fn find_prop_str_items_any<'a>(props: &'a [Property], names: &[&str]) -> Vec<&'a str> {
    for name in names {
        let items = find_prop_str_items(props, name);
        if !items.is_empty() {
            return items;
        }
    }
    Vec::new()
}

pub fn prop_value_short(
    val: &PropValue,
    imports: &[ImportEntry],
    export_names: &[String],
) -> String {
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
        PropValue::Struct {
            struct_type,
            fields,
        } => match struct_type.as_str() {
            "Vector" | "Rotator" => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|f| prop_value_short(&f.value, imports, export_names))
                    .collect();
                format!("({})", parts.join(", "))
            }
            _ => format!("{} {{...}}", struct_type),
        },
        _ => "...".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_props() -> Vec<Property> {
        vec![
            Property {
                name: "Name".into(),
                value: PropValue::Str("hello".into()),
            },
            Property {
                name: "Count".into(),
                value: PropValue::Int(42),
            },
            Property {
                name: "Flag".into(),
                value: PropValue::Bool(true),
            },
        ]
    }

    #[test]
    fn find_prop_by_name() {
        let props = make_props();
        assert!(find_prop(&props, "Name").is_some());
        assert!(find_prop(&props, "Missing").is_none());
    }

    #[test]
    fn find_prop_str_extracts_string() {
        let props = make_props();
        assert_eq!(find_prop_str(&props, "Name"), Some("hello".into()));
        assert_eq!(find_prop_str(&props, "Count"), None);
    }

    #[test]
    fn find_prop_i32_extracts_int() {
        let props = make_props();
        assert_eq!(find_prop_i32(&props, "Count"), Some(42));
        assert_eq!(find_prop_i32(&props, "Name"), None);
    }
}
