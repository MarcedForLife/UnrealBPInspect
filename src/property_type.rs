//! Classified Unreal property/FField class name parsed from the on-disk FName
//! (e.g. "StructProperty"). Dispatch-only; the original spelling round-trips
//! via `as_str()` so output stays byte-identical.

use std::borrow::Cow;

/// Suffix shared by every property/FField class name. Single-sourced so the
/// validity gates and display fallbacks don't repeat the literal.
pub(crate) const PROPERTY_CLASS_SUFFIX: &str = "Property";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PropertyType {
    Bool,
    Byte,
    Int,
    Int8,
    Int16,
    Int32,
    UInt16,
    UInt32,
    Int64,
    UInt64,
    Float,
    Double,
    Str,
    Name,
    Text,
    Object,
    WeakObject,
    LazyObject,
    SoftObject,
    Interface,
    Class,
    SoftClass,
    Struct,
    Enum,
    Array,
    Set,
    Map,
    Delegate,
    MulticastInlineDelegate,
    MulticastSparseDelegate,
    MulticastDelegate,
    /// Any spelling not classified above; preserves the exact original FName.
    Unknown(String),
}

impl PropertyType {
    /// Classify an on-disk class name. Every spelling that any dispatch site
    /// reads via a specific match arm must land on a non-`Unknown` variant;
    /// otherwise it would silently route to the old `_` fallback.
    pub(crate) fn from_fname(name: &str) -> PropertyType {
        use PropertyType::*;
        match name {
            "BoolProperty" => Bool,
            "ByteProperty" => Byte,
            "IntProperty" => Int,
            "Int8Property" => Int8,
            "Int16Property" => Int16,
            "Int32Property" => Int32,
            "UInt16Property" => UInt16,
            "UInt32Property" => UInt32,
            "Int64Property" => Int64,
            "UInt64Property" => UInt64,
            "FloatProperty" => Float,
            "DoubleProperty" => Double,
            "StrProperty" => Str,
            "NameProperty" => Name,
            "TextProperty" => Text,
            "ObjectProperty" => Object,
            "WeakObjectProperty" => WeakObject,
            "LazyObjectProperty" => LazyObject,
            "SoftObjectProperty" => SoftObject,
            "InterfaceProperty" => Interface,
            "ClassProperty" => Class,
            "SoftClassProperty" => SoftClass,
            "StructProperty" => Struct,
            "EnumProperty" => Enum,
            "ArrayProperty" => Array,
            "SetProperty" => Set,
            "MapProperty" => Map,
            "DelegateProperty" => Delegate,
            "MulticastInlineDelegateProperty" => MulticastInlineDelegate,
            "MulticastSparseDelegateProperty" => MulticastSparseDelegate,
            "MulticastDelegateProperty" => MulticastDelegate,
            other => Unknown(other.to_string()),
        }
    }

    /// Canonical on-disk spelling. Known variants return their fixed literal;
    /// `Unknown` returns the preserved original.
    pub(crate) fn as_str(&self) -> Cow<'_, str> {
        use PropertyType::*;
        let known = match self {
            Bool => "BoolProperty",
            Byte => "ByteProperty",
            Int => "IntProperty",
            Int8 => "Int8Property",
            Int16 => "Int16Property",
            Int32 => "Int32Property",
            UInt16 => "UInt16Property",
            UInt32 => "UInt32Property",
            Int64 => "Int64Property",
            UInt64 => "UInt64Property",
            Float => "FloatProperty",
            Double => "DoubleProperty",
            Str => "StrProperty",
            Name => "NameProperty",
            Text => "TextProperty",
            Object => "ObjectProperty",
            WeakObject => "WeakObjectProperty",
            LazyObject => "LazyObjectProperty",
            SoftObject => "SoftObjectProperty",
            Interface => "InterfaceProperty",
            Class => "ClassProperty",
            SoftClass => "SoftClassProperty",
            Struct => "StructProperty",
            Enum => "EnumProperty",
            Array => "ArrayProperty",
            Set => "SetProperty",
            Map => "MapProperty",
            Delegate => "DelegateProperty",
            MulticastInlineDelegate => "MulticastInlineDelegateProperty",
            MulticastSparseDelegate => "MulticastSparseDelegateProperty",
            MulticastDelegate => "MulticastDelegateProperty",
            Unknown(original) => return Cow::Borrowed(original.as_str()),
        };
        Cow::Borrowed(known)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every known spelling round-trips through classify then `as_str`.
    const KNOWN_SPELLINGS: &[&str] = &[
        "BoolProperty",
        "ByteProperty",
        "IntProperty",
        "Int8Property",
        "Int16Property",
        "Int32Property",
        "UInt16Property",
        "UInt32Property",
        "Int64Property",
        "UInt64Property",
        "FloatProperty",
        "DoubleProperty",
        "StrProperty",
        "NameProperty",
        "TextProperty",
        "ObjectProperty",
        "WeakObjectProperty",
        "LazyObjectProperty",
        "SoftObjectProperty",
        "InterfaceProperty",
        "ClassProperty",
        "SoftClassProperty",
        "StructProperty",
        "EnumProperty",
        "ArrayProperty",
        "SetProperty",
        "MapProperty",
        "DelegateProperty",
        "MulticastInlineDelegateProperty",
        "MulticastSparseDelegateProperty",
        "MulticastDelegateProperty",
    ];

    #[test]
    fn known_spellings_round_trip() {
        for spelling in KNOWN_SPELLINGS {
            let parsed = PropertyType::from_fname(spelling);
            assert_ne!(
                parsed,
                PropertyType::Unknown(spelling.to_string()),
                "{spelling} must classify to a known variant"
            );
            assert_eq!(parsed.as_str(), *spelling, "{spelling} must round-trip");
        }
    }

    #[test]
    fn unknown_preserves_spelling() {
        let parsed = PropertyType::from_fname("ZzzProperty");
        assert_eq!(parsed, PropertyType::Unknown("ZzzProperty".to_string()));
        assert_eq!(parsed.as_str(), "ZzzProperty");
    }

    /// Correctness invariant: every spelling that appears in a specific (non-`_`)
    /// match arm of properties.rs or ffield.rs must classify to a non-`Unknown`
    /// variant. A missing mapping would silently route the type to the old
    /// fallback arm, a behavior regression. If you add a specific arm for a new
    /// spelling, add it here so a missing `from_fname` entry fails loudly.
    #[test]
    fn every_dispatch_spelling_is_known() {
        // properties.rs: read_primitive_value, read_value_with_meta,
        // read_typed_value, UE4/UE5 tag preamble matches.
        // ffield.rs: field_extra, resolve_ffield_type simple/OneRef matches.
        const DISPATCH_SPELLINGS: &[&str] = &[
            "BoolProperty",
            "ByteProperty",
            "IntProperty",
            "Int8Property",
            "Int16Property",
            "Int32Property",
            "UInt16Property",
            "UInt32Property",
            "Int64Property",
            "UInt64Property",
            "FloatProperty",
            "DoubleProperty",
            "StrProperty",
            "NameProperty",
            "TextProperty",
            "ObjectProperty",
            "WeakObjectProperty",
            "LazyObjectProperty",
            "SoftObjectProperty",
            "InterfaceProperty",
            "ClassProperty",
            "SoftClassProperty",
            "StructProperty",
            "EnumProperty",
            "ArrayProperty",
            "SetProperty",
            "MapProperty",
            "DelegateProperty",
            "MulticastDelegateProperty",
            "MulticastInlineDelegateProperty",
            "MulticastSparseDelegateProperty",
        ];
        for spelling in DISPATCH_SPELLINGS {
            assert!(
                !matches!(PropertyType::from_fname(spelling), PropertyType::Unknown(_)),
                "{spelling} appears in a specific dispatch arm but classifies as Unknown"
            );
        }
    }
}
