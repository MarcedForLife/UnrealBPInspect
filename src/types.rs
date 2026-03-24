//! Core data types shared across the parser.

// -- UE4 file_ver gates --
pub const VER_UE4_TEMPLATE_INDEX: i32 = 459;
pub const VER_UE4_PROPERTY_GUID: i32 = 503;
pub const VER_UE4_LOCALIZATION_ID: i32 = 516;
pub const VER_UE4_PACKAGE_NAME_IN_IMPORT: i32 = 518;

// -- UE5 file_ver_ue5 gates --
pub const VER_UE5_OPTIONAL_RESOURCES: i32 = 1003;
pub const VER_UE5_LARGE_WORLD_COORDINATES: i32 = 1004;
pub const VER_UE5_REMOVE_EXPORT_GUID: i32 = 1005;
pub const VER_UE5_TRACK_INHERITED: i32 = 1006;
pub const VER_UE5_SOFT_OBJECT_PATH_LIST: i32 = 1007;
pub const VER_UE5_SCRIPT_SERIALIZATION_OFFSET: i32 = 1010;
pub const VER_UE5_PROPERTY_TAG_EXTENSION: i32 = 1011;
pub const VER_UE5_COMPLETE_TYPE_NAME: i32 = 1012;

/// Tracks the .uasset file format version across UE4 and UE5.
#[derive(Clone, Copy)]
pub struct AssetVersion {
    pub file_ver: i32,     // UE4 version (e.g. 522 for UE4.27)
    pub file_ver_ue5: i32, // UE5 version (0 for UE4 assets, 1000+ for UE5)
}

impl AssetVersion {
    /// UE5 Large World Coordinates: vectors/rotators use f64, math ops renamed.
    pub fn is_lwc(&self) -> bool {
        self.file_ver_ue5 >= VER_UE5_LARGE_WORLD_COORDINATES
    }
    /// UE5.2+: FPropertyTag uses recursive FPropertyTypeName format.
    pub fn has_complete_type_name(&self) -> bool {
        self.file_ver_ue5 >= VER_UE5_COMPLETE_TYPE_NAME
    }
}

#[derive(Debug, Clone)]
pub struct ImportEntry {
    pub class_package: String,
    pub class_name: String,
    pub object_name: String,
    pub outer_index: i32,
}

#[derive(Debug, Clone)]
pub struct ExportHeader {
    pub class_index: i32,
    pub super_index: i32,
    pub outer_index: i32,
    pub object_name: String,
    pub serial_offset: i64,
    pub serial_size: i64,
}

#[derive(Debug, Clone)]
pub enum PropValue {
    Bool(bool),
    Int(i32),
    Int64(i64),
    Float(f32),
    Double(f64),
    Str(String),
    Name(String),
    Object(i32),
    Enum {
        enum_name: String,
        value: String,
    },
    Struct {
        struct_type: String,
        fields: Vec<Property>,
    },
    Array {
        inner_type: String,
        items: Vec<PropValue>,
    },
    Map {
        key_type: String,
        value_type: String,
        entries: Vec<(PropValue, PropValue)>,
    },
    Text(String),
    SoftObject(String),
    Byte {
        enum_name: String,
        value: String,
    },
    Unknown {
        type_name: String,
        size: i32,
    },
}

#[derive(Debug, Clone)]
pub struct Property {
    pub name: String,
    pub value: PropValue,
}

pub struct ParsedAsset {
    pub imports: Vec<ImportEntry>,
    pub exports: Vec<(ExportHeader, Vec<Property>)>,
}
