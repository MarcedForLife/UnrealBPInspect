/// Tracks the .uasset file format version across UE4 and UE5.
///
/// Epic added a separate UE5 version track in the binary header rather than
/// continuing to increment the UE4 version number. `file_ver_ue5` is only
/// present in the file when `legacy_ver <= -8` (UE5-era); for UE4 assets
/// it defaults to 0. Each field gates different format variations:
/// - `file_ver`: property GUIDs (>=503), template indices (>=459), localization IDs (>=516)
/// - `file_ver_ue5`: LWC/f64 vectors (>=1004), removed export GUIDs (>=1005), optional resources (>=1003)
#[derive(Clone, Copy)]
pub struct AssetVersion {
    pub file_ver: i32,     // UE4 version (e.g. 522 for UE4.27)
    pub file_ver_ue5: i32, // UE5 version (0 for UE4 assets, 1000+ for UE5)
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
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
        enum_type: String,
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
