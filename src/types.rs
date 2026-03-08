#[derive(Clone, Copy)]
pub struct AssetVersion {
    pub file_ver: i32,      // UE4 version (e.g. 522 for UE4.27)
    pub file_ver_ue5: i32,  // UE5 version (0 for UE4 assets, 1000+ for UE5)
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
    Enum { enum_type: String, value: String },
    Struct { struct_type: String, fields: Vec<Property> },
    Array { inner_type: String, items: Vec<PropValue> },
    Map { key_type: String, value_type: String, entries: Vec<(PropValue, PropValue)> },
    Text(String),
    SoftObject(String),
    Byte { enum_name: String, value: String },
    Unknown { type_name: String, size: i32 },
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
