//! Core data types shared across the parser.

use std::collections::{BTreeMap, HashMap};

// UE4 file_ver gates
pub const VER_UE4_TEMPLATE_INDEX: i32 = 459;
pub const VER_UE4_PROPERTY_GUID: i32 = 503;
pub const VER_UE4_LOCALIZATION_ID: i32 = 516;
pub const VER_UE4_PACKAGE_NAME_IN_IMPORT: i32 = 518;

// UE5 file_ver_ue5 gates
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

pub const PIN_DIRECTION_INPUT: u8 = 0;
pub const PIN_DIRECTION_OUTPUT: u8 = 1;
pub const PIN_TYPE_EXEC: &str = "exec";

/// A reference from one pin to another pin on a target node. Produced
/// directly from `UEdGraphPin::LinkedTo` on disk, which serializes each
/// entry as (OwningNode, PinId).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LinkedPin {
    /// 1-based export index of the node owning the target pin.
    pub node: usize,
    /// FGuid of the target pin on that node.
    pub pin_id: [u8; 16],
}

/// A single pin on an EdGraph node.
#[derive(Debug, Clone)]
pub struct EdGraphPin {
    /// Pin name from FName serialization. For sub-pins on split structs,
    /// contains field identifiers (e.g. "Output_Get_IsClimbable_8_...").
    pub name: String,
    /// Pin category from FEdGraphPinType (e.g. "exec", "bool", "object").
    pub pin_type: String,
    pub direction: u8,
    /// FGuid of this pin, used to match incoming links on other nodes that
    /// target this pin via `LinkedPin::pin_id`.
    pub pin_id: [u8; 16],
    /// Links to target pins on connected nodes, in on-disk order
    /// (deduplicated by (node, pin_id)).
    pub linked_to: Vec<LinkedPin>,
}

impl EdGraphPin {
    pub fn is_exec_output(&self) -> bool {
        self.pin_type == PIN_TYPE_EXEC && self.direction == PIN_DIRECTION_OUTPUT
    }

    pub fn is_data_output(&self) -> bool {
        self.pin_type != PIN_TYPE_EXEC && self.direction == PIN_DIRECTION_OUTPUT
    }

    pub fn is_data_input(&self) -> bool {
        self.pin_type != PIN_TYPE_EXEC && self.direction == PIN_DIRECTION_INPUT
    }
}

/// Pin data parsed from a K2Node export's post-property serialization.
#[derive(Debug, Clone)]
pub struct NodePinData {
    pub pins: Vec<EdGraphPin>,
}

/// One parameter of a Blueprint function or event signature.
///
/// `flags` carries the raw UE property flags read off disk; the meaningful
/// bits for downstream consumers are `CPF_PARM` (0x80), `CPF_OUT_PARM`
/// (0x100), and `CPF_RETURN_PARM` (0x200).
#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub type_name: String,
    pub flags: u64,
}

/// Parameter list and return type for a single function export.
///
/// Used by the bytecode decoder to look up callee signatures so it can
/// wrap call-site arguments at OUT-parameter positions in `Expr::Out`.
/// Imported (cross-asset) functions are not represented here, the lookup
/// falls back gracefully for unknown names.
#[derive(Debug, Clone, Default)]
pub struct FunctionSignature {
    pub params: Vec<ParamInfo>,
    pub return_type: Option<String>,
}

pub struct ParsedAsset {
    pub imports: Vec<ImportEntry>,
    pub exports: Vec<(ExportHeader, Vec<Property>)>,
    /// Pin connection data per export index (1-based). Only populated for
    /// EdGraph node exports where pin serialization was successfully parsed.
    pub pin_data: HashMap<usize, NodePinData>,
    /// Function name to parameter signature, populated for every Function
    /// export with at least one declared FField child. Keyed by the export's
    /// `object_name`. Multiple exports sharing a name would collide; in
    /// practice Blueprint functions have unique names within an asset.
    pub function_signatures: BTreeMap<String, FunctionSignature>,
    /// Raw bytecode bytes captured during the prologue walk, keyed by
    /// 1-based export index. Value is `(disk_bytes, mem_size)` where
    /// `mem_size` is the runtime memory size used to translate jump
    /// targets between memory and disk coordinates. Only populated for
    /// function-class exports whose serialized bytecode block was
    /// successfully read.
    pub bytecode_by_export: BTreeMap<usize, (Vec<u8>, u32)>,
}
