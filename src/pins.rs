//! EdGraph pin parsing: reads pin connection data from K2Node exports.
//!
//! UE4 serializes pin arrays after each K2Node's tagged property stream.
//! This module scans for the pin signature and parses pin types, directions,
//! and LinkedTo connections used for comment placement and structural analysis.

use anyhow::{ensure, Result};
use std::io::{Seek, SeekFrom};

use crate::binary::*;
use crate::types::{AssetVersion, EdGraphPin};

/// Sanity cap on pin count per node (most nodes have < 50 pins).
const MAX_PIN_COUNT: i32 = 500;

/// Sanity cap on LinkedTo entries per pin (most pins have 0-3 links).
const MAX_LINKED_COUNT: i32 = 200;

/// Sanity cap on SubPins per pin.
const MAX_SUBPIN_COUNT: i32 = 50;

/// Maximum SubPin nesting depth to prevent stack overflow on corrupt data.
const MAX_SUBPIN_DEPTH: usize = 10;

/// Scan forward from the current reader position to find pin data.
///
/// K2Node subclasses serialize class-specific data between the tagged
/// property stream and the pin array. We scan at 4-byte (i32) alignment
/// looking for the pin signature: deprecated_count(i32=0) followed by a
/// reasonable pin_count(i32 in 1..MAX_PIN_COUNT), then attempt to parse
/// pins at each candidate. Tries both UE5 and UE4 formats for UE5 assets.
pub fn scan_for_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
) -> Option<Vec<EdGraphPin>> {
    let scan_start = reader.position();
    let scan_limit = end.saturating_sub(8);

    // First try at the current position (no scan needed if properties consumed correctly)
    let direct = try_pins_at(reader, name_table, end, ver, scan_start);
    if direct.is_some() {
        return direct;
    }

    // Scan at i32 alignment for the deprecated_count=0 + pin_count signature
    let mut pos = scan_start;
    while pos <= scan_limit {
        reader.seek(SeekFrom::Start(pos)).ok()?;

        let deprecated = read_i32(reader).ok()?;
        if deprecated != 0 {
            pos += 4;
            continue;
        }

        let pin_count_val = read_i32(reader).ok()?;
        if !(1..=MAX_PIN_COUNT).contains(&pin_count_val) {
            pos += 4;
            continue;
        }

        let result = try_pins_at(reader, name_table, end, ver, pos);
        if result.is_some() {
            return result;
        }

        pos += 4;
    }

    None
}

/// Try parsing pins at a specific position, with UE5/UE4 format negotiation.
fn try_pins_at(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
    pos: u64,
) -> Option<Vec<EdGraphPin>> {
    if ver.file_ver_ue5 > 0 {
        reader.seek(SeekFrom::Start(pos)).ok()?;
        let ue5_result = try_parse_pins(reader, name_table, end, true);
        reader.seek(SeekFrom::Start(pos)).ok()?;
        let ue4_result = try_parse_pins(reader, name_table, end, false);
        match (ue5_result, ue4_result) {
            (Some(a), Some(b)) => Some(if a.len() >= b.len() { a } else { b }),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    } else {
        reader.seek(SeekFrom::Start(pos)).ok()?;
        try_parse_pins(reader, name_table, end, false)
    }
}

/// Parse EdGraph pin data from a node export's post-property stream.
///
/// Returns a Vec of pins with per-pin LinkedTo connections.
/// Based on UE4.27 `UEdGraphPin::Serialize` format.
fn try_parse_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
) -> Option<Vec<EdGraphPin>> {
    let result: Result<Vec<EdGraphPin>> = (|| {
        let remaining = end.saturating_sub(reader.position());
        if remaining < 8 {
            return Ok(Vec::new());
        }

        // UEdGraphNode::Serialize writes deprecated pins (always 0) then new pin count
        let deprecated_count = read_i32(reader)?;
        let pin_count = read_i32(reader)?;
        if deprecated_count != 0 {
            anyhow::bail!("deprecated_pin_count={deprecated_count}");
        }
        if !(0..=MAX_PIN_COUNT).contains(&pin_count) {
            anyhow::bail!("pin_count={pin_count}");
        }

        let mut pins = Vec::new();
        for _ in 0..pin_count {
            match read_one_pin(reader, name_table, end, ue5, 0) {
                Ok(pin_group) => pins.extend(pin_group),
                Err(_) => break,
            }
        }

        Ok(pins)
    })();

    match result {
        Ok(pins) if !pins.is_empty() => Some(pins),
        Err(err) => {
            eprintln!("  pin err: {err}");
            None
        }
        _ => None,
    }
}

/// Read a single pin from the owning node's pin array.
///
/// UE4.27 format: SerializePin writes (bNullPtr, OwningNode, PinId),
/// then UEdGraphPin::Serialize writes the full pin data starting with
/// (OwningNode, PinId) again, followed by name, type, defaults, LinkedTo, etc.
///
/// `depth` tracks SubPin recursion to prevent stack overflow on corrupt data.
#[allow(clippy::only_used_in_recursion)] // end is threaded for future bounds checks
fn read_one_pin(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
    depth: usize,
) -> Result<Vec<EdGraphPin>> {
    // SerializePin wrapper: bNullPtr(i32) + OwningNode(i32) + PinGuid(FGuid)
    let is_null = read_i32(reader)?;
    if is_null != 0 {
        anyhow::bail!("null pin");
    }
    let _wrapper_owner = read_i32(reader)?;
    let _wrapper_guid = read_guid(reader)?;

    // UEdGraphPin::Serialize: OwningNode + PinId (repeated from wrapper)
    let _owning_node = read_i32(reader)?;
    let _pin_id = read_guid(reader)?;
    let pin_name = name_table.fname(reader)?;

    skip_ftext(reader, name_table)?; // PinFriendlyName

    // UE5: SourceIndex (i32) added after PinFriendlyName
    if ue5 {
        let _source_index = read_i32(reader)?;
    }

    let _tooltip = read_fstring(reader)?; // PinToolTip
    let direction = read_u8(reader)?; // Direction
    let type_name = read_pin_type(reader, name_table, ue5)?; // FEdGraphPinType

    // Default values
    let _default_value = read_fstring(reader)?;
    let _autogen_default = read_fstring(reader)?;
    let _default_object = read_i32(reader)?;
    skip_ftext(reader, name_table)?; // DefaultTextValue

    let linked_to = read_linked_to(reader)?;
    let sub_pins = read_sub_pins(reader, name_table, end, ue5, depth)?;

    // ParentPin + ReferencePassThroughConnection
    read_pin_ref(reader)?;
    read_pin_ref(reader)?;

    // Editor-only: PersistentGuid(16) + bitfield(4)
    let _persistent_guid = read_guid(reader)?;
    let _bitfield = read_u32(reader)?;

    let mut result = vec![EdGraphPin {
        name: pin_name,
        pin_type: type_name,
        direction,
        linked_to,
    }];
    result.extend(sub_pins);
    Ok(result)
}

/// Read the LinkedTo array: export indices of nodes connected to this pin.
fn read_linked_to(reader: &mut Reader) -> Result<Vec<usize>> {
    let count = read_i32(reader)?;
    ensure!(
        (0..MAX_LINKED_COUNT).contains(&count),
        "linked_count={count}"
    );
    let mut linked_to: Vec<usize> = Vec::new();
    for _ in 0..count {
        let is_null = read_i32(reader)?;
        if is_null == 0 {
            let owner_idx = read_i32(reader)?;
            let _pin_guid = read_guid(reader)?;
            if owner_idx > 0 {
                let idx = owner_idx as usize;
                if !linked_to.contains(&idx) {
                    linked_to.push(idx);
                }
            }
        }
    }
    Ok(linked_to)
}

/// Read the SubPins array (recursive, depth-limited).
///
/// Sub-pins on split structs contain field-specific names and connections
/// used for comment placement.
fn read_sub_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
    depth: usize,
) -> Result<Vec<EdGraphPin>> {
    let count = read_i32(reader)?;
    ensure!((0..MAX_SUBPIN_COUNT).contains(&count), "sub_count={count}");
    ensure!(
        depth < MAX_SUBPIN_DEPTH,
        "SubPin nesting too deep ({depth})"
    );
    let mut sub_pins: Vec<EdGraphPin> = Vec::new();
    for _ in 0..count {
        let is_null = read_i32(reader)?;
        if is_null == 0 {
            let _owner = read_i32(reader)?;
            let _guid = read_guid(reader)?;
            sub_pins.extend(read_one_pin(reader, name_table, end, ue5, depth + 1)?);
        }
    }
    Ok(sub_pins)
}

/// Read a nullable pin reference (bNullPtr + optional OwningNode + PinGuid).
fn read_pin_ref(reader: &mut Reader) -> Result<()> {
    let is_null = read_i32(reader)?; // bool as i32
    if is_null == 0 {
        let _owner = read_i32(reader)?;
        let _guid = read_guid(reader)?;
    }
    Ok(())
}

/// Read FEdGraphPinType (UE4.27 format).
/// Returns the pin category name (e.g., "exec", "bool", "object").
fn read_pin_type(reader: &mut Reader, name_table: &NameTable, ue5: bool) -> Result<String> {
    let category = name_table.fname(reader)?;
    let _subcategory = name_table.fname(reader)?;
    let _subcategory_object = read_i32(reader)?; // TWeakObjectPtr as package index

    // ContainerType (EPinContainerType: u8, None=0, Array=1, Set=2, Map=3)
    let container_type = read_u8(reader)?;
    if container_type == 3 {
        // Map value type: FEdGraphTerminalType
        read_terminal_type(reader, name_table)?;
    }

    // bIsReference and bIsWeakPointer (bools serialized as i32)
    let _is_reference = read_i32(reader)?;
    let _is_weak_pointer = read_i32(reader)?;

    // FSimpleMemberReference (for delegate pins)
    let _member_parent = read_i32(reader)?; // UObject*
    let _member_name = name_table.fname(reader)?;
    let _member_guid = read_guid(reader)?;

    // bIsConst (bool as i32)
    let _is_const = read_i32(reader)?;

    // bIsUObjectWrapper (bool as i32)
    let _is_uobject_wrapper = read_i32(reader)?;

    // UE5: bSerializeAsSinglePrecisionFloat (bool as i32, editor-only)
    if ue5 {
        let _single_precision = read_i32(reader)?;
    }

    Ok(category)
}

/// Read FEdGraphTerminalType.
fn read_terminal_type(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    let _category = name_table.fname(reader)?;
    let _subcategory = name_table.fname(reader)?;
    let _subcategory_object = read_i32(reader)?;
    let _is_const = read_i32(reader)?; // bool as i32
    let _is_weak = read_i32(reader)?; // bool as i32
    let _is_uobject_wrapper = read_i32(reader)?; // bool as i32
    Ok(())
}

/// Skip an FText in the binary stream.
///
/// UE4 FText format: i32 Flags, i8 HistoryType, then type-specific content.
/// For None (-1): bool bHasCultureInvariantString + optional FString.
/// For Base (0): FString Namespace + FString Key + FString SourceString.
fn skip_ftext(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    let _flags = read_i32(reader)?;
    let history_type = {
        let val = read_u8(reader)?;
        val as i8
    };
    match history_type {
        -1 => {
            // None: bool bHasCultureInvariantString + optional FString
            let has_invariant = read_i32(reader)?; // bool as i32
            if has_invariant != 0 {
                let _invariant = read_fstring(reader)?;
            }
        }
        0 => {
            // Base: namespace + key + source string
            let _ns = read_fstring(reader)?;
            let _key = read_fstring(reader)?;
            let _src = read_fstring(reader)?;
        }
        1 | 2 => {
            // NamedFormat / OrderedFormat: pattern FText + arguments array.
            // Each argument: FString key + FText value.
            skip_ftext(reader, name_table)?;
            let arg_count = read_i32(reader)?;
            for _ in 0..arg_count {
                let _arg_name = read_fstring(reader)?;
                skip_ftext(reader, name_table)?;
            }
        }
        11 => {
            // StringTableEntry: table_id (FName) + key (FString)
            let _table = name_table.fname(reader)?;
            let _key = read_fstring(reader)?;
        }
        _ => anyhow::bail!("unhandled FText history_type={history_type}"),
    }
    Ok(())
}
