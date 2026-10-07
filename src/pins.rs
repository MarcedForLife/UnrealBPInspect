//! EdGraph pin parsing: reads pin connection data from K2Node exports.
//!
//! UE4 serializes pin arrays after each K2Node's tagged property stream.
//! This module scans for the pin signature and parses pin types, directions,
//! and LinkedTo connections used for comment placement and structural analysis.

use anyhow::{ensure, Context, Result};
use std::io::{Seek, SeekFrom};

use crate::binary::*;
use crate::properties::read_edgraph_pin_type;
use crate::types::{AssetVersion, EdGraphPin, EdGraphPinMetadata, LinkedPin, PropValue, Property};

/// Sanity cap on pin count per node (most nodes have < 50 pins).
const MAX_PIN_COUNT: i32 = 500;

/// Sanity cap on LinkedTo entries per pin (most pins have 0-3 links).
const MAX_LINKED_COUNT: i32 = 200;

/// Sanity cap on SubPins per pin.
const MAX_SUBPIN_COUNT: i32 = 50;

/// Maximum bytes past the property stream to scan for pin data.
/// K2Node class-specific data is typically 0-60 bytes of flags and references.
const MAX_SCAN_DISTANCE: u64 = 256;

/// Find a complete pin array, including the cached location in the scan.
/// Speculative signature misses are not errors. Once a repeated pin wrapper
/// identifies an array, failure in every supported layout is reported unless
/// another complete candidate is found. Partial arrays are never returned.
pub fn scan_for_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
    hint: Option<u64>,
) -> Result<(Option<Vec<EdGraphPin>>, Option<u64>)> {
    let scan_start = reader.position();
    let bounded_end = end.min(reader.get_ref().len() as u64);
    let scan_limit = scan_start
        .saturating_add(MAX_SCAN_DISTANCE)
        .min(bounded_end);
    let mut candidates = vec![scan_start];
    if let Some(delta) = hint.filter(|delta| *delta > 0) {
        let hinted = scan_start.saturating_add(delta);
        if hinted <= scan_limit {
            candidates.push(hinted);
        }
    }
    candidates.extend((scan_start..=scan_limit).step_by(4));
    // Earlier arrays take precedence over apparent headers inside their pins.
    // A cached offset cannot safely bypass these ownership checks.
    candidates.sort_unstable();
    candidates.dedup();
    let mut consumed: Vec<std::ops::Range<u64>> = Vec::new();
    let mut failure = None;
    let mut candidate_reader = std::io::Cursor::new(&reader.get_ref()[..bounded_end as usize]);
    for pos in candidates {
        if consumed.iter().any(|range| range.contains(&pos))
            || !has_pin_signature(candidate_reader.get_ref(), pos as usize)
        {
            continue;
        }
        match try_pins_at(
            &mut candidate_reader,
            name_table,
            bounded_end,
            ver,
            pos,
            &mut consumed,
        ) {
            Ok(pins) => {
                reader.set_position(candidate_reader.position());
                return Ok((Some(pins), Some(pos - scan_start)));
            }
            Err(error) => {
                if failure.is_none() {
                    failure = Some((candidate_reader.position(), error));
                }
            }
        }
    }
    if let Some((position, error)) = failure {
        reader.set_position(position);
        return Err(error);
    }
    reader.set_position(scan_start);
    Ok((None, hint))
}

/// The owning-node wrapper repeats the positive owner and pin GUID. This
/// distinguishes real pin records from incidental zero/count pairs in class
/// metadata, even when the first pin's remaining payload is malformed.
fn pin_wrapper_at(bytes: &[u8], pos: usize) -> bool {
    let Some(wrapper) = pos.checked_add(44).and_then(|end| bytes.get(pos..end)) else {
        return false;
    };
    wrapper[..4] == [0; 4]
        && i32::from_le_bytes(wrapper[4..8].try_into().unwrap()) > 0
        && wrapper[4..8] == wrapper[24..28]
        && wrapper[8..24] == wrapper[28..44]
        && wrapper[8..24] != [0; 16]
}

fn has_pin_signature(bytes: &[u8], pos: usize) -> bool {
    let Some(header) = pos.checked_add(8).and_then(|end| bytes.get(pos..end)) else {
        return false;
    };
    header[..4] == [0; 4] && pin_wrapper_at(bytes, pos + 8)
}

/// UE5 packages may carry UE4 pin serialization. A complete fallback takes
/// precedence over any error from the first layout attempt.
fn try_pins_at(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ver: AssetVersion,
    pos: u64,
    consumed: &mut Vec<std::ops::Range<u64>>,
) -> Result<Vec<EdGraphPin>> {
    reader.seek(SeekFrom::Start(pos))?;
    if ver.file_ver_ue5 > 0 {
        match try_parse_pins(reader, name_table, end, true, consumed) {
            Ok(pins) => return Ok(pins),
            Err(ue5_error) => {
                reader.seek(SeekFrom::Start(pos))?;
                return try_parse_pins(reader, name_table, end, false, consumed).with_context(|| {
                    format!("pin array at file offset {pos}, UE5 layout failed ({ue5_error:#}) and UE4 fallback failed")
                });
            }
        }
    }
    try_parse_pins(reader, name_table, end, false, consumed)
        .with_context(|| format!("pin array at file offset {pos}"))
}

/// All declared records must decode within the export. The caller publishes
/// the array only after this function succeeds, so no prefix escapes on error.
fn try_parse_pins(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
    consumed: &mut Vec<std::ops::Range<u64>>,
) -> Result<Vec<EdGraphPin>> {
    ensure!(
        end.saturating_sub(reader.position()) >= 8,
        "truncated pin array header"
    );
    let deprecated_count = read_i32(reader)?;
    let pin_count = read_i32(reader)?;
    ensure!(
        deprecated_count == 0,
        "deprecated_pin_count={deprecated_count}"
    );
    ensure!(
        (0..=MAX_PIN_COUNT).contains(&pin_count),
        "pin_count={pin_count}"
    );
    let mut pins = Vec::new();
    for index in 0..pin_count {
        let position = reader.position();
        pins.push(read_one_pin(reader, name_table, end, ue5).with_context(|| {
            format!("pin {} of {pin_count} at file offset {position}", index + 1)
        })?);
        consumed.push(position..reader.position());
    }
    ensure!(
        !pin_wrapper_at(reader.get_ref(), reader.position() as usize),
        "pin array contains more records than its declared count {pin_count}"
    );
    Ok(pins)
}

/// Read a single pin from the owning node's pin array.
///
/// UE4.27 format: SerializePin writes (bNullPtr, OwningNode, PinId),
/// then UEdGraphPin::Serialize writes the full pin data starting with
/// (OwningNode, PinId) again, followed by name, type, defaults, LinkedTo, etc.
///
fn read_one_pin(
    reader: &mut Reader,
    name_table: &NameTable,
    end: u64,
    ue5: bool,
) -> Result<EdGraphPin> {
    // SerializePin wrapper: bNullPtr(i32) + OwningNode(i32) + PinGuid(FGuid)
    let is_null = read_i32(reader)?;
    if is_null != 0 {
        anyhow::bail!("null pin");
    }
    let wrapper_owner = read_i32(reader)?;
    let wrapper_guid = read_guid(reader)?;

    // UEdGraphPin::Serialize: OwningNode + PinId (repeated from wrapper)
    let owning_node = read_i32(reader)?;
    let pin_id = read_guid(reader)?;
    ensure!(
        wrapper_owner == owning_node && wrapper_guid == pin_id,
        "pin wrapper does not match its owning payload"
    );
    let pin_name = name_table.fname(reader)?;

    skip_ftext(reader, name_table)?; // PinFriendlyName

    // UE5: SourceIndex (i32) added after PinFriendlyName
    if ue5 {
        let _source_index = read_i32(reader)?;
    }

    let _tooltip = read_pin_string(reader)?; // PinToolTip
    let direction = read_u8(reader)?; // Direction
    ensure!(direction <= 1, "invalid pin direction {direction}");
    let (type_name, type_details) = read_pin_type(reader, name_table, ue5)?; // FEdGraphPinType

    // Default values
    let default_value = read_pin_string(reader)?;
    let autogenerated_default_value = read_pin_string(reader)?;
    let default_object = read_i32(reader)?;
    let default_text_start = reader.position() as usize;
    let default_text_source = read_ftext_source(reader, name_table, 0)?;
    let default_text_payload =
        reader.get_ref()[default_text_start..reader.position() as usize].to_vec();

    let linked_to = read_linked_to(reader)?;
    let sub_pins = read_sub_pins(reader)?;
    let parent_pin = read_pin_ref(reader)?;
    let reference_pass_through = read_pin_ref(reader)?;

    // Editor-only: PersistentGuid(16) + bitfield(4)
    let _persistent_guid = read_guid(reader)?;
    let _bitfield = read_u32(reader)?;

    ensure!(reader.position() <= end, "pin crosses export boundary");
    Ok(EdGraphPin {
        name: pin_name,
        pin_type: type_name,
        direction,
        pin_id,
        linked_to,
        metadata: Some(EdGraphPinMetadata {
            default_value,
            autogenerated_default_value,
            default_object,
            default_text_source,
            default_text_payload,
            type_details,
            parent_pin,
            sub_pins,
            reference_pass_through,
        }),
    })
}

/// Read the LinkedTo array: (owning node export index, target pin FGuid) pairs.
fn read_linked_to(reader: &mut Reader) -> Result<Vec<LinkedPin>> {
    let count = read_i32(reader)?;
    ensure!(
        (0..MAX_LINKED_COUNT).contains(&count),
        "linked_count={count}"
    );
    let mut linked_to: Vec<LinkedPin> = Vec::new();
    for _ in 0..count {
        if let Some(link) = read_pin_ref(reader)? {
            if !linked_to.contains(&link) {
                linked_to.push(link);
            }
        }
    }
    Ok(linked_to)
}

/// SubPins contains references, like LinkedTo. Each referenced pin's full
/// payload appears separately in the owning node's pin array.
fn read_sub_pins(reader: &mut Reader) -> Result<Vec<LinkedPin>> {
    let count = read_i32(reader)?;
    ensure!((0..MAX_SUBPIN_COUNT).contains(&count), "sub_count={count}");
    let mut sub_pins = Vec::new();
    for _ in 0..count {
        if let Some(pin) = read_pin_ref(reader)? {
            sub_pins.push(pin);
        }
    }
    Ok(sub_pins)
}

/// Read a nullable pin reference (bNullPtr + optional OwningNode + PinGuid).
fn read_pin_ref(reader: &mut Reader) -> Result<Option<LinkedPin>> {
    let is_null = read_i32(reader)?;
    ensure!(
        matches!(is_null, 0 | 1),
        "invalid pin reference null flag {is_null}"
    );
    if is_null == 1 {
        return Ok(None);
    }
    let owner = read_i32(reader)?;
    let pin_id = read_guid(reader)?;
    ensure!(owner > 0, "invalid pin reference owner {owner}");
    Ok(Some(LinkedPin {
        node: owner as usize,
        pin_id,
    }))
}

fn read_pin_type(
    reader: &mut Reader,
    name_table: &NameTable,
    ue5: bool,
) -> Result<(String, Vec<Property>)> {
    let fields = read_edgraph_pin_type(reader, name_table, ue5)?;
    let category = fields
        .iter()
        .find_map(|field| match (field.name.as_str(), &field.value) {
            ("PinCategory", PropValue::Name(category)) => Some(category.clone()),
            _ => None,
        })
        .context("pin type has no category")?;
    Ok((category, fields))
}

fn read_pin_string(reader: &mut Reader) -> Result<String> {
    let length = read_i32(reader)?;
    if length == 0 {
        return Ok(String::new());
    }
    let byte_count = u64::from(length.unsigned_abs()) * if length < 0 { 2 } else { 1 };
    let start = reader.position();
    let end = start
        .checked_add(byte_count)
        .context("pin string length overflow")?;
    let payload = reader
        .get_ref()
        .get(start as usize..usize::try_from(end)?)
        .context("pin string exceeds available data")?;
    let value = if length > 0 {
        ensure!(payload.last() == Some(&0), "pin string has no terminator");
        String::from_utf8(payload[..payload.len() - 1].to_vec())
            .context("invalid UTF-8 pin string")?
    } else {
        ensure!(payload.ends_with(&[0, 0]), "pin string has no terminator");
        let characters: Vec<u16> = payload[..payload.len() - 2]
            .as_chunks::<2>()
            .0
            .iter()
            .map(|bytes| u16::from_le_bytes([bytes[0], bytes[1]]))
            .collect();
        String::from_utf16(&characters).context("invalid UTF-16 pin string")?
    };
    reader.set_position(end);
    Ok(value)
}

/// Skip an FText in the binary stream.
///
/// UE4 FText format: i32 Flags, i8 HistoryType, then type-specific content.
/// For None (-1): bool bHasCultureInvariantString + optional FString.
/// For Base (0): FString Namespace + FString Key + FString SourceString.
fn skip_ftext(reader: &mut Reader, name_table: &NameTable) -> Result<()> {
    read_ftext_source(reader, name_table, 0).map(|_| ())
}

fn read_ftext_source(
    reader: &mut Reader,
    name_table: &NameTable,
    depth: usize,
) -> Result<Option<String>> {
    ensure!(depth < 64, "formatted pin text nesting exceeds limit");
    let _flags = read_i32(reader)?;
    let history_type = {
        let val = read_u8(reader)?;
        val as i8
    };
    match history_type {
        -1 => {
            // None: bool bHasCultureInvariantString + optional FString
            let has_invariant = read_i32(reader)?; // bool as i32
            ensure!(
                matches!(has_invariant, 0 | 1),
                "invalid invariant text flag {has_invariant}"
            );
            return Ok(Some(if has_invariant != 0 {
                read_pin_string(reader)?
            } else {
                String::new()
            }));
        }
        0 => {
            // Base: namespace + key + source string
            let _ns = read_pin_string(reader)?;
            let _key = read_pin_string(reader)?;
            return read_pin_string(reader).map(Some);
        }
        1 | 2 => {
            // Named and ordered histories store typed format arguments.
            read_ftext_source(reader, name_table, depth + 1)?;
            let arg_count = read_i32(reader)?;
            ensure!(
                (0..=MAX_PIN_COUNT).contains(&arg_count),
                "invalid formatted text argument count"
            );
            for _ in 0..arg_count {
                if history_type == 1 {
                    let _arg_name = read_pin_string(reader)?;
                }
                // Pin labels use text placeholders. Other payload widths can
                // depend on custom versions we have not retained here.
                let argument_type = read_u8(reader)?;
                ensure!(
                    argument_type == 4,
                    "unsupported formatted pin text argument type {argument_type}"
                );
                read_ftext_source(reader, name_table, depth + 1)?;
            }
        }
        11 => {
            // StringTableEntry: table_id (FName) + key (FString)
            let _table = name_table.fname(reader)?;
            let _key = read_pin_string(reader)?;
        }
        _ => anyhow::bail!("unhandled FText history_type={history_type}"),
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn integer(bytes: &mut Vec<u8>, value: i32) {
        bytes.extend(value.to_le_bytes());
    }
    fn name(bytes: &mut Vec<u8>, index: i32) {
        integer(bytes, index);
        integer(bytes, 0);
    }
    fn string(bytes: &mut Vec<u8>, value: &str) {
        integer(bytes, (value.len() + 1) as i32);
        bytes.extend(value.as_bytes());
        bytes.push(0);
    }
    fn empty_text(bytes: &mut Vec<u8>) {
        integer(bytes, 0);
        bytes.push(255);
        integer(bytes, 0);
    }
    fn formatted_text(bytes: &mut Vec<u8>, history: u8) {
        integer(bytes, 0);
        bytes.push(history);
        empty_text(bytes);
        integer(bytes, 1);
        if history == 1 {
            string(bytes, "Field");
        }
        bytes.push(4);
        empty_text(bytes);
    }
    fn pin_reference(bytes: &mut Vec<u8>, identifier: u8) {
        integer(bytes, 0);
        integer(bytes, 1);
        bytes.extend([identifier; 16]);
    }
    fn pin(bytes: &mut Vec<u8>, child: bool, ue5: bool) {
        let identifier = if child { 2 } else { 1 };
        pin_reference(bytes, identifier);
        integer(bytes, 1);
        bytes.extend([identifier; 16]);
        name(bytes, if child { 2 } else { 1 });
        if child {
            formatted_text(bytes, 1);
        } else {
            empty_text(bytes);
        }
        if ue5 {
            integer(bytes, 0);
        }
        integer(bytes, 0);
        bytes.push(1);
        name(bytes, if child { 4 } else { 3 });
        name(bytes, 0);
        integer(bytes, 0);
        bytes.push(0);
        for _ in 0..3 {
            integer(bytes, 0);
        }
        name(bytes, 0);
        bytes.extend([0; 16]);
        integer(bytes, 0);
        integer(bytes, 0);
        if ue5 {
            integer(bytes, 0);
        }
        for _ in 0..3 {
            integer(bytes, 0);
        }
        empty_text(bytes);
        integer(bytes, 0);
        integer(bytes, if child { 0 } else { 1 });
        if !child {
            pin_reference(bytes, 2);
        }
        if child {
            pin_reference(bytes, 1);
        } else {
            integer(bytes, 1);
        }
        integer(bytes, 1);
        bytes.extend([0; 16]);
        integer(bytes, 0);
    }

    #[test]
    fn split_pins_are_owned_payloads_with_references_and_formatted_labels() {
        let names = NameTable::from_names(
            ["None", "Value", "Value_Field", "struct", "float"]
                .map(String::from)
                .to_vec(),
        );
        for ue5 in [false, true] {
            let mut bytes = Vec::new();
            integer(&mut bytes, 0);
            integer(&mut bytes, 2);
            pin(&mut bytes, false, ue5);
            pin(&mut bytes, true, ue5);
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let pins = try_parse_pins(
                &mut reader,
                &names,
                bytes.len() as u64,
                ue5,
                &mut Vec::new(),
            )
            .expect("complete synthetic pins");
            assert_eq!(pins.len(), 2);
            assert_eq!(pins[0].name, "Value");
            assert_eq!(pins[1].name, "Value_Field");
            assert_eq!(pins[1].pin_type, "float");
            assert_eq!(pins[1].pin_id, [2; 16]);
            let parent = pins[0].metadata.as_ref().unwrap();
            let child = pins[1].metadata.as_ref().unwrap();
            assert_eq!(
                parent.sub_pins,
                vec![LinkedPin {
                    node: 1,
                    pin_id: [2; 16]
                }]
            );
            assert_eq!(
                child.parent_pin,
                Some(LinkedPin {
                    node: 1,
                    pin_id: [1; 16]
                })
            );
            assert!(parent.parent_pin.is_none());
            assert!(child.sub_pins.is_empty());
            assert!(parent.reference_pass_through.is_none());
            assert_eq!(parent.default_text_source.as_deref(), Some(""));
            assert_eq!(reader.position(), bytes.len() as u64);
        }
    }

    fn pin_with_metadata(ue5: bool, default_text: &[u8]) -> Vec<u8> {
        let mut bytes = Vec::new();
        pin_reference(&mut bytes, 1);
        integer(&mut bytes, 1);
        bytes.extend([1; 16]);
        name(&mut bytes, 1);
        empty_text(&mut bytes);
        if ue5 {
            integer(&mut bytes, 0);
        }
        string(&mut bytes, "Tooltip");
        bytes.push(0);
        name(&mut bytes, 3); // Object category.
        name(&mut bytes, 2); // Subcategory.
        integer(&mut bytes, -9);
        bytes.push(3); // Map container.
        name(&mut bytes, 4); // Float terminal category.
        name(&mut bytes, 0);
        for value in [-8, 1, 0, 1, 1, 0, -5] {
            integer(&mut bytes, value);
        }
        name(&mut bytes, 5);
        bytes.extend([7; 16]);
        integer(&mut bytes, 1);
        integer(&mut bytes, 0);
        if ue5 {
            integer(&mut bytes, 1);
        }
        string(&mut bytes, "Explicit");
        string(&mut bytes, "Generated");
        integer(&mut bytes, -6);
        bytes.extend(default_text);
        integer(&mut bytes, 1);
        pin_reference(&mut bytes, 2); // LinkedTo.
        integer(&mut bytes, 1);
        pin_reference(&mut bytes, 3); // SubPins.
        pin_reference(&mut bytes, 4); // ParentPin.
        pin_reference(&mut bytes, 5); // ReferencePassThroughConnection.
        bytes.extend([0; 16]);
        integer(&mut bytes, 0);
        bytes
    }

    #[test]
    fn pin_metadata_retains_defaults_types_and_distinct_reference_roles() {
        let names = NameTable::from_names(
            ["None", "Value", "SubCategory", "object", "float", "Handler"]
                .map(String::from)
                .to_vec(),
        );
        for ue5 in [false, true] {
            for history in [0, 1] {
                let mut default_text = Vec::new();
                if history == 0 {
                    integer(&mut default_text, 0);
                    default_text.push(0);
                    for value in ["Example", "Key", "Default source"] {
                        string(&mut default_text, value);
                    }
                } else {
                    formatted_text(&mut default_text, 1);
                }
                let bytes = pin_with_metadata(ue5, &default_text);
                let mut reader = std::io::Cursor::new(bytes.as_slice());
                let pin = read_one_pin(&mut reader, &names, bytes.len() as u64, ue5).unwrap();
                assert_eq!(pin.pin_type, "object");
                assert_eq!(
                    pin.linked_to,
                    vec![LinkedPin {
                        node: 1,
                        pin_id: [2; 16]
                    }]
                );
                let metadata = pin.metadata.unwrap();
                assert_eq!(metadata.default_value, "Explicit");
                assert_eq!(metadata.autogenerated_default_value, "Generated");
                assert_eq!(metadata.default_object, -6);
                assert_eq!(metadata.default_text_payload, default_text);
                assert_eq!(
                    metadata.default_text_source.as_deref(),
                    (history == 0).then_some("Default source")
                );
                assert_eq!(
                    metadata.sub_pins,
                    vec![LinkedPin {
                        node: 1,
                        pin_id: [3; 16]
                    }]
                );
                assert_eq!(
                    metadata.parent_pin,
                    Some(LinkedPin {
                        node: 1,
                        pin_id: [4; 16]
                    })
                );
                assert_eq!(
                    metadata.reference_pass_through,
                    Some(LinkedPin {
                        node: 1,
                        pin_id: [5; 16]
                    })
                );
                let fields = &metadata.type_details;
                assert!(fields
                    .iter()
                    .any(|field| field.name == "PinSubCategoryObject"
                        && matches!(field.value, PropValue::Object(-9))));
                assert!(fields.iter().any(|field| field.name == "ContainerType"
                    && matches!(&field.value, PropValue::Enum { value, .. } if value == "Map")));
                assert!(fields.iter().any(|field| field.name == "PinValueType" && matches!(&field.value, PropValue::Struct { fields, .. } if fields.len() == 6)));
                assert_eq!(
                    fields
                        .iter()
                        .any(|field| field.name == "bSerializeAsSinglePrecisionFloat"),
                    ue5
                );
                assert_eq!(reader.position(), bytes.len() as u64);
            }
        }
    }

    #[test]
    fn pin_references_preserve_null_and_reject_invalid_owners_or_flags() {
        assert!(
            read_pin_ref(&mut std::io::Cursor::new(1i32.to_le_bytes().as_slice()))
                .unwrap()
                .is_none()
        );
        for owner in [-1, 0] {
            let mut bytes = vec![0; 4];
            integer(&mut bytes, owner);
            bytes.extend([1; 16]);
            assert!(read_pin_ref(&mut std::io::Cursor::new(bytes.as_slice())).is_err());
        }
        assert!(read_pin_ref(&mut std::io::Cursor::new(2i32.to_le_bytes().as_slice())).is_err());
    }

    #[test]
    fn text_sources_do_not_claim_to_render_formatted_or_table_histories() {
        let names = NameTable::from_names(vec!["None".into(), "Labels".into()]);
        for history in [-1i8, 0, 1, 2, 11] {
            let mut bytes = Vec::new();
            match history {
                -1 => {
                    integer(&mut bytes, 0);
                    bytes.push(255);
                    integer(&mut bytes, 1);
                    string(&mut bytes, "Exact source");
                }
                0 => {
                    integer(&mut bytes, 0);
                    bytes.push(0);
                    string(&mut bytes, "Example");
                    string(&mut bytes, "Label");
                    string(&mut bytes, "Exact source");
                }
                1 | 2 => formatted_text(&mut bytes, history as u8),
                11 => {
                    integer(&mut bytes, 0);
                    bytes.push(11);
                    name(&mut bytes, 1);
                    string(&mut bytes, "Label");
                }
                _ => unreachable!(),
            }
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let source = read_ftext_source(&mut reader, &names, 0).unwrap();
            assert_eq!(source.as_deref(), (history <= 0).then_some("Exact source"));
            assert_eq!(reader.position(), bytes.len() as u64);
        }
    }

    #[test]
    fn malformed_default_strings_cannot_become_matching_evidence() {
        for (length, payload) in [
            (2i32, vec![b'a', b'b']),
            (2, vec![0xff, 0]),
            (-2, vec![b'a', 0, b'b', 0]),
            (-2, vec![0, 0xd8, 0, 0]),
            (i32::MAX, vec![]),
        ] {
            let bytes = [length.to_le_bytes().to_vec(), payload].concat();
            assert!(read_pin_string(&mut std::io::Cursor::new(bytes.as_slice())).is_err());
        }
        let expected = "A\u{1f680}\0";
        let characters: Vec<u16> = expected.encode_utf16().chain([0]).collect();
        let mut bytes = (-(characters.len() as i32)).to_le_bytes().to_vec();
        bytes.extend(characters.into_iter().flat_map(u16::to_le_bytes));
        assert_eq!(
            read_pin_string(&mut std::io::Cursor::new(bytes.as_slice())).unwrap(),
            expected
        );
    }

    #[test]
    fn named_and_ordered_text_consume_argument_type_before_text_payload() {
        let names = NameTable::from_names(Vec::new());
        for history in [1, 2] {
            let mut bytes = Vec::new();
            formatted_text(&mut bytes, history);
            integer(&mut bytes, 1234);
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            skip_ftext(&mut reader, &names).unwrap();
            assert_eq!(read_i32(&mut reader).unwrap(), 1234);
        }
    }

    #[test]
    fn formatted_text_rejects_excessive_nesting_and_unknown_argument_types() {
        let names = NameTable::from_names(Vec::new());
        let mut nested = Vec::new();
        for _ in 0..65 {
            integer(&mut nested, 0);
            nested.push(2);
        }
        empty_text(&mut nested);
        assert!(skip_ftext(&mut std::io::Cursor::new(nested.as_slice()), &names).is_err());
        let mut unknown = Vec::new();
        integer(&mut unknown, 0);
        unknown.push(2);
        empty_text(&mut unknown);
        integer(&mut unknown, 1);
        unknown.push(255);
        assert!(skip_ftext(&mut std::io::Cursor::new(unknown.as_slice()), &names).is_err());
    }

    fn complete_pin_array(ue5: bool) -> (Vec<u8>, NameTable, usize) {
        let names = NameTable::from_names(
            ["None", "Value", "Value_Field", "struct", "float"]
                .map(String::from)
                .to_vec(),
        );
        let mut bytes = Vec::new();
        integer(&mut bytes, 0);
        integer(&mut bytes, 2);
        pin(&mut bytes, false, ue5);
        let second_pin = bytes.len();
        pin(&mut bytes, true, ue5);
        (bytes, names, second_pin)
    }

    #[test]
    fn truncated_arrays_never_publish_a_successfully_parsed_prefix() {
        for ue5 in [false, true] {
            let (bytes, names, second_pin) = complete_pin_array(ue5);
            let version = AssetVersion {
                file_ver: 522,
                file_ver_ue5: if ue5 { 1012 } else { 0 },
            };
            for end in [52, second_pin, bytes.len() - 1] {
                let mut reader = std::io::Cursor::new(bytes.as_slice());
                let error =
                    scan_for_pins(&mut reader, &names, end as u64, version, None).unwrap_err();
                let message = format!("{error:#}");
                assert!(message.contains("pin array at file offset 0"), "{message}");
                assert!(
                    message.contains(if end == 52 {
                        "pin 1 of 2"
                    } else {
                        "pin 2 of 2"
                    }),
                    "{message}"
                );
                assert!(reader.position() <= end as u64);
            }
        }
    }

    #[test]
    fn complete_ue4_fallback_wins_over_a_failed_ue5_layout() {
        let (bytes, names, _) = complete_pin_array(false);
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let (pins, hint) = scan_for_pins(
            &mut reader,
            &names,
            bytes.len() as u64,
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 1012,
            },
            Some(12),
        )
        .unwrap();
        assert_eq!(pins.unwrap().len(), 2);
        assert_eq!(hint, Some(0));
        assert_eq!(reader.position(), bytes.len() as u64);
    }

    #[test]
    fn a_later_complete_candidate_wins_over_an_incomplete_candidate() {
        let (complete, names, _) = complete_pin_array(false);
        let mut bytes = Vec::new();
        integer(&mut bytes, 0);
        integer(&mut bytes, 2);
        pin_reference(&mut bytes, 8);
        integer(&mut bytes, 1);
        bytes.extend([8; 16]);
        name(&mut bytes, 1);
        integer(&mut bytes, 0);
        bytes.push(127); // Unsupported text history makes this candidate fail.
        while bytes.len() % 4 != 0 {
            bytes.push(0);
        }
        let valid_start = bytes.len();
        bytes.extend(complete);
        for hint in [None, Some(4), Some(valid_start as u64)] {
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let (pins, new_hint) = scan_for_pins(
                &mut reader,
                &names,
                bytes.len() as u64,
                AssetVersion {
                    file_ver: 522,
                    file_ver_ue5: 0,
                },
                hint,
            )
            .unwrap();
            assert_eq!(pins.unwrap().len(), 2);
            assert_eq!(new_hint, Some(valid_start as u64));
        }
    }

    #[test]
    fn speculative_count_pairs_do_not_create_pin_diagnostics() {
        let names = NameTable::from_names(Vec::new());
        let mut bytes = vec![0; 80];
        bytes[4..8].copy_from_slice(&3i32.to_le_bytes());
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let (pins, hint) = scan_for_pins(
            &mut reader,
            &names,
            bytes.len() as u64,
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
            Some(16),
        )
        .unwrap();
        assert!(pins.is_none());
        assert_eq!(hint, Some(16));
        assert_eq!(reader.position(), 0);
    }

    #[test]
    fn declared_count_and_wrapper_mismatches_are_errors() {
        for ue5 in [false, true] {
            let (original, names, second_pin) = complete_pin_array(ue5);
            let version = AssetVersion {
                file_ver: 522,
                file_ver_ue5: if ue5 { 1012 } else { 0 },
            };
            for count in [0, 1, 3, MAX_PIN_COUNT + 1] {
                let mut bytes = original.clone();
                bytes[4..8].copy_from_slice(&count.to_le_bytes());
                let mut reader = std::io::Cursor::new(bytes.as_slice());
                assert!(
                    scan_for_pins(&mut reader, &names, bytes.len() as u64, version, None).is_err(),
                    "UE5 layout={ue5}, count={count}"
                );
            }
            let mut bytes = original;
            bytes[second_pin + 28] ^= 1;
            let mut reader = std::io::Cursor::new(bytes.as_slice());
            let error =
                scan_for_pins(&mut reader, &names, bytes.len() as u64, version, None).unwrap_err();
            assert!(format!("{error:#}").contains("pin wrapper does not match"));
        }
    }

    #[test]
    fn a_failed_array_cannot_be_replaced_with_its_valid_middle_pin() {
        let (mut bytes, names, second_pin) = complete_pin_array(false);
        bytes[4..8].copy_from_slice(&3i32.to_le_bytes());
        // Flags on the first pin look like an array count immediately
        // before the valid second pin, but are still inside the first record.
        bytes[second_pin - 4..second_pin].copy_from_slice(&1i32.to_le_bytes());
        let third_pin = bytes.len();
        pin(&mut bytes, true, false);
        bytes[third_pin + 8..third_pin + 24].fill(3);
        bytes[third_pin + 28..third_pin + 44].fill(4);
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        assert!(scan_for_pins(
            &mut reader,
            &names,
            bytes.len() as u64,
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0
            },
            None
        )
        .is_err());
    }

    #[test]
    fn a_hint_inside_a_pin_cannot_hide_the_complete_array_before_it() {
        let (mut array, names, second_pin) = complete_pin_array(false);
        array[second_pin - 4..second_pin].copy_from_slice(&1i32.to_le_bytes());
        let mut bytes = vec![255; 4];
        bytes.extend(array);
        let mut reader = std::io::Cursor::new(bytes.as_slice());
        let (pins, hint) = scan_for_pins(
            &mut reader,
            &names,
            bytes.len() as u64,
            AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
            Some((4 + second_pin - 8) as u64),
        )
        .unwrap();
        assert_eq!(pins.unwrap().len(), 2);
        assert_eq!(hint, Some(4));
    }

    #[test]
    fn fallback_cannot_turn_a_truncated_single_pin_into_a_complete_array() {
        for ue5 in [false, true] {
            let (mut bytes, names, second_pin) = complete_pin_array(ue5);
            bytes[4..8].copy_from_slice(&1i32.to_le_bytes());
            bytes.truncate(second_pin);
            for missing in 1..=20 {
                let mut reader = std::io::Cursor::new(bytes.as_slice());
                assert!(
                    scan_for_pins(
                        &mut reader,
                        &names,
                        (bytes.len() - missing) as u64,
                        AssetVersion {
                            file_ver: 522,
                            file_ver_ue5: 1012
                        },
                        None
                    )
                    .is_err(),
                    "UE5 layout={ue5}, missing={missing}"
                );
            }
        }
    }
}
