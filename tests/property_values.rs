mod common;

use std::process::Command;
use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::bytecode::emit::emit_summary_with_asset;
use unreal_bp_inspect::output_diff::diff_summary_texts;
use unreal_bp_inspect::output_summary::filter_summary;
use unreal_bp_inspect::parser::parse_asset;
use unreal_bp_inspect::prop_query::prop_value_short;
use unreal_bp_inspect::types::{ImportEntry, PropValue, Property};

fn replace_default_payload(property_type: &str, metadata: &[&str], payload: &[u8]) -> Vec<u8> {
    let mut bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let parsed = parse_asset(&bytes, false).unwrap();
    let (header, _) = parsed
        .exports
        .iter()
        .find(|(header, _)| header.object_name.starts_with("Default__"))
        .unwrap();
    let fname = |name: &str| {
        let index = (0_i32..10_000)
            .find(|index| parsed.name_table.get(*index) == name)
            .unwrap_or_else(|| panic!("fixture is missing {name}"));
        [index.to_le_bytes(), 0_i32.to_le_bytes()].concat()
    };
    let mut properties = fname("PrimaryActorTick");
    properties.extend(fname(property_type));
    properties.extend((payload.len() as i32).to_le_bytes());
    properties.extend(0_i32.to_le_bytes());
    for name in metadata {
        properties.extend(fname(name));
    }
    if property_type == "StructProperty" {
        properties.extend([0; 16]); // Struct GUID.
    }
    properties.push(0); // No property GUID.
    properties.extend(payload);
    properties.extend(fname("None"));
    assert!(properties.len() <= header.serial_size as usize);
    properties.resize(header.serial_size as usize, 0);
    let start = header.serial_offset as usize;
    bytes[start..start + properties.len()].copy_from_slice(&properties);
    let replaced = parse_asset(&bytes, false).unwrap();
    assert!(
        replaced.diagnostics.is_empty(),
        "{:?}",
        replaced.diagnostics
    );
    bytes
}

#[test]
fn cli_diff_reports_precise_defaults_and_equal_length_collection_changes() {
    let integers = |values: &[i32]| {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect::<Vec<_>>()
    };
    for (property_type, metadata, before, after, expected) in [
        (
            "FloatProperty",
            vec![],
            2.0_f32.to_le_bytes().to_vec(),
            2.00001_f32.to_le_bytes().to_vec(),
            "2.00001",
        ),
        (
            "ArrayProperty",
            vec!["IntProperty"],
            integers(&[1, 1]),
            integers(&[1, 2]),
            "Array<IntProperty>[2]",
        ),
        (
            "MapProperty",
            vec!["IntProperty", "IntProperty"],
            integers(&[0, 1, 7, 1]),
            integers(&[0, 1, 7, 2]),
            "7: 2",
        ),
        (
            "MapProperty",
            vec!["IntProperty", "IntProperty"],
            integers(&[0, 1, 7, 1]),
            integers(&[0, 1, 8, 1]),
            "8: 1",
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let before_path = directory.path().join("before.uasset");
        let after_path = directory.path().join("after.uasset");
        std::fs::write(
            &before_path,
            replace_default_payload(property_type, &metadata, &before),
        )
        .unwrap();
        std::fs::write(
            &after_path,
            replace_default_payload(property_type, &metadata, &after),
        )
        .unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
            .arg("--diff")
            .arg(&before_path)
            .arg(&after_path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{property_type}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("+  PrimaryActorTick ="), "{text}");
        assert!(text.contains(expected), "{text}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn nested_component_changes_remain_visible_and_filterable() {
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let decoded = decode_asset(&parsed);
    let export_index = parsed
        .exports
        .iter()
        .position(|(header, _)| header.object_name.ends_with("_GEN_VARIABLE"))
        .unwrap();
    let mut summaries = Vec::new();
    for value in ["before-value", "after-value"] {
        parsed.exports[export_index].1 = vec![Property {
            name: "ReviewProperty".into(),
            value: PropValue::Struct {
                struct_type: "Settings".into(),
                fields: vec![Property {
                    name: "Options".into(),
                    value: PropValue::Array {
                        inner_type: "MapProperty".into(),
                        items: vec![PropValue::Map {
                            key_type: "NameProperty".into(),
                            value_type: "TextProperty".into(),
                            entries: vec![(
                                PropValue::Name("nestedneedle".into()),
                                PropValue::Text(value.into()),
                            )],
                        }],
                    },
                }],
            },
        }];
        let summary = emit_summary_with_asset(&decoded, &parsed);
        let filtered = filter_summary(&decoded, &parsed, &["nestedneedle".into()]);
        assert!(filtered.contains("Components:"), "{filtered}");
        assert!(
            filtered.contains("ReviewProperty: Settings {Options:"),
            "{filtered}"
        );
        assert!(filtered.contains(value), "{filtered}");
        assert!(!filtered.contains("Functions:"), "{filtered}");
        summaries.push(summary);
    }
    let (diff, changed) = diff_summary_texts(&summaries[0], &summaries[1], "before", "after", 3);
    assert!(changed);
    assert!(
        diff.contains("before-value") && diff.contains("after-value"),
        "{diff}"
    );
}

#[test]
fn property_numbers_round_trip_at_their_original_precision() {
    for value in [
        2.00001_f32,
        f32::MIN_POSITIVE,
        f32::from_bits(1),
        f32::MAX,
        -0.0,
        f32::INFINITY,
        f32::NEG_INFINITY,
    ] {
        let rendered = prop_value_short(&PropValue::Float(value), &[], &[]);
        assert_eq!(
            rendered.parse::<f32>().unwrap().to_bits(),
            value.to_bits(),
            "{rendered}"
        );
    }
    for value in [
        2.00000000001_f64,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        f64::MAX,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ] {
        let rendered = prop_value_short(&PropValue::Double(value), &[], &[]);
        assert_eq!(
            rendered.parse::<f64>().unwrap().to_bits(),
            value.to_bits(),
            "{rendered}"
        );
    }
    assert_ne!(
        prop_value_short(&PropValue::Float(f32::from_bits(0x7fc00001)), &[], &[]),
        prop_value_short(&PropValue::Float(f32::from_bits(0x7fc00002)), &[], &[])
    );
    assert_ne!(
        prop_value_short(
            &PropValue::Double(f64::from_bits(0x7ff8000000000001)),
            &[],
            &[]
        ),
        prop_value_short(
            &PropValue::Double(f64::from_bits(0x7ff8000000000002)),
            &[],
            &[]
        )
    );
}

#[test]
fn property_text_escapes_delimiters_without_hiding_text_or_soft_objects() {
    let text = "first\n\"second\"\\third";
    assert_eq!(
        prop_value_short(&PropValue::Str(text.into()), &[], &[]),
        "\"first\\n\\\"second\\\"\\\\third\""
    );
    assert_eq!(
        prop_value_short(&PropValue::Text("label".into()), &[], &[]),
        "Text(\"label\")"
    );
    assert_eq!(
        prop_value_short(&PropValue::SoftObject("/Game/First.Asset".into()), &[], &[]),
        "SoftObject(\"/Game/First.Asset\")"
    );
    assert_eq!(
        prop_value_short(
            &PropValue::Unknown {
                type_name: "UnsupportedProperty".into(),
                size: 8,
                payload_sha256: "0".repeat(64)
            },
            &[],
            &[]
        ),
        format!(
            "<unknown UnsupportedProperty, 8 bytes, sha256={}>",
            "0".repeat(64)
        )
    );
}

#[test]
fn property_collection_identity_preserves_array_order_and_ignores_map_order() {
    let array = |items| PropValue::Array {
        inner_type: "IntProperty".into(),
        items,
    };
    let map = |entries| PropValue::Map {
        key_type: "IntProperty".into(),
        value_type: "IntProperty".into(),
        entries,
    };
    assert_ne!(
        prop_value_short(&array(vec![PropValue::Int(1), PropValue::Int(2)]), &[], &[]),
        prop_value_short(&array(vec![PropValue::Int(2), PropValue::Int(1)]), &[], &[])
    );
    let entries = vec![
        (PropValue::Int(1), PropValue::Int(2)),
        (PropValue::Int(3), PropValue::Int(4)),
    ];
    assert_eq!(
        prop_value_short(&map(entries.clone()), &[], &[]),
        prop_value_short(&map(entries.into_iter().rev().collect()), &[], &[])
    );
    assert_ne!(
        prop_value_short(&array(vec![]), &[], &[]),
        prop_value_short(
            &PropValue::Array {
                inner_type: "FloatProperty".into(),
                items: vec![]
            },
            &[],
            &[]
        )
    );
}

#[test]
fn object_defaults_distinguish_identically_named_imports_in_different_packages() {
    let imports: Vec<_> = [
        ("/Game/First", 0),
        ("/Game/Second", 0),
        ("SharedName", -1),
        ("SharedName", -2),
    ]
    .into_iter()
    .map(|(name, outer_index)| ImportEntry {
        class_package: String::new(),
        class_name: String::new(),
        object_name: name.into(),
        outer_index,
    })
    .collect();
    let first = prop_value_short(&PropValue::Object(-3), &imports, &[]);
    let second = prop_value_short(&PropValue::Object(-4), &imports, &[]);
    assert_eq!(first, "/Game/First.SharedName");
    assert_eq!(second, "/Game/Second.SharedName");
}

#[test]
fn property_enums_retain_type_identity_without_repeating_qualified_names() {
    let first = PropValue::Enum {
        enum_name: "FirstEnum".into(),
        value: "FirstEnum::Shared".into(),
    };
    let second = PropValue::Enum {
        enum_name: "SecondEnum".into(),
        value: "Shared".into(),
    };
    assert_eq!(prop_value_short(&first, &[], &[]), "FirstEnum::Shared");
    assert_eq!(prop_value_short(&second, &[], &[]), "SecondEnum::Shared");
}

#[test]
fn opaque_payload_changes_are_visible_in_cli_diff_and_every_output_mode() {
    let payload = |last: i32| {
        [0i32, 1, 7, 99, 99, 99, last]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect::<Vec<_>>()
    };
    let directory = tempfile::tempdir().unwrap();
    let mut hashes = Vec::new();
    let mut paths = Vec::new();
    for (name, last) in [("before", 99), ("after", 100)] {
        let bytes = replace_default_payload(
            "MapProperty",
            &["IntProperty", "StructProperty"],
            &payload(last),
        );
        let mut parsed = parse_asset(&bytes, false).unwrap();
        let (_, properties) = parsed
            .exports
            .iter_mut()
            .find(|(header, _)| header.object_name.starts_with("Default__"))
            .unwrap();
        let PropValue::Unknown {
            size,
            payload_sha256,
            ..
        } = &properties[0].value
        else {
            panic!("expected opaque native struct map");
        };
        assert_eq!(*size, payload(last).len() as i32);
        let hash = payload_sha256.clone();
        properties[0].value = PropValue::Struct {
            struct_type: "Container".into(),
            fields: vec![Property {
                name: "Payload".into(),
                value: properties[0].value.clone(),
            }],
        };
        let summary = emit_summary_with_asset(&decode_asset(&parsed), &parsed);
        assert!(summary.contains(&hash));
        assert!(unreal_bp_inspect::output_text::format_text(&parsed, &[]).contains(&hash));
        assert!(unreal_bp_inspect::output_json::to_json(&parsed, &[])
            .to_string()
            .contains(&hash));
        let path = directory.path().join(format!("{name}.uasset"));
        std::fs::write(&path, bytes).unwrap();
        for mode in [None, Some("--dump"), Some("--json")] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_bp-inspect"));
            command.arg(&path);
            if let Some(mode) = mode {
                command.arg(mode);
            }
            let output = command.output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains(&hash), "{mode:?}: {text}");
            if mode == Some("--json") {
                assert!(text.contains("payload_sha256"));
            }
        }
        hashes.push(hash);
        paths.push(path);
    }
    assert_ne!(hashes[0], hashes[1]);
    let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg("--diff")
        .args(&paths)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stderr.is_empty());
    let diff = String::from_utf8(output.stdout).unwrap();
    assert!(hashes.iter().all(|hash| diff.contains(hash)), "{diff}");
    let identical = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg("--diff")
        .arg(&paths[0])
        .arg(&paths[0])
        .output()
        .unwrap();
    assert!(identical.status.success());
    assert!(identical.stdout.is_empty());
}

#[test]
fn cli_diff_detects_equal_size_opaque_payload_changes_inside_a_tagged_struct() {
    let directory = tempfile::tempdir().unwrap();
    let mut paths = Vec::new();
    let mut hashes = Vec::new();
    for last in [99i32, 100] {
        let payload: Vec<u8> = [0i32, 1, 7, 99, 99, 99, last]
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect();
        let map_file =
            replace_default_payload("MapProperty", &["IntProperty", "StructProperty"], &payload);
        let parsed = parse_asset(&map_file, false).unwrap();
        let (header, properties) = parsed
            .exports
            .iter()
            .find(|(header, _)| header.object_name.starts_with("Default__"))
            .unwrap();
        let PropValue::Unknown { payload_sha256, .. } = &properties[0].value else {
            unreachable!()
        };
        hashes.push(payload_sha256.clone());
        // UE4 tag, two map-type names, GUID flag, payload and None terminator.
        let stream_length = 24 + 16 + 1 + payload.len() + 8;
        let start = header.serial_offset as usize;
        let nested_file = replace_default_payload(
            "StructProperty",
            &["ActorTickFunction"],
            &map_file[start..start + stream_length],
        );
        let nested = parse_asset(&nested_file, false).unwrap();
        assert!(nested.diagnostics.is_empty());
        let path = directory.path().join(format!("nested-{last}.uasset"));
        std::fs::write(&path, nested_file).unwrap();
        paths.push(path);
    }
    let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg("--diff")
        .args(&paths)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("ActorTickFunction"));
    assert!(hashes.iter().all(|hash| text.contains(hash)), "{text}");
}
