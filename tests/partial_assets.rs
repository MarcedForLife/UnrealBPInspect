mod common;

use std::process::Command;
use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::parser::parse_asset;

#[test]
fn complete_fixtures_have_no_reported_failures() {
    for fixture in [
        "ue_4.27/Helm_BP.uasset",
        "ue_4.27/BP_DecoderTest.uasset",
        "ue_5.3/Helm_BP.uasset",
        "ue_5.5/Helm_BP.uasset",
    ] {
        let bytes = common::load_fixture(fixture);
        let parsed = parse_asset(&bytes, false).unwrap();
        assert!(
            parsed.diagnostics.is_empty(),
            "{fixture}: {:?}",
            parsed.diagnostics
        );
        assert_eq!(
            parsed.version.file_ver_ue5 == 0,
            fixture.starts_with("ue_4")
        );
        let decoded = decode_asset(&parsed);
        assert!(
            decoded.diagnostics.is_empty(),
            "{fixture}: {:?}",
            decoded.diagnostics
        );
        assert!(!decoded.functions.is_empty());
    }
}

#[test]
fn truncated_exports_retain_results_and_diagnostics_through_decode() {
    let mut bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    bytes.truncate(bytes.len() / 2);
    let parsed = parse_asset(&bytes, false).unwrap();
    assert!(!parsed.diagnostics.is_empty());
    assert!(parsed
        .exports
        .iter()
        .any(|(_, properties)| !properties.is_empty()));
    assert!(parsed
        .diagnostics
        .iter()
        .all(|diagnostic| diagnostic.export_index.is_some()));
    let decoded = decode_asset(&parsed);
    for diagnostic in &parsed.diagnostics {
        assert!(decoded.diagnostics.contains(diagnostic));
    }
}

#[test]
fn malformed_property_tag_is_reported_without_losing_other_exports() {
    let mut bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let original = parse_asset(&bytes, false).unwrap();
    let (index, (header, _)) = original
        .exports
        .iter()
        .enumerate()
        .find(|(_, (_, properties))| !properties.is_empty())
        .unwrap();
    let type_offset = header.serial_offset as usize + 8;
    bytes[type_offset..type_offset + 4].copy_from_slice(&i32::MAX.to_le_bytes());
    let parsed = parse_asset(&bytes, false).unwrap();
    assert!(parsed
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.export_index == Some(index + 1)));
    assert!(parsed
        .exports
        .iter()
        .enumerate()
        .any(|(other, (_, properties))| other != index && !properties.is_empty()));
}

#[test]
fn missing_captured_function_bytecode_is_reported() {
    let bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let export_index = *parsed
        .bytecode_by_export
        .keys()
        .find(|index| {
            parsed
                .function_signatures
                .contains_key(&parsed.exports[**index - 1].0.object_name)
        })
        .unwrap();
    parsed.bytecode_by_export.remove(&export_index);
    let decoded = decode_asset(&parsed);
    assert!(decoded
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.export_index == Some(export_index)
            && diagnostic.reason.contains("no captured bytecode")));
}

#[test]
fn cli_preserves_partial_outputs_and_uses_failure_exit_for_diff_and_batch() {
    let directory = tempfile::tempdir().unwrap();
    let full_path = directory.path().join("full.uasset");
    let partial_path = directory.path().join("partial.uasset");
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    std::fs::write(&full_path, &bytes).unwrap();
    std::fs::write(&partial_path, &bytes[..bytes.len() / 2]).unwrap();
    for mode in [None, Some("--dump"), Some("--json")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bp-inspect"));
        command.arg(&partial_path);
        if let Some(mode) = mode {
            command.arg(mode);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(2), "mode {mode:?}");
        assert!(!output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        if mode == Some("--json") {
            let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert!(!json["diagnostics"].as_array().unwrap().is_empty());
        }
    }
    for before in [&full_path, &partial_path] {
        let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
            .args(["--diff", "--filter", "cannot-match-anything"])
            .arg(before)
            .arg(&partial_path)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(!output.stderr.is_empty());
    }
    let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg("--json")
        .arg(&full_path)
        .arg(&partial_path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json.as_array().unwrap().len(), 2);
    assert!(json
        .as_array()
        .unwrap()
        .iter()
        .any(|asset| asset["diagnostics"].is_array()));
}

#[test]
fn explicitly_empty_function_bytecode_is_not_a_capture_failure() {
    let bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let export_index = *parsed
        .bytecode_by_export
        .keys()
        .find(|index| {
            parsed
                .function_signatures
                .contains_key(&parsed.exports[**index - 1].0.object_name)
        })
        .unwrap();
    parsed
        .bytecode_by_export
        .insert(export_index, (Vec::new(), 0));
    let decoded = decode_asset(&parsed);
    assert!(decoded.diagnostics.is_empty(), "{:?}", decoded.diagnostics);
}

#[test]
fn overflowing_export_ranges_are_diagnostics_instead_of_panics() {
    let mut bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let original = parse_asset(&bytes, false).unwrap();
    let header = &original.exports[0].0;
    let serialized_range: Vec<u8> = header
        .serial_size
        .to_le_bytes()
        .into_iter()
        .chain(header.serial_offset.to_le_bytes())
        .collect();
    let range_offset = bytes
        .windows(serialized_range.len())
        .position(|window| window == serialized_range)
        .unwrap();
    bytes[range_offset + 8..range_offset + 16].copy_from_slice(&i64::MAX.to_le_bytes());
    let parsed = parse_asset(&bytes, false).unwrap();
    assert!(parsed
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.export_index == Some(1)
            && diagnostic.reason.contains("invalid serialized range")));
}

#[test]
fn corrupt_bytecode_address_walk_is_a_structured_failure() {
    let bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let export_index = *parsed
        .bytecode_by_export
        .iter()
        .find(|(index, (bytes, _))| {
            !bytes.is_empty() && parsed.exports[**index - 1].0.object_name == "GetSteeringAngle"
        })
        .unwrap()
        .0;
    for opcode in [
        unreal_bp_inspect::bytecode::opcodes::EX_NOTHING_INT32,
        unreal_bp_inspect::bytecode::opcodes::EX_INT_CONST,
        unreal_bp_inspect::bytecode::opcodes::EX_FLOAT_CONST,
    ] {
        parsed.bytecode_by_export.get_mut(&export_index).unwrap().0 = vec![opcode];
        let decoded = decode_asset(&parsed);
        assert!(
            decoded
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.export_index == Some(export_index)
                    && diagnostic
                        .reason
                        .contains("bytecode address translation failed")
                    && diagnostic.reason.contains("truncated bytecode")),
            "{:?}",
            decoded.diagnostics
        );
    }
}

#[test]
fn string_terminators_are_required_at_the_bytecode_boundary() {
    use unreal_bp_inspect::bytecode::opcodes::{
        EX_RETURN, EX_STRING_CONST, EX_TEXT_CONST, EX_UNICODE_STRING_CONST,
    };
    use unreal_bp_inspect::bytecode::stmt::Stmt;
    let bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let export_index = parsed
        .exports
        .iter()
        .enumerate()
        .find(|(index, (header, _))| {
            header.object_name == "GetSteeringAngle"
                && parsed.bytecode_by_export.contains_key(&(index + 1))
        })
        .unwrap()
        .0
        + 1;
    let cases = [
        (vec![EX_RETURN, EX_STRING_CONST, 0], true),
        (vec![EX_RETURN, EX_STRING_CONST, b'a', 0], true),
        (vec![EX_RETURN, EX_UNICODE_STRING_CONST, 0, 0], true),
        (
            vec![EX_RETURN, EX_UNICODE_STRING_CONST, b'a', 0, 0, 0],
            true,
        ),
        (vec![EX_RETURN, EX_STRING_CONST], false),
        (vec![EX_RETURN, EX_STRING_CONST, b'a', b'b'], false),
        (vec![EX_RETURN, EX_UNICODE_STRING_CONST], false),
        (vec![EX_RETURN, EX_UNICODE_STRING_CONST, b'a'], false),
        (vec![EX_RETURN, EX_UNICODE_STRING_CONST, b'a', 0], false),
        (vec![EX_RETURN, EX_UNICODE_STRING_CONST, b'a', 0, 0], false),
        (
            vec![EX_RETURN, EX_TEXT_CONST, 2, EX_STRING_CONST, b'a'],
            false,
        ),
    ];
    for (bytecode, valid) in cases {
        parsed.bytecode_by_export.get_mut(&export_index).unwrap().0 = bytecode.clone();
        let decoded = decode_asset(&parsed);
        assert_eq!(
            decoded.diagnostics.is_empty(),
            valid,
            "{bytecode:?}: {:?}",
            decoded.diagnostics
        );
        let function = decoded
            .functions
            .iter()
            .find(|function| function.export_index == Some(export_index))
            .unwrap();
        if valid {
            assert!(
                matches!(
                    function.body.as_slice(),
                    [Stmt::Return { value: Some(_), .. }]
                ),
                "{bytecode:?}"
            );
        } else {
            assert!(
                matches!(function.body.as_slice(), [Stmt::Unknown { .. }]),
                "{bytecode:?}"
            );
            assert!(decoded
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.reason.contains("truncated bytecode")));
        }
    }
}

#[test]
fn cli_reports_unterminated_string_bytecode_without_discarding_the_asset() {
    use unreal_bp_inspect::bytecode::opcodes::{EX_RETURN, EX_STRING_CONST};
    let mut bytes = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let parsed = parse_asset(&bytes, false).unwrap();
    let (index, (header, _)) = parsed
        .exports
        .iter()
        .enumerate()
        .find(|(index, (header, _))| {
            header.object_name == "GetSteeringAngle"
                && parsed.bytecode_by_export.contains_key(&(index + 1))
        })
        .unwrap();
    let original = &parsed.bytecode_by_export[&(index + 1)].0;
    let export_start = header.serial_offset as usize;
    let export_end = export_start + header.serial_size as usize;
    let script_start = export_start
        + bytes[export_start..export_end]
            .windows(original.len())
            .position(|window| window == original)
            .unwrap();
    let flags: Vec<u8> =
        bytes[script_start + original.len()..script_start + original.len() + 4].to_vec();
    let truncated = [EX_RETURN, EX_STRING_CONST, b'a', b'b', b'c'];
    bytes[script_start..script_start + truncated.len()].copy_from_slice(&truncated);
    bytes[script_start - 8..script_start - 4]
        .copy_from_slice(&(truncated.len() as i32).to_le_bytes());
    bytes[script_start - 4..script_start].copy_from_slice(&(truncated.len() as i32).to_le_bytes());
    bytes[script_start + truncated.len()..script_start + truncated.len() + 4]
        .copy_from_slice(&flags);
    let directory = tempfile::tempdir().unwrap();
    let fixture = directory.path().join("unterminated.uasset");
    std::fs::write(&fixture, bytes).unwrap();
    for mode in [None, Some("--dump"), Some("--json")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bp-inspect"));
        command.arg(&fixture);
        if let Some(mode) = mode {
            command.arg(mode);
        }
        let result = command.output().unwrap();
        assert_eq!(
            result.status.code(),
            Some(2),
            "{mode:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains("truncated bytecode"), "{stderr}");
        assert!(!stderr.contains("panicked"), "{stderr}");
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(output.contains("GetSteeringAngle"), "{mode:?}");
        assert!(output.contains("UNKNOWN"), "{mode:?}");
        if mode == Some("--json") {
            let json: serde_json::Value = serde_json::from_str(&output).unwrap();
            assert!(!json["diagnostics"].as_array().unwrap().is_empty());
        }
    }
}
