mod common;

use unreal_bp_inspect::output_diff::diff_summary_texts;
use unreal_bp_inspect::output_summary::filter_summary;
use unreal_bp_inspect::parser::parse_asset;

#[test]
fn helm_parses_without_error() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).expect("parse should succeed");
    assert!(!asset.imports.is_empty());
    assert!(!asset.exports.is_empty());
}

#[test]
fn helm_structural_checks() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let has_blueprint = asset
        .exports
        .iter()
        .any(|(h, _)| h.object_name == "Helm_BP");
    assert!(has_blueprint, "Should have Helm_BP export");
}

#[test]
fn function_signatures_populated_for_function_exports() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    assert!(
        !asset.function_signatures.is_empty(),
        "Helm_BP should expose at least one function signature"
    );
    for sig in asset.function_signatures.values() {
        for param in &sig.params {
            // CPF_PARM=0x80; every recorded entry must carry it.
            assert!(
                param.flags & 0x80 != 0,
                "param {} for a recorded signature missing CPF_PARM (flags=0x{:x})",
                param.name,
                param.flags
            );
        }
    }
}

#[test]
fn bytecode_by_export_captures_function_bytes() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    use unreal_bp_inspect::resolve::resolve_index;
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let mut function_indices: Vec<usize> = Vec::new();
    let mut non_function_indices: Vec<usize> = Vec::new();
    for (idx, (hdr, _)) in asset.exports.iter().enumerate() {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if class.ends_with(".Function") {
            function_indices.push(idx + 1);
        } else {
            non_function_indices.push(idx + 1);
        }
    }
    assert!(
        !function_indices.is_empty(),
        "Helm_BP should expose at least one function export"
    );

    let captured_function = function_indices
        .iter()
        .any(|index| asset.bytecode_by_export.contains_key(index));
    assert!(
        captured_function,
        "expected bytecode_by_export to contain bytes for at least one function export"
    );
    for index in &function_indices {
        if let Some((bytes, mem_size)) = asset.bytecode_by_export.get(index) {
            assert!(
                !bytes.is_empty(),
                "captured bytecode for export {index} is empty"
            );
            assert!(
                *mem_size > 0,
                "captured mem_size for export {index} should be positive"
            );
        }
    }

    for index in &non_function_indices {
        assert!(
            !asset.bytecode_by_export.contains_key(index),
            "bytecode_by_export should not contain non-function export {index}"
        );
    }
}

#[test]
fn helm_text_snapshot() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    common::assert_snapshot("helm_text", &common::decoded_text(&data));
}

#[test]
fn helm_json_valid() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let _: serde_json::Value =
        serde_json::from_str(&common::decoded_json(&data)).expect("JSON should round-trip");
}

#[test]
fn helm_json_snapshot() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    // The CLI appends a trailing newline to the JSON output file.
    common::assert_snapshot("helm_json", &format!("{}\n", common::decoded_json(&data)));
}

#[test]
fn helm_filter_works() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let full = common::decoded_summary(&data);
    let asset = parse_asset(&data, false).unwrap();
    let decoded = unreal_bp_inspect::bytecode::decode::decode_asset(&asset);
    let filtered = filter_summary(&decoded, &asset, &["getsteeringangle".to_string()]);
    assert!(!filtered.is_empty());
    assert!(
        filtered.len() < full.len(),
        "Filtered output should be shorter"
    );
    assert!(
        filtered.contains("GetSteeringAngle"),
        "Filtered output should contain GetSteeringAngle"
    );
    assert!(
        !filtered.contains("UserConstructionScript"),
        "Filtered output should not contain other functions"
    );
}

#[test]
fn empty_input_returns_error() {
    assert!(parse_asset(&[], false).is_err());
}

#[test]
fn truncated_input_returns_error() {
    assert!(parse_asset(&[0xC1, 0x83, 0x2A, 0x9E], false).is_err());
}

#[test]
fn garbage_input_returns_error() {
    assert!(parse_asset(b"not a uasset file", false).is_err());
}

/// Run all three output modes several times and require identical output.
/// Each helper call re-parses, so every run gets fresh HashMaps with new
/// random seeds, catching any iteration-order nondeterminism.
#[test]
fn output_determinism() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let baseline_summary = common::decoded_summary(&data);
    let baseline_text = common::decoded_text(&data);
    let baseline_json = common::decoded_json(&data);
    for _ in 0..4 {
        assert_eq!(
            common::decoded_summary(&data),
            baseline_summary,
            "summary output is nondeterministic"
        );
        assert_eq!(
            common::decoded_text(&data),
            baseline_text,
            "text output is nondeterministic"
        );
        assert_eq!(
            common::decoded_json(&data),
            baseline_json,
            "json output is nondeterministic"
        );
    }
}

/// Mirror the CLI `--diff` path: emit each side's v2 summary, filter, then
/// unified-diff the two texts.
fn v2_diff(before: &[u8], after: &[u8], label_a: &str, label_b: &str) -> (String, bool) {
    let before_text = common::decoded_summary(before);
    let after_text = common::decoded_summary(after);
    diff_summary_texts(&before_text, &after_text, label_a, label_b, 3)
}

#[test]
fn diff_identical_files_produces_no_output() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let (output, has_changes) = v2_diff(&data, &data, "a.uasset", "b.uasset");
    assert!(!has_changes);
    assert!(output.is_empty());
}

#[test]
fn diff_different_versions_produces_unified_diff() {
    let ue4 = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let ue5_path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("samples/ue_5.5/Helm_BP.uasset");
    if !ue5_path.exists() {
        return; // UE5.5 fixture not available locally.
    }
    let ue5 = std::fs::read(ue5_path).unwrap();
    let (output, has_changes) = v2_diff(&ue4, &ue5, "ue4.uasset", "ue5.uasset");
    // Same blueprint in two engine versions: the diff may or may not be empty,
    // but the two return values must agree.
    assert!(output.is_empty() != has_changes);
}

#[test]
fn cli_diff_preserves_argument_order() {
    let first = common::samples_dir().join("ue_4.27/BP_DecoderTest.uasset");
    let second = common::samples_dir().join("ue_4.27/Helm_BP.uasset");
    for (before, after) in [(&first, &second), (&second, &first)] {
        let result = std::process::Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
            .arg("--diff")
            .arg(before)
            .arg(after)
            .output()
            .expect("CLI should run");
        assert_eq!(result.status.code(), Some(1));
        assert!(result.stderr.is_empty());
        let (expected, has_changes) = v2_diff(
            &std::fs::read(before).unwrap(),
            &std::fs::read(after).unwrap(),
            &before.display().to_string(),
            &after.display().to_string(),
        );
        assert!(has_changes);
        assert!(
            String::from_utf8(result.stdout).unwrap() == expected,
            "CLI diff should compare {} before {}",
            before.display(),
            after.display()
        );
    }
}

#[test]
fn cli_diff_distinguishes_matches_from_errors() {
    let fixture = common::samples_dir().join("ue_4.27/Helm_BP.uasset");
    let missing = tempfile::tempdir().unwrap().path().join("missing.uasset");
    for (after, expected) in [(&fixture, 0), (&missing, 2)] {
        let result = std::process::Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
            .arg("--diff")
            .arg(&fixture)
            .arg(after)
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(expected));
        assert!(result.stdout.is_empty());
        assert_eq!(result.stderr.is_empty(), expected == 0);
    }
}

#[test]
fn cli_partial_batch_retains_results_and_reports_failure() {
    let fixture = common::samples_dir().join("ue_4.27/Helm_BP.uasset");
    let directory = tempfile::tempdir().unwrap();
    let invalid = directory.path().join("invalid.uasset");
    std::fs::write(&invalid, b"not an asset").unwrap();
    for mode in ["--json", "--dump"] {
        let result = std::process::Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
            .arg(mode)
            .arg(&fixture)
            .arg(&invalid)
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&result.stderr).contains("1 of 2 files failed"));
        assert!(!result.stdout.is_empty());
        if mode == "--json" {
            let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
            let results = output.as_array().unwrap();
            assert_eq!(results.len(), 1);
            assert_eq!(results[0]["file"], fixture.to_string_lossy().as_ref());
        }
    }
}

#[cfg(unix)]
#[test]
fn cli_directory_scan_does_not_follow_symlink_cycles() {
    let directory = tempfile::tempdir().unwrap();
    std::os::unix::fs::symlink(directory.path(), directory.path().join("cycle")).unwrap();
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg(directory.path())
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&result.stderr).contains("No .uasset files found"));
}
