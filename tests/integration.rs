mod common;

use unreal_bp_inspect::output_diff::format_diff;
use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::{filter_summary, format_summary};
use unreal_bp_inspect::output_text::format_text;
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
fn helm_summary_snapshot() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let output = format_summary(&asset);
    common::assert_snapshot("helm_summary", &output);
}

#[test]
fn helm_text_snapshot() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let output = format_text(&asset, &[]);
    common::assert_snapshot("helm_text", &output);
}

#[test]
fn helm_json_valid() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let val = to_json(&asset, &[]);
    let s = serde_json::to_string_pretty(&val).unwrap();
    let _: serde_json::Value = serde_json::from_str(&s).expect("JSON should round-trip");
}

#[test]
fn helm_json_snapshot() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let val = to_json(&asset, &[]);
    let output = serde_json::to_string_pretty(&val).unwrap();
    // JSON adds a trailing newline in the snapshot from the CLI
    common::assert_snapshot("helm_json", &format!("{}\n", output));
}

#[test]
fn helm_filter_works() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let full = format_summary(&asset);
    let filtered = filter_summary(&full, &["getsteeringangle".to_string()]);
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

/// Run all three output modes multiple times and verify identical output.
/// Each call creates fresh HashMaps with different random seeds, so this
/// catches any HashMap iteration order nondeterminism.
#[test]
fn output_determinism() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let baseline_summary = format_summary(&asset);
    let baseline_text = format_text(&asset, &[]);
    let baseline_json = serde_json::to_string_pretty(&to_json(&asset, &[])).unwrap();
    for _ in 0..4 {
        assert_eq!(
            format_summary(&asset),
            baseline_summary,
            "summary output is nondeterministic"
        );
        assert_eq!(
            format_text(&asset, &[]),
            baseline_text,
            "text output is nondeterministic"
        );
        assert_eq!(
            serde_json::to_string_pretty(&to_json(&asset, &[])).unwrap(),
            baseline_json,
            "json output is nondeterministic"
        );
    }
}

#[test]
fn diff_identical_files_produces_no_output() {
    let data = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let (output, has_changes) = format_diff(&data, &data, "a.uasset", "b.uasset", &[], 3).unwrap();
    assert!(!has_changes);
    assert!(output.is_empty());
}

#[test]
fn diff_different_versions_produces_unified_diff() {
    let ue4 = common::load_fixture("ue_4.27/Helm_BP.uasset");
    let ue5_path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("samples/ue_5.5/Helm_BP.uasset");
    if !ue5_path.exists() {
        // Skip if UE5.5 fixture not available
        return;
    }
    let ue5 = std::fs::read(ue5_path).unwrap();
    let (output, has_changes) =
        format_diff(&ue4, &ue5, "ue4.uasset", "ue5.uasset", &[], 3).unwrap();
    // Same blueprint saved in two engine versions — may or may not have textual diffs,
    // but the diff function itself should succeed without error.
    assert!(output.is_empty() != has_changes);
}
