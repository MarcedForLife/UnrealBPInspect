mod common;

use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::format_summary;
use unreal_bp_inspect::output_text::format_text;
use unreal_bp_inspect::parser::parse_asset;

#[test]
fn helm_parses_without_error() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).expect("parse should succeed");
    assert!(!asset.imports.is_empty());
    assert!(!asset.exports.is_empty());
}

#[test]
fn helm_structural_checks() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let has_blueprint = asset
        .exports
        .iter()
        .any(|(h, _)| h.object_name == "Helm_BP");
    assert!(has_blueprint, "Should have Helm_BP export");
}

#[test]
fn helm_summary_snapshot() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let output = format_summary(&asset, &[]);
    common::assert_snapshot("helm_summary", &output);
}

#[test]
fn helm_text_snapshot() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let output = format_text(&asset, &[]);
    common::assert_snapshot("helm_text", &output);
}

#[test]
fn helm_json_valid() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let val = to_json(&asset, &[]);
    let s = serde_json::to_string_pretty(&val).unwrap();
    let _: serde_json::Value = serde_json::from_str(&s).expect("JSON should round-trip");
}

#[test]
fn helm_json_snapshot() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let val = to_json(&asset, &[]);
    let output = serde_json::to_string_pretty(&val).unwrap();
    // JSON adds a trailing newline in the snapshot from the CLI
    common::assert_snapshot("helm_json", &format!("{}\n", output));
}

#[test]
fn helm_filter_works() {
    let data = common::load_fixture("Helm_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let full = format_summary(&asset, &[]);
    let filtered = format_summary(&asset, &["getsteeringangle".to_string()]);
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
