mod common;

use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::format_summary;
use unreal_bp_inspect::parser::parse_asset;

#[test]
fn vrhand_parses_without_error() {
    if !common::fixture_exists("VRHand_BP.uasset") {
        eprintln!("Skipping: VRHand_BP.uasset not found");
        return;
    }
    let data = common::load_fixture("VRHand_BP.uasset");
    let asset = parse_asset(&data, false).expect("parse should succeed");
    assert!(!asset.imports.is_empty());
    assert!(!asset.exports.is_empty());
}

#[test]
fn vrhand_json_valid() {
    if !common::fixture_exists("VRHand_BP.uasset") {
        eprintln!("Skipping: VRHand_BP.uasset not found");
        return;
    }
    let data = common::load_fixture("VRHand_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let val = to_json(&asset, &[]);
    let s = serde_json::to_string_pretty(&val).unwrap();
    let _: serde_json::Value = serde_json::from_str(&s).expect("JSON should round-trip");
}

#[test]
fn vrhand_summary_nonempty() {
    if !common::fixture_exists("VRHand_BP.uasset") {
        eprintln!("Skipping: VRHand_BP.uasset not found");
        return;
    }
    let data = common::load_fixture("VRHand_BP.uasset");
    let asset = parse_asset(&data, false).unwrap();
    let output = format_summary(&asset, &[]);
    assert!(output.contains("VRHand_BP"));
}
