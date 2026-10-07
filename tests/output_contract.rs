mod common;

use std::process::Command;
use unreal_bp_inspect::bytecode::asset::Function;
use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::bytecode::emit::emit_summary_with_asset;
use unreal_bp_inspect::bytecode::expr::Expr;
use unreal_bp_inspect::bytecode::stmt::Stmt;
use unreal_bp_inspect::output_summary::filter_summary;
use unreal_bp_inspect::parser::parse_asset;

#[test]
fn sequence_pin_identity_agrees_in_summary_dump_and_json() {
    let fixture = common::samples_dir().join("ue_4.27/BP_DecoderTest.uasset");
    for mode in [None, Some("--dump"), Some("--json")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bp-inspect"));
        command.arg(&fixture).args(["--filter", "Seq_WithEmptyPin"]);
        if let Some(mode) = mode {
            command.arg(mode);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{:?}: {}",
            mode,
            String::from_utf8_lossy(&output.stderr)
        );
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("Sequence [2] (empty):"), "{mode:?}: {text}");
        assert!(text.contains("Sequence [3]:"), "{mode:?}: {text}");
        assert!(!text.contains("Sequence [2]:"), "{mode:?}: {text}");
    }
}

#[test]
fn filters_keep_a_whole_function_even_when_literal_text_contains_section_headings() {
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let parsed = parse_asset(&bytes, false).unwrap();
    let mut decoded = decode_asset(&parsed);
    decoded.events.clear();
    decoded.functions = vec![
        Function {
            name: "FilterProbe".into(),
            export_index: None,
            body: vec![Stmt::Call {
                func: Expr::Var("PrintString".into()),
                args: vec![Expr::Literal("\"first\n\nFunctions:\nneedle\"".into())],
                offset: 0,
            }],
        },
        Function {
            name: "OtherProbe".into(),
            export_index: None,
            body: vec![],
        },
    ];
    let filtered = filter_summary(&decoded, &parsed, &["NEEDLE".into()]);
    assert!(filtered.contains("FilterProbe()"), "{filtered}");
    assert!(filtered.contains("PrintString("), "{filtered}");
    assert!(
        filtered.contains("first\n\nFunctions:\nneedle"),
        "{filtered}"
    );
    assert!(!filtered.contains("OtherProbe()"), "{filtered}");
    assert_eq!(
        filter_summary(&decoded, &parsed, &[]),
        emit_summary_with_asset(&decoded, &parsed)
    );
}

#[test]
fn filters_match_bodies_and_keep_related_call_graph_edges() {
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let parsed = parse_asset(&bytes, false).unwrap();
    let decoded = decode_asset(&parsed);
    let filtered = filter_summary(&decoded, &parsed, &["Attempt(".into()]);
    assert!(filtered.contains("OnLeftAxis("), "{filtered}");
    assert!(filtered.contains("OnRightAxis("), "{filtered}");
    assert!(
        filtered.contains("OnLeftAxis → Attempt, Release"),
        "{filtered}"
    );
    assert!(!filtered.contains("Seq_WithEmptyPin()"), "{filtered}");
    let no_matches = filter_summary(&decoded, &parsed, &["no_such_name_7824".into()]);
    assert!(no_matches.starts_with("Blueprint: BP_DecoderTest"));
    assert!(!no_matches.contains("Functions:"));
    assert!(!no_matches.contains("Call graph:"));
}

#[test]
fn diff_detects_float_changes_smaller_than_four_decimal_places() {
    let original = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let parsed = parse_asset(&original, false).unwrap();
    let (export_index, (header, _)) = parsed
        .exports
        .iter()
        .enumerate()
        .find(|(index, (header, _))| {
            header.object_name == "Seq_WithEmptyPin"
                && parsed.bytecode_by_export.contains_key(&(index + 1))
        })
        .unwrap();
    let bytecode = &parsed.bytecode_by_export[&(export_index + 1)].0;
    let export_start = header.serial_offset as usize;
    let export_end = export_start + header.serial_size as usize;
    let bytecode_start = export_start
        + original[export_start..export_end]
            .windows(bytecode.len())
            .position(|window| window == bytecode)
            .unwrap();
    let float_constant = [0x1e, 0x00, 0x00, 0x00, 0x40];
    let operand = bytecode
        .windows(float_constant.len())
        .position(|window| window == float_constant)
        .unwrap()
        + 1;
    let mut changed = original.clone();
    changed[bytecode_start + operand..bytecode_start + operand + 4]
        .copy_from_slice(&2.00001_f32.to_le_bytes());
    let directory = tempfile::tempdir().unwrap();
    let before = directory.path().join("before.uasset");
    let after = directory.path().join("after.uasset");
    std::fs::write(&before, original).unwrap();
    std::fs::write(&after, changed).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .arg("--diff")
        .arg(before)
        .arg(after)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("2.00001"), "{text}");
    assert!(output.stderr.is_empty());
}

#[test]
fn component_property_match_retains_its_component_item() {
    use unreal_bp_inspect::types::{PropValue, Property};
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let decoded = decode_asset(&parsed);
    let (header, properties) = parsed
        .exports
        .iter_mut()
        .find(|(header, _)| header.object_name.ends_with("_GEN_VARIABLE"))
        .unwrap();
    let component = header
        .object_name
        .trim_end_matches("_GEN_VARIABLE")
        .to_string();
    properties.push(Property {
        name: "ReviewProperty".into(),
        value: PropValue::Str("componentneedle".into()),
    });
    let filtered = filter_summary(&decoded, &parsed, &["componentneedle".into()]);
    assert!(filtered.contains("Components:"), "{filtered}");
    assert!(filtered.contains(&component), "{filtered}");
    assert!(filtered.contains("ReviewProperty:"), "{filtered}");
    assert!(!filtered.contains("Functions:"), "{filtered}");
}

#[test]
fn multiline_default_match_retains_its_name_and_value() {
    use unreal_bp_inspect::types::{PropValue, Property};
    let bytes = common::load_fixture("ue_4.27/BP_DecoderTest.uasset");
    let mut parsed = parse_asset(&bytes, false).unwrap();
    let decoded = decode_asset(&parsed);
    for (_, properties) in &mut parsed.exports {
        properties.retain(|property| property.name != "Members");
    }
    let (_, properties) = parsed
        .exports
        .iter_mut()
        .find(|(header, _)| header.object_name.starts_with("Default__"))
        .unwrap();
    properties.push(Property {
        name: "ReviewDefault".into(),
        value: PropValue::Str("first\n\nFunctions:\ndefaultneedle".into()),
    });
    let filtered = filter_summary(&decoded, &parsed, &["defaultneedle".into()]);
    assert!(filtered.contains("Default values:"), "{filtered}");
    assert!(filtered.contains("ReviewDefault ="), "{filtered}");
    assert!(
        filtered.contains("first\\n\\nFunctions:\\ndefaultneedle"),
        "{filtered}"
    );
    assert!(!filtered.contains("Seq_WithEmptyPin()"), "{filtered}");
}
