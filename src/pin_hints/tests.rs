//! Unit tests for the pin-hints module. Shared fixtures live here;
//! individual test cases cover the public API and a handful of
//! module-internal helpers deliberately exposed with `pub(super)`.

use std::collections::{BTreeSet, HashMap};

use crate::types::{
    EdGraphPin, ExportHeader, ImportEntry, LinkedPin, NodePinData, ParsedAsset, PropValue,
    Property, PIN_DIRECTION_INPUT, PIN_DIRECTION_OUTPUT, PIN_TYPE_EXEC,
};

use super::bytecode_map::{
    condition_matches, parse_if_jump_cond, split_bytecode_line, ConditionIdentity,
};
use super::routing::exec_successors_for;
use super::{build_branch_hints, build_bytecode_branch_map, BranchHints, BranchInfo};

fn import(class_name: &str) -> ImportEntry {
    ImportEntry {
        class_package: "/Script/CoreUObject".into(),
        class_name: "Class".into(),
        object_name: class_name.into(),
        outer_index: 0,
    }
}

fn make_header(class_index: i32, object_name: &str) -> ExportHeader {
    ExportHeader {
        class_index,
        super_index: 0,
        outer_index: 0,
        object_name: object_name.into(),
        serial_offset: 0,
        serial_size: 0,
    }
}

/// Deterministic pin id derived from (owning node export, pin name).
/// Two test pins with the same (node, name) get the same id, so `LinkedPin`
/// entries can be constructed symbolically without threading raw guids.
fn make_pin_id(node: usize, name: &str) -> [u8; 16] {
    let mut id = [0u8; 16];
    let bytes = name.as_bytes();
    id[0] = node as u8;
    id[1] = (node >> 8) as u8;
    for (slot, byte) in id[2..].iter_mut().zip(bytes.iter()) {
        *slot = *byte;
    }
    id
}

fn exec_pin_on(owner: usize, name: &str, direction: u8, links: Vec<(usize, &str)>) -> EdGraphPin {
    EdGraphPin {
        name: name.into(),
        pin_type: PIN_TYPE_EXEC.into(),
        direction,
        pin_id: make_pin_id(owner, name),
        linked_to: links
            .into_iter()
            .map(|(node, pin_name)| LinkedPin {
                node,
                pin_id: make_pin_id(node, pin_name),
            })
            .collect(),
    }
}

/// Legacy helper (pre-pin-aware tests): creates a pin with deterministic
/// id and links to the target nodes' `execute` pin by convention.
fn exec_pin(name: &str, direction: u8, links: Vec<usize>) -> EdGraphPin {
    EdGraphPin {
        name: name.into(),
        pin_type: PIN_TYPE_EXEC.into(),
        direction,
        pin_id: make_pin_id(0, name),
        linked_to: links
            .into_iter()
            .map(|node| LinkedPin {
                node,
                pin_id: make_pin_id(node, "execute"),
            })
            .collect(),
    }
}

fn function_reference(member: &str) -> Property {
    Property {
        name: "FunctionReference".into(),
        value: PropValue::Struct {
            struct_type: "MemberReference".into(),
            fields: vec![Property {
                name: "MemberName".into(),
                value: PropValue::Name(member.into()),
            }],
        },
    }
}

/// Fixture: an input-axis event with one Branch; Then -> CallFoo, Else -> CallBar.
fn build_minimal_asset() -> ParsedAsset {
    let imports = vec![
        import("K2Node_InputAxisEvent"),
        import("K2Node_IfThenElse"),
        import("K2Node_CallFunction"),
    ];
    let exports = vec![
        (
            make_header(-1, "InpAxisEvt_TestAxis_Event"),
            vec![Property {
                name: "CustomFunctionName".into(),
                value: PropValue::Name("InpAxisEvt_TestAxis_Event".into()),
            }],
        ),
        (make_header(-2, "K2Node_IfThenElse_0"), vec![]),
        (
            make_header(-3, "K2Node_CallFunction_0"),
            vec![function_reference("CallFoo")],
        ),
        (
            make_header(-3, "K2Node_CallFunction_1"),
            vec![function_reference("CallBar")],
        ),
    ];

    let mut pin_data: HashMap<usize, NodePinData> = HashMap::new();
    pin_data.insert(
        1,
        NodePinData {
            pins: vec![exec_pin("then", PIN_DIRECTION_OUTPUT, vec![2])],
        },
    );
    pin_data.insert(
        2,
        NodePinData {
            pins: vec![
                exec_pin("execute", PIN_DIRECTION_INPUT, vec![1]),
                exec_pin("then", PIN_DIRECTION_OUTPUT, vec![3]),
                exec_pin("else", PIN_DIRECTION_OUTPUT, vec![4]),
            ],
        },
    );
    pin_data.insert(
        3,
        NodePinData {
            pins: vec![exec_pin("execute", PIN_DIRECTION_INPUT, vec![2])],
        },
    );
    pin_data.insert(
        4,
        NodePinData {
            pins: vec![exec_pin("execute", PIN_DIRECTION_INPUT, vec![2])],
        },
    );

    ParsedAsset {
        imports,
        exports,
        pin_data,
    }
}

#[test]
fn minimal_fixture_classifies_then_and_else() {
    let asset = build_minimal_asset();
    let hints = build_branch_hints(&asset);

    let infos = hints
        .by_function
        .get("InpAxisEvt_TestAxis_Event")
        .expect("entry key should be present");
    assert_eq!(infos.len(), 1);
    let info = &infos[0];
    assert_eq!(info.branch_export_idx, 2);
    assert!(info.then_callees.contains("CallFoo"));
    assert!(info.else_callees.contains("CallBar"));
    assert!(!info.then_callees.contains("CallBar"));
    assert!(!info.else_callees.contains("CallFoo"));
}

#[test]
fn build_branch_hints_is_deterministic() {
    let asset = build_minimal_asset();
    let first = format!("{:?}", build_branch_hints(&asset));
    let second = format!("{:?}", build_branch_hints(&asset));
    assert_eq!(first, second);
}

#[test]
fn empty_asset_produces_no_hints() {
    let asset = ParsedAsset {
        imports: Vec::new(),
        exports: Vec::new(),
        pin_data: HashMap::new(),
    };
    let hints = build_branch_hints(&asset);
    assert!(hints.by_function.is_empty());
}

#[test]
fn then_only_and_else_only_compute_set_differences() {
    let mut info = BranchInfo {
        branch_export_idx: 42,
        then_callees: BTreeSet::new(),
        else_callees: BTreeSet::new(),
    };
    info.then_callees.insert("AttemptGrip".into());
    info.then_callees.insert("Shared".into());
    info.else_callees.insert("ReleaseGrip".into());
    info.else_callees.insert("Shared".into());

    let then_only = info.then_only_callees();
    let else_only = info.else_only_callees();

    assert!(then_only.contains("AttemptGrip"));
    assert!(!then_only.contains("Shared"));
    assert!(!then_only.contains("ReleaseGrip"));
    assert!(else_only.contains("ReleaseGrip"));
    assert!(!else_only.contains("Shared"));
    assert!(!else_only.contains("AttemptGrip"));
}

#[test]
fn set_difference_helpers_handle_full_overlap() {
    let mut info = BranchInfo {
        branch_export_idx: 1,
        then_callees: BTreeSet::new(),
        else_callees: BTreeSet::new(),
    };
    info.then_callees.insert("Both".into());
    info.else_callees.insert("Both".into());
    assert!(info.then_only_callees().is_empty());
    assert!(info.else_only_callees().is_empty());
}

#[test]
fn bytecode_branch_map_is_empty_on_empty_hints() {
    let asset = ParsedAsset {
        imports: Vec::new(),
        exports: Vec::new(),
        pin_data: HashMap::new(),
    };
    let hints = BranchHints::default();
    let map = build_bytecode_branch_map(&asset, &hints);
    assert!(map.offset_to_branch.is_empty());
    assert!(map.unmatched_branches.is_empty());
}

#[test]
fn parse_if_jump_cond_extracts_condition() {
    assert_eq!(
        parse_if_jump_cond("if !($GreaterEqual_FloatFloat_ReturnValue_1) jump 0xcfc"),
        Some("$GreaterEqual_FloatFloat_ReturnValue_1")
    );
    assert_eq!(parse_if_jump_cond("nothing"), None);
    assert_eq!(parse_if_jump_cond("if !(x) jump"), None);
}

#[test]
fn split_bytecode_line_parses_offset_and_body() {
    let parsed = split_bytecode_line("0d56: if !(cond) jump 0xcfc");
    assert_eq!(parsed, Some((0x0d56, "if !(cond) jump 0xcfc")));
    assert_eq!(split_bytecode_line("short"), None);
    assert_eq!(split_bytecode_line("XXXX: body"), None);
}

#[test]
fn condition_matches_callfunction_with_suffix() {
    let id = ConditionIdentity::CallFunction {
        prefix: "GreaterEqual_FloatFloat".into(),
    };
    assert!(condition_matches(
        &id,
        "$GreaterEqual_FloatFloat_ReturnValue"
    ));
    assert!(condition_matches(
        &id,
        "$GreaterEqual_FloatFloat_ReturnValue_2"
    ));
    assert!(!condition_matches(&id, "$Other_ReturnValue"));
}

/// Build a three-node fixture rooted at `root_class` with exec-output
/// pins on the root linking into downstream `K2Node_CallFunction`s.
/// Returns `(asset, root_export)`.
fn build_routing_fixture(
    root_class: &str,
    pins: Vec<EdGraphPin>,
    callee_exports: &[(usize, &str, i32)],
) -> (ParsedAsset, usize) {
    let imports = vec![import(root_class), import("K2Node_CallFunction")];
    let root_class_idx = -1;
    let call_class_idx = -2;

    let mut exports: Vec<(ExportHeader, Vec<Property>)> = Vec::new();
    exports.push((make_header(root_class_idx, "Root"), Vec::new()));
    for (_idx, name, _) in callee_exports {
        exports.push((
            make_header(call_class_idx, name),
            vec![function_reference(name)],
        ));
    }

    let mut pin_data: HashMap<usize, NodePinData> = HashMap::new();
    pin_data.insert(1, NodePinData { pins });
    for (idx, _, _) in callee_exports {
        pin_data.insert(
            *idx,
            NodePinData {
                pins: vec![exec_pin_on(
                    *idx,
                    "execute",
                    PIN_DIRECTION_INPUT,
                    vec![(1, "n/a")],
                )],
            },
        );
    }

    (
        ParsedAsset {
            imports,
            exports,
            pin_data,
        },
        1,
    )
}

#[test]
fn sequence_fans_out_all_then_n() {
    let pins = vec![
        exec_pin_on(1, "execute", PIN_DIRECTION_INPUT, vec![]),
        exec_pin_on(1, "then_0", PIN_DIRECTION_OUTPUT, vec![(2, "execute")]),
        exec_pin_on(1, "then_1", PIN_DIRECTION_OUTPUT, vec![(3, "execute")]),
        exec_pin_on(1, "then_2", PIN_DIRECTION_OUTPUT, vec![(4, "execute")]),
    ];
    let (asset, root) = build_routing_fixture(
        "K2Node_ExecutionSequence",
        pins,
        &[(2, "A", 0), (3, "B", 0), (4, "C", 0)],
    );
    let succ = exec_successors_for(&asset, root, "K2Node_ExecutionSequence", "execute");
    let targets: BTreeSet<usize> = succ.iter().map(|(n, _)| *n).collect();
    assert_eq!(targets, BTreeSet::from([2usize, 3, 4]));
}

#[test]
fn doonce_reset_does_not_propagate_to_completed() {
    // Minimal DoOnce macro instance: Start -> Completed, Reset -> nothing.
    let mut imports = vec![
        import("K2Node_MacroInstance"),
        import("K2Node_CallFunction"),
        import("Function"),
    ];
    // Override the third import's object_name so resolve yields ".DoOnce".
    imports[2].object_name = "DoOnce".into();

    let macro_graph_ref_prop = Property {
        name: "MacroGraphReference".into(),
        value: PropValue::Struct {
            struct_type: "GraphReference".into(),
            fields: vec![Property {
                name: "MacroGraph".into(),
                value: PropValue::Object(-3),
            }],
        },
    };

    let exports = vec![
        (make_header(-1, "DoOnce_0"), vec![macro_graph_ref_prop]),
        (
            make_header(-2, "CompletedCallee"),
            vec![function_reference("CompletedCallee")],
        ),
    ];

    let mut pin_data: HashMap<usize, NodePinData> = HashMap::new();
    pin_data.insert(
        1,
        NodePinData {
            pins: vec![
                exec_pin_on(1, "Start", PIN_DIRECTION_INPUT, vec![]),
                exec_pin_on(1, "Reset", PIN_DIRECTION_INPUT, vec![]),
                exec_pin_on(1, "Completed", PIN_DIRECTION_OUTPUT, vec![(2, "execute")]),
            ],
        },
    );
    pin_data.insert(
        2,
        NodePinData {
            pins: vec![exec_pin_on(2, "execute", PIN_DIRECTION_INPUT, vec![])],
        },
    );

    let asset = ParsedAsset {
        imports,
        exports,
        pin_data,
    };

    let via_reset = exec_successors_for(&asset, 1, "K2Node_MacroInstance", "Reset");
    assert!(via_reset.is_empty());

    let via_start = exec_successors_for(&asset, 1, "K2Node_MacroInstance", "Start");
    let start_targets: BTreeSet<usize> = via_start.iter().map(|(n, _)| *n).collect();
    assert_eq!(start_targets, BTreeSet::from([2usize]));
}

#[test]
fn unknown_node_class_enqueues_all_exec_outputs() {
    let pins = vec![
        exec_pin_on(1, "execute", PIN_DIRECTION_INPUT, vec![]),
        exec_pin_on(1, "out_a", PIN_DIRECTION_OUTPUT, vec![(2, "execute")]),
        exec_pin_on(1, "out_b", PIN_DIRECTION_OUTPUT, vec![(3, "execute")]),
    ];
    let (asset, root) = build_routing_fixture(
        "K2Node_SomethingUnclassified",
        pins,
        &[(2, "X", 0), (3, "Y", 0)],
    );
    let succ = exec_successors_for(&asset, root, "K2Node_SomethingUnclassified", "execute");
    let targets: BTreeSet<usize> = succ.iter().map(|(n, _)| *n).collect();
    assert_eq!(targets, BTreeSet::from([2usize, 3]));
}

#[test]
fn ifthenelse_routes_execute_to_then_and_else() {
    let pins = vec![
        exec_pin_on(1, "execute", PIN_DIRECTION_INPUT, vec![]),
        exec_pin_on(1, "then", PIN_DIRECTION_OUTPUT, vec![(2, "execute")]),
        exec_pin_on(1, "else", PIN_DIRECTION_OUTPUT, vec![(3, "execute")]),
    ];
    let (asset, root) =
        build_routing_fixture("K2Node_IfThenElse", pins, &[(2, "T", 0), (3, "E", 0)]);
    let succ = exec_successors_for(&asset, root, "K2Node_IfThenElse", "execute");
    let targets: BTreeSet<usize> = succ.iter().map(|(n, _)| *n).collect();
    assert_eq!(targets, BTreeSet::from([2usize, 3]));
}

#[test]
fn condition_matches_variable_get_shapes() {
    let id = ConditionIdentity::VariableGet {
        var_name: "EnableDebugHandRotation".into(),
    };
    assert!(condition_matches(&id, "self.EnableDebugHandRotation"));
    assert!(condition_matches(&id, "EnableDebugHandRotation"));
    assert!(condition_matches(&id, "!self.EnableDebugHandRotation"));
    assert!(!condition_matches(&id, "self.Other"));
}
