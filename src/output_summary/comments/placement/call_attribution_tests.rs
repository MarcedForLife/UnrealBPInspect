use super::super::anchor::anchor_to_node;
use super::super::context::ClassifyContext;
use super::super::{Classification, PlacementClass, TraceRecorder};
use super::*;
use crate::output_summary::comments::{audit::Strategy, CommentBox};
use crate::types::{AssetVersion, ExportHeader, ImportEntry, NodePinData, PropValue, Property};

fn pin(name: &str, direction: u8, identity: u8, source: Option<usize>) -> EdGraphPin {
    EdGraphPin {
        metadata: None,
        name: name.into(),
        pin_type: if name == "execute" { "exec" } else { "object" }.into(),
        direction,
        pin_id: [identity; 16],
        linked_to: source
            .map(|node| {
                vec![LinkedPin {
                    node,
                    pin_id: [node as u8; 16],
                }]
            })
            .unwrap_or_default(),
    }
}

fn reference(kind: &str, member: &str) -> Property {
    Property {
        name: kind.into(),
        value: PropValue::Struct {
            struct_type: "MemberReference".into(),
            fields: vec![Property {
                name: "MemberName".into(),
                value: PropValue::Name(member.into()),
            }],
        },
    }
}

fn parsed_calls() -> ParsedAsset {
    let mut parsed = ParsedAsset {
        version: AssetVersion {
            file_ver: 522,
            file_ver_ue5: 0,
        },
        name_table: crate::binary::NameTable::from_names(Vec::new()),
        diagnostics: Vec::new(),
        imports: [
            "K2Node_CallFunction",
            "K2Node_VariableGet",
            "K2Node_Knot",
            "K2Node_GetArrayItem",
        ]
        .into_iter()
        .map(|class| ImportEntry {
            class_package: String::new(),
            class_name: "Class".into(),
            object_name: class.into(),
            outer_index: 0,
        })
        .collect(),
        exports: Vec::new(),
        pin_data: Default::default(),
        function_signatures: Default::default(),
        bytecode_by_export: Default::default(),
    };
    for (class, properties) in [
        (-1, vec![reference("FunctionReference", "Attach")]),
        (-1, vec![reference("FunctionReference", "Attach")]),
        (-1, vec![reference("FunctionReference", "Attach")]),
        (-2, vec![reference("VariableReference", "Primary")]),
        (-2, vec![reference("VariableReference", "Secondary")]),
        (-3, Vec::new()),
        (-4, Vec::new()),
        (-2, vec![reference("VariableReference", "Mesh")]),
    ] {
        parsed.exports.push((
            ExportHeader {
                class_index: class,
                super_index: 0,
                outer_index: 20,
                object_name: format!("Node{}", parsed.exports.len() + 1),
                serial_offset: 0,
                serial_size: 0,
            },
            properties,
        ));
    }
    for (node, source) in [(1, 6), (2, 5), (3, 7)] {
        parsed.pin_data.insert(
            node,
            NodePinData {
                pins: vec![
                    pin("execute", 0, 0, None),
                    pin("self", 0, 0, Some(8)),
                    pin("Parent", 0, 0, Some(source)),
                ],
            },
        );
    }
    for (node, name) in [(4, "Primary"), (5, "Secondary"), (7, "Output"), (8, "Mesh")] {
        parsed.pin_data.insert(
            node,
            NodePinData {
                pins: vec![pin(name, 1, node as u8, None)],
            },
        );
    }
    parsed.pin_data.insert(
        6,
        NodePinData {
            pins: vec![pin("Input", 0, 0, Some(4)), pin("Output", 1, 6, None)],
        },
    );
    parsed
}

fn call(offset: usize, parent: &str) -> Stmt {
    Stmt::Call {
        func: Expr::FieldAccess {
            recv: Box::new(Expr::Var("self.Mesh".into())),
            field: "Attach".into(),
        },
        args: vec![Expr::Var(parent.into())],
        offset,
    }
}

fn branch_calls(with_alias: bool) -> Vec<Stmt> {
    let mut indexed = Vec::new();
    if with_alias {
        indexed.push(Stmt::Assignment {
            lhs: Expr::Var("$Element".into()),
            rhs: Expr::Index {
                recv: Box::new(Expr::Var("Items".into())),
                idx: Box::new(Expr::Literal("0".into())),
            },
            offset: 8,
        });
    }
    indexed.push(call(10, "$Element"));
    vec![Stmt::Branch {
        cond: Expr::Var("Route".into()),
        then_body: vec![call(30, "self.Secondary")],
        else_body: vec![Stmt::Branch {
            cond: Expr::Var("OtherRoute".into()),
            then_body: indexed,
            else_body: vec![call(20, "self.Primary")],
            offset: 2,
        }],
        offset: 1,
    }]
}

#[test]
fn repeated_calls_match_data_paths_across_branches_and_reroutes() {
    let parsed = parsed_calls();
    let body = branch_calls(true);
    let mapping = call_statements_by_node(1, &[&body], &parsed).unwrap();
    assert_eq!(mapping[&1].offset(), 20);
    assert_eq!(mapping[&2].offset(), 30);
    assert_eq!(mapping[&3].offset(), 10);
}

#[test]
fn unresolved_temporary_cannot_prove_a_different_graph_input() {
    let parsed = parsed_calls();
    let body = branch_calls(false);
    assert!(call_statements_by_node(1, &[&body], &parsed)
        .unwrap()
        .is_empty());
}

#[test]
fn ambiguous_inputs_and_reroute_cycles_do_not_guess_by_order() {
    let mut parsed = parsed_calls();
    let body = branch_calls(true);
    parsed.pin_data.get_mut(&2).unwrap().pins[2].linked_to[0] = LinkedPin {
        node: 6,
        pin_id: [6; 16],
    };
    assert!(call_statements_by_node(1, &[&body], &parsed)
        .unwrap()
        .is_empty());
    parsed.pin_data.get_mut(&2).unwrap().pins[2].linked_to[0] = LinkedPin {
        node: 5,
        pin_id: [5; 16],
    };
    parsed.pin_data.get_mut(&6).unwrap().pins[0].linked_to[0] = LinkedPin {
        node: 6,
        pin_id: [6; 16],
    };
    let mapping = call_statements_by_node(1, &[&body], &parsed).unwrap();
    assert!(!mapping.contains_key(&1));
    assert_eq!(mapping[&2].offset(), 30);
}

fn bubble_on(node: usize) -> CommentBox {
    CommentBox {
        text: "Authored note".into(),
        x: 0,
        y: 0,
        width: 0,
        height: 0,
        is_bubble: true,
        owner_export: Some(node),
        graph_page: Some("Example".into()),
    }
}

fn decoded_body(body: Vec<Stmt>) -> crate::bytecode::asset::DecodedAsset {
    crate::bytecode::asset::DecodedAsset {
        function_origins: Default::default(),
        event_origins: Default::default(),
        resume_origins: Default::default(),
        diagnostics: Vec::new(),
        functions: vec![crate::bytecode::asset::Function {
            name: "Example".into(),
            body,
            export_index: None,
        }],
        events: Vec::new(),
        resume_bodies: Default::default(),
        resume_owner_events: Default::default(),
        byte_maps: Default::default(),
    }
}

#[test]
fn ambiguous_call_bubble_retains_authored_text_at_an_explicitly_unresolved_location() {
    let parsed = parsed_calls();
    let decoded = decoded_body(branch_calls(false));
    let model = super::super::super::CommentModel {
        boxes: Vec::new(),
        nodes: Vec::new(),
    };
    let names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let context = ClassifyContext::new(&decoded, &parsed, &names, &model);
    let outcome = anchor_to_node(
        &bubble_on(1),
        "Example",
        1,
        Strategy::BubbleDirect,
        &context,
        &TraceRecorder::default(),
    );
    let Classification::Placed(placed) = outcome else {
        panic!("comment must remain visible")
    };
    assert_eq!(placed.locations[0].class, PlacementClass::Unresolved);
    assert_eq!(placed.text, "Authored note");
    assert_eq!(placed.locations[0].block, "Example");
}

#[test]
fn branch_bubble_uses_both_proven_arms_even_after_polarity_inversion() {
    let mut parsed = parsed_calls();
    parsed.imports.push(ImportEntry {
        class_package: String::new(),
        class_name: "Class".into(),
        object_name: "K2Node_IfThenElse".into(),
        outer_index: 0,
    });
    parsed.exports.push((
        ExportHeader {
            class_index: -5,
            super_index: 0,
            outer_index: 20,
            object_name: "Branch".into(),
            serial_offset: 0,
            serial_size: 0,
        },
        Vec::new(),
    ));
    let mut first = pin("then", 1, 9, Some(1));
    let mut second = pin("else", 1, 10, Some(2));
    first.pin_type = "exec".into();
    second.pin_type = "exec".into();
    parsed.pin_data.insert(
        9,
        NodePinData {
            pins: vec![first, second],
        },
    );
    let decoded = decoded_body(branch_calls(true));
    let model = super::super::super::CommentModel {
        boxes: Vec::new(),
        nodes: Vec::new(),
    };
    let names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let context = ClassifyContext::new(&decoded, &parsed, &names, &model);
    let outcome = anchor_to_node(
        &bubble_on(9),
        "Example",
        9,
        Strategy::BubbleDirect,
        &context,
        &TraceRecorder::default(),
    );
    let Classification::Placed(placed) = outcome else {
        panic!("expected branch anchor")
    };
    assert_eq!(
        placed.locations[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 1,
            statement_path: Vec::new(),
        }
    );

    // Both graph paths reaching one statement cannot identify a branch.
    parsed.pin_data.get_mut(&9).unwrap().pins[1].linked_to[0].node = 1;
    assert!(branch_statement_for_node(9, &decoded.functions[0].body, &parsed).is_none());
}

#[test]
fn repeated_calls_match_across_event_and_resume_bodies() {
    let parsed = parsed_calls();
    let first_event = vec![call(20, "self.Primary")];
    let second_event = vec![call(30, "self.Secondary")];
    let continuation = vec![
        Stmt::Assignment {
            lhs: Expr::Var("$Element".into()),
            rhs: Expr::Index {
                recv: Box::new(Expr::Var("Items".into())),
                idx: Box::new(Expr::Literal("0".into())),
            },
            offset: 8,
        },
        call(10, "$Element"),
    ];
    let mapping =
        call_statements_by_node(1, &[&first_event, &second_event, &continuation], &parsed).unwrap();
    assert_eq!(mapping[&1].offset(), 20);
    assert_eq!(mapping[&2].offset(), 30);
    assert_eq!(mapping[&3].offset(), 10);
}

#[test]
fn branch_evidence_does_not_cross_another_fork() {
    let mut parsed = parsed_calls();
    let mut first = pin("then", 1, 9, Some(1));
    let mut second = pin("else", 1, 10, Some(2));
    first.pin_type = "exec".into();
    second.pin_type = "exec".into();
    parsed.pin_data.insert(
        9,
        NodePinData {
            pins: vec![first, second],
        },
    );
    assert!(first_mapped_exec_statement(9, &branch_calls(true), &parsed).is_none());
}

#[test]
fn event_comment_matches_the_correct_repeated_call_without_a_byte_map() {
    let parsed = parsed_calls();
    let mut decoded = decoded_body(Vec::new());
    decoded.functions.clear();
    decoded.events.push(crate::bytecode::asset::Event {
        name: "OnUpdate".into(),
        body: branch_calls(true),
        export_index: None,
    });
    let mut comment = bubble_on(1);
    comment.graph_page = Some("EventGraph".into());
    let model = super::super::super::CommentModel {
        boxes: vec![comment],
        nodes: vec![],
    };
    let plan = super::super::build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.placed[0].locations[0].block, "OnUpdate");
    assert_eq!(
        plan.placed[0].locations[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 20,
            statement_path: vec![0, 0, 1, 0, 1, 0],
        }
    );
}

#[test]
fn ambiguous_event_call_cannot_fall_through_to_a_downstream_call() {
    let mut parsed = parsed_calls();
    let mut output = pin("then", 1, 10, Some(2));
    output.pin_type = "exec".into();
    parsed.pin_data.get_mut(&1).unwrap().pins.push(output);
    let mut decoded = decoded_body(Vec::new());
    decoded.functions.clear();
    decoded.events.push(crate::bytecode::asset::Event {
        name: "OnUpdate".into(),
        body: branch_calls(false),
        export_index: None,
    });
    let mut comment = bubble_on(1);
    comment.graph_page = Some("EventGraph".into());
    let model = super::super::super::CommentModel {
        boxes: vec![comment],
        nodes: vec![],
    };
    let plan = super::super::build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(
        plan.placed[0].locations[0].class,
        PlacementClass::Unresolved
    );
    assert_eq!(plan.placed[0].locations[0].block, "EventGraph");
}

#[test]
fn unique_branch_condition_resolves_an_empty_arm_and_inverted_predicate() {
    let mut parsed = parsed_calls();
    parsed.imports.push(ImportEntry {
        class_package: String::new(),
        class_name: "Class".into(),
        object_name: "K2Node_IfThenElse".into(),
        outer_index: 0,
    });
    parsed.exports.push((
        ExportHeader {
            class_index: -5,
            super_index: 0,
            outer_index: 20,
            object_name: "Branch".into(),
            serial_offset: 0,
            serial_size: 0,
        },
        Vec::new(),
    ));
    parsed.pin_data.insert(
        9,
        NodePinData {
            pins: vec![pin("Condition", 0, 9, Some(4))],
        },
    );
    let body = vec![Stmt::Branch {
        cond: Expr::Unary {
            op: crate::bytecode::expr::UnaryOp::Not,
            operand: Box::new(Expr::Var("self.Primary".into())),
        },
        then_body: vec![call(20, "self.Secondary")],
        else_body: vec![],
        offset: 10,
    }];
    assert_eq!(
        branch_statement_for_node(9, &body, &parsed)
            .unwrap()
            .offset(),
        10
    );

    let mut duplicate = parsed.exports[8].clone();
    duplicate.0.object_name = "AnotherBranch".into();
    parsed.exports.push(duplicate);
    parsed.pin_data.insert(10, parsed.pin_data[&9].clone());
    assert!(branch_statement_for_node(9, &body, &parsed).is_none());
}

#[test]
fn repeated_variable_writes_with_shared_bytes_remain_unresolved() {
    use crate::bytecode::decode::cross_event_inline::K2NodeClass;
    use crate::bytecode::k2node_byte_map::{ByteMaps, K2NodeByteMap, K2NodePartition};
    let mut parsed = parsed_calls();
    parsed.imports[1].object_name = "K2Node_VariableSet".into();
    let mut decoded = decoded_body(vec![Stmt::Assignment {
        lhs: Expr::Var("self.Value".into()),
        rhs: Expr::Literal("1".into()),
        offset: 10,
    }]);
    let mut byte_map = K2NodeByteMap::default();
    for node in [4, 5] {
        byte_map.partitions.insert(
            node,
            K2NodePartition {
                node_id: node,
                ranges: std::iter::once(10..11).collect(),
                owner_events: Default::default(),
                kind: K2NodeClass::Other,
                macro_kind: None,
                via_fallback: vec![],
            },
        );
    }
    decoded.byte_maps = ByteMaps {
        ubergraph: None,
        functions: BTreeMap::from([("Example".into(), byte_map)]),
    };
    let model = super::super::super::CommentModel {
        boxes: vec![bubble_on(4)],
        nodes: vec![],
    };
    let plan = super::super::build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(
        plan.placed[0].locations[0].class,
        PlacementClass::Unresolved
    );
}

#[test]
fn forced_call_pair_survives_ambiguous_neighbors() {
    let mut parsed = parsed_calls();
    for node in [1, 2] {
        parsed.pin_data.get_mut(&node).unwrap().pins[2].linked_to[0] = LinkedPin {
            node: 7,
            pin_id: [7; 16],
        };
    }
    parsed.pin_data.get_mut(&3).unwrap().pins[2].linked_to[0] = LinkedPin {
        node: 4,
        pin_id: [4; 16],
    };
    let body = vec![
        call(10, "self.Primary"),
        call(20, "self.Secondary"),
        call(30, "self.Tertiary"),
    ];
    let mapping = call_statements_by_node(1, &[&body], &parsed).unwrap();
    assert_eq!(mapping.len(), 1);
    assert_eq!(mapping[&3].offset(), 10);
}

fn default_pin(name: &str, category: &str, value: &str) -> EdGraphPin {
    EdGraphPin {
        name: name.into(),
        pin_type: category.into(),
        direction: 0,
        metadata: Some(crate::types::EdGraphPinMetadata {
            default_value: value.into(),
            ..Default::default()
        }),
        ..Default::default()
    }
}

fn export_names(parsed: &ParsedAsset) -> Vec<String> {
    parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect()
}

#[test]
fn repeated_calls_match_typed_unconnected_defaults() {
    let mut parsed = parsed_calls();
    for (node, value) in [(1, "1"), (2, "2"), (3, "3")] {
        parsed.pin_data.get_mut(&node).unwrap().pins[2] = default_pin("Parent", "int", value);
    }
    let body: Vec<Stmt> = [(10, "3"), (20, "1"), (30, "2")]
        .into_iter()
        .map(|(offset, value)| {
            let mut stmt = call(offset, "unused");
            let Stmt::Call { args, .. } = &mut stmt else {
                unreachable!()
            };
            args[0] = Expr::Literal(value.into());
            stmt
        })
        .collect();
    let mapping = call_statements_by_node(1, &[&body], &parsed).unwrap();
    assert_eq!(mapping[&1].offset(), 20);
    assert_eq!(mapping[&2].offset(), 30);
    assert_eq!(mapping[&3].offset(), 10);
}

#[test]
fn defaults_preserve_float_width_signed_zero_and_empty_string() {
    let parsed = parsed_calls();
    let names = export_names(&parsed);
    let single =
        graph_default_expression(&default_pin("Value", "float", "-0.0"), &parsed, &names).unwrap();
    assert_eq!(
        single,
        Expr::Literal(LiteralValue::Float32((-0.0f32).to_bits()))
    );
    let mut double = default_pin("Value", "real", "1.00000000001");
    double
        .metadata
        .as_mut()
        .unwrap()
        .type_details
        .push(Property {
            name: "PinSubCategory".into(),
            value: PropValue::Name("double".into()),
        });
    let value = graph_default_expression(&double, &parsed, &names).unwrap();
    assert_eq!(
        value,
        Expr::Literal(LiteralValue::Float64(1.00000000001f64.to_bits()))
    );
    assert_eq!(
        expression_matches(
            &Expr::Literal(LiteralValue::Float32(1.0f32.to_bits())),
            &value,
            None
        ),
        Some(false)
    );
    let mut empty = default_pin("Value", "string", "");
    empty.metadata.as_mut().unwrap().autogenerated_default_value = "fallback".into();
    assert_eq!(
        graph_default_expression(&empty, &parsed, &names),
        Some(Expr::Literal("\"\"".into()))
    );
    let mut numeric = default_pin("Value", "int", "");
    numeric
        .metadata
        .as_mut()
        .unwrap()
        .autogenerated_default_value = "7".into();
    assert_eq!(
        graph_default_expression(&numeric, &parsed, &names),
        Some(Expr::Literal("7".into()))
    );
    assert!(
        graph_default_expression(&default_pin("Value", "float", "NaN"), &parsed, &names).is_none()
    );
}

#[test]
fn name_object_and_text_defaults_require_recoverable_identity() {
    let parsed = parsed_calls();
    let names = export_names(&parsed);
    assert_eq!(
        graph_default_expression(&default_pin("Value", "name", "Label"), &parsed, &names),
        Some(Expr::Literal("'Label'".into()))
    );
    let mut object = default_pin("Value", "object", "");
    object.metadata.as_mut().unwrap().default_object = -1;
    assert_eq!(
        graph_default_expression(&object, &parsed, &names),
        Some(Expr::Literal("K2Node_CallFunction".into()))
    );
    for index in [-999, i32::MIN, i32::MAX] {
        object.metadata.as_mut().unwrap().default_object = index;
        assert!(graph_default_expression(&object, &parsed, &names).is_none());
    }
    let mut text = default_pin("Value", "text", "");
    let metadata = text.metadata.as_mut().unwrap();
    metadata.default_text_source = Some("Hello".into());
    metadata.default_text_payload = vec![0; 5];
    assert_eq!(
        graph_default_expression(&text, &parsed, &names),
        Some(Expr::Literal("LOCTEXT(\"Hello\")".into()))
    );
    text.metadata.as_mut().unwrap().default_text_payload[4] = 1;
    assert!(graph_default_expression(&text, &parsed, &names).is_none());
}

fn graph_node(
    parsed: &mut ParsedAsset,
    class: &str,
    properties: Vec<Property>,
    pins: Vec<EdGraphPin>,
) -> usize {
    parsed.imports.push(ImportEntry {
        class_package: String::new(),
        class_name: "Class".into(),
        object_name: class.into(),
        outer_index: 0,
    });
    let node = parsed.exports.len() + 1;
    parsed.exports.push((
        ExportHeader {
            class_index: -(parsed.imports.len() as i32),
            super_index: 0,
            outer_index: 20,
            object_name: format!("Node{node}"),
            serial_offset: 0,
            serial_size: 0,
        },
        properties,
    ));
    parsed.pin_data.insert(node, NodePinData { pins });
    node
}

#[test]
fn pure_operator_index_and_cast_graph_expressions_match_raw_and_lowered_forms() {
    let mut parsed = parsed_calls();
    let pure = graph_node(
        &mut parsed,
        "K2Node_CallFunction",
        vec![reference("FunctionReference", "Add_IntInt")],
        vec![
            default_pin("A", "int", "1"),
            default_pin("B", "int", "2"),
            pin("ReturnValue", 1, 9, None),
        ],
    );
    let expected = graph_pin_expression(
        &LinkedPin {
            node: pure,
            pin_id: [9; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    let raw = Expr::Call {
        name: "Add_IntInt".into(),
        args: vec![Expr::Literal("1".into()), Expr::Literal("2".into())],
    };
    assert_eq!(expression_matches(&raw, &expected, None), Some(true));
    assert_eq!(
        expression_matches(&normalized_expression(&raw), &expected, None),
        Some(true)
    );
    parsed.pin_data.get_mut(&7).unwrap().pins = vec![
        pin("Array", 0, 0, Some(4)),
        default_pin("Dimension1", "int", "0"),
        pin("Output", 1, 7, None),
    ];
    let indexed = graph_pin_expression(
        &LinkedPin {
            node: 7,
            pin_id: [7; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert_eq!(
        expression_matches(
            &Expr::Index {
                recv: Box::new(Expr::Var("self.Primary".into())),
                idx: Box::new(Expr::Literal("0".into()))
            },
            &indexed,
            None
        ),
        Some(true)
    );
    let cast = graph_node(
        &mut parsed,
        "K2Node_DynamicCast",
        vec![Property {
            name: "TargetType".into(),
            value: PropValue::Object(-1),
        }],
        vec![pin("Object", 0, 0, Some(4)), pin("AsResult", 1, 10, None)],
    );
    let cast_expr = graph_pin_expression(
        &LinkedPin {
            node: cast,
            pin_id: [10; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert!(
        matches!(cast_expr, Expr::Cast { kind: CastKind::Class { target }, .. } if target == "K2Node_CallFunction")
    );
}

#[test]
fn split_and_pass_through_values_use_serialized_pin_identity() {
    let mut parsed = parsed_calls();
    let mut parent = pin("Settings", 1, 9, None);
    let mut child = pin("Settings_Value", 1, 10, None);
    parent.metadata = Some(crate::types::EdGraphPinMetadata {
        sub_pins: vec![LinkedPin {
            node: 9,
            pin_id: [10; 16],
        }],
        ..Default::default()
    });
    child.metadata = Some(crate::types::EdGraphPinMetadata {
        parent_pin: Some(LinkedPin {
            node: 9,
            pin_id: [9; 16],
        }),
        ..Default::default()
    });
    let node = graph_node(
        &mut parsed,
        "K2Node_FunctionEntry",
        vec![],
        vec![parent, child, pin("Settings_Unrelated", 1, 11, None)],
    );
    let field = graph_pin_expression(
        &LinkedPin {
            node,
            pin_id: [10; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert_eq!(
        expression_matches(&Expr::Var("Settings.Value".into()), &field, None),
        Some(true)
    );
    let unrelated = graph_pin_expression(
        &LinkedPin {
            node,
            pin_id: [11; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert_eq!(unrelated, Expr::Var("Settings_Unrelated".into()));
    parsed.pin_data.get_mut(&7).unwrap().pins[0].metadata =
        Some(crate::types::EdGraphPinMetadata {
            reference_pass_through: Some(LinkedPin {
                node: 4,
                pin_id: [4; 16],
            }),
            ..Default::default()
        });
    let value = graph_pin_expression(
        &LinkedPin {
            node: 7,
            pin_id: [7; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert_eq!(
        expression_matches(&Expr::Var("self.Primary".into()), &value, None),
        Some(true)
    );
}

#[test]
fn assignment_attribution_preserves_repeated_compiled_occurrences_and_rejects_peers() {
    let mut parsed = parsed_calls();
    let node = graph_node(
        &mut parsed,
        "K2Node_VariableSet",
        vec![reference("VariableReference", "Level")],
        vec![default_pin("Level", "int", "1")],
    );
    let body: Vec<Stmt> = [10, 20]
        .into_iter()
        .map(|offset| Stmt::Assignment {
            lhs: Expr::Var("self.Level".into()),
            rhs: Expr::Literal("1".into()),
            offset,
        })
        .collect();
    assert_eq!(
        statement_for_node(node, &body, &parsed)
            .iter()
            .map(|stmt| stmt.offset())
            .collect::<Vec<_>>(),
        vec![10, 20]
    );
    graph_node(
        &mut parsed,
        "K2Node_VariableSet",
        vec![reference("VariableReference", "Other")],
        vec![default_pin("Other", "wildcard", "")],
    );
    assert_eq!(statement_for_node(node, &body, &parsed).len(), 2);
    graph_node(
        &mut parsed,
        "K2Node_VariableSet",
        vec![reference("VariableReference", "Level")],
        vec![default_pin("Level", "int", "1")],
    );
    assert!(statement_for_node(node, &body, &parsed).is_empty());
}

#[test]
fn adjacent_alias_matching_stops_at_intervening_statements() {
    let expected = Expr::Literal("42".into());
    let temporary = Expr::Var("$Value".into());
    let assignment = Stmt::Assignment {
        lhs: temporary.clone(),
        rhs: expected.clone(),
        offset: 10,
    };
    assert_eq!(
        expression_matches(&temporary, &expected, Some(&assignment)),
        Some(true)
    );
    assert_eq!(
        expression_matches(&temporary, &expected, Some(&call(20, "Other"))),
        None
    );
}

#[test]
fn known_graph_receivers_cannot_match_implicit_self_calls() {
    let parsed = parsed_calls();
    let stmt = Stmt::Call {
        func: Expr::Var("Attach".into()),
        args: vec![Expr::Var("self.Primary".into())],
        offset: 1,
    };
    assert!(!call_inputs_match(
        1,
        &stmt,
        None,
        &parsed,
        &export_names(&parsed)
    ));
    let empty_object = default_pin("WorldContextObject", "object", "");
    assert!(graph_default_expression(&empty_object, &parsed, &export_names(&parsed)).is_none());
}

#[test]
fn pass_through_receivers_never_fall_back_to_implicit_self() {
    let mut parsed = parsed_calls();
    let mut receiver = pin("self", 0, 0, None);
    receiver.metadata = Some(crate::types::EdGraphPinMetadata {
        reference_pass_through: Some(LinkedPin {
            node: 8,
            pin_id: [8; 16],
        }),
        ..Default::default()
    });
    parsed
        .pin_data
        .get_mut(&4)
        .unwrap()
        .pins
        .push(receiver.clone());
    let source = graph_pin_expression(
        &LinkedPin {
            node: 4,
            pin_id: [4; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert_eq!(
        expression_matches(&Expr::Var("self.Mesh.Primary".into()), &source, None),
        Some(true)
    );
    assert_eq!(
        expression_matches(&Expr::Var("self.Primary".into()), &source, None),
        Some(false)
    );
    let pure = graph_node(
        &mut parsed,
        "K2Node_CallFunction",
        vec![reference("FunctionReference", "ReadValue")],
        vec![receiver, pin("ReturnValue", 1, 9, None)],
    );
    let source = graph_pin_expression(
        &LinkedPin {
            node: pure,
            pin_id: [9; 16],
        },
        &parsed,
        &export_names(&parsed),
        &mut BTreeSet::new(),
    )
    .unwrap();
    assert!(
        matches!(&source, Expr::MethodCall { recv, .. } if expression_matches(recv, &Expr::Var("self.Mesh".into()), None) == Some(true))
    );
    assert_eq!(
        expression_matches(
            &Expr::Call {
                name: "ReadValue".into(),
                args: vec![]
            },
            &source,
            None
        ),
        Some(false)
    );
}
