use super::super::anchor::anchor_to_node;
use super::super::context::ClassifyContext;
use super::super::{Classification, PlacementClass, TraceRecorder};
use super::*;
use crate::output_summary::comments::{audit::Strategy, CommentBox};
use crate::types::{AssetVersion, ExportHeader, ImportEntry, NodePinData, PropValue, Property};

fn pin(name: &str, direction: u8, identity: u8, source: Option<usize>) -> EdGraphPin {
    EdGraphPin {
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
    let mapping = call_statements_by_node(1, &body, &parsed).unwrap();
    assert_eq!(mapping[&1].offset(), 20);
    assert_eq!(mapping[&2].offset(), 30);
    assert_eq!(mapping[&3].offset(), 10);
}

#[test]
fn unresolved_temporary_cannot_prove_a_different_graph_input() {
    let parsed = parsed_calls();
    let body = branch_calls(false);
    assert!(call_statements_by_node(1, &body, &parsed)
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
    assert!(call_statements_by_node(1, &body, &parsed)
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
    assert!(call_statements_by_node(1, &body, &parsed)
        .unwrap()
        .is_empty());
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
    assert_eq!(placed.class, PlacementClass::FunctionLevel);
    assert_eq!(placed.text, "Authored note");
    assert_eq!(
        placed.lines[0],
        "    // Graph comment (location unresolved)"
    );
    assert!(placed.lines[1].contains("Authored note"));
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
        placed.class,
        PlacementClass::InlineAtStatement {
            statement_offset: 1
        }
    );

    // Both graph paths reaching one statement cannot identify a branch.
    parsed.pin_data.get_mut(&9).unwrap().pins[1].linked_to[0].node = 1;
    assert!(branch_statement_for_node(9, &decoded.functions[0].body, &parsed).is_none());
}
