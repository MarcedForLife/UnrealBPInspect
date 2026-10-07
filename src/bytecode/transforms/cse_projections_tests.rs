//! Semantic regressions for expression movement and projection sharing.

use std::collections::BTreeMap;

use super::cse_projections::hoist_repeated_projections;
use super::expr_transforms::inline_single_use_temps;
use super::test_fixtures::{assign, assign_expr, call, lit, var};
use crate::bytecode::expr::{BinaryOp, Expr, LiteralValue};
use crate::bytecode::stmt::{LoopKind, Stmt};

fn field(name: &str) -> Expr {
    Expr::FieldAccess {
        recv: Box::new(var("self")),
        field: name.into(),
    }
}

fn invoke(name: &str) -> Expr {
    Expr::Call {
        name: name.into(),
        args: vec![],
    }
}

fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
    Stmt::Branch {
        cond,
        then_body,
        else_body,
        offset: 0,
    }
}

fn evaluate(expr: &Expr, values: &mut BTreeMap<String, i64>, trace: &mut Vec<String>) -> i64 {
    match expr {
        Expr::Literal(LiteralValue::Text(text)) => match text.as_str() {
            "true" => 1,
            "false" => 0,
            _ => text.parse().unwrap(),
        },
        Expr::Var(name) => *values
            .get(name)
            .unwrap_or_else(|| panic!("undefined {name}")),
        Expr::FieldAccess { recv, field } if **recv == var("self") => {
            values[&format!("self.{field}")]
        }
        Expr::Call { name, args } => execute_call(name, args, values, trace),
        Expr::Binary { op, lhs, rhs } => {
            let left = evaluate(lhs, values, trace);
            match op {
                BinaryOp::And if left == 0 => return 0,
                BinaryOp::Or if left != 0 => return 1,
                _ => {}
            }
            let right = evaluate(rhs, values, trace);
            match op {
                BinaryOp::Add => left + right,
                BinaryOp::Gt => i64::from(left > right),
                BinaryOp::Lt => i64::from(left < right),
                BinaryOp::And | BinaryOp::Or => i64::from(right != 0),
                _ => panic!("unsupported operator {op:?}"),
            }
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            let selected = if evaluate(cond, values, trace) != 0 {
                then_expr
            } else {
                else_expr
            };
            evaluate(selected, values, trace)
        }
        _ => panic!("unsupported expression {expr:?}"),
    }
}

fn execute_call(
    name: &str,
    args: &[Expr],
    values: &mut BTreeMap<String, i64>,
    trace: &mut Vec<String>,
) -> i64 {
    if name == "Fill" {
        let Expr::Out(storage) = &args[0] else {
            panic!("missing out marker")
        };
        let Expr::Var(name) = storage.as_ref() else {
            panic!("invalid out storage")
        };
        values.insert(name.clone(), 99);
        trace.push("Fill".into());
        return 0;
    }
    let arguments: Vec<_> = args
        .iter()
        .map(|arg| evaluate(arg, values, trace))
        .collect();
    match name {
        "AcquireTicket" => {
            trace.push("AcquireTicket".into());
            7
        }
        "TakeDamage" => {
            values.insert("self.Health".into(), 0);
            trace.push("TakeDamage".into());
            0
        }
        "Advance" => {
            *values.get_mut("self.Health").unwrap() -= 1;
            0
        }
        "Print" | "UseTicket" => {
            trace.push(format!("{name}{arguments:?}"));
            0
        }
        _ => panic!("unsupported call {name}"),
    }
}

fn execute(body: &[Stmt], values: &mut BTreeMap<String, i64>, trace: &mut Vec<String>) {
    for stmt in body {
        match stmt {
            Stmt::Assignment { lhs, rhs, .. } => {
                let value = evaluate(rhs, values, trace);
                let name = match lhs {
                    Expr::Var(name) => name.clone(),
                    Expr::FieldAccess { recv, field } if **recv == var("self") => {
                        format!("self.{field}")
                    }
                    _ => panic!("unsupported assignment {lhs:?}"),
                };
                values.insert(name, value);
            }
            Stmt::Call {
                func: Expr::Var(name),
                args,
                ..
            } => {
                execute_call(name, args, values, trace);
            }
            Stmt::Branch {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let selected = if evaluate(cond, values, trace) != 0 {
                    then_body
                } else {
                    else_body
                };
                execute(selected, values, trace);
            }
            Stmt::Loop {
                kind: LoopKind::While,
                cond: Some(cond),
                body,
                ..
            } => {
                let mut iterations = 0;
                while evaluate(cond, values, trace) != 0 {
                    assert!(iterations < 10, "loop failed to terminate");
                    iterations += 1;
                    execute(body, values, trace);
                }
            }
            _ => panic!("unsupported statement"),
        }
    }
}

fn assert_preserved(body: Vec<Stmt>, expected: &[&str]) -> Vec<Stmt> {
    let initial = BTreeMap::from([("self.Health".into(), 2), ("condition".into(), 0)]);
    let mut before_values = initial.clone();
    let mut before_trace = vec![];
    execute(&body, &mut before_values, &mut before_trace);
    assert_eq!(before_trace, expected);
    let mut pipeline_body = body.clone();
    let mut transformed = body;
    inline_single_use_temps(&mut transformed);
    hoist_repeated_projections(&mut transformed);
    inline_single_use_temps(&mut transformed);
    let mut after_values = initial;
    let mut after_trace = vec![];
    execute(&transformed, &mut after_values, &mut after_trace);
    assert_eq!(
        after_trace,
        before_trace,
        "transformed body {}",
        serde_json::to_string(&transformed).unwrap()
    );
    assert_eq!(after_values["self.Health"], before_values["self.Health"]);
    crate::bytecode::decode::apply_transform_stack_to_body(&mut pipeline_body);
    let mut pipeline_values = BTreeMap::from([("self.Health".into(), 2), ("condition".into(), 0)]);
    let mut pipeline_trace = vec![];
    execute(&pipeline_body, &mut pipeline_values, &mut pipeline_trace);
    assert_eq!(
        pipeline_trace,
        before_trace,
        "pipeline body {}",
        serde_json::to_string(&pipeline_body).unwrap()
    );
    assert_eq!(pipeline_values["self.Health"], before_values["self.Health"]);
    transformed
}

#[test]
fn saved_field_value_survives_intervening_call_and_write() {
    for change in [
        call("TakeDamage", vec![]),
        assign_expr(field("Health"), lit("0")),
    ] {
        let expected: &[&str] = if matches!(change, Stmt::Call { .. }) {
            &["TakeDamage", "Print[2]"]
        } else {
            &["Print[2]"]
        };
        assert_preserved(
            vec![
                assign("$Saved", field("Health")),
                change,
                call("Print", vec![var("$Saved")]),
            ],
            expected,
        );
    }
}

#[test]
fn unconditional_call_is_not_moved_into_branch_or_ternary() {
    for use_site in [
        branch(
            var("condition"),
            vec![call("UseTicket", vec![var("$Ticket")])],
            vec![],
        ),
        call(
            "Print",
            vec![Expr::Ternary {
                cond: Box::new(var("condition")),
                then_expr: Box::new(var("$Ticket")),
                else_expr: Box::new(lit("0")),
            }],
        ),
    ] {
        let expected: &[&str] = if matches!(use_site, Stmt::Branch { .. }) {
            &["AcquireTicket"]
        } else {
            &["AcquireTicket", "Print[0]"]
        };
        assert_preserved(
            vec![assign("$Ticket", invoke("AcquireTicket")), use_site],
            expected,
        );
    }
}

#[test]
fn earlier_call_arguments_keep_evaluation_order() {
    assert_preserved(
        vec![
            assign("$Saved", field("Health")),
            call("Print", vec![invoke("TakeDamage"), var("$Saved")]),
        ],
        &["TakeDamage", "Print[0, 2]"],
    );
    assert_preserved(
        vec![
            assign("$Changed", invoke("TakeDamage")),
            call("Print", vec![field("Health"), var("$Changed")]),
        ],
        &["TakeDamage", "Print[0, 0]"],
    );
}

#[test]
fn short_circuit_operand_does_not_consume_unconditional_call() {
    assert_preserved(
        vec![
            assign("$Ticket", invoke("AcquireTicket")),
            call(
                "Print",
                vec![Expr::Binary {
                    op: BinaryOp::And,
                    lhs: Box::new(lit("false")),
                    rhs: Box::new(var("$Ticket")),
                }],
            ),
        ],
        &["AcquireTicket", "Print[0]"],
    );
}

#[test]
fn projections_are_refreshed_after_writes_and_calls() {
    for change in [
        call("TakeDamage", vec![]),
        assign_expr(field("Health"), lit("0")),
    ] {
        let expected: &[&str] = if matches!(change, Stmt::Call { .. }) {
            &["Print[2]", "TakeDamage", "Print[0]"]
        } else {
            &["Print[2]", "Print[0]"]
        };
        assert_preserved(
            vec![
                call("Print", vec![field("Health")]),
                change,
                call("Print", vec![field("Health")]),
            ],
            expected,
        );
    }
}

#[test]
fn projections_and_inlining_keep_loop_evaluation_frequency() {
    assert_preserved(
        vec![
            assign("$Ticket", invoke("AcquireTicket")),
            Stmt::Loop {
                kind: LoopKind::While,
                cond: Some(field("Health")),
                completion: None,
                offset: 0,
                body: vec![
                    call("UseTicket", vec![var("$Ticket")]),
                    call("Print", vec![field("Health")]),
                    call("Advance", vec![]),
                ],
            },
            call("Print", vec![field("Health")]),
        ],
        &[
            "AcquireTicket",
            "UseTicket[7]",
            "Print[2]",
            "UseTicket[7]",
            "Print[1]",
            "Print[0]",
        ],
    );
}

#[test]
fn nested_definition_keeps_uses_outside_its_body() {
    assert_preserved(
        vec![
            branch(
                lit("true"),
                vec![
                    assign("$Saved", field("Health")),
                    call("Print", vec![var("$Saved")]),
                ],
                vec![],
            ),
            call("TakeDamage", vec![]),
            call("Print", vec![var("$Saved")]),
        ],
        &["Print[2]", "TakeDamage", "Print[2]"],
    );
}

#[test]
fn multiple_definitions_and_out_storage_survive() {
    assert_preserved(
        vec![
            assign("$Saved", lit("1")),
            assign("$Saved", lit("2")),
            call("Print", vec![var("$Saved")]),
        ],
        &["Print[2]"],
    );
    let transformed = assert_preserved(
        vec![
            assign("$Saved", lit("1")),
            call("Fill", vec![Expr::Out(Box::new(var("$Saved")))]),
            call("Print", vec![var("$Saved")]),
        ],
        &["Fill", "Print[99]"],
    );
    assert_eq!(transformed.len(), 3);
}

#[test]
fn unused_effectful_assignments_are_preserved() {
    let transformed = assert_preserved(
        vec![assign("$Unused", invoke("AcquireTicket"))],
        &["AcquireTicket"],
    );
    assert_eq!(transformed.len(), 1);
}

#[test]
fn adjacent_unconditional_calls_still_inline() {
    let transformed = assert_preserved(
        vec![
            assign("$Ticket", invoke("AcquireTicket")),
            call("UseTicket", vec![var("$Ticket")]),
        ],
        &["AcquireTicket", "UseTicket[7]"],
    );
    assert_eq!(transformed.len(), 1);
}

#[test]
fn repeated_arguments_share_one_local_projection() {
    let transformed = assert_preserved(
        vec![call("Print", vec![field("Health"), field("Health")])],
        &["Print[2, 2]"],
    );
    assert!(
        matches!(&transformed[0], Stmt::Assignment { lhs: Expr::Var(name), .. } if name == "$Health")
    );
    assert_eq!(transformed.len(), 2);
}

#[test]
fn nested_calls_and_out_arguments_block_projection_sharing() {
    let projection = field("Health");
    for argument in [invoke("TakeDamage"), Expr::Out(Box::new(var("Output")))] {
        let mut body = vec![call(
            "Print",
            vec![projection.clone(), argument, projection.clone()],
        )];
        let original = body.clone();
        hoist_repeated_projections(&mut body);
        assert_eq!(
            serde_json::to_value(&body).unwrap(),
            serde_json::to_value(&original).unwrap()
        );
    }
}

#[test]
fn conditional_and_loop_reads_are_not_hoisted() {
    let projection = field("Health");
    let mut body = vec![
        branch(
            var("condition"),
            vec![call("Print", vec![projection.clone()])],
            vec![call("Print", vec![projection.clone()])],
        ),
        Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(projection.clone()),
            body: vec![call("Print", vec![projection])],
            completion: None,
            offset: 0,
        },
    ];
    let original = body.clone();
    hoist_repeated_projections(&mut body);
    assert_eq!(
        serde_json::to_value(&body).unwrap(),
        serde_json::to_value(&original).unwrap()
    );
}

#[test]
fn projection_names_avoid_nested_variable_and_loop_item_collisions() {
    let mut body = vec![
        call("Print", vec![field("Health"), field("Health")]),
        Stmt::Loop {
            kind: LoopKind::ForEach {
                item: "$Health".into(),
                array: var("Items"),
            },
            cond: None,
            body: vec![call("Print", vec![var("$Cse_1")])],
            completion: None,
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);
    assert!(matches!(&body[0], Stmt::Assignment { lhs: Expr::Var(name), .. } if name == "$Cse_2"));
}

#[test]
fn projection_thresholds_and_left_right_names_are_retained() {
    let projection = Expr::Ternary {
        cond: Box::new(var("condition")),
        then_expr: Box::new(var("self.LeftHand")),
        else_expr: Box::new(var("self.RightHand")),
    };
    let mut body = vec![call("Print", vec![projection.clone(), projection])];
    hoist_repeated_projections(&mut body);
    assert!(matches!(&body[0], Stmt::Assignment { lhs: Expr::Var(name), .. } if name == "$Hand"));
    let projection = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("Value")),
        rhs: Box::new(lit("1")),
    };
    for count in [2, 3] {
        let mut body = vec![call("Print", vec![projection.clone(); count])];
        hoist_repeated_projections(&mut body);
        assert_eq!(body.len(), if count == 3 { 2 } else { 1 });
    }
}

#[test]
fn lazy_projection_arguments_do_not_read_invalid_fields() {
    let projection = Expr::Ternary {
        cond: Box::new(var("condition")),
        then_expr: Box::new(field("Missing")),
        else_expr: Box::new(lit("0")),
    };
    assert_preserved(
        vec![call("Print", vec![projection.clone(), projection])],
        &["Print[0, 0]"],
    );
    assert_preserved(
        vec![Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(var("condition")),
            completion: None,
            offset: 0,
            body: vec![call("Print", vec![field("Missing"), field("Missing")])],
        }],
        &[],
    );
}

#[test]
fn loop_condition_is_not_replaced_by_captured_value() {
    let mut body = vec![
        assign("$Condition", field("Health")),
        Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(var("$Condition")),
            body: vec![call("TakeDamage", vec![])],
            completion: None,
            offset: 0,
        },
    ];
    let original = serde_json::to_value(&body).unwrap();
    inline_single_use_temps(&mut body);
    assert_eq!(serde_json::to_value(&body).unwrap(), original);
}

#[test]
fn computed_receivers_and_bound_handles_precede_argument_evaluation() {
    for func in [
        Expr::FieldAccess {
            recv: Box::new(invoke("AcquireTicket")),
            field: "Use".into(),
        },
        Expr::FieldAccess {
            recv: Box::new(var("self")),
            field: "Use".into(),
        },
        var("$Callback"),
    ] {
        let mut body = vec![
            assign("$Ticket", invoke("AcquireTicket")),
            Stmt::Call {
                func,
                args: vec![var("$Ticket")],
                offset: 0,
            },
        ];
        let original = serde_json::to_value(&body).unwrap();
        inline_single_use_temps(&mut body);
        assert_eq!(serde_json::to_value(&body).unwrap(), original);
    }
}

#[test]
fn definition_used_as_assignment_receiver_is_not_removed() {
    let mut body = vec![
        assign("$Receiver", var("Object")),
        assign_expr(
            Expr::FieldAccess {
                recv: Box::new(var("$Receiver")),
                field: "Value".into(),
            },
            lit("1"),
        ),
    ];
    let original = serde_json::to_value(&body).unwrap();
    inline_single_use_temps(&mut body);
    super::dead_stmt::remove_dead_assignments(&mut body);
    assert_eq!(serde_json::to_value(&body).unwrap(), original);
}

#[test]
fn unused_potentially_failing_read_is_not_removed() {
    let mut body = vec![assign("$Unused", field("Missing"))];
    let original = serde_json::to_value(&body).unwrap();
    crate::bytecode::decode::apply_transform_stack_to_body(&mut body);
    assert_eq!(serde_json::to_value(&body).unwrap(), original);
}

#[test]
fn repeated_parameter_copies_keep_values_across_out_writes() {
    assert_preserved(
        vec![
            assign("Input", lit("2")),
            assign("Temp_bool_First", var("Input")),
            call("Fill", vec![Expr::Out(Box::new(var("Input")))]),
            assign("Temp_bool_First", var("Input")),
            call("Print", vec![var("Temp_bool_First")]),
        ],
        &["Fill", "Print[99]"],
    );
}

#[test]
fn recomputed_loop_condition_keeps_final_value_and_termination() {
    let condition = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("counter")),
        rhs: Box::new(lit("2")),
    };
    assert_preserved(
        vec![
            assign("counter", lit("0")),
            assign("$Condition", condition.clone()),
            Stmt::Loop {
                kind: LoopKind::While,
                cond: Some(var("$Condition")),
                completion: None,
                offset: 0,
                body: vec![
                    call("Print", vec![var("counter")]),
                    assign(
                        "counter",
                        Expr::Binary {
                            op: BinaryOp::Add,
                            lhs: Box::new(var("counter")),
                            rhs: Box::new(lit("1")),
                        },
                    ),
                    assign("$Condition", condition),
                ],
            },
            call("Print", vec![var("$Condition")]),
        ],
        &["Print[0]", "Print[1]", "Print[0]"],
    );
}

#[test]
fn earlier_fallible_argument_blocks_later_projection_hoist() {
    for earlier in [
        field("Missing"),
        Expr::Index {
            recv: Box::new(var("Items")),
            idx: Box::new(lit("99")),
        },
    ] {
        let mut body = vec![call(
            "Print",
            vec![earlier, field("Health"), field("Health")],
        )];
        let original = serde_json::to_value(&body).unwrap();
        hoist_repeated_projections(&mut body);
        assert_eq!(serde_json::to_value(&body).unwrap(), original);
    }
}
