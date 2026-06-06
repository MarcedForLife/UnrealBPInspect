//! FlipFlop recognizer tests (positive recognitions only; `_unchanged`
//! and decline cases live in `negatives.rs`).

use super::*;
use crate::bytecode::stmt::LatchKind;
use crate::bytecode::transforms::latch_recognition::recognize_latches;
use crate::bytecode::transforms::test_fixtures::stmt_kind;

#[test]
fn recognizes_post_inline_flipflop() {
    let mut body = flipflop_post_inline(
        "Temp_bool_Variable_2",
        vec![call_stmt("DoA")],
        vec![call_stmt("DoB")],
    );

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind,
        body: latch_body,
        init,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert!(init.is_empty());
    match kind {
        LatchKind::FlipFlop { gate_var, names } => {
            assert_eq!(gate_var, "Temp_bool_Variable_2");
            assert!(names.is_none(), "FlipFlop recognizer leaves names = None");
        }
        _ => panic!("expected LatchKind::FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
    match &latch_body[0] {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            assert_eq!(then_body.len(), 1);
            assert_eq!(else_body.len(), 1);
        }
        _ => panic!("FlipFlop body should hold a Branch"),
    }
}

#[test]
fn recognizes_pre_inline_flipflop() {
    let mut body = flipflop_pre_inline(
        "Temp_bool_Variable_5",
        "Tmp_NotPre",
        vec![call_stmt("DoA")],
        vec![call_stmt("DoB")],
    );

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch { kind, .. } = &body[0] else {
        panic!("expected Stmt::Latch");
    };
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, "Temp_bool_Variable_5");
        }
        _ => panic!("expected FlipFlop"),
    }
}

#[test]
fn recognizes_alias_chained_flipflop() {
    let mut body = flipflop_alias_chained(
        "Temp_bool_Variable_7",
        "$Tmp_NotPre",
        "$Tmp_Mid",
        vec![call_stmt("DoA")],
        vec![call_stmt("DoB")],
    );

    recognize_latches(&mut body);

    assert_eq!(
        body.len(),
        1,
        "alias chain should drain into a single Latch"
    );
    let Stmt::Latch {
        kind,
        body: latch_body,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, "Temp_bool_Variable_7");
        }
        _ => panic!("expected FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
}

#[test]
fn recognizes_shared_arms_flipflop_with_trailing_siblings() {
    // Reproduces the InpActEvt_Fly shape: the BP compiler emits the toggle
    // update as preceding siblings, the JIN over the toggle var dispatches
    // to two scaffold-only arms, and the user body lives as TRAILING
    // siblings. The recognizer should absorb the trailing siblings into
    // the FlipFlop body and produce a single Latch with the canonical
    // `Branch { then: <user>, else: [] }` shape the emitter renders as
    // `A|B: { ... }`.
    let toggle = "Temp_bool_Variable";
    let mut body = vec![
        Stmt::Assignment {
            lhs: var("$Not_PreBool"),
            rhs: not_pre_bool_call(toggle),
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: var("$Not_PreBool"),
            offset: 0x14,
        },
        Stmt::Branch {
            cond: var(toggle),
            then_body: vec![],
            else_body: vec![
                Stmt::Assignment {
                    lhs: var("$Not_PreBool"),
                    rhs: not_pre_bool_call(toggle),
                    offset: 0x18,
                },
                Stmt::Assignment {
                    lhs: var(toggle),
                    rhs: var("$Not_PreBool"),
                    offset: 0x1c,
                },
            ],
            offset: 0x20,
        },
        // First trailing sibling: alias-set assignment to the user var.
        Stmt::Assignment {
            lhs: var("self.FlyEnabled"),
            rhs: var(toggle),
            offset: 0x24,
        },
        // Second trailing sibling: shim temp-def (doesn't ref toggle directly)
        // whose lhs is consumed by the third.
        Stmt::Assignment {
            lhs: var("$SelectFloat_B_1"),
            rhs: Expr::FieldAccess {
                recv: Box::new(var("self.Movement")),
                field: "MaxSwimSpeed".to_string(),
            },
            offset: 0x28,
        },
        // Third trailing sibling: refs the user alias var and the shim.
        Stmt::Assignment {
            lhs: var("$SelectFloat_2"),
            rhs: Expr::Call {
                name: "SelectFloat".to_string(),
                args: vec![
                    lit("800.0"),
                    var("$SelectFloat_B_1"),
                    var("self.FlyEnabled"),
                ],
            },
            offset: 0x2c,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1, "all stmts should fold into the FlipFlop");
    let Stmt::Latch {
        kind,
        body: latch_body,
        init,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert!(init.is_empty());
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, toggle);
        }
        _ => panic!("expected LatchKind::FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &latch_body[0]
    else {
        panic!("expected inner Branch inside Latch");
    };
    assert!(
        else_body.is_empty(),
        "shared-arms shape uses empty else for A|B rendering"
    );
    assert_eq!(then_body.len(), 3, "all three trailing siblings absorbed");
}

#[test]
fn recognizes_shared_arms_flipflop_with_trailing_toggle() {
    // Reproduces the InpActEvt_Fly alt-path shape: the BP compiler placed the
    // toggle preamble's block after the gate JIN's block on disk, so the
    // toggle update emits as TRAILING siblings (pre-inline 2-stmt form). The
    // Branch arms are scaffold-only. Recognizer should drain the trailing
    // toggle chain and wrap the absorbed user content (here empty) in a
    // FlipFlop latch.
    let toggle = "Temp_bool_Variable";
    let mut body = vec![
        Stmt::Branch {
            cond: var(toggle),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        // Trailing toggle pair (pre-inline 2-stmt form, no user body).
        Stmt::Assignment {
            lhs: var("$Not_PreBool"),
            rhs: not_pre_bool_call(toggle),
            offset: 0x14,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: var("$Not_PreBool"),
            offset: 0x18,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1, "trailing toggle pair should drain");
    let Stmt::Latch {
        kind,
        body: latch_body,
        init,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert!(init.is_empty());
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, toggle);
        }
        _ => panic!("expected LatchKind::FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &latch_body[0]
    else {
        panic!("expected inner Branch inside Latch");
    };
    assert!(then_body.is_empty(), "no user body in this fixture");
    assert!(else_body.is_empty());
}

#[test]
fn recognizes_shared_arms_flipflop_with_trailing_toggle_and_user_body() {
    // Generalised trailing-toggle shape: user body content sits between the
    // Branch and the trailing toggle pair. Recognizer absorbs user stmts as
    // the FlipFlop body and drains the trailing toggle pair.
    let toggle = "Temp_bool_Variable_3";
    let mut body = vec![
        Stmt::Branch {
            cond: var(toggle),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var("self.FlyEnabled"),
            rhs: var(toggle),
            offset: 0x14,
        },
        call_stmt("DoSomething"),
        // Trailing toggle pair.
        Stmt::Assignment {
            lhs: var("$Not_PreBool"),
            rhs: not_pre_bool_call(toggle),
            offset: 0x1c,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: var("$Not_PreBool"),
            offset: 0x20,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind,
        body: latch_body,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, toggle);
        }
        _ => panic!("expected LatchKind::FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &latch_body[0]
    else {
        panic!("expected inner Branch");
    };
    assert!(else_body.is_empty());
    assert_eq!(then_body.len(), 2, "user body absorbed (2 stmts)");
}

#[test]
fn recognizes_shared_arms_flipflop_with_trailing_post_inline_toggle() {
    // Post-inline 1-stmt trailing toggle form: `toggle = Not_PreBool(toggle)`.
    // Should also fold via the unified Var-alias-chain walker.
    let toggle = "Temp_bool_Variable_4";
    let mut body = vec![
        Stmt::Branch {
            cond: var(toggle),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: not_pre_bool_call(toggle),
            offset: 0x14,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind,
        body: latch_body,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch");
    };
    match kind {
        LatchKind::FlipFlop { gate_var, .. } => {
            assert_eq!(gate_var, toggle);
        }
        _ => panic!("expected FlipFlop"),
    }
    assert_eq!(latch_body.len(), 1);
}

#[test]
fn doonce_inside_flipflop_arm_is_recognised() {
    let inner_gate = "Temp_bool_IsClosed_Variable_7";
    let arm_a = vec![doonce_branch(inner_gate, vec![call_stmt("Once")])];
    let mut body = flipflop_post_inline("Temp_bool_Variable_3", arm_a, vec![call_stmt("DoB")]);

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        body: ff_body,
        kind,
        ..
    } = &body[0]
    else {
        panic!("outer should be Latch");
    };
    match kind {
        LatchKind::FlipFlop { .. } => {}
        _ => panic!("outer LatchKind should be FlipFlop"),
    }
    let Stmt::Branch { then_body, .. } = &ff_body[0] else {
        panic!("expected branch inside FlipFlop");
    };
    assert!(matches!(then_body[0], Stmt::Latch { .. }));
}

/// Shape selector for the embedded-flip recognizer driver.
#[derive(Clone, Copy)]
enum ElseShape {
    /// 1-stmt else: `else { toggle = neg }`.
    OneStmt,
    /// 2-stmt else chain: `else { $tmp = neg; toggle = $tmp }`.
    TwoStmtChain,
}

/// Consumer variant. Determines what precedes the inner Branch and
/// what the recognizer must pick up via the toggle-alias walk.
#[derive(Clone, Copy)]
enum ConsumerShape {
    /// Single direct consumer that reads the toggle var by name.
    DirectField,
    /// Forward alias setup followed by an aliased read; the alias walk
    /// must trace `$alias = Var(toggle)` through to the field assignment.
    AliasedField,
}

/// Negation factory selector for the else-arm RHS.
#[derive(Clone, Copy)]
enum NegShape {
    Unary,
    NotPreBoolCall,
}

#[test]
fn embedded_flip_recognizer_cases() {
    struct Case {
        label: &'static str,
        toggle: &'static str,
        else_shape: ElseShape,
        neg: NegShape,
        consumer: ConsumerShape,
        // None = test asserts only Latch + FlipFlop kind, no then_body length.
        expected_then_len: Option<usize>,
    }
    let cases = vec![
        Case {
            label: "embedded_flip_unary_negation",
            toggle: "Temp_bool_Variable_1",
            else_shape: ElseShape::OneStmt,
            neg: NegShape::Unary,
            consumer: ConsumerShape::DirectField,
            expected_then_len: Some(1),
        },
        Case {
            label: "embedded_flip_not_pre_bool_call_negation",
            toggle: "Temp_bool_Variable_2",
            else_shape: ElseShape::OneStmt,
            neg: NegShape::NotPreBoolCall,
            consumer: ConsumerShape::DirectField,
            expected_then_len: None,
        },
        Case {
            label: "two_stmt_else_chain_unary_direct_consumer",
            toggle: "Temp_bool_Variable_6",
            else_shape: ElseShape::TwoStmtChain,
            neg: NegShape::Unary,
            consumer: ConsumerShape::DirectField,
            expected_then_len: Some(1),
        },
        Case {
            label: "two_stmt_else_chain_not_pre_bool_direct_consumer",
            toggle: "Temp_bool_Variable_7",
            else_shape: ElseShape::TwoStmtChain,
            neg: NegShape::NotPreBoolCall,
            consumer: ConsumerShape::DirectField,
            expected_then_len: None,
        },
        Case {
            label: "two_stmt_else_chain_unary_aliased_consumer",
            toggle: "Temp_bool_Variable_8",
            else_shape: ElseShape::TwoStmtChain,
            neg: NegShape::Unary,
            consumer: ConsumerShape::AliasedField,
            expected_then_len: Some(2),
        },
        Case {
            label: "two_stmt_else_chain_not_pre_bool_aliased_consumer",
            toggle: "Temp_bool_Variable_9",
            else_shape: ElseShape::TwoStmtChain,
            neg: NegShape::NotPreBoolCall,
            consumer: ConsumerShape::AliasedField,
            expected_then_len: Some(2),
        },
    ];

    for case in cases {
        let neg = match case.neg {
            NegShape::Unary => not_unary(case.toggle),
            NegShape::NotPreBoolCall => not_pre_bool_call(case.toggle),
        };
        let consumers = match case.consumer {
            ConsumerShape::DirectField => vec![field_from_toggle(case.toggle)],
            ConsumerShape::AliasedField => {
                let alias = "$AliasTemp";
                let alias_setup = Stmt::Assignment {
                    lhs: var(alias),
                    rhs: var(case.toggle),
                    offset: 0x04,
                };
                let aliased_consumer = Stmt::Assignment {
                    lhs: Expr::FieldAccess {
                        recv: Box::new(var("self")),
                        field: "Mirror".to_string(),
                    },
                    rhs: var(alias),
                    offset: 0x08,
                };
                vec![alias_setup, aliased_consumer]
            }
        };
        let mut body = match case.else_shape {
            ElseShape::OneStmt => embedded_flip_body(case.toggle, neg, consumers),
            ElseShape::TwoStmtChain => {
                embedded_flip_two_stmt_chain_body(case.toggle, "$Not_PreBool", neg, consumers)
            }
        };

        recognize_latches(&mut body);

        assert_eq!(
            body.len(),
            1,
            "case {}: should collapse to one Latch",
            case.label
        );
        let Stmt::Latch {
            kind,
            body: latch_body,
            init,
            ..
        } = &body[0]
        else {
            panic!(
                "case {}: expected Stmt::Latch, got {:?}",
                case.label,
                stmt_kind(&body[0])
            );
        };
        assert!(init.is_empty(), "case {}: init should be empty", case.label);
        match kind {
            LatchKind::FlipFlop { gate_var, names } => {
                assert_eq!(gate_var, case.toggle, "case {}: gate_var", case.label);
                assert!(names.is_none(), "case {}: names should be None", case.label);
            }
            _ => panic!("case {}: expected LatchKind::FlipFlop", case.label),
        }
        if let Some(expected_len) = case.expected_then_len {
            assert_eq!(latch_body.len(), 1, "case {}: latch body len", case.label);
            let Stmt::Branch { then_body, .. } = &latch_body[0] else {
                panic!("case {}: expected Branch inside FlipFlop", case.label);
            };
            assert_eq!(
                then_body.len(),
                expected_len,
                "case {}: then_body len",
                case.label
            );
        }
    }
}
