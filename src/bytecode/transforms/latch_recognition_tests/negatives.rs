//! Negative-path / `_unchanged` tests across all latch recognizers. A
//! shape that doesn't match any recognizer's preconditions must leave
//! the body untouched.

use super::*;
use crate::bytecode::transforms::latch_recognition::recognize_latches;

#[test]
fn non_doonce_branch_unchanged() {
    let mut body = vec![Stmt::Branch {
        cond: Expr::Unary {
            op: UnaryOp::Not,
            operand: Box::new(var("SomeOtherFlag")),
        },
        then_body: vec![call_stmt("DoThing")],
        else_body: vec![],
        offset: 0x10,
    }];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn doonce_with_else_unchanged() {
    let gate = "Temp_bool_IsClosed_Variable_4";
    let mut body = vec![Stmt::Branch {
        cond: Expr::Unary {
            op: UnaryOp::Not,
            operand: Box::new(var(gate)),
        },
        then_body: vec![assign(gate, lit("true")), call_stmt("DoThing")],
        else_body: vec![call_stmt("ElseThing")],
        offset: 0x10,
    }];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn missing_gate_self_assign_unchanged() {
    let gate = "Temp_bool_IsClosed_Variable_5";
    let mut body = vec![Stmt::Branch {
        cond: Expr::Unary {
            op: UnaryOp::Not,
            operand: Box::new(var(gate)),
        },
        then_body: vec![call_stmt("DoThing")],
        else_body: vec![],
        offset: 0x10,
    }];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn flipflop_branch_alone_is_not_flipflop() {
    // A branch on a Temp_bool_Variable without a preceding toggle is not
    // a FlipFlop and must be left alone.
    let mut body = vec![Stmt::Branch {
        cond: var("Temp_bool_Variable_9"),
        then_body: vec![call_stmt("DoA")],
        else_body: vec![call_stmt("DoB")],
        offset: 0x10,
    }];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn flipflop_branch_on_unrelated_var_unchanged() {
    let mut body = vec![
        Stmt::Assignment {
            lhs: var("Temp_bool_Variable_2"),
            rhs: Expr::Unary {
                op: UnaryOp::Not,
                operand: Box::new(var("Temp_bool_Variable_2")),
            },
            offset: 0,
        },
        Stmt::Branch {
            cond: var("UnrelatedFlag"),
            then_body: vec![],
            else_body: vec![],
            offset: 0,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 2);
    assert!(matches!(body[1], Stmt::Branch { .. }));
}

#[test]
fn flipflop_chain_terminating_in_non_negation_unchanged() {
    // toggle = $temp; $temp = SomeCall(). Chain terminates at a call,
    // not !toggle, so this is NOT a FlipFlop.
    let mut body = vec![
        Stmt::Assignment {
            lhs: var("$temp"),
            rhs: call("SomeCall"),
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var("Temp_bool_Variable_4"),
            rhs: var("$temp"),
            offset: 0x14,
        },
        Stmt::Branch {
            cond: var("Temp_bool_Variable_4"),
            then_body: vec![call_stmt("DoA")],
            else_body: vec![call_stmt("DoB")],
            offset: 0x18,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 3);
    assert!(matches!(body[2], Stmt::Branch { .. }));
}

#[test]
fn compound_doonce_without_init_proof_is_left_alone() {
    // Gate-check + gate-set without any init evidence isn't a DoOnce.
    let gate_var = "Temp_bool_IsClosed_Variable";
    let mut body = vec![
        Stmt::Branch {
            cond: var(gate_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        assign(gate_var, lit("true")),
        call_stmt("DoStuff"),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 3, "no init proof - body should be unchanged");
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn scaffold_only_sub_body_is_left_alone() {
    // A body that's ENTIRELY scaffolding (e.g. an init pin viewed in
    // isolation) must not collapse to an empty DoOnce. The recognizer
    // bails before it would empty the caller's body.
    let init_var = "Temp_bool_Has_Been_Initd_Variable_2";
    let gate_var = "Temp_bool_IsClosed_Variable_2";
    let mut body = vec![
        Stmt::Branch {
            cond: var(init_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        assign(init_var, lit("true")),
        assign(gate_var, lit("true")),
    ];
    let original_len = body.len();

    recognize_latches(&mut body);

    assert_eq!(
        body.len(),
        original_len,
        "scaffold-only body must stay intact"
    );
}

#[test]
fn scaffold_leading_sequence_with_same_gate_in_tail_is_left_alone() {
    // A tail containing scaffold for the SAME gate variable as the
    // outer scaffold means the outer DoOnce's own scaffold leaked
    // into the tail (a different broken shape we still want to
    // surface by refusing to fold). Don't fold.
    let same_gate = "Temp_bool_IsClosed_Variable_5";
    let mut body = vec![doonce_scaffold_leading_sequence(
        "Temp_bool_Has_Been_Initd_Variable_5",
        "Temp_bool_IsClosed_Variable_5",
        vec![
            call_stmt("PerformMoveAction_SnapTurn"),
            // gate-set for the SAME outer DoOnce - looks broken.
            assign(same_gate, lit("true")),
        ],
    )];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    assert!(
        matches!(body[0], Stmt::Sequence { .. }),
        "same-gate scaffold in tail should leave the Sequence in place"
    );
}

#[test]
fn embedded_flip_with_no_consumers_is_not_flipflop() {
    // A toggle-branch with the flip in else but NO preceding consumers
    // that read toggle_var must NOT fire the embedded-flip arm. We have
    // no A/B body to put into the latch.
    let toggle = "Temp_bool_Variable_3";
    let mut body = vec![Stmt::Branch {
        cond: var(toggle),
        then_body: vec![],
        else_body: vec![Stmt::Assignment {
            lhs: var(toggle),
            rhs: not_unary(toggle),
            offset: 0x10,
        }],
        offset: 0x14,
    }];

    recognize_latches(&mut body);

    // No consumer — must remain a Branch.
    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], Stmt::Branch { .. }));
}

#[test]
fn embedded_flip_stops_consuming_at_non_toggle_stmt() {
    // Only stmts directly referencing toggle_var should be consumed.
    // An unrelated call separating two toggle-reading stmts stops the walk.
    let toggle = "Temp_bool_Variable_4";
    let unrelated = call_stmt("Unrelated");
    let consumer = field_from_toggle(toggle);
    // body: [unrelated, consumer, if (toggle) {} else { toggle = !toggle }]
    let mut body = embedded_flip_body(toggle, not_unary(toggle), vec![unrelated, consumer]);

    recognize_latches(&mut body);

    // Walk backward: consumer (reads toggle) is consumed; unrelated stops it.
    // Latch collapses with 1 consumer. unrelated remains as sibling.
    assert_eq!(body.len(), 2, "unrelated stmt should stay as sibling");
    assert!(matches!(body[0], Stmt::Call { .. }));
    assert!(matches!(body[1], Stmt::Latch { .. }));
}

#[test]
fn embedded_flip_then_body_not_empty_unchanged() {
    // If then_body is non-empty the standard FlipFlop or the branch
    // should handle it, not the embedded-flip arm.
    let toggle = "Temp_bool_Variable_5";
    let consumer = field_from_toggle(toggle);
    let mut body = vec![
        consumer,
        Stmt::Branch {
            cond: var(toggle),
            then_body: vec![call_stmt("DoA")],
            else_body: vec![Stmt::Assignment {
                lhs: var(toggle),
                rhs: not_unary(toggle),
                offset: 0x10,
            }],
            offset: 0x14,
        },
    ];

    recognize_latches(&mut body);

    // Non-empty then_body means neither standard nor embedded arm fires.
    assert_eq!(body.len(), 2);
    assert!(matches!(body[1], Stmt::Branch { .. }));
}

#[test]
fn reset_doonce_with_true_true_unchanged() {
    // `IsClosed = true; Has_Been_Initd = true` is the gate-set pattern
    // a real DoOnce uses to seed itself, NOT a reset. Decline.
    let mut body = vec![
        assign("Temp_bool_IsClosed_Variable_4", lit("true")),
        assign("Temp_bool_Has_Been_Initd_Variable_4", lit("true")),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 2);
    assert!(matches!(body[0], Stmt::Assignment { .. }));
    assert!(matches!(body[1], Stmt::Assignment { .. }));
}

#[test]
fn reset_doonce_with_false_false_unchanged() {
    let mut body = vec![
        assign("Temp_bool_IsClosed_Variable_4", lit("false")),
        assign("Temp_bool_Has_Been_Initd_Variable_4", lit("false")),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 2);
    assert!(matches!(body[0], Stmt::Assignment { .. }));
    assert!(matches!(body[1], Stmt::Assignment { .. }));
}

#[test]
fn reset_doonce_lone_gate_clear_unchanged() {
    // Single `IsClosed = false` with no following init-touch is not a
    // ResetDoOnce expansion, leave it alone for dead-elim to handle.
    let mut body = vec![
        assign("Temp_bool_IsClosed_Variable_4", lit("false")),
        call_stmt("Foo"),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 2);
    assert!(matches!(body[0], Stmt::Assignment { .. }));
}
