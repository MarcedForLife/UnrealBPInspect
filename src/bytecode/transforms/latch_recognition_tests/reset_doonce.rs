//! ResetDoOnce gate-reset pair recognizer tests (positive + post-chain
//! absorption). `_unchanged` cases live in `negatives.rs`.

use super::*;
use crate::bytecode::transforms::latch_recognition::recognize_latches;

/// Parameterised driver for the canonical reset-pair shape: two
/// assignments at the same body level that should fold into a
/// `ResetDoOnce(<name>)` Stmt::Call.
///
/// Each case carries the (lhs, rhs) literal-string pair the BP compiler
/// would emit for the gate-side and init-side assignments, plus the
/// expected `ResetDoOnce` argument name. `label` mirrors the original
/// individual test name so failure messages identify the offending input.
fn run_reset_pair_case(label: &str, pair: Vec<Stmt>, expected_name: &str) {
    let mut body = pair;
    recognize_latches(&mut body);
    assert_eq!(body.len(), 1, "case {}: expected single Stmt", label);
    assert_reset_doonce_call(&body[0], expected_name);
}

#[test]
fn reset_doonce_pair_cases() {
    struct Case {
        label: &'static str,
        pair: Vec<Stmt>,
        expected_name: &'static str,
    }
    let cases = vec![
        Case {
            label: "matching_suffix",
            pair: reset_doonce_pair("_4"),
            expected_name: "DoOnce_4",
        },
        Case {
            label: "bare_names",
            pair: reset_doonce_pair(""),
            expected_name: "DoOnce",
        },
        Case {
            // The BP compiler can allocate the gate and init halves from
            // different temp slots when the same K2Node DoOnce is referenced
            // across multiple events (e.g. one event reaching a shared
            // macro). The pair shape is still a reset.
            label: "mismatched_suffix",
            pair: vec![
                assign("Temp_bool_IsClosed_Variable_2", lit("false")),
                assign("Temp_bool_Has_Been_Initd_Variable", lit("true")),
            ],
            // Display name derived from the gate-side suffix.
            expected_name: "DoOnce_2",
        },
        Case {
            // Init-then-gate ordering is also emitted by the BP compiler
            // (observed in an else arm).
            label: "reverse_order",
            pair: vec![
                assign("Temp_bool_Has_Been_Initd_Variable", lit("true")),
                assign("Temp_bool_IsClosed_Variable_2", lit("false")),
            ],
            expected_name: "DoOnce_2",
        },
    ];
    for case in cases {
        run_reset_pair_case(case.label, case.pair, case.expected_name);
    }
}

#[test]
fn reset_doonce_inside_latch_body_folds() {
    // The compound DoOnce's user body sometimes contains an inline
    // ResetDoOnce(<other macro>) pair (a then-arm shape). The recursive
    // walker must reach that body and fold the pair before dead-elim runs.
    let inner_pair = reset_doonce_pair("_1");
    let outer_gate = "Temp_bool_IsClosed_Variable_2";
    let mut user_body = vec![call_stmt("AttemptGrip")];
    user_body.extend(inner_pair);
    let mut body = vec![doonce_branch(outer_gate, user_body)];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch { body: inner, .. } = &body[0] else {
        panic!("expected Stmt::Latch");
    };
    // Outer body now holds the user call followed by the rewritten
    // ResetDoOnce(...) Stmt::Call rather than the bare assignment pair.
    assert_eq!(inner.len(), 2);
    assert!(matches!(inner[0], Stmt::Call { .. }));
    assert_reset_doonce_call(&inner[1], "DoOnce_1");
}

#[test]
fn post_chain_reset_absorbs_into_empty_else() {
    // An outer Branch whose then-arm folds into a DoOnce Latch, immediately
    // followed by the synthetic ResetDoOnce produced by the gate-reset
    // pair recognizer at the same body level.
    let outer_gate = "Temp_bool_IsClosed_Variable_5";
    let then_body = vec![call_stmt("PerformMoveAction_SnapTurn")];
    let outer_branch = doonce_branch(outer_gate, then_body);
    let mut body = vec![Stmt::Branch {
        cond: var("$GreaterEqual"),
        then_body: vec![outer_branch],
        else_body: vec![],
        offset: 0x100,
    }];
    body.extend(reset_doonce_pair("_5"));

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Branch");
    };
    assert_eq!(then_body.len(), 1);
    assert!(matches!(&then_body[0], Stmt::Latch { .. }));
    assert_eq!(else_body.len(), 1);
    assert_reset_doonce_call(&else_body[0], "DoOnce_5");
}

#[test]
fn post_chain_reset_skipped_when_else_already_populated() {
    // Branches with an already-populated else must not have a trailing
    // ResetDoOnce moved into them.
    let outer_gate = "Temp_bool_IsClosed_Variable_5";
    let then_body = vec![call_stmt("PerformMoveAction_SnapTurn")];
    let outer_branch = doonce_branch(outer_gate, then_body);
    let mut body = vec![
        Stmt::Branch {
            cond: var("$GreaterEqual"),
            then_body: vec![outer_branch],
            else_body: vec![call_stmt("ExistingElse")],
            offset: 0x100,
        },
        // A trailing reset that doesn't belong to this branch.
        Stmt::Call {
            func: var("ResetDoOnce"),
            args: vec![var("DoOnce_99")],
            offset: 0x200,
        },
    ];

    recognize_latches(&mut body);

    // Both stmts stay siblings; reset is not absorbed.
    assert_eq!(body.len(), 2);
    let Stmt::Branch { else_body, .. } = &body[0] else {
        panic!("expected Stmt::Branch");
    };
    assert_eq!(else_body.len(), 1);
    assert!(matches!(&else_body[0], Stmt::Call { .. }));
}

#[test]
fn post_chain_reset_skipped_when_branch_lacks_doonce() {
    // A Branch with empty else but no DoOnce inside its then arm
    // shouldn't claim a trailing ResetDoOnce. Without the DoOnce
    // signal the trailing reset could belong to entirely different
    // structure.
    let mut body = vec![
        Stmt::Branch {
            cond: var("$cond"),
            then_body: vec![call_stmt("DoSomething")],
            else_body: vec![],
            offset: 0x100,
        },
        Stmt::Call {
            func: var("ResetDoOnce"),
            args: vec![var("DoOnce_99")],
            offset: 0x200,
        },
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 2);
    assert!(matches!(&body[0], Stmt::Branch { .. }));
    assert!(matches!(&body[1], Stmt::Call { .. }));
}
