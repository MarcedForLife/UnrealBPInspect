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
    let mut user_body = vec![call_stmt("TryAcquire")];
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

fn named_latch(name: &str, gate: &str) -> Stmt {
    Stmt::Latch {
        kind: crate::bytecode::stmt::LatchKind::DoOnce {
            name: name.into(),
            gate_var: gate.into(),
        },
        init: Vec::new(),
        body: vec![call_stmt("PerformAction")],
        offset: 0,
    }
}

fn reset_gate(name: &str) -> Stmt {
    Stmt::Call {
        func: var("ResetDoOnce"),
        args: vec![var(name)],
        offset: 0,
    }
}

fn latch_name(stmt: &Stmt) -> &str {
    match stmt {
        Stmt::Latch {
            kind: crate::bytecode::stmt::LatchKind::DoOnce { name, .. },
            ..
        } => name,
        _ => panic!("expected a DoOnce latch"),
    }
}

#[test]
fn shared_gate_has_one_name_across_event_entries_and_resume_bodies() {
    use crate::bytecode::asset::Event;
    use crate::bytecode::transforms::latch_recognition::rewrite_asset_wide_reset_doonce_names;
    let gate = "Temp_bool_IsClosed_Variable_7";
    let mut events = vec![
        Event {
            name: "StartAction".into(),
            body: vec![named_latch("PerformAction", gate)],
            export_index: None,
        },
        Event {
            name: "ResumeAction".into(),
            body: vec![named_latch("DoOnce_7", gate), reset_gate("DoOnce_7")],
            export_index: None,
        },
    ];
    let mut resumes = std::collections::BTreeMap::from([(100, vec![reset_gate("DoOnce_7")])]);
    rewrite_asset_wide_reset_doonce_names(&mut [], &mut events, &mut resumes);
    assert_eq!(latch_name(&events[0].body[0]), "PerformAction");
    assert_eq!(latch_name(&events[1].body[0]), "PerformAction");
    assert_reset_doonce_call(&events[1].body[1], "PerformAction");
    assert_reset_doonce_call(&resumes[&100][0], "PerformAction");
}

#[test]
fn independent_gates_calling_the_same_action_keep_distinct_reset_targets() {
    use crate::bytecode::asset::Event;
    use crate::bytecode::transforms::latch_recognition::rewrite_asset_wide_reset_doonce_names;
    let mut events = vec![
        Event {
            name: "FirstInput".into(),
            body: vec![
                named_latch("PerformAction", "Temp_bool_IsClosed_Variable_3"),
                reset_gate("DoOnce_5"),
            ],
            export_index: None,
        },
        Event {
            name: "SecondInput".into(),
            body: vec![
                named_latch("PerformAction", "Temp_bool_IsClosed_Variable_5"),
                reset_gate("DoOnce_3"),
            ],
            export_index: None,
        },
    ];
    rewrite_asset_wide_reset_doonce_names(
        &mut [],
        &mut events,
        &mut std::collections::BTreeMap::new(),
    );
    assert_eq!(latch_name(&events[0].body[0]), "DoOnce_3");
    assert_eq!(latch_name(&events[1].body[0]), "DoOnce_5");
    assert_reset_doonce_call(&events[0].body[1], "DoOnce_5");
    assert_reset_doonce_call(&events[1].body[1], "DoOnce_3");
}

#[test]
fn local_function_gates_do_not_alias_ubergraph_gates() {
    use crate::bytecode::asset::{Event, Function};
    use crate::bytecode::transforms::latch_recognition::rewrite_asset_wide_reset_doonce_names;
    let gate = "Temp_bool_IsClosed_Variable_3";
    let mut functions = vec![Function {
        name: "FunctionScope".into(),
        body: vec![named_latch("FunctionAction", gate), reset_gate("DoOnce_3")],
        export_index: None,
    }];
    let mut events = vec![Event {
        name: "EventScope".into(),
        body: vec![named_latch("EventAction", gate), reset_gate("DoOnce_3")],
        export_index: None,
    }];
    rewrite_asset_wide_reset_doonce_names(
        &mut functions,
        &mut events,
        &mut std::collections::BTreeMap::new(),
    );
    assert_eq!(latch_name(&functions[0].body[0]), "FunctionAction");
    assert_reset_doonce_call(&functions[0].body[1], "FunctionAction");
    assert_eq!(latch_name(&events[0].body[0]), "EventAction");
    assert_reset_doonce_call(&events[0].body[1], "EventAction");
}

#[test]
fn action_names_cannot_collide_with_another_gates_canonical_identifier() {
    use crate::bytecode::transforms::latch_recognition::rewrite_reset_doonce_names;
    let mut body = vec![
        named_latch("DoOnce_5", "Temp_bool_IsClosed_Variable_3"),
        named_latch("OtherAction", "Temp_bool_IsClosed_Variable_5"),
        reset_gate("DoOnce_3"),
        reset_gate("DoOnce_5"),
    ];
    rewrite_reset_doonce_names(&mut body);
    assert_eq!(latch_name(&body[0]), "DoOnce_3");
    assert_eq!(latch_name(&body[1]), "OtherAction");
    assert_reset_doonce_call(&body[2], "DoOnce_3");
    assert_reset_doonce_call(&body[3], "OtherAction");
}

#[test]
fn an_unseen_reset_gate_still_reserves_its_identifier() {
    use crate::bytecode::transforms::latch_recognition::rewrite_reset_doonce_names;
    let mut body = vec![
        named_latch("DoOnce_5", "Temp_bool_IsClosed_Variable_3"),
        reset_gate("DoOnce_5"),
    ];
    rewrite_reset_doonce_names(&mut body);
    assert_eq!(latch_name(&body[0]), "DoOnce_3");
    assert_reset_doonce_call(&body[1], "DoOnce_5");
}
