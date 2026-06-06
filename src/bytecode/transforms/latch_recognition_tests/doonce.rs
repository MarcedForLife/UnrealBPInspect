//! DoOnce recognizer tests (positive recognitions only; `_unchanged` and
//! decline cases live in `negatives.rs`).

use super::*;
use crate::bytecode::stmt::LatchKind;
use crate::bytecode::transforms::latch_recognition::recognize_latches;
use crate::bytecode::transforms::test_fixtures::stmt_kind;

#[test]
fn recognizes_simple_doonce() {
    let mut body = vec![doonce_branch(
        "Temp_bool_IsClosed_Variable_3",
        vec![call_stmt("ApplyDamage")],
    )];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind,
        init,
        body: inner,
        ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert!(init.is_empty());
    assert_eq!(inner.len(), 1);
    match kind {
        LatchKind::DoOnce { name, .. } => {
            assert_eq!(name, "ApplyDamage");
        }
        _ => panic!("expected LatchKind::DoOnce"),
    }
}

#[test]
fn nested_doonce_inside_doonce() {
    let outer_gate = "Temp_bool_IsClosed_Variable_1";
    let inner_gate = "Temp_bool_IsClosed_Variable_2";
    let inner = doonce_branch(inner_gate, vec![call_stmt("InnerCall")]);
    let mut body = vec![doonce_branch(
        outer_gate,
        vec![call_stmt("OuterCall"), inner],
    )];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind: outer_kind,
        body: outer_body,
        ..
    } = &body[0]
    else {
        panic!("outer should be Latch");
    };
    match outer_kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "OuterCall"),
        _ => panic!("outer LatchKind should be DoOnce"),
    }
    // Outer body has the call plus the (now-rewritten) inner Latch.
    assert_eq!(outer_body.len(), 2);
    let Stmt::Latch {
        kind: inner_kind, ..
    } = &outer_body[1]
    else {
        panic!("inner should be Latch");
    };
    match inner_kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "InnerCall"),
        _ => panic!("inner LatchKind should be DoOnce"),
    }
}

#[test]
fn falls_back_to_gate_suffix_when_body_has_no_calls() {
    let gate = "Temp_bool_IsClosed_Variable_7";
    let mut body = vec![doonce_branch(gate, vec![assign("X", lit("1"))])];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch { kind, .. } = &body[0] else {
        panic!("expected Latch");
    };
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "DoOnce_7"),
        _ => panic!("expected DoOnce"),
    }
}

#[test]
fn library_call_only_uses_library_name_as_fallback() {
    let gate = "Temp_bool_IsClosed_Variable_9";
    let mut body = vec![doonce_branch(
        gate,
        vec![Stmt::Call {
            func: call("PrintString"),
            args: vec![],
            offset: 0,
        }],
    )];

    recognize_latches(&mut body);

    let Stmt::Latch { kind, .. } = &body[0] else {
        panic!("expected Latch");
    };
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "PrintString"),
        _ => panic!("expected DoOnce"),
    }
}

#[test]
fn recognizes_compound_doonce_outer_call_then_sequence() {
    // A compound DoOnce shape: scaffold Sequence runs
    // first (gate-check + gate-set), then the user body Call. In
    // exec order, the scaffold sits at the lower index because it
    // gates execution before reaching the body.
    let mut body = vec![
        doonce_scaffold_sequence(
            "Temp_bool_Has_Been_Initd_Variable_3",
            "Temp_bool_IsClosed_Variable_3",
        ),
        call_stmt("ReleaseGrip"),
    ];

    recognize_latches(&mut body);

    assert_eq!(
        body.len(),
        1,
        "compound DoOnce should collapse to a single Latch"
    );
    let Stmt::Latch {
        kind, body: inner, ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert_eq!(inner.len(), 1);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "ReleaseGrip"),
        _ => panic!("expected LatchKind::DoOnce"),
    }
}

#[test]
fn recognizes_compound_doonce_with_outer_gate_check() {
    // A compound DoOnce shape: outer body interleaves
    // gate-check, gate-set, user body, then the scaffold-only Sequence.
    let init_var = "Temp_bool_Has_Been_Initd_Variable_1";
    let gate_var = "Temp_bool_IsClosed_Variable";
    let mut body = vec![
        Stmt::Branch {
            cond: var(gate_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x10,
        },
        assign(gate_var, lit("true")),
        call_stmt("ReleaseGrip"),
        doonce_scaffold_sequence(init_var, gate_var),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind, body: inner, ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert_eq!(inner.len(), 1);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "ReleaseGrip"),
        _ => panic!("expected LatchKind::DoOnce"),
    }
}

#[test]
fn recognizes_scaffold_leading_sequence_with_embedded_user_body() {
    // Scaffold-leading shape: outer if-arm contains only a Sequence whose
    // gate pin trails into the user body. The recognizer should pull the
    // tail out and wrap it in a DoOnce.
    let mut body = vec![doonce_scaffold_leading_sequence(
        "Temp_bool_Has_Been_Initd_Variable_5",
        "Temp_bool_IsClosed_Variable_5",
        vec![call_stmt("PerformMoveAction_SnapTurn")],
    )];

    recognize_latches(&mut body);

    assert_eq!(
        body.len(),
        1,
        "scaffold-leading Sequence should collapse to one Latch"
    );
    let Stmt::Latch {
        kind, body: inner, ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[0]));
    };
    assert_eq!(inner.len(), 1);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "PerformMoveAction_SnapTurn"),
        _ => panic!("expected LatchKind::DoOnce"),
    }
}

#[test]
fn scaffold_leading_sequence_with_other_doonce_in_tail_folds() {
    // A trailing tail that contains a gate-set assignment for ANOTHER
    // DoOnce (different gate-var suffix) is the inline ResetDoOnce
    // expansion of a sibling macro. A paired-event compound shape
    // emits this pattern: the
    // outer DoOnce body contains an inline reset for the paired
    // event's DoOnce. Fold the outer wrap; the inline reset survives
    // as raw assignments inside the user body.
    let other_gate = "Temp_bool_IsClosed_Variable_99";
    let mut body = vec![doonce_scaffold_leading_sequence(
        "Temp_bool_Has_Been_Initd_Variable_5",
        "Temp_bool_IsClosed_Variable_5",
        vec![
            call_stmt("PerformMoveAction_SnapTurn"),
            // gate-set for an unrelated DoOnce sneaking into the tail.
            assign(other_gate, lit("true")),
        ],
    )];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        body: inner, kind, ..
    } = &body[0]
    else {
        panic!("expected Stmt::Latch");
    };
    match kind {
        LatchKind::DoOnce { name, .. } => assert_eq!(name, "PerformMoveAction_SnapTurn"),
        _ => panic!("expected LatchKind::DoOnce"),
    }
    // Inner body has the user call plus the inlined reset assignment.
    assert_eq!(inner.len(), 2);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
    assert!(matches!(&inner[1], Stmt::Assignment { .. }));
}

#[test]
fn empty_sequence_alongside_real_doonce_is_dropped_into_wrap() {
    // The BP partitioner sometimes leaves a stray empty Sequence
    // alongside the real scaffold. The recognizer treats it as
    // a (non-substantive) scaffold-only Sequence and folds it away
    // when the surrounding body matches a DoOnce shape. The user
    // body lands inside the Latch with no leaked empty Sequence.
    let mut body = vec![
        Stmt::Sequence {
            pins: vec![vec![], vec![]],
            offset: 0x10,
        },
        doonce_scaffold_sequence(
            "Temp_bool_Has_Been_Initd_Variable_6",
            "Temp_bool_IsClosed_Variable_6",
        ),
        call_stmt("UserCall"),
    ];

    recognize_latches(&mut body);

    assert_eq!(body.len(), 1);
    let Stmt::Latch { body: inner, .. } = &body[0] else {
        panic!("expected Stmt::Latch");
    };
    // User body has only the call. The empty Sequence is gone.
    assert_eq!(inner.len(), 1);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
}

#[test]
fn folds_user_body_pin_with_sibling_scaffold_pin() {
    // Models an else-arm pre-recognition shape:
    // one Sequence carries the user body in one pin and the macro's
    // post-body gate-clear pair in another pin, while a sibling
    // Sequence holds the full init-check + init-set + gate-set scaffold.
    // The cross-Sequence pass folds the user body into a DoOnce wrap,
    // consumes the scaffold Sequence by suffix matching, AND lifts the
    // gate-clear pair (post Pass -1 fold to `Call(ResetDoOnce(DoOnce_4))`)
    // as a leading sibling so the cross-macro reset survives.
    let gate_var = "Temp_bool_IsClosed_Variable_4";
    let init_var = "Temp_bool_Has_Been_Initd_Variable_4";
    let user_body_sequence = Stmt::Sequence {
        pins: vec![
            vec![
                assign(gate_var, lit("false")),
                assign(init_var, lit("true")),
            ],
            vec![call_stmt("ReleaseGrip")],
        ],
        offset: 0x100,
    };
    let scaffold_sequence = doonce_scaffold_sequence(init_var, gate_var);
    let mut body = vec![user_body_sequence, scaffold_sequence];

    recognize_latches(&mut body);

    // Expected: [Call(ResetDoOnce(DoOnce_4)), Latch::DoOnce(ReleaseGrip)].
    assert_eq!(
        body.len(),
        2,
        "expected lifted ResetDoOnce + Latch, scaffold Sequence consumed"
    );
    super::assert_reset_doonce_call(&body[0], "DoOnce_4");
    let Stmt::Latch {
        kind,
        body: inner,
        init,
        ..
    } = &body[1]
    else {
        panic!("expected Stmt::Latch, got {:?}", stmt_kind(&body[1]));
    };
    assert!(init.is_empty(), "DoOnce latches carry no init clause");
    match kind {
        LatchKind::DoOnce { name, gate_var: g } => {
            assert_eq!(name, "ReleaseGrip");
            assert_eq!(g, gate_var);
        }
        _ => panic!("expected LatchKind::DoOnce"),
    }
    assert_eq!(inner.len(), 1);
    assert!(matches!(&inner[0], Stmt::Call { .. }));
}

#[test]
fn reset_then_call_does_not_synthesise_phantom_doonce() {
    // Models the inside of an outer DoOnce body:
    // a gate-CLEAR pair (the macro's ResetDoOnce, which Pass -1 folds into
    // `Call(ResetDoOnce(DoOnce_4))`) followed by a plain user call, with NO
    // real DoOnce-OPEN anywhere. A reset re-arms an existing gate; it must
    // NOT seed a fresh DoOnce wrap around the trailing call. The user call
    // stays a bare sibling next to the reset, not a phantom second latch.
    let mut body = vec![Stmt::Sequence {
        pins: vec![reset_doonce_pair("_4"), vec![call_stmt("PrintString")]],
        offset: 0x200,
    }];

    recognize_latches(&mut body);

    fn count_latches(stmt: &Stmt, count: &mut usize) {
        if matches!(stmt, Stmt::Latch { .. }) {
            *count += 1;
        }
        match stmt {
            Stmt::Sequence { pins, .. } => {
                for inner in pins.iter().flatten() {
                    count_latches(inner, count);
                }
            }
            Stmt::Latch { body, .. } => {
                for inner in body {
                    count_latches(inner, count);
                }
            }
            _ => {}
        }
    }
    let mut latch_count = 0;
    for stmt in &body {
        count_latches(stmt, &mut latch_count);
    }
    assert_eq!(
        latch_count,
        0,
        "a reset + user call must not synthesise a phantom DoOnce wrap; got body {:?}",
        body.iter().map(stmt_kind).collect::<Vec<_>>()
    );
}
