use super::*;
use crate::bytecode::expr::LiteralValue;

/// The single `Var` argument of a `Call(ResetDoOnce(<arg>))`, for the
/// leading-duplicate comparison. `None` for any other shape.
fn reset_doonce_arg(stmt: &Stmt) -> Option<String> {
    let Stmt::Call { func, args, .. } = stmt else {
        return None;
    };
    if call_func_name(func).as_deref() != Some(RESET_DOONCE_CALL_NAME) || args.len() != 1 {
        return None;
    }
    match &args[0] {
        crate::bytecode::expr::Expr::Var(name) => Some(name.clone()),
        crate::bytecode::expr::Expr::Literal(LiteralValue::Text(value)) => Some(value.clone()),
        _ => None,
    }
}

fn reset_call(target: &str) -> Stmt {
    Stmt::Call {
        func: crate::bytecode::expr::Expr::Var("ResetDoOnce".into()),
        args: vec![crate::bytecode::expr::Expr::Var(target.into())],
        offset: 10,
    }
}

const SYNTH_GATE_VAR: &str = "Temp_bool_IsClosed_Variable_0";

fn user_call(name: &str) -> Stmt {
    Stmt::Call {
        func: crate::bytecode::expr::Expr::Var(name.into()),
        args: Vec::new(),
        offset: 20,
    }
}

fn synth_plan(target: &str) -> SynthWrapPlan {
    SynthWrapPlan {
        gate_var: SYNTH_GATE_VAR.into(),
        target_name: Some(target.into()),
        body_offsets: vec![20, 10],
        rekey_latch_named: None,
    }
}

/// `apply_doonce_wrap_synthesis` wraps a flat guarded call plus its
/// trailing `ResetDoOnce` into a `Latch{DoOnce}`, preserving the gate
/// target and dropping a duplicate emission of the same bytecode offset.
#[test]
fn synth_apply_wraps_flat_guarded_call() {
    let mut body = vec![
        reset_call("DoOnce_3"),
        user_call("BeginAction"),
        reset_call("DoOnce_3"),
    ];
    let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(wrapped, 1);
    // Leading duplicate reset dropped, single Latch remains.
    assert_eq!(body.len(), 1);
    let Stmt::Latch {
        kind: LatchKind::DoOnce { name, gate_var },
        body: gated,
        ..
    } = &body[0]
    else {
        panic!("expected synthesized Latch{{DoOnce}} at body[0]");
    };
    assert_eq!(name, "BeginAction");
    assert_eq!(gate_var, SYNTH_GATE_VAR);
    // The guarded call is followed by the reset of its original gate.
    assert_eq!(gated.len(), 2);
    assert!(
        matches!(&gated[0], Stmt::Call { func, .. } if call_func_name(func).as_deref() == Some("BeginAction"))
    );
    assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("DoOnce_3"));
}

/// When the gate is already wrapped (`locate_doonce` finds it), the
/// apply step does NOT double-wrap and reports zero synthesized wraps.
#[test]
fn synth_apply_skips_already_wrapped_gate() {
    let mut body = vec![Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: "BeginAction".into(),
            gate_var: SYNTH_GATE_VAR.into(),
        },
        init: Vec::new(),
        body: vec![user_call("BeginAction")],
        offset: 0,
    }];
    let before = body.clone();
    let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(wrapped, 0);
    // Byte-identical: no second Latch, body unchanged.
    assert_eq!(body.len(), before.len());
    assert!(matches!(&body[0], Stmt::Latch { body, .. } if body.len() == 1));
}

/// A nearby latch never overrides the reset target recorded in bytecode.
#[test]
fn synth_apply_preserves_reset_target_with_one_other_latch() {
    let mut body = vec![
        doonce_latch_named(
            "EndAction",
            "Temp_bool_Other_0",
            vec![user_call("EndAction")],
        ),
        user_call("BeginAction"),
        reset_call("DoOnce_3"),
    ];
    let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(wrapped, 1);
    let gated = synthesized_gated_body(&body, "BeginAction");
    assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("DoOnce_3"));
}

/// Reset-target fallback ambiguity: with no plan-time sibling and two or
/// more other recognized DoOnce latches, the captured reset is left
/// untouched (its unresolved fallback name).
#[test]
fn synth_apply_reset_untouched_when_ambiguous() {
    let mut body = vec![
        doonce_latch_named("EndAction", "Temp_bool_A_0", Vec::new()),
        doonce_latch_named("DropItem", "Temp_bool_B_0", Vec::new()),
        user_call("BeginAction"),
        reset_call("DoOnce_3"),
    ];
    let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(wrapped, 1);
    let gated = synthesized_gated_body(&body, "BeginAction");
    assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("DoOnce_3"));
}

fn doonce_latch_named(name: &str, gate_var: &str, body: Vec<Stmt>) -> Stmt {
    Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: name.into(),
            gate_var: gate_var.into(),
        },
        init: Vec::new(),
        body,
        offset: 0,
    }
}

/// Extract the gated body of the synthesized `Latch{DoOnce}` named
/// `name`, searching the top level of `body`.
fn synthesized_gated_body<'a>(body: &'a [Stmt], name: &str) -> &'a [Stmt] {
    body.iter()
        .find_map(|stmt| match stmt {
            Stmt::Latch {
                kind: LatchKind::DoOnce {
                    name: latch_name, ..
                },
                body: gated,
                ..
            } if latch_name == name => Some(gated.as_slice()),
            _ => None,
        })
        .expect("synthesized Latch present")
}

/// Positive body-before-scaffold discriminator: fires only when the
/// POP/continuation precedes the PUSH on disk. Weakening this (so an
/// in-range / normally-laid-out node fires) breaks the over-fire guard.
#[test]
fn synth_body_before_scaffold_predicate() {
    assert!(is_body_before_scaffold(0x10, 0x40));
    assert!(!is_body_before_scaffold(0x40, 0x40));
    assert!(!is_body_before_scaffold(0x80, 0x40));
}

/// Negative gate-set discriminator: every gate-SET must lie outside the
/// event's owned ranges. A gate-SET inside an owned range means the
/// scaffold is reachable, so synthesis must not fire.
#[test]
fn synth_gate_sets_out_of_range_predicate() {
    let owned = [0x00..0x50usize, 0x80..0xa0usize];
    assert!(all_gate_sets_out_of_range(&[0x100, 0x200], &owned));
    assert!(!all_gate_sets_out_of_range(&[0x100, 0x20], &owned));
    assert!(!all_gate_sets_out_of_range(&[0x90], &owned));
    // No owned ranges: every gate-set is trivially out of range.
    assert!(all_gate_sets_out_of_range(&[0x10], &[]));
}

#[test]
fn displaced_reset_follows_its_guarded_call_inside_the_latch() {
    let mut body = vec![reset_call("DoOnce_3"), user_call("BeginAction")];
    apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(body.len(), 1);
    let gated = synthesized_gated_body(&body, "BeginAction");
    assert_eq!(gated.len(), 2);
    assert_eq!(gated[0].offset(), 20);
    assert_eq!(gated[1].offset(), 10);
    assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("DoOnce_3"));
}

#[test]
fn same_call_name_and_reset_name_at_other_offsets_are_not_captured() {
    let mut earlier_call = user_call("BeginAction");
    let Stmt::Call { offset, .. } = &mut earlier_call else {
        unreachable!()
    };
    *offset = 100;
    let mut unrelated_reset = reset_call("DoOnce_3");
    let Stmt::Call { offset, .. } = &mut unrelated_reset else {
        unreachable!()
    };
    *offset = 110;
    let mut body = vec![
        earlier_call,
        unrelated_reset,
        reset_call("DoOnce_3"),
        user_call("BeginAction"),
    ];
    apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    assert_eq!(body.len(), 3);
    assert_eq!(body[0].offset(), 100);
    assert_eq!(body[1].offset(), 110);
    let gated = synthesized_gated_body(&body, "BeginAction");
    assert_eq!(
        gated.iter().map(Stmt::offset).collect::<Vec<_>>(),
        vec![20, 10]
    );
}

#[test]
fn displaced_reset_does_not_cross_a_branch_arm() {
    let mut body = vec![Stmt::Branch {
        cond: crate::bytecode::expr::Expr::Var("Enabled".into()),
        then_body: vec![user_call("BeginAction")],
        else_body: vec![reset_call("DoOnce_3")],
        offset: 0,
    }];
    apply_doonce_wrap_synthesis(&mut body, &[synth_plan("BeginAction")]);
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[0]
    else {
        unreachable!()
    };
    assert_eq!(synthesized_gated_body(then_body, "BeginAction").len(), 1);
    assert_eq!(reset_doonce_arg(&else_body[0]).as_deref(), Some("DoOnce_3"));
}

#[test]
fn body_offsets_follow_backwards_jumps_and_stop_at_flow_boundaries() {
    use crate::bytecode::opcodes::*;
    let graph = OpcodeGraph {
        boundaries: [10, 11, 12, 20, 21, 22, 30].into_iter().collect(),
        successors: [
            (20, vec![21]),
            (21, vec![22]),
            (22, vec![10]),
            (10, vec![11]),
            (11, vec![12]),
            (12, vec![30]),
        ]
        .into_iter()
        .collect(),
        opcodes: [
            (20, EX_LOCAL_FINAL_FUNCTION),
            (21, EX_TRACEPOINT),
            (22, EX_JUMP),
            (10, EX_LET_BOOL),
            (11, EX_LET_BOOL),
            (12, EX_POP_EXECUTION_FLOW),
            (30, EX_LET_BOOL),
        ]
        .into_iter()
        .collect(),
        flow_frames: Vec::new(),
    };
    assert_eq!(
        straight_line_body_offsets(&graph, 20, &[0..40, 50..60]),
        vec![20, 21, 22, 10, 11]
    );
}

#[test]
fn body_offsets_do_not_prove_resets_after_conditional_successors() {
    use crate::bytecode::opcodes::*;
    let graph = OpcodeGraph {
        boundaries: [10, 20, 21, 30].into_iter().collect(),
        successors: [(20, vec![21]), (21, vec![10, 30])].into_iter().collect(),
        opcodes: [
            (20, EX_LOCAL_FINAL_FUNCTION),
            (21, EX_JUMP_IF_NOT),
            (10, EX_LET_BOOL),
            (30, EX_LET_BOOL),
        ]
        .into_iter()
        .collect(),
        flow_frames: Vec::new(),
    };
    assert_eq!(
        straight_line_body_offsets(&graph, 20, &[0..40, 50..60]),
        vec![20, 21]
    );
}

#[test]
fn graph_call_elsewhere_does_not_remove_an_independent_nested_gate() {
    let mut body = vec![Stmt::Branch {
        cond: crate::bytecode::expr::Expr::Var("Enabled".into()),
        then_body: vec![user_call("BeginAction")],
        else_body: vec![doonce_latch_named(
            "Outer",
            SYNTH_GATE_VAR,
            vec![doonce_latch_named(
                "Inner",
                "Temp_bool_IsClosed_Variable_3",
                vec![],
            )],
        )],
        offset: 0,
    }];
    unwrap_misbound_latch(
        &mut body,
        &synth_plan("BeginAction"),
        &K2NodeByteMap::empty(),
    );
    let Stmt::Branch { else_body, .. } = &body[0] else {
        unreachable!()
    };
    assert!(
        matches!(&else_body[0], Stmt::Latch { body, .. } if matches!(body[0], Stmt::Latch { .. }))
    );
}

#[test]
fn validated_shared_macro_repairs_duplicate_wrappers_at_another_entry() {
    let inner = doonce_latch_named(
        "BeginAction",
        SYNTH_GATE_VAR,
        vec![user_call("BeginAction")],
    );
    let mut outer = doonce_latch_named("Unresolved", SYNTH_GATE_VAR, vec![inner]);
    let Stmt::Latch { offset, .. } = &mut outer else {
        unreachable!()
    };
    *offset = 100;
    let mut body = vec![outer];
    let mut plan = synth_plan("BeginAction");
    plan.target_name = None;
    let mut map = K2NodeByteMap::empty();
    map.gate_let_var_by_offset
        .insert(100, SYNTH_GATE_VAR.into());
    map.gate_let_is_set_by_offset.insert(100, true);
    map.gate_let_owner_by_offset.insert(100, 1);
    map.byte_to_node.insert(0, vec![1]);
    map.byte_to_node.insert(100, vec![1]);
    unwrap_misbound_latch(&mut body, &plan, &map);
    assert_eq!(synthesized_gated_body(&body, "BeginAction").len(), 1);
    assert!(matches!(
        synthesized_gated_body(&body, "BeginAction")[0],
        Stmt::Call { .. }
    ));
}

#[test]
fn unrelated_graph_anchor_does_not_remove_nested_gates() {
    let inner = doonce_latch_named(
        "OtherAction",
        SYNTH_GATE_VAR,
        vec![user_call("OtherAction")],
    );
    let mut body = vec![doonce_latch_named(
        "Unresolved",
        SYNTH_GATE_VAR,
        vec![inner],
    )];
    let mut plan = synth_plan("BeginAction");
    plan.body_offsets = vec![200];
    unwrap_misbound_latch(&mut body, &plan, &K2NodeByteMap::empty());
    assert!(matches!(&body[0], Stmt::Latch { body, .. } if matches!(body[0], Stmt::Latch { .. })));
}
