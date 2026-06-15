//! Tests for the FlipFlop display-name derivation pass.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::flipflop_naming::derive_flipflop_names;
use crate::bytecode::transforms::test_fixtures::{assign, assign_expr, stmt_kind, var};

const GATE: &str = "Temp_bool_Variable";

/// Wrap a list of consumer statements in the recognizer's canonical
/// FlipFlop body shape: a single `Branch { cond: Var(gate), then: <consumers> }`.
fn wrap_consumers(consumers: Vec<Stmt>) -> Vec<Stmt> {
    vec![Stmt::Branch {
        cond: var(GATE),
        then_body: consumers,
        else_body: vec![],
        offset: 0,
    }]
}

fn flipflop(body: Vec<Stmt>) -> Stmt {
    Stmt::Latch {
        kind: LatchKind::FlipFlop {
            gate_var: GATE.to_string(),
            names: None,
        },
        init: vec![],
        body,
        offset: 0,
    }
}

/// Helper: assert the FlipFlop's `names` slot matches `expected_pair`.
fn assert_names(stmt: &Stmt, expected_pair: Option<(&str, &str)>) {
    let Stmt::Latch {
        kind: LatchKind::FlipFlop { names, .. },
        ..
    } = stmt
    else {
        panic!("expected FlipFlop latch, got {:?}", stmt_kind(stmt));
    };
    match (names, expected_pair) {
        (Some((a, b)), Some((expected_a, expected_b))) => {
            assert_eq!(a, expected_a);
            assert_eq!(b, expected_b);
        }
        (None, None) => {}
        (got, want) => panic!("names mismatch: got {:?}, want {:?}", got, want),
    }
}

#[test]
fn derives_name_from_self_field_alias_set() {
    // `self.FlyEnabled = Var(GATE)` inside the consumer block should
    // produce `("FlyEnabled", "FlyEnabled")` and rewrite the rhs.
    let alias_set = assign_expr(
        Expr::FieldAccess {
            recv: Box::new(var("self")),
            field: "FlyEnabled".into(),
        },
        var(GATE),
    );
    let mut body = vec![flipflop(wrap_consumers(vec![alias_set]))];
    derive_flipflop_names(&mut body);

    assert_names(&body[0], Some(("FlyEnabled", "FlyEnabled")));

    // The alias-set's rhs is now `Var("$FlyEnabled_IsA")`.
    let Stmt::Latch {
        body: latch_body, ..
    } = &body[0]
    else {
        unreachable!()
    };
    let Stmt::Branch { then_body, .. } = &latch_body[0] else {
        unreachable!()
    };
    let Stmt::Assignment { rhs, .. } = &then_body[0] else {
        panic!("expected assignment");
    };
    assert!(matches!(rhs, Expr::Var(name) if name == "$FlyEnabled_IsA"));
}

#[test]
fn derives_name_from_var_alias_set() {
    // `BareName = Var(GATE)` should produce `("BareName", "BareName")`.
    let alias_set = assign("BareName", var(GATE));
    let mut body = vec![flipflop(wrap_consumers(vec![alias_set]))];
    derive_flipflop_names(&mut body);

    assert_names(&body[0], Some(("BareName", "BareName")));
}

#[test]
fn falls_back_to_none_when_no_alias_set() {
    // Body has no `<lhs> = Var(GATE)` assignment, just an unrelated call.
    let unrelated = Stmt::Call {
        func: var("Foo"),
        args: vec![],
        offset: 0,
    };
    let mut body = vec![flipflop(wrap_consumers(vec![unrelated]))];
    derive_flipflop_names(&mut body);

    assert_names(&body[0], None);
}

#[test]
fn rewrites_subsequent_gate_var_references() {
    // The alias-set is the first stmt; later stmts should also have
    // their `Var(GATE)` references rewritten to `$<name>_IsA`.
    let alias_set = assign_expr(
        Expr::FieldAccess {
            recv: Box::new(var("self")),
            field: "FlyEnabled".into(),
        },
        var(GATE),
    );
    let later_use = assign(
        "OtherTemp",
        Expr::Call {
            name: "SelectFloat".into(),
            args: vec![var(GATE)],
        },
    );
    let mut body = vec![flipflop(wrap_consumers(vec![alias_set, later_use]))];
    derive_flipflop_names(&mut body);

    let Stmt::Latch {
        body: latch_body, ..
    } = &body[0]
    else {
        unreachable!()
    };
    let Stmt::Branch { then_body, .. } = &latch_body[0] else {
        unreachable!()
    };
    let Stmt::Assignment { rhs, .. } = &then_body[1] else {
        panic!("expected assignment as second stmt");
    };
    let Expr::Call { args, .. } = rhs else {
        panic!("expected Call rhs")
    };
    assert!(matches!(&args[0], Expr::Var(name) if name == "$FlyEnabled_IsA"));
}

#[test]
fn does_not_rewrite_already_named_flipflop() {
    // Pre-populated names should be left alone.
    let alias_set = assign("BareName", var(GATE));
    let mut body = vec![Stmt::Latch {
        kind: LatchKind::FlipFlop {
            gate_var: GATE.to_string(),
            names: Some(("Existing".into(), "Existing".into())),
        },
        init: vec![],
        body: wrap_consumers(vec![alias_set]),
        offset: 0,
    }];
    derive_flipflop_names(&mut body);
    assert_names(&body[0], Some(("Existing", "Existing")));
}
