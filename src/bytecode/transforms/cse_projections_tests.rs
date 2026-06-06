//! Unit tests for the CSE-projection hoist pass.
//!
//! Each test builds a small synthetic body, runs `hoist_repeated_projections`,
//! and inspects the resulting `Vec<Stmt>`. Helpers from `test_fixtures` keep
//! the bodies one canonical shape; the rare test-local builders are inline
//! at the call site.

use super::cse_projections::hoist_repeated_projections;
use super::test_fixtures::{assign, assign_expr, call, lit, var};
use crate::bytecode::expr::{BinaryOp, Expr, SwitchExprCase};
use crate::bytecode::stmt::Stmt;

fn ternary(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    Expr::Ternary {
        cond: Box::new(cond),
        then_expr: Box::new(then_expr),
        else_expr: Box::new(else_expr),
    }
}

fn field(recv: Expr, field_name: &str) -> Expr {
    Expr::FieldAccess {
        recv: Box::new(recv),
        field: field_name.to_string(),
    }
}

fn method(recv: Expr, name: &str, args: Vec<Expr>) -> Stmt {
    Stmt::Call {
        func: Expr::FieldAccess {
            recv: Box::new(recv),
            field: name.to_string(),
        },
        args,
        offset: 0,
    }
}

/// Walk the body and gather every `Stmt::Assignment` lhs as a string. Used
/// by tests to assert the synthetic Assignments landed under the expected
/// derived names.
fn assignment_lhs_names(body: &[Stmt]) -> Vec<String> {
    body.iter()
        .filter_map(|stmt| match stmt {
            Stmt::Assignment {
                lhs: Expr::Var(name),
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// Synthesise a real fixture's ApplyClimbingMovement shape: a 3-arg call in
/// which the same `(cond ? self.LeftHandGrippedActor : self.RightHandGrippedActor)`
/// projection is read three times under different trailing fields.
#[test]
fn hoists_left_right_ternary_with_three_uses() {
    let projection = ternary(
        var("Cond"),
        var("self.LeftHandGrippedActor"),
        var("self.RightHandGrippedActor"),
    );
    let mut body = vec![
        assign_expr(field(projection.clone(), "Actor"), lit("0")),
        assign_expr(field(projection.clone(), "Component"), lit("1")),
        assign_expr(field(projection.clone(), "SocketName"), lit("\"None\"")),
    ];

    hoist_repeated_projections(&mut body);

    assert_eq!(
        assignment_lhs_names(&body),
        vec![
            "$HandGrippedActor".to_string(),
            // The three field-access lhs forms still render through the
            // Stmt::Assignment path but their lhs is FieldAccess, not Var,
            // so they won't appear in this list.
        ]
    );
    let Stmt::Assignment { rhs, .. } = &body[0] else {
        panic!("expected synthetic Assignment first");
    };
    assert!(matches!(rhs, Expr::Ternary { .. }));
    // Subsequent statements should reference $HandGrippedActor as the recv.
    for stmt in &body[1..] {
        let Stmt::Assignment { lhs, .. } = stmt else {
            panic!("expected Assignment in tail");
        };
        let Expr::FieldAccess { recv, .. } = lhs else {
            panic!("expected FieldAccess lhs");
        };
        assert!(matches!(recv.as_ref(), Expr::Var(name) if name == "$HandGrippedActor"));
    }
}

/// Trailing dot-component naming when no Left/Right pattern applies. Two
/// uses of `expr.GripSocketName` should hoist as `$GripSocketName`.
#[test]
fn hoists_trailing_field_with_two_uses() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body = vec![
        Stmt::Call {
            func: var("Foo"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Bar"),
            args: vec![projection.clone()],
            offset: 0,
        },
    ];

    hoist_repeated_projections(&mut body);

    assert_eq!(
        assignment_lhs_names(&body),
        vec!["$GripSocketName".to_string()]
    );
}

/// Fallback `$Cse_N` naming. Two scope-local fallback groups hoist as
/// `$Cse_1` and `$Cse_2` in deterministic order.
#[test]
fn fallback_cse_names_are_sequential() {
    let one = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("X")),
        rhs: Box::new(lit("1")),
    };
    let two = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("Y")),
        rhs: Box::new(lit("2")),
    };
    let mut body = vec![
        Stmt::Call {
            func: var("Use1"),
            args: vec![one.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use1"),
            args: vec![one.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use1"),
            args: vec![one.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use2"),
            args: vec![two.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use2"),
            args: vec![two.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use2"),
            args: vec![two.clone()],
            offset: 0,
        },
    ];

    hoist_repeated_projections(&mut body);

    let names = assignment_lhs_names(&body);
    assert!(names.contains(&"$Cse_1".to_string()));
    assert!(names.contains(&"$Cse_2".to_string()));
}

/// Tier-1/2 derivable names hoist at 2+ uses. A single use of a derivable
/// projection is left untouched.
#[test]
fn named_threshold_two_hoists_one_does_not() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body_two = vec![
        Stmt::Call {
            func: var("Foo"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Bar"),
            args: vec![projection.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body_two);
    assert_eq!(assignment_lhs_names(&body_two).len(), 1);

    let mut body_one = vec![Stmt::Call {
        func: var("Foo"),
        args: vec![projection],
        offset: 0,
    }];
    hoist_repeated_projections(&mut body_one);
    assert!(assignment_lhs_names(&body_one).is_empty());
}

/// Fallback threshold is 3+. Two uses of a non-derivable shape should not
/// hoist; three uses should.
#[test]
fn fallback_threshold_three_hoists_two_does_not() {
    let shape = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("X")),
        rhs: Box::new(lit("1")),
    };
    let mut body_two = vec![
        Stmt::Call {
            func: var("Foo"),
            args: vec![shape.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Foo"),
            args: vec![shape.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body_two);
    assert!(assignment_lhs_names(&body_two).is_empty());

    let mut body_three = vec![
        Stmt::Call {
            func: var("Foo"),
            args: vec![shape.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Foo"),
            args: vec![shape.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Foo"),
            args: vec![shape.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body_three);
    assert_eq!(
        assignment_lhs_names(&body_three),
        vec!["$Cse_1".to_string()]
    );
}

/// Bare `Var` is rejected as already-hoisted. Three repeated `Var("Foo")`
/// references should leave the body unchanged.
#[test]
fn bare_var_is_not_hoisted() {
    let mut body = vec![
        Stmt::Call {
            func: var("Use"),
            args: vec![var("Foo")],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![var("Foo")],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![var("Foo")],
            offset: 0,
        },
    ];
    let before = body.len();
    hoist_repeated_projections(&mut body);
    assert_eq!(body.len(), before);
    assert!(assignment_lhs_names(&body).is_empty());
}

/// A top-level `Call` is on the disallowed list. Even with three repeated
/// uses, the projection should not hoist.
#[test]
fn top_level_call_is_rejected() {
    let projection = Expr::Call {
        name: "Foo".to_string(),
        args: vec![var("X")],
    };
    let mut body = vec![
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
    ];
    let before = body.len();
    hoist_repeated_projections(&mut body);
    assert_eq!(body.len(), before);
    assert!(assignment_lhs_names(&body).is_empty());
}

/// A `Call` nested inside an otherwise-allowlisted `FieldAccess` should
/// disqualify the entire outer expression.
#[test]
fn transitive_call_is_rejected() {
    let projection = field(
        Expr::Call {
            name: "Foo".to_string(),
            args: vec![],
        },
        "Y",
    );
    let mut body = vec![
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);
    assert!(assignment_lhs_names(&body).is_empty());
}

/// `Out` inside a `FieldAccess` is also disallowed. Out-parameters mark
/// real ABI-distinct call sites and must never be hoisted.
#[test]
fn out_inside_field_access_is_rejected() {
    let projection = field(Expr::Out(Box::new(var("X"))), "Y");
    let mut body = vec![
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);
    assert!(assignment_lhs_names(&body).is_empty());
}

/// Cross-scope hoist (test C in the cross-scope plan): two sibling Branch
/// arms each carrying one occurrence of a tier-2 named projection. Total
/// = 2, DCA is the parent of the Branch (root scope). The synthetic
/// Assignment lands BEFORE the Branch and both arms reference it.
#[test]
fn cross_branch_uses_hoist_at_parent_scope() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body = vec![Stmt::Branch {
        cond: var("Cond"),
        then_body: vec![Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        }],
        else_body: vec![Stmt::Call {
            func: var("Use"),
            args: vec![projection.clone()],
            offset: 0,
        }],
        offset: 0,
    }];
    hoist_repeated_projections(&mut body);

    // Synthetic Assignment lands before the Branch at root scope.
    assert_eq!(
        assignment_lhs_names(&body),
        vec!["$GripSocketName".to_string()]
    );
    let Stmt::Assignment { lhs, .. } = &body[0] else {
        panic!("expected synthetic Assignment first");
    };
    assert!(matches!(lhs, Expr::Var(name) if name == "$GripSocketName"));

    // Both arms now pass `$GripSocketName` as the Call arg.
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[1]
    else {
        panic!("expected Branch second");
    };
    let then_call = &then_body[0];
    let Stmt::Call {
        args: then_args, ..
    } = then_call
    else {
        panic!("expected Call in then arm");
    };
    assert!(matches!(&then_args[0], Expr::Var(name) if name == "$GripSocketName"));
    let else_call = &else_body[0];
    let Stmt::Call {
        args: else_args, ..
    } = else_call
    else {
        panic!("expected Call in else arm");
    };
    assert!(matches!(&else_args[0], Expr::Var(name) if name == "$GripSocketName"));
}

/// When the tier-1 derived name `HandGrippedActor` collides with an
/// existing `Var("HandGrippedActor")` in the scope, the pass falls back
/// to `$Cse_N` rather than silently shadowing.
#[test]
fn collision_falls_back_to_cse() {
    let projection = ternary(
        var("Cond"),
        var("self.LeftHandGrippedActor"),
        var("self.RightHandGrippedActor"),
    );
    let mut body = vec![
        // Existing reference to the bare `HandGrippedActor` name.
        Stmt::Call {
            func: var("HandGrippedActor"),
            args: vec![],
            offset: 0,
        },
        assign_expr(field(projection.clone(), "Actor"), lit("0")),
        assign_expr(field(projection.clone(), "Component"), lit("1")),
    ];
    hoist_repeated_projections(&mut body);

    let names = assignment_lhs_names(&body);
    assert!(names.contains(&"$Cse_1".to_string()));
    assert!(!names.contains(&"$HandGrippedActor".to_string()));
}

/// `Expr::Switch` is in the allowlist. A 2-case Left/Right shape used
/// twice under `.Bar` should hoist with the Left/Right-derived name.
#[test]
fn switch_left_right_arms_hoist() {
    let switch_expr = Expr::Switch {
        index: Box::new(var("InstigatingHand")),
        cases: vec![
            SwitchExprCase {
                value: lit("0"),
                body: var("self.LeftFoo"),
            },
            SwitchExprCase {
                value: lit("1"),
                body: var("self.RightFoo"),
            },
        ],
        default: Box::new(var("$Select_Default")),
    };
    let mut body = vec![
        Stmt::Call {
            func: var("Use"),
            args: vec![field(switch_expr.clone(), "Bar")],
            offset: 0,
        },
        Stmt::Call {
            func: var("Use"),
            args: vec![field(switch_expr.clone(), "Bar")],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);

    // Tier-1 picks the projection that hosts the Switch — the FieldAccess
    // `<switch>.Bar` — so the derived name is `$Bar` (tier-2 trailing
    // field), since the Switch-arm shape is wrapped inside the
    // FieldAccess. Verify a hoist landed under a $-prefixed name.
    let names = assignment_lhs_names(&body);
    assert_eq!(names.len(), 1);
    assert!(
        names[0].starts_with('$'),
        "expected $-prefixed hoist, got {:?}",
        names
    );
}

/// Regression: nested scopes must not produce a chained hoist of the
/// form `$Outer = $Cse_N`. Reproduces the OnComponentGripped artifact
/// where the outer-scope hoist's deep substitute used to rewrite the
/// inner-scope hoist's rhs into the outer hoist's variable.
///
/// Setup: outer body has two uses of `Var(GrippedActor) FieldAccess
/// Component` (in a Branch cond's left and right Binary operands).
/// The inner else-body has two uses of the same expression in two
/// Call args. The else-body's local CSE fires first (bottom-up),
/// hoisting `$Component = GrippedActor.Component`. The outer scope's
/// CSE fires next; before the fix, its deep substitute reached into
/// the else body and rewrote the rhs of the inner Assignment, leaving
/// `$Component = $Cse_1` (or similar). After the fix, the outer scope's
/// substitute is shallow and stops at the Branch cond.
#[test]
fn nested_scope_does_not_chain_hoist() {
    let projection = field(var("GrippedActor"), "Component");
    let mut body = vec![Stmt::Branch {
        // Outer cond uses the projection twice in a Binary AND.
        cond: Expr::Binary {
            op: BinaryOp::And,
            lhs: Box::new(Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(projection.clone()),
                rhs: Box::new(var("LeftA")),
            }),
            rhs: Box::new(Expr::Binary {
                op: BinaryOp::Eq,
                lhs: Box::new(projection.clone()),
                rhs: Box::new(var("RightA")),
            }),
        },
        then_body: vec![],
        // Inner else uses the projection twice in two Call args.
        else_body: vec![
            Stmt::Call {
                func: var("UseA"),
                args: vec![projection.clone()],
                offset: 0,
            },
            Stmt::Call {
                func: var("UseB"),
                args: vec![projection.clone()],
                offset: 0,
            },
        ],
        offset: 0,
    }];

    hoist_repeated_projections(&mut body);

    // Locate the Branch in the post-hoist body. The outer scope's two
    // cond-side uses meet tier-2 threshold, so a synthetic Assignment may
    // land before the Branch. We inspect the inner else-body either way.
    let branch_stmt = body
        .iter()
        .find(|stmt| matches!(stmt, Stmt::Branch { .. }))
        .expect("Branch must remain in body after hoist");
    let Stmt::Branch { else_body, .. } = branch_stmt else {
        unreachable!();
    };

    // The inner else-body must contain at most one synthetic Assignment
    // for the Component projection, AND that Assignment's rhs must still
    // be the canonical FieldAccess shape, NOT a bare `Var` pointing at
    // the outer scope's hoist (which would form the `$Component = $Cse_1`
    // chain artifact).
    for stmt in else_body.iter() {
        let Stmt::Assignment { rhs, .. } = stmt else {
            continue;
        };
        assert!(
            !matches!(rhs, Expr::Var(name) if name.starts_with('$')),
            "inner Assignment rhs was rewritten into a chain reference \
             (a `$<Outer>` Var) rather than the original FieldAccess",
        );
    }
}

/// Cross-scope hoist motivating fixture (test A): a Branch cond uses E
/// once and the Branch then-body uses E twice. Total = 3, DCA is the
/// parent of the Branch (root scope). The hoist lands BEFORE the Branch
/// and the cond plus both then-body uses reference the synthetic Var.
#[test]
fn cross_scope_branch_cond_plus_then_body_hoists_at_parent() {
    let projection = ternary(
        var("Cond"),
        var("self.LeftHandGrippedActor"),
        var("self.RightHandGrippedActor"),
    );
    let mut body = vec![Stmt::Branch {
        cond: field(projection.clone(), "Actor"),
        then_body: vec![
            assign_expr(field(projection.clone(), "Component"), lit("0")),
            assign_expr(field(projection.clone(), "SocketName"), lit("\"None\"")),
        ],
        else_body: vec![],
        offset: 0,
    }];
    hoist_repeated_projections(&mut body);

    // Synthetic Assignment for the ternary lands first at root scope.
    let names = assignment_lhs_names(&body);
    assert!(
        names.contains(&"$HandGrippedActor".to_string()),
        "expected $HandGrippedActor at root scope, got {:?}",
        names
    );
    let Stmt::Assignment { lhs, rhs, .. } = &body[0] else {
        panic!("expected synthetic Assignment first");
    };
    assert!(matches!(lhs, Expr::Var(name) if name == "$HandGrippedActor"));
    assert!(matches!(rhs, Expr::Ternary { .. }));

    // Branch cond's FieldAccess.recv is now `$HandGrippedActor`.
    let Stmt::Branch {
        cond, then_body, ..
    } = &body[1]
    else {
        panic!("expected Branch second");
    };
    let Expr::FieldAccess { recv, .. } = cond else {
        panic!("expected FieldAccess cond");
    };
    assert!(matches!(recv.as_ref(), Expr::Var(name) if name == "$HandGrippedActor"));

    // Both then-body Assignments' lhs FieldAccess.recv is `$HandGrippedActor`.
    for stmt in then_body.iter() {
        let Stmt::Assignment { lhs, .. } = stmt else {
            continue;
        };
        let Expr::FieldAccess { recv, .. } = lhs else {
            continue;
        };
        assert!(matches!(recv.as_ref(), Expr::Var(name) if name == "$HandGrippedActor"));
    }
}

/// Cross-scope hoist (test B): DCA is the innermost scope. Branch then-body
/// uses E twice, else-body and cond use E zero times. DCA = then-body, so
/// the hoist lands inside the then-body, not at root scope.
#[test]
fn cross_scope_dca_innermost_scope_hoists_inside_branch() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body = vec![Stmt::Branch {
        cond: var("Cond"),
        then_body: vec![
            Stmt::Call {
                func: var("Foo"),
                args: vec![projection.clone()],
                offset: 0,
            },
            Stmt::Call {
                func: var("Bar"),
                args: vec![projection.clone()],
                offset: 0,
            },
        ],
        else_body: vec![],
        offset: 0,
    }];
    hoist_repeated_projections(&mut body);

    // Root scope contains only the Branch (no synthetic Assignment landed).
    assert!(assignment_lhs_names(&body).is_empty());
    let Stmt::Branch { then_body, .. } = &body[0] else {
        panic!("expected Branch");
    };
    // Synthetic Assignment lands inside then_body.
    assert_eq!(
        assignment_lhs_names(then_body),
        vec!["$GripSocketName".to_string()]
    );
}

/// Cross-scope hoist (test D): a Loop body uses E twice and a sibling
/// statement before the Loop uses E once. Total = 3, DCA = root scope.
/// Hoist lands before the Loop.
#[test]
fn cross_scope_loop_body_plus_sibling_hoists_before_loop() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body = vec![
        Stmt::Call {
            func: var("Pre"),
            args: vec![projection.clone()],
            offset: 0,
        },
        Stmt::Loop {
            kind: crate::bytecode::stmt::LoopKind::While,
            cond: Some(var("LoopCond")),
            body: vec![
                Stmt::Call {
                    func: var("InLoopA"),
                    args: vec![projection.clone()],
                    offset: 0,
                },
                Stmt::Call {
                    func: var("InLoopB"),
                    args: vec![projection.clone()],
                    offset: 0,
                },
            ],
            completion: None,
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);

    // Root scope: synthetic Assignment first, then the original Pre call,
    // then the Loop. The hoist needs to dominate every use.
    assert_eq!(
        assignment_lhs_names(&body),
        vec!["$GripSocketName".to_string()]
    );
    let Stmt::Assignment { lhs, .. } = &body[0] else {
        panic!("expected synthetic Assignment first");
    };
    assert!(matches!(lhs, Expr::Var(name) if name == "$GripSocketName"));
    // Loop's body now references the hoisted Var.
    let Stmt::Loop {
        body: loop_body, ..
    } = &body[2]
    else {
        panic!("expected Loop");
    };
    for stmt in loop_body.iter() {
        let Stmt::Call { args, .. } = stmt else {
            continue;
        };
        assert!(matches!(&args[0], Expr::Var(name) if name == "$GripSocketName"));
    }
}

/// Cross-scope hoist (test E): different Switch case bodies each use E
/// once. Two cases trigger the named threshold. DCA is the parent of the
/// Switch (root scope).
#[test]
fn cross_scope_switch_cases_hoist_at_parent_of_switch() {
    let projection = field(var("self.Hand"), "GripSocketName");
    let mut body = vec![Stmt::Switch {
        expr: var("Selector"),
        cases: vec![
            crate::bytecode::stmt::SwitchCase {
                values: vec![lit("0")],
                body: vec![Stmt::Call {
                    func: var("CaseZero"),
                    args: vec![projection.clone()],
                    offset: 0,
                }],
            },
            crate::bytecode::stmt::SwitchCase {
                values: vec![lit("1")],
                body: vec![Stmt::Call {
                    func: var("CaseOne"),
                    args: vec![projection.clone()],
                    offset: 0,
                }],
            },
        ],
        default: None,
        offset: 0,
    }];
    hoist_repeated_projections(&mut body);

    // Synthetic Assignment lands before the Switch at root scope.
    assert_eq!(
        assignment_lhs_names(&body),
        vec!["$GripSocketName".to_string()]
    );
    // Both case bodies reference the hoisted Var.
    let Stmt::Switch { cases, .. } = &body[1] else {
        panic!("expected Switch");
    };
    for case in cases.iter() {
        let Stmt::Call { args, .. } = &case.body[0] else {
            panic!("expected Call in case body");
        };
        assert!(matches!(&args[0], Expr::Var(name) if name == "$GripSocketName"));
    }
}

/// Cross-scope hoist (test F): overlapping groups. Outer expression
/// `(cond ? L : R).Field` (key A) and inner `(cond ? L : R)` (key B).
/// After hoisting A, the inner's key changes. The fixpoint loop must
/// not infinite-loop and must terminate.
#[test]
fn cross_scope_overlapping_groups_terminate() {
    let inner = ternary(
        var("Cond"),
        var("self.LeftHandGrippedActor"),
        var("self.RightHandGrippedActor"),
    );
    let outer = field(inner.clone(), "Actor");
    let mut body = vec![
        Stmt::Call {
            func: var("UseOuterA"),
            args: vec![outer.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("UseOuterB"),
            args: vec![outer.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("UseInnerOnly"),
            args: vec![field(inner.clone(), "Component")],
            offset: 0,
        },
        Stmt::Call {
            func: var("UseInnerOnlyAgain"),
            args: vec![field(inner.clone(), "SocketName")],
            offset: 0,
        },
    ];
    // Body holds 4 inner-ternary occurrences and 2 outer.Actor occurrences.
    // The pass must terminate (the iteration cap is the safety net) and
    // hoist the inner ternary (4 uses, named-derivable as $HandGrippedActor).
    hoist_repeated_projections(&mut body);

    let names = assignment_lhs_names(&body);
    assert!(
        names.iter().any(|name| name == "$HandGrippedActor"),
        "expected $HandGrippedActor hoist, got {:?}",
        names
    );
}

/// Cross-scope naming collision: a derived `$Component` would collide with
/// a Var inside a different scope. The deep-collection collision check
/// must catch this and fall back to `$Cse_N`.
#[test]
fn cross_scope_naming_collision_falls_back_to_cse() {
    let projection = field(var("GrippedActor"), "Component");
    let mut body = vec![Stmt::Branch {
        cond: var("Cond"),
        then_body: vec![
            // A use in a nested scope.
            Stmt::Call {
                func: var("UseA"),
                args: vec![projection.clone()],
                offset: 0,
            },
        ],
        else_body: vec![
            // Another use in a different nested scope, plus a colliding
            // bare `Var("Component")` reference.
            Stmt::Call {
                func: var("Component"),
                args: vec![],
                offset: 0,
            },
            Stmt::Call {
                func: var("UseB"),
                args: vec![projection.clone()],
                offset: 0,
            },
        ],
        offset: 0,
    }];
    hoist_repeated_projections(&mut body);

    // The two uses are in disjoint scopes (then-body and else-body), so
    // the cross-scope DCA is the root. The derived name `$Component` would
    // collide with bare `Var("Component")` inside else-body, so the pass
    // must fall back to `$Cse_N`.
    let names = assignment_lhs_names(&body);
    assert!(!names.iter().any(|name| name == "$Component"));
    assert!(
        names.iter().any(|name| name.starts_with("$Cse_")),
        "expected $Cse_ fallback, got {:?}",
        names
    );
}

/// BP-temp-slot reuse: a Var that appears as Assignment lhs more than
/// once in the body is treated as a Blueprint-compiler temp slot. The
/// CSE pass must NOT count its rhs as a use site, otherwise substituting
/// it produces a `$Slot = $Cse_N` chain artifact the post-CSE inliner
/// cannot collapse (the slot's reuse blocks single-use inlining).
#[test]
fn multi_def_var_lhs_rhs_is_not_counted_as_use() {
    let shape = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("Segment")),
        rhs: Box::new(lit("1")),
    };
    let mut body = vec![
        // First defining Assignment (slot reuse, multi-def).
        assign("$Add_IntInt", shape.clone()),
        // Use site (true read).
        Stmt::Call {
            func: var("UseA"),
            args: vec![shape.clone()],
            offset: 0,
        },
        // Second defining Assignment (multi-def of the same slot).
        assign("$Add_IntInt", shape.clone()),
    ];
    hoist_repeated_projections(&mut body);

    // Without the BP-temp-slot exclusion: 3 uses of the Add expression
    // would meet the fallback threshold and hoist as `$Cse_1`, leaving
    // `$Add_IntInt = $Cse_1` aliases on lines 1 and 3. With the exclusion:
    // only the middle Call site is counted, total = 1, no hoist.
    let names = assignment_lhs_names(&body);
    assert!(
        !names.iter().any(|name| name.starts_with("$Cse_")),
        "BP-temp-slot reuse should suppress the hoist, got names {:?}",
        names
    );
    // Both `$Add_IntInt` defs are preserved.
    assert_eq!(
        names.iter().filter(|name| *name == "$Add_IntInt").count(),
        2
    );
}

/// Single-def Var slot is NOT excluded: a Var that appears as Assignment
/// lhs exactly once is fair game, and its rhs may be hoisted into a
/// Cse temp like any other use site. Distinguishes the multi-def-only
/// exclusion from a blanket Assignment-rhs skip.
#[test]
fn single_def_var_lhs_rhs_still_counts_as_use() {
    let shape = Expr::Binary {
        op: BinaryOp::Add,
        lhs: Box::new(var("Segment")),
        rhs: Box::new(lit("1")),
    };
    let mut body = vec![
        // Single-def Assignment (the rhs counts as a use).
        assign("$Add_IntInt", shape.clone()),
        Stmt::Call {
            func: var("UseA"),
            args: vec![shape.clone()],
            offset: 0,
        },
        Stmt::Call {
            func: var("UseB"),
            args: vec![shape.clone()],
            offset: 0,
        },
    ];
    hoist_repeated_projections(&mut body);

    // Total = 3, fallback threshold met, hoist fires under `$Cse_N`.
    let names = assignment_lhs_names(&body);
    assert!(
        names.iter().any(|name| name == "$Cse_1"),
        "single-def slot should not block hoist, got names {:?}",
        names
    );
}

/// Sanity: `assign` and `call` from the shared test fixtures still build
/// the expected shapes. Guards against accidental refactors of the
/// fixture module that would invalidate the tests above.
#[test]
fn fixture_helpers_build_expected_shapes() {
    let body = vec![assign("X", lit("1")), call("Foo", vec![])];
    assert_eq!(assignment_lhs_names(&body), vec!["X".to_string()]);
    let _unused_method = method(var("self"), "Bar", vec![]);
}
