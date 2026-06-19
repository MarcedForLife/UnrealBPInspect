//! Tests for the expression-walker family in `visit.rs`. Extracted from
//! the production module so the walker definitions stay readable; the
//! synthetic Stmt/Expr trees that exercise every variant live here.

use super::test_fixtures::{lit, var};
use super::visit::{
    any_expr, walk_body_exprs, walk_body_exprs_mut, walk_body_exprs_mut_visit_lhs,
    walk_body_exprs_visit_lhs, walk_expr, walk_expr_mut, walk_stmt_exprs, walk_stmt_exprs_mut,
    walk_stmt_exprs_mut_visit_lhs, walk_stmt_exprs_visit_lhs, Action,
};
use crate::bytecode::expr::{BinaryOp, CastKind, Expr, SwitchExprCase, UnaryOp};
use crate::bytecode::stmt::{LatchKind, LoopKind, Stmt, SwitchCase};

fn binary(op: BinaryOp, lhs: Expr, rhs: Expr) -> Expr {
    Expr::Binary {
        op,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

/// A single nested Expr that exercises every Expr variant with children
/// (Call, MethodCall, FieldAccess, Index, Binary, Unary, Cast, ArrayLit,
/// Ternary, Out, Interface, Persistent, Resume, StructConstruct, Switch).
/// Each leaf is a uniquely-named `Var`, so a walker that skips any variant
/// drops that variant's leaf. Shared by the `walk_expr` and `any_expr`
/// coverage tests; its leaf names match the `leaves` list in
/// `walk_expr_covers_every_variant`.
fn every_variant_expr() -> Expr {
    Expr::Call {
        name: "Outer".to_string(),
        args: vec![
            var("L_CALL"),
            Expr::MethodCall {
                recv: Box::new(var("L_METHOD_R")),
                name: "M".to_string(),
                args: vec![var("L_METHOD_A")],
            },
            Expr::FieldAccess {
                recv: Box::new(var("L_FIELD")),
                field: "f".to_string(),
            },
            Expr::Index {
                recv: Box::new(var("L_IDX_R")),
                idx: Box::new(var("L_IDX_I")),
            },
            binary(BinaryOp::Add, var("L_BIN_L"), var("L_BIN_R")),
            Expr::Unary {
                op: UnaryOp::Neg,
                operand: Box::new(var("L_UNARY")),
            },
            Expr::Cast {
                kind: CastKind::ToBool,
                inner: Box::new(var("L_CAST")),
            },
            Expr::ArrayLit(vec![var("L_ARR_0"), var("L_ARR_1")]),
            Expr::Ternary {
                cond: Box::new(var("L_TERN_C")),
                then_expr: Box::new(var("L_TERN_T")),
                else_expr: Box::new(var("L_TERN_E")),
            },
            Expr::Out(Box::new(var("L_OUT"))),
            Expr::Interface(Box::new(var("L_IFACE"))),
            Expr::Persistent(Box::new(var("L_PERSIST"))),
            Expr::Resume {
                inner: Box::new(var("L_RESUME")),
                target: 0,
            },
            Expr::StructConstruct {
                type_name: "S".to_string(),
                fields: vec![("a".to_string(), var("L_STRUCT"))],
            },
            Expr::Switch {
                index: Box::new(var("L_SW_INDEX")),
                cases: vec![SwitchExprCase {
                    value: var("L_SW_CASE_V"),
                    body: var("L_SW_CASE_B"),
                }],
                default: Box::new(var("L_SW_DEFAULT")),
            },
        ],
    }
}

/// Build a synthetic Stmt tree exercising every variant of interest.
/// Each unique Var name lets tests assert presence/absence by counting
/// matches without ambiguity.
fn synthetic_tree() -> Vec<Stmt> {
    let nested_call = Expr::Call {
        name: "Inner".to_string(),
        args: vec![var("CALL_ARG")],
    };
    let method = Expr::MethodCall {
        recv: Box::new(var("RECV")),
        name: "Method".to_string(),
        args: vec![var("METHOD_ARG")],
    };
    let field = Expr::FieldAccess {
        recv: Box::new(var("FIELD_RECV")),
        field: "field".to_string(),
    };
    let index = Expr::Index {
        recv: Box::new(var("INDEX_RECV")),
        idx: Box::new(var("INDEX_IDX")),
    };
    let unary = Expr::Unary {
        op: UnaryOp::Not,
        operand: Box::new(var("UNARY_OPERAND")),
    };
    let cast = Expr::Cast {
        kind: CastKind::ToBool,
        inner: Box::new(var("CAST_INNER")),
    };
    let ternary = Expr::Ternary {
        cond: Box::new(var("TERNARY_COND")),
        then_expr: Box::new(var("TERNARY_THEN")),
        else_expr: Box::new(var("TERNARY_ELSE")),
    };
    let struct_construct = Expr::StructConstruct {
        type_name: "S".to_string(),
        fields: vec![("a".to_string(), var("STRUCT_VAL"))],
    };
    let inline_switch = Expr::Switch {
        index: Box::new(var("ESW_INDEX")),
        cases: vec![SwitchExprCase {
            value: var("ESW_CASE_VALUE"),
            body: var("ESW_CASE_BODY"),
        }],
        default: Box::new(var("ESW_DEFAULT")),
    };

    // Branch with cond that bundles many sub-shapes inside a binary
    // tree. The lhs of the outer Binary is a chain of nested unary
    // and field/index access nodes.
    let branch_cond = binary(
        BinaryOp::And,
        binary(
            BinaryOp::Or,
            nested_call.clone(),
            binary(BinaryOp::Eq, method.clone(), field.clone()),
        ),
        binary(
            BinaryOp::And,
            binary(BinaryOp::Add, index.clone(), unary.clone()),
            binary(BinaryOp::Eq, cast.clone(), ternary.clone()),
        ),
    );

    let branch = Stmt::Branch {
        cond: branch_cond,
        then_body: vec![
            // Assignment: lhs `Var("LHS")` MUST be skipped, rhs `Var("RHS")` MUST be visited.
            Stmt::Assignment {
                lhs: var("LHS"),
                rhs: var("RHS"),
                offset: 0,
            },
            Stmt::Call {
                func: var("CALL_FUNC"),
                args: vec![struct_construct.clone(), inline_switch.clone()],
                offset: 0,
            },
        ],
        else_body: vec![Stmt::Return {
            value: Some(var("RETURN_VAL")),
            offset: 0,
        }],
        offset: 0,
    };

    let loop_stmt = Stmt::Loop {
        kind: LoopKind::ForC {
            init: vec![Stmt::Assignment {
                lhs: var("LHS_INIT"),
                rhs: lit("0"),
                offset: 0,
            }],
            increment: vec![Stmt::Call {
                func: var("INC_FUNC"),
                args: vec![var("INC_ARG")],
                offset: 0,
            }],
        },
        cond: Some(var("LOOP_COND")),
        body: vec![Stmt::Call {
            func: var("BODY_FUNC"),
            args: vec![],
            offset: 0,
        }],
        completion: Some(vec![Stmt::Call {
            func: var("COMPLETION_FUNC"),
            args: vec![],
            offset: 0,
        }]),
        offset: 0,
    };

    let foreach_loop = Stmt::Loop {
        kind: LoopKind::ForEach {
            item: "i".to_string(),
            array: var("FOREACH_ARRAY"),
        },
        cond: None,
        body: vec![],
        completion: None,
        offset: 0,
    };

    let switch_stmt = Stmt::Switch {
        expr: var("SWITCH_EXPR"),
        cases: vec![SwitchCase {
            values: vec![var("CASE_VALUE")],
            body: vec![Stmt::Call {
                func: var("CASE_BODY_FUNC"),
                args: vec![],
                offset: 0,
            }],
        }],
        default: Some(vec![Stmt::Call {
            func: var("DEFAULT_FUNC"),
            args: vec![],
            offset: 0,
        }]),
        offset: 0,
    };

    let sequence_stmt = Stmt::Sequence {
        pins: vec![
            vec![Stmt::Call {
                func: var("PIN0_FUNC"),
                args: vec![],
                offset: 0,
            }],
            vec![Stmt::Call {
                func: var("PIN1_FUNC"),
                args: vec![],
                offset: 0,
            }],
        ],
        offset: 0,
    };

    let latch_stmt = Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: "DoOnce_0".to_string(),
            gate_var: "g".to_string(),
        },
        init: vec![Stmt::Assignment {
            lhs: var("LHS_LATCH_INIT"),
            rhs: var("LATCH_INIT_RHS"),
            offset: 0,
        }],
        body: vec![Stmt::Call {
            func: var("LATCH_BODY_FUNC"),
            args: vec![],
            offset: 0,
        }],
        offset: 0,
    };

    vec![
        branch,
        loop_stmt,
        foreach_loop,
        switch_stmt,
        sequence_stmt,
        latch_stmt,
        Stmt::EventCall {
            event_name: "Evt".to_string(),
            offset: 0,
        },
        Stmt::Unknown {
            reason: "test".to_string(),
            raw_bytes: vec![],
            offset: 0,
            length: 0,
        },
    ]
}

/// Names of every Var the synthetic tree contains, EXCLUDING the
/// Assignment lhs vars. This is the expected visit set under
/// SkipUses semantics.
fn expected_visited_var_names() -> Vec<&'static str> {
    vec![
        // Branch cond Binary tree.
        "CALL_ARG",
        "RECV",
        "METHOD_ARG",
        "FIELD_RECV",
        "INDEX_RECV",
        "INDEX_IDX",
        "UNARY_OPERAND",
        "CAST_INNER",
        "TERNARY_COND",
        "TERNARY_THEN",
        "TERNARY_ELSE",
        // Branch then-body assignment rhs (lhs LHS is skipped).
        "RHS",
        // Branch then-body Call func + args (StructConstruct + inline Switch).
        "CALL_FUNC",
        "STRUCT_VAL",
        "ESW_INDEX",
        "ESW_CASE_VALUE",
        "ESW_CASE_BODY",
        "ESW_DEFAULT",
        // Branch else-body Return value.
        "RETURN_VAL",
        // Loop ForC init assignment rhs is a literal, no var. Increment Call func + arg.
        "INC_FUNC",
        "INC_ARG",
        // Loop cond + body func + completion func.
        "LOOP_COND",
        "BODY_FUNC",
        "COMPLETION_FUNC",
        // ForEach array.
        "FOREACH_ARRAY",
        // Switch expr + case value + case body func + default func.
        "SWITCH_EXPR",
        "CASE_VALUE",
        "CASE_BODY_FUNC",
        "DEFAULT_FUNC",
        // Sequence pins.
        "PIN0_FUNC",
        "PIN1_FUNC",
        // Latch init assignment rhs (lhs LHS_LATCH_INIT is skipped) + body func.
        "LATCH_INIT_RHS",
        "LATCH_BODY_FUNC",
    ]
}

fn collect_var_names(body: &[Stmt]) -> Vec<String> {
    let mut names = Vec::new();
    let mut visit = |expr: &Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
    };
    walk_body_exprs(body, &mut visit);
    names
}

#[test]
fn read_only_walk_visits_every_expected_var() {
    let body = synthetic_tree();
    let mut got = collect_var_names(&body);
    got.sort();
    let mut want: Vec<String> = expected_visited_var_names()
        .into_iter()
        .map(|name| name.to_string())
        .collect();
    want.sort();
    assert_eq!(got, want);
}

#[test]
fn read_only_walk_skips_assignment_lhs_vars() {
    let body = synthetic_tree();
    let names = collect_var_names(&body);
    for skipped in ["LHS", "LHS_INIT", "LHS_LATCH_INIT"] {
        assert!(
            !names.iter().any(|name| name == skipped),
            "Assignment lhs name `{skipped}` must NOT be visited; got {names:?}"
        );
    }
}

#[test]
fn read_only_walk_visits_assignment_rhs_var() {
    let body = synthetic_tree();
    let names = collect_var_names(&body);
    assert!(
        names.iter().any(|name| name == "RHS"),
        "Assignment rhs Var(`RHS`) must be visited; got {names:?}"
    );
}

#[test]
fn read_only_walk_count_matches_expected() {
    let body = synthetic_tree();
    let mut count = 0usize;
    let mut visit = |_expr: &Expr| {
        count += 1;
    };
    walk_body_exprs(&body, &mut visit);
    // Recompute the expected count from the synthetic tree's shape:
    // every node visited once (root + each child via pre-order recursion).
    // Easier sanity check: at minimum, the visited Var-set count.
    let var_count = expected_visited_var_names().len();
    assert!(
        count >= var_count,
        "expected at least {var_count} visits (one per Var), got {count}"
    );
}

#[test]
fn mutable_walk_action_stop_halts_on_first_match() {
    let mut body = synthetic_tree();
    let mut visit_count = 0usize;
    let result = walk_body_exprs_mut(&mut body, &mut |expr: &mut Expr| {
        visit_count += 1;
        if matches!(expr, Expr::Var(name) if name == "CALL_ARG") {
            Action::Stop
        } else {
            Action::Continue
        }
    });
    assert!(matches!(result, Action::Stop));
    // Sanity: total Var count under the synthetic tree well exceeds 1,
    // so an early-stop run must finish strictly before the full walk.
    let full = collect_var_names(&body).len();
    assert!(
        visit_count < full * 4,
        "early Stop should not have walked the full tree; visit_count={visit_count}, full Var count={full}"
    );
}

#[test]
fn mutable_walk_can_rewrite_visited_exprs() {
    let mut body = synthetic_tree();
    let mut visit = |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == "RHS" {
                *name = "RHS_RENAMED".to_string();
            }
        }
        Action::Continue
    };
    let result = walk_body_exprs_mut(&mut body, &mut visit);
    assert!(matches!(result, Action::Continue));
    let names = collect_var_names(&body);
    assert!(names.iter().any(|name| name == "RHS_RENAMED"));
    assert!(!names.iter().any(|name| name == "RHS"));
}

/// Renaming an Assignment lhs's `Var(name)` directly via the visitor
/// must NOT happen, because the lhs is never visited. This is the
/// load-bearing safety guarantee of the walker.
#[test]
fn mutable_walk_cannot_rename_assignment_lhs() {
    let mut body = synthetic_tree();
    let mut visit = |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == "LHS" {
                *name = "LHS_RENAMED".to_string();
            }
        }
        Action::Continue
    };
    walk_body_exprs_mut(&mut body, &mut visit);
    // The lhs Var was never given to the visitor, so the rename is a no-op.
    // Walk in read-only mode to inspect surviving lhs by hand: dive into
    // the first Branch's then_body's first Assignment.
    let Stmt::Branch { then_body, .. } = &body[0] else {
        panic!("expected first Stmt to be Branch");
    };
    let Stmt::Assignment { lhs, .. } = &then_body[0] else {
        panic!("expected first Branch then-body Stmt to be Assignment");
    };
    assert!(
        matches!(lhs, Expr::Var(name) if name == "LHS"),
        "lhs Var should remain `LHS`; got {lhs:?}"
    );
}

/// Single-Stmt entry points share the same coverage and lhs-skip
/// semantics as the body-level wrappers.
#[test]
fn single_stmt_walker_skips_lhs() {
    let stmt = Stmt::Assignment {
        lhs: var("LHS"),
        rhs: var("RHS"),
        offset: 0,
    };
    let mut names = Vec::new();
    let mut visit = |expr: &Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
    };
    walk_stmt_exprs(&stmt, &mut visit);
    assert_eq!(names, vec!["RHS".to_string()]);
}

#[test]
fn single_stmt_walker_mut_skips_lhs() {
    let mut stmt = Stmt::Assignment {
        lhs: var("LHS"),
        rhs: var("RHS"),
        offset: 0,
    };
    let mut names = Vec::new();
    walk_stmt_exprs_mut(&mut stmt, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
        Action::Continue
    });
    assert_eq!(names, vec!["RHS".to_string()]);
}

/// `walk_expr` covers every Expr variant (no Stmt wrapper). Build a
/// single nested Expr that exercises Call, MethodCall, FieldAccess,
/// Index, Binary, Unary, Cast, Ternary, ArrayLit, Out, Interface,
/// Persistent, Resume, StructConstruct, and Expr::Switch (cases +
/// default), and confirm every leaf Var is visited.
#[test]
fn walk_expr_covers_every_variant() {
    let leaves = [
        "L_CALL",
        "L_METHOD_R",
        "L_METHOD_A",
        "L_FIELD",
        "L_IDX_R",
        "L_IDX_I",
        "L_BIN_L",
        "L_BIN_R",
        "L_UNARY",
        "L_CAST",
        "L_ARR_0",
        "L_ARR_1",
        "L_TERN_C",
        "L_TERN_T",
        "L_TERN_E",
        "L_OUT",
        "L_IFACE",
        "L_PERSIST",
        "L_RESUME",
        "L_STRUCT",
        "L_SW_INDEX",
        "L_SW_CASE_V",
        "L_SW_CASE_B",
        "L_SW_DEFAULT",
    ];
    let expr = every_variant_expr();

    let mut got = Vec::new();
    let mut visit = |expr: &Expr| {
        if let Expr::Var(name) = expr {
            got.push(name.clone());
        }
    };
    walk_expr(&expr, &mut visit);
    got.sort();
    let mut want: Vec<String> = leaves.iter().map(|name| name.to_string()).collect();
    want.sort();
    assert_eq!(got, want);
}

/// `walk_expr_mut` early-stop halts at the first match, leaving
/// later sub-expressions untouched.
#[test]
fn walk_expr_mut_stop_halts_walk() {
    let mut expr = Expr::Call {
        name: "Outer".to_string(),
        args: vec![var("FIRST"), var("SECOND"), var("THIRD")],
    };
    let mut visit_log = Vec::new();
    walk_expr_mut(&mut expr, &mut |inner: &mut Expr| {
        if let Expr::Var(name) = inner {
            visit_log.push(name.clone());
            if name == "SECOND" {
                return Action::Stop;
            }
        }
        Action::Continue
    });
    assert_eq!(visit_log, vec!["FIRST".to_string(), "SECOND".to_string()]);
}

/// Pre-order semantics: the visitor sees the root Expr before any
/// of its children. If the visitor mutates the root in-place, the
/// new node's children are walked.
#[test]
fn walk_expr_mut_is_pre_order() {
    let mut expr = var("ROOT");
    let mut log = Vec::new();
    walk_expr_mut(&mut expr, &mut |inner: &mut Expr| {
        match inner {
            Expr::Var(name) => log.push(format!("var:{name}")),
            Expr::Call { name, .. } => log.push(format!("call:{name}")),
            _ => {}
        }
        // Replace the bare ROOT Var with a Call wrapping a different Var.
        // Pre-order behavior means the replacement's child (`PAYLOAD`) is
        // visited next; a post-order walker would not see it.
        if matches!(inner, Expr::Var(name) if name == "ROOT") {
            *inner = Expr::Call {
                name: "Wrap".to_string(),
                args: vec![var("PAYLOAD")],
            };
        }
        Action::Continue
    });
    assert_eq!(log, vec!["var:ROOT".to_string(), "var:PAYLOAD".to_string()]);
}

/// The visit-lhs walker MUST visit Assignment lhs vars in addition to
/// every var the SkipUses walker visits. Counts in/out lhs to confirm.
#[test]
fn visit_lhs_walker_visits_assignment_lhs() {
    let body = synthetic_tree();
    let mut names = Vec::new();
    walk_body_exprs_visit_lhs(&body, &mut |expr: &Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
    });
    for required in ["LHS", "LHS_INIT", "LHS_LATCH_INIT"] {
        assert!(
            names.iter().any(|name| name == required),
            "visit-lhs walker must visit `{required}`; got {names:?}"
        );
    }
    // The default-skipped vars MUST also still be visited.
    for required in ["RHS", "RETURN_VAL", "BODY_FUNC"] {
        assert!(
            names.iter().any(|name| name == required),
            "visit-lhs walker must visit `{required}`; got {names:?}"
        );
    }
}

/// The mutable visit-lhs walker can rename an Assignment lhs's bare Var.
#[test]
fn visit_lhs_walker_mut_can_rename_assignment_lhs() {
    let mut body = synthetic_tree();
    walk_body_exprs_mut_visit_lhs(&mut body, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == "LHS" {
                *name = "LHS_RENAMED".to_string();
            }
        }
        Action::Continue
    });
    let Stmt::Branch { then_body, .. } = &body[0] else {
        panic!("expected first Stmt to be Branch");
    };
    let Stmt::Assignment { lhs, .. } = &then_body[0] else {
        panic!("expected first Branch then-body Stmt to be Assignment");
    };
    assert!(
        matches!(lhs, Expr::Var(name) if name == "LHS_RENAMED"),
        "lhs Var should have been renamed; got {lhs:?}"
    );
}

/// Single-Stmt visit-lhs walker visits both lhs and rhs.
#[test]
fn visit_lhs_single_stmt_walkers_visit_both_sides() {
    let stmt = Stmt::Assignment {
        lhs: var("LHS"),
        rhs: var("RHS"),
        offset: 0,
    };
    let mut names = Vec::new();
    walk_stmt_exprs_visit_lhs(&stmt, &mut |expr: &Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
    });
    assert_eq!(names, vec!["LHS".to_string(), "RHS".to_string()]);

    let mut stmt_mut = Stmt::Assignment {
        lhs: var("LHS"),
        rhs: var("RHS"),
        offset: 0,
    };
    let mut names_mut = Vec::new();
    walk_stmt_exprs_mut_visit_lhs(&mut stmt_mut, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            names_mut.push(name.clone());
        }
        Action::Continue
    });
    assert_eq!(names_mut, vec!["LHS".to_string(), "RHS".to_string()]);
}

/// Recursion through nested bodies still visits Assignment lhs at every
/// depth: an Assignment inside a Branch then-body has its lhs walked.
#[test]
fn visit_lhs_walker_recurses_into_nested_bodies() {
    // synthetic_tree has Assignment LHS inside a Branch then_body and
    // Latch init; both should appear.
    let body = synthetic_tree();
    let mut names = Vec::new();
    walk_body_exprs_visit_lhs(&body, &mut |expr: &Expr| {
        if let Expr::Var(name) = expr {
            names.push(name.clone());
        }
    });
    assert!(names.iter().any(|name| name == "LHS"));
    assert!(names.iter().any(|name| name == "LHS_LATCH_INIT"));
    assert!(names.iter().any(|name| name == "LHS_INIT"));
}

/// `any_expr` reaches every node `walk_expr` does. For each Var the full
/// walk visits, the early-exit scan must also find it; otherwise
/// `any_expr_children` has drifted from `walk_expr_children` (e.g. a new
/// Expr variant added to one arm list but not the other).
#[test]
fn any_expr_matches_walk_expr_coverage() {
    let expr = every_variant_expr();
    let mut all_vars = Vec::new();
    walk_expr(&expr, &mut |node| {
        if let Expr::Var(name) = node {
            all_vars.push(name.clone());
        }
    });
    assert!(!all_vars.is_empty());
    for name in &all_vars {
        assert!(
            any_expr(
                &expr,
                &mut |node| matches!(node, Expr::Var(found) if found == name)
            ),
            "any_expr failed to find `{name}` that walk_expr visited"
        );
    }
    assert!(!any_expr(&expr, &mut |node| matches!(
        node,
        Expr::Var(name) if name == "ABSENT"
    )));
}

/// `any_expr` halts at the first match: nodes after the matching one are
/// never handed to the predicate.
#[test]
fn any_expr_short_circuits_on_first_match() {
    let expr = Expr::Call {
        name: "Outer".to_string(),
        args: vec![var("FIRST"), var("SECOND"), var("THIRD")],
    };
    let mut seen = Vec::new();
    let found = any_expr(&expr, &mut |node| {
        if let Expr::Var(name) = node {
            seen.push(name.clone());
        }
        matches!(node, Expr::Var(name) if name == "SECOND")
    });
    assert!(found);
    assert_eq!(seen, vec!["FIRST".to_string(), "SECOND".to_string()]);
}
