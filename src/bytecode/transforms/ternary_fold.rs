//! Ternary fold for the IR.
//!
//! Walks the decoded statement tree and rewrites `Stmt::Branch` shapes
//! whose `then_body` and `else_body` each consist of a single
//! `Stmt::Assignment` with structurally-equal lhs into one assignment
//! whose rhs is `Expr::Ternary`.
//!
//! Pattern:
//! ```text
//! if (cond) {
//!   X = a;
//! } else {
//!   X = b;
//! }
//! ```
//! collapses to:
//! ```text
//! X = cond ? a : b;
//! ```
//!
//! Conditions:
//!  - both branch bodies are exactly one statement
//!  - both statements are `Stmt::Assignment`
//!  - the two lhs expressions are structurally equal (`Expr` PartialEq)
//!  - neither `rhs` nor the branch `cond` contains `Expr::Unknown`
//!
//! Walks top-down so outer simple ternaries fold before nested
//! complex shapes are reduced; this matches the cascade-fold ordering
//! and prevents an inner fold from masking an outer two-arm Branch.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{
    expr_contains_unknown, walk_body_exprs_mut, walk_stmt_children_mut, Action,
};

/// Walk a statement body and fold `Branch` statements whose two arms
/// each contain a single matching `Assignment` into a single
/// `Stmt::Assignment` whose rhs is `Expr::Ternary`. Recurses into every
/// nested body so independent ternaries fold inside branches,
/// sequences, loops, switches, and latches.
pub fn fold_ternaries(body: &mut [Stmt]) {
    fold_in_body(body);
}

/// Rewrite expression-position `EX_SwitchValue` shapes whose index is a
/// bool-typed expression and whose two cases pair `true:` and `false:`
/// arms into an `Expr::Ternary { cond, then = true-arm, else = false-arm }`.
///
/// Blueprint compiles the editor's `(cond) ? a : b` ternary node as a
/// 2-arm `EX_SwitchValue` over a bool expression. The compiler's
/// `$Select_Default` sentinel sits in the default slot since both bool
/// values are covered by the cases. Folding the shape lets downstream
/// inlining collapse alias chains the bool-switch was keeping multi-use.
///
/// Walks every expression in the statement body via the shared mut
/// visitor; the walker's pre-order semantics mean nested bool-switches
/// (e.g. inside a Ternary's then-arm) fold on the same pass.
pub fn fold_bool_switches(body: &mut [Stmt]) {
    walk_body_exprs_mut(body, &mut |expr| {
        if let Some(folded) = try_fold_bool_switch(expr) {
            *expr = folded;
        }
        Action::Continue
    });
}

/// Returns `Some(Expr::Ternary { ... })` when `expr` is a 2-arm
/// `Expr::Switch` with `true:` / `false:` case values; otherwise `None`.
/// The case order on disk is not guaranteed, both `[true, false]` and
/// `[false, true]` arrangements are accepted and routed to the matching
/// then/else slot.
fn try_fold_bool_switch(expr: &Expr) -> Option<Expr> {
    let Expr::Switch {
        index,
        cases,
        default: _,
    } = expr
    else {
        return None;
    };
    if cases.len() != 2 {
        return None;
    }
    let value_a = bool_literal_value(&cases[0].value)?;
    let value_b = bool_literal_value(&cases[1].value)?;
    if value_a == value_b {
        return None;
    }
    // The compiler's `$Select_Default` sentinel is unreachable when both
    // bool values are covered, so the default arm is dropped without
    // inspecting it. A non-sentinel default is similarly unreachable
    // under bool semantics; either way the ternary is sound.
    let (then_arm, else_arm) = if value_a {
        (cases[0].body.clone(), cases[1].body.clone())
    } else {
        (cases[1].body.clone(), cases[0].body.clone())
    };
    Some(Expr::Ternary {
        cond: index.clone(),
        then_expr: Box::new(then_arm),
        else_expr: Box::new(else_arm),
    })
}

/// Recognise the bool literals the constant-opcode decoders emit
/// (`Expr::Literal("true")` / `Expr::Literal("false")`, see
/// `decode/expr_decode.rs::EX_TRUE` / `EX_FALSE`). Returns `None` for
/// any other shape, including integer-coded bool stand-ins, since those
/// can land in non-bool switches and should not trigger this fold.
fn bool_literal_value(expr: &Expr) -> Option<bool> {
    match expr {
        Expr::Literal(text) if text == "true" => Some(true),
        Expr::Literal(text) if text == "false" => Some(false),
        _ => None,
    }
}

fn fold_in_body(body: &mut [Stmt]) {
    // Top-down: try to fold each statement at this level before
    // recursing into its children. If we recursed first, an inner
    // ternary could collapse into a single Assignment, then the outer
    // Branch wouldn't match the "single Assignment per arm" shape.
    for stmt in body.iter_mut() {
        try_fold_branch_into_ternary(stmt);
        walk_stmt_children_mut(stmt, &mut |sub_body| fold_in_body(sub_body));
    }
}

/// If `stmt` is a `Stmt::Branch` matching the ternary fold pattern,
/// rewrite it in place to a `Stmt::Assignment` with `Expr::Ternary`
/// rhs. Otherwise leaves `stmt` unchanged.
fn try_fold_branch_into_ternary(stmt: &mut Stmt) {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        offset,
    } = stmt
    else {
        return;
    };

    if then_body.len() != 1 || else_body.len() != 1 {
        return;
    }

    let then_assign = match &then_body[0] {
        Stmt::Assignment { lhs, rhs, .. } => (lhs.clone(), rhs.clone()),
        _ => return,
    };
    let else_assign = match &else_body[0] {
        Stmt::Assignment { lhs, rhs, .. } => (lhs.clone(), rhs.clone()),
        _ => return,
    };

    if then_assign.0 != else_assign.0 {
        return;
    }
    if expr_contains_unknown(cond)
        || expr_contains_unknown(&then_assign.1)
        || expr_contains_unknown(&else_assign.1)
    {
        return;
    }

    let lhs = then_assign.0;
    let then_rhs = then_assign.1;
    let else_rhs = else_assign.1;
    let cond_clone = cond.clone();
    let stmt_offset = *offset;

    *stmt = Stmt::Assignment {
        lhs,
        rhs: Expr::Ternary {
            cond: Box::new(cond_clone),
            then_expr: Box::new(then_rhs),
            else_expr: Box::new(else_rhs),
        },
        offset: stmt_offset,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign_expr as assign, call, lit, var};

    fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: 0x10,
        }
    }

    #[test]
    fn simple_ternary_fold() {
        let mut body = vec![branch(
            var("Cond"),
            vec![assign(var("X"), lit("1"))],
            vec![assign(var("X"), lit("2"))],
        )];
        fold_ternaries(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Assignment { lhs, rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        assert_eq!(lhs, &var("X"));
        let Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } = rhs
        else {
            panic!("expected Ternary rhs, got {:?}", rhs);
        };
        assert_eq!(**cond, var("Cond"));
        assert_eq!(**then_expr, lit("1"));
        assert_eq!(**else_expr, lit("2"));
    }

    #[test]
    fn branch_with_multi_stmt_body_unchanged() {
        let mut body = vec![branch(
            var("Cond"),
            vec![assign(var("X"), lit("1")), call("Side", vec![])],
            vec![assign(var("X"), lit("2"))],
        )];
        fold_ternaries(&mut body);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    #[test]
    fn branch_with_different_lhs_unchanged() {
        let mut body = vec![branch(
            var("Cond"),
            vec![assign(var("X"), lit("1"))],
            vec![assign(var("Y"), lit("2"))],
        )];
        fold_ternaries(&mut body);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    #[test]
    fn branch_only_then_or_only_else_unchanged() {
        // Only-then.
        let mut body = vec![branch(
            var("Cond"),
            vec![assign(var("X"), lit("1"))],
            vec![],
        )];
        fold_ternaries(&mut body);
        assert!(matches!(body[0], Stmt::Branch { .. }));

        // Only-else.
        let mut body = vec![branch(
            var("Cond"),
            vec![],
            vec![assign(var("X"), lit("2"))],
        )];
        fold_ternaries(&mut body);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    #[test]
    fn nested_ternary_fold() {
        // An outer Branch whose then-arm is itself a foldable Branch.
        // The outer fold cannot match because its then-body is a
        // Branch, not an Assignment, so only the inner ternary lands
        // after recursion.
        let inner = branch(
            var("InnerCond"),
            vec![assign(var("X"), lit("1"))],
            vec![assign(var("X"), lit("2"))],
        );
        let mut body = vec![Stmt::Branch {
            cond: var("OuterCond"),
            then_body: vec![inner],
            else_body: vec![call("OtherSide", vec![])],
            offset: 0x20,
        }];
        fold_ternaries(&mut body);

        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("outer Branch should remain");
        };
        assert_eq!(then_body.len(), 1);
        let Stmt::Assignment { rhs, .. } = &then_body[0] else {
            panic!("inner branch should fold to Assignment with Ternary rhs");
        };
        assert!(matches!(rhs, Expr::Ternary { .. }));
    }

    #[test]
    fn unknown_cond_does_not_fold() {
        let unknown = Expr::Unknown {
            reason: "test".into(),
            raw_bytes: vec![],
            offset: 0,
        };
        let mut body = vec![branch(
            unknown,
            vec![assign(var("X"), lit("1"))],
            vec![assign(var("X"), lit("2"))],
        )];
        fold_ternaries(&mut body);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    fn bool_switch(index: Expr, true_body: Expr, false_body: Expr, true_first: bool) -> Expr {
        use crate::bytecode::expr::SwitchExprCase;
        let true_case = SwitchExprCase {
            value: lit("true"),
            body: true_body,
        };
        let false_case = SwitchExprCase {
            value: lit("false"),
            body: false_body,
        };
        let cases = if true_first {
            vec![true_case, false_case]
        } else {
            vec![false_case, true_case]
        };
        Expr::Switch {
            index: Box::new(index),
            cases,
            default: Box::new(var("$Select_Default")),
        }
    }

    #[test]
    fn bool_switch_true_first_folds_to_ternary() {
        let switch_expr = bool_switch(var("Cond"), lit("A"), lit("B"), true);
        let mut body = vec![assign(var("X"), switch_expr)];
        fold_bool_switches(&mut body);

        let Stmt::Assignment { rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        let Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } = rhs
        else {
            panic!("expected Ternary, got {:?}", rhs);
        };
        assert_eq!(**cond, var("Cond"));
        assert_eq!(**then_expr, lit("A"));
        assert_eq!(**else_expr, lit("B"));
    }

    #[test]
    fn bool_switch_false_first_routes_arms_correctly() {
        let switch_expr = bool_switch(var("Cond"), lit("A"), lit("B"), false);
        let mut body = vec![assign(var("X"), switch_expr)];
        fold_bool_switches(&mut body);

        let Stmt::Assignment { rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        let Expr::Ternary {
            then_expr,
            else_expr,
            ..
        } = rhs
        else {
            panic!("expected Ternary");
        };
        assert_eq!(**then_expr, lit("A"));
        assert_eq!(**else_expr, lit("B"));
    }

    #[test]
    fn nested_bool_switch_inside_field_access_folds() {
        // `switch(Cond) { false: R, true: L }.Field` is the
        // ApplyClimbingMovement shape: the switch sits behind a
        // FieldAccess. The walker should descend through FieldAccess
        // and fold the inner Switch.
        let switch_expr = bool_switch(var("Cond"), var("Left"), var("Right"), false);
        let field_access = Expr::FieldAccess {
            recv: Box::new(switch_expr),
            field: "Component".into(),
        };
        let mut body = vec![assign(var("X"), field_access)];
        fold_bool_switches(&mut body);

        let Stmt::Assignment { rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        let Expr::FieldAccess { recv, .. } = rhs else {
            panic!("expected FieldAccess");
        };
        assert!(matches!(recv.as_ref(), Expr::Ternary { .. }));
    }

    #[test]
    fn non_bool_switch_unchanged() {
        use crate::bytecode::expr::SwitchExprCase;
        let switch_expr = Expr::Switch {
            index: Box::new(var("EnumVar")),
            cases: vec![
                SwitchExprCase {
                    value: lit("0"),
                    body: lit("A"),
                },
                SwitchExprCase {
                    value: lit("1"),
                    body: lit("B"),
                },
            ],
            default: Box::new(var("$Select_Default")),
        };
        let mut body = vec![assign(var("X"), switch_expr)];
        fold_bool_switches(&mut body);

        let Stmt::Assignment { rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        assert!(matches!(rhs, Expr::Switch { .. }));
    }

    #[test]
    fn three_arm_bool_switch_unchanged() {
        // A 3-arm switch with bool literals shouldn't fold; the third
        // arm has no semantic equivalent in a binary ternary.
        use crate::bytecode::expr::SwitchExprCase;
        let switch_expr = Expr::Switch {
            index: Box::new(var("Cond")),
            cases: vec![
                SwitchExprCase {
                    value: lit("true"),
                    body: lit("A"),
                },
                SwitchExprCase {
                    value: lit("false"),
                    body: lit("B"),
                },
                SwitchExprCase {
                    value: lit("true"),
                    body: lit("C"),
                },
            ],
            default: Box::new(var("$Select_Default")),
        };
        let mut body = vec![assign(var("X"), switch_expr)];
        fold_bool_switches(&mut body);

        let Stmt::Assignment { rhs, .. } = &body[0] else {
            panic!("expected Assignment");
        };
        assert!(matches!(rhs, Expr::Switch { .. }));
    }
}
