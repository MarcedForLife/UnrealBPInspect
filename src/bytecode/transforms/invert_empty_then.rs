//! Invert empty-then Branch arms so the body lives in the then-arm.
//!
//! The region emitter chooses which CFG successor becomes the body arm
//! from the JIN-taken side. For some shapes this leaves `then_body`
//! empty and `else_body` carrying the work, producing
//! `if (cond) {} else { body }`. This pass rewrites the shape as
//! `if (!cond) { body }`, swapping arms and negating the condition.
//! Double-negation is collapsed via `visit::negated_operand`, so an
//! already-negated condition unwraps rather than nesting another
//! `Unary { Not, ... }`.
//!
//! Branches with both arms empty stay untouched. An empty-both-arms
//! branch with a real (non-literal-true) condition is a diagnostic
//! signal that an earlier pass cleared a body it shouldn't have;
//! dropping the wrapper would hide that bug. `strip_scaffold_residue`
//! already drops the `cond: Literal("true")` scaffold shape.
//!
//! Runs late in the transform stack (after `fold_ternaries`, before
//! `normalize_var_names`) so cascade-fold and sentinel-cascade have
//! already consumed the un-inverted shape.

use crate::bytecode::expr::{Expr, UnaryOp};
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{negated_operand, walk_stmt_children_mut};

pub fn invert_empty_then_branches(body: &mut Vec<Stmt>) {
    body.retain_mut(|stmt| {
        walk_stmt_children_mut(stmt, &mut invert_empty_then_branches);
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } = stmt
        else {
            return true;
        };
        if then_body.is_empty() && !else_body.is_empty() {
            let placeholder = Expr::Literal(String::new());
            let old_cond = std::mem::replace(cond, placeholder);
            *cond = negate_cond(old_cond);
            std::mem::swap(then_body, else_body);
        }
        true
    });
}

fn negate_cond(cond: Expr) -> Expr {
    if let Some(inner) = negated_operand(&cond) {
        return inner.clone();
    }
    Expr::Unary {
        op: UnaryOp::Not,
        operand: Box::new(cond),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::transforms::test_fixtures::{call, lit, var};

    fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: 0,
        }
    }

    #[test]
    fn invert_simple_empty_then() {
        let mut body = vec![branch(lit("cond"), vec![], vec![call("Body", vec![])])];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        assert!(matches!(
            cond,
            Expr::Unary {
                op: UnaryOp::Not,
                ..
            }
        ));
        assert_eq!(then_body.len(), 1);
        assert!(else_body.is_empty());
    }

    #[test]
    fn keep_empty_both_arms_with_real_cond() {
        // Empty-both-arms with a real condition is a diagnostic signal
        // that an upstream pass cleared the body. Must stay visible.
        let mut body = vec![branch(lit("RealCond > 0"), vec![], vec![])];
        invert_empty_then_branches(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        assert!(then_body.is_empty());
        assert!(else_body.is_empty());
    }

    #[test]
    fn keep_canonical_then_with_empty_else() {
        let mut body = vec![branch(lit("cond"), vec![call("Body", vec![])], vec![])];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        assert!(matches!(cond, Expr::Literal(s) if s == "cond"));
        assert_eq!(then_body.len(), 1);
        assert!(else_body.is_empty());
    }

    #[test]
    fn keep_both_arms_nonempty() {
        let mut body = vec![branch(
            lit("cond"),
            vec![call("Then", vec![])],
            vec![call("Else", vec![])],
        )];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
        assert_eq!(else_body.len(), 1);
    }

    #[test]
    fn collapse_double_negation_unary() {
        let already_negated = Expr::Unary {
            op: UnaryOp::Not,
            operand: Box::new(var("X")),
        };
        let mut body = vec![branch(already_negated, vec![], vec![call("Body", vec![])])];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch { cond, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert!(matches!(cond, Expr::Var(name) if name == "X"));
    }

    #[test]
    fn collapse_not_prebool_call() {
        let already_negated = Expr::Call {
            name: "Not_PreBool".to_string(),
            args: vec![var("X")],
        };
        let mut body = vec![branch(already_negated, vec![], vec![call("Body", vec![])])];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch { cond, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert!(matches!(cond, Expr::Var(name) if name == "X"));
    }

    #[test]
    fn recurse_into_else_body() {
        let inner = branch(lit("inner"), vec![], vec![call("Inner", vec![])]);
        let outer = branch(lit("outer"), vec![call("Pre", vec![])], vec![inner]);
        let mut body = vec![outer];
        invert_empty_then_branches(&mut body);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("expected outer Branch");
        };
        let Stmt::Branch {
            cond, then_body, ..
        } = &else_body[0]
        else {
            panic!("expected inner Branch");
        };
        assert!(matches!(
            cond,
            Expr::Unary {
                op: UnaryOp::Not,
                ..
            }
        ));
        assert_eq!(then_body.len(), 1);
    }
}
