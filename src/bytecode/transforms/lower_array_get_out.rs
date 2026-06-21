//! Lower OUT-parameter array-get calls to canonical assignments.
//!
//! UE emits Blueprint array-fetch macros as static-library calls with
//! the result delivered through an OUT parameter, e.g.
//! `Array_Get(arr, idx, &out)`. Downstream matchers (notably
//! `find_foreach_item` in `refine_loops`) expect the canonical
//! `Stmt::Assignment { lhs: target, rhs: Index/Call }` shape.
//! Multi-OUT functions (`BreakHitResult` and friends) are NOT
//! assignments, so the rewrite is restricted to a small known list of
//! single-out array-get-style functions.
//!
//! Pipeline position: runs after `lower_static_library_calls` (so the
//! function name is canonical) and before `inline_single_use_temps`
//! (so the resulting Assignment participates in temp inlining like
//! any other Assignment).

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::rewrite_stmts_preorder;

/// Function names recognised as single-OUT array-get macros. The OUT
/// parameter is the last argument and represents the assignment lhs.
const ARRAY_GET_OUT_FUNCTIONS: &[&str] = &["Array_Get", "GetArrayItem"];

/// Rewrite recognised OUT-parameter array-get calls into assignments.
pub fn lower_array_get_out_to_assignment(body: &mut [Stmt]) {
    // Preorder. try_rewrite only matches single-OUT array-get Call statements,
    // which carry no child bodies, so interleaving the rewrite with the
    // descent is byte-identical to rewriting the whole level then recursing:
    // both a rewritten node (now an Assignment) and the original Call have no
    // sub-bodies to revisit, and statements that DO have children never match.
    rewrite_stmts_preorder(body, &mut |stmt| {
        if let Some(replacement) = try_rewrite(stmt) {
            *stmt = replacement;
        }
    });
}

/// Attempt to rewrite `stmt` if it is a recognised OUT-parameter
/// array-get call. Returns the replacement Assignment, or `None` if
/// the statement should stay as-is.
fn try_rewrite(stmt: &Stmt) -> Option<Stmt> {
    let Stmt::Call { func, args, offset } = stmt else {
        return None;
    };
    let name = match func {
        Expr::Var(name) => name.as_str(),
        _ => return None,
    };
    if !ARRAY_GET_OUT_FUNCTIONS.contains(&name) {
        return None;
    }
    if args.len() != 3 {
        return None;
    }
    // The function name guarantees the third arg is the OUT destination.
    // Accept both shapes: Expr::Out(inner) when the caller-side opcode or
    // signature lookup wrapped it, or bare expressions when the library
    // function's signature wasn't available at decode time. Library
    // functions live in other assets so their signatures aren't in the
    // local function_signatures map.
    let last = args.last()?;
    let target = match last {
        Expr::Out(inner) => (**inner).clone(),
        other => other.clone(),
    };
    let array = args[0].clone();
    let idx = args[1].clone();
    Some(Stmt::Assignment {
        lhs: target,
        rhs: Expr::Index {
            recv: Box::new(array),
            idx: Box::new(idx),
        },
        offset: *offset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::transforms::test_fixtures::var;

    fn call_stmt(name: &str, args: Vec<Expr>) -> Stmt {
        Stmt::Call {
            func: Expr::Var(name.into()),
            args,
            offset: 0,
        }
    }

    #[test]
    fn array_get_three_arg_lowers_to_assignment() {
        let mut body = vec![call_stmt(
            "Array_Get",
            vec![
                var("my_array"),
                var("idx"),
                Expr::Out(Box::new(var("item"))),
            ],
        )];
        lower_array_get_out_to_assignment(&mut body);
        match &body[0] {
            Stmt::Assignment { lhs, rhs, .. } => {
                assert_eq!(*lhs, var("item"));
                match rhs {
                    Expr::Index { recv, idx } => {
                        assert_eq!(**recv, var("my_array"));
                        assert_eq!(**idx, var("idx"));
                    }
                    _ => panic!("expected Index rhs"),
                }
            }
            _ => panic!("expected Assignment"),
        }
    }

    #[test]
    fn break_hit_result_unchanged() {
        // BreakHitResult has multiple OUT params; not in the list so
        // it must stay a Call. Using BreakHitResult here is symbolic;
        // the test passes a 3-arg call with the BreakHitResult name.
        let mut body = vec![call_stmt(
            "BreakHitResult",
            vec![
                var("hit"),
                var("ignored"),
                Expr::Out(Box::new(var("result"))),
            ],
        )];
        lower_array_get_out_to_assignment(&mut body);
        assert!(matches!(body[0], Stmt::Call { .. }));
    }

    #[test]
    fn array_get_with_bare_third_arg_lowers() {
        // Library functions (Array_Get, GetArrayItem) live in other assets;
        // their signatures aren't in the local function_signatures map, so
        // wrap_out_args at decode time can't mark the OUT-position arg.
        // The function name itself is the ground truth, the lowering pass
        // accepts bare expressions in the third slot.
        let mut body = vec![call_stmt(
            "Array_Get",
            vec![var("arr"), var("idx"), var("x")],
        )];
        lower_array_get_out_to_assignment(&mut body);
        match &body[0] {
            Stmt::Assignment { lhs, .. } => assert_eq!(*lhs, var("x")),
            _ => panic!("expected Assignment after lowering"),
        }
    }

    #[test]
    fn array_get_two_arg_unchanged() {
        // 2 args (no OUT) is the canonical fetch shape; must not be
        // rewritten because the matcher already accepts it.
        let mut body = vec![call_stmt("Array_Get", vec![var("arr"), var("idx")])];
        lower_array_get_out_to_assignment(&mut body);
        assert!(matches!(body[0], Stmt::Call { .. }));
    }

    #[test]
    fn get_array_item_alias_lowers() {
        let mut body = vec![call_stmt(
            "GetArrayItem",
            vec![var("arr"), var("idx"), Expr::Out(Box::new(var("item")))],
        )];
        lower_array_get_out_to_assignment(&mut body);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
    }

    #[test]
    fn lowering_recurses_into_branch() {
        let inner = call_stmt(
            "Array_Get",
            vec![var("arr"), var("i"), Expr::Out(Box::new(var("item")))],
        );
        let mut body = vec![Stmt::Branch {
            cond: Expr::Literal("true".into()),
            then_body: vec![inner],
            else_body: vec![],
            offset: 0,
        }];
        lower_array_get_out_to_assignment(&mut body);
        match &body[0] {
            Stmt::Branch { then_body, .. } => {
                assert!(matches!(then_body[0], Stmt::Assignment { .. }));
            }
            _ => panic!("expected Branch"),
        }
    }
}
