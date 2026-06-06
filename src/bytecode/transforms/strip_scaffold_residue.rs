//! Strip residual constant-true Branch / empty-pin Sequence scaffold from
//! statement bodies as a final cleanup pass.
//!
//! After `latch_recognition` and `inline_single_use_temps` collapse DoOnce
//! gate variables into their literal values, some scaffold-shaped Branches
//! remain visible at the body level (not inside Sequence pins, where D.1's
//! `is_scaffold_noop_branch` already handles them). These are no-op shapes
//! left over from the structurer's pop_flow handling and add no semantic
//! content, only visual noise.
//!
//! Two shapes are removed, recursively, after first cleaning every nested
//! body:
//!
//! - `Stmt::Branch { cond: Literal("true"), then_body: [], else_body: [] }`
//!   — a fully empty constant-true Branch.
//! - `Stmt::Branch { cond: Literal("true"), then_body: [<all-noop>],
//!   else_body: [] }` whose `then_body`, after recursive cleanup, becomes
//!   empty. This is the nested wrapper shape, `if (true) { Sequence{...} }`
//!   where every pin in the Sequence was itself empty or noop.
//! - `Stmt::Sequence { pins }` where every pin is empty after recursive
//!   cleanup. A noop-only Sequence carries no statements to emit.
//!
//! Conservative: a Branch is removed only when its arm bodies are empty
//! after recursion. Real statement content keeps the Branch alive, so
//! a deliberate `if (true) { Foo() }` shape (if such a thing existed) is
//! preserved.
//!
//! This pass cleans at the structured Stmt tree post-structuring, since
//! the residue surfaces only after the inliner has substituted gate
//! variables for their literal values.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::walk_stmt_children_mut;

/// Recursively strip constant-true noop Branches and empty-pin Sequences
/// from `body`. Runs over every nested sub-body before evaluating the
/// outer wrapper so a `if (true) { Sequence{[], []} }` collapses in one
/// pass: the Sequence empties, the Branch's `then_body` empties, the
/// Branch is removed.
pub fn strip_scaffold_residue(body: &mut Vec<Stmt>) {
    // Recurse into children first so inner residues are removed before
    // the outer wrapper is checked. Without this, an `if (true) { Seq{} }`
    // shape would keep its Branch alive on the first pass (Seq is non-empty
    // until its pins are visited) and need a second pass to collapse.
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut strip_scaffold_residue);
    }

    body.retain(|stmt| !is_removable_residue(stmt));
}

/// Return `true` when `stmt` is a fully-empty constant-true Branch or a
/// Sequence whose every pin is empty. Both shapes are scaffold residue
/// safe to drop. Called after children have been cleaned so the emptiness
/// check sees the post-cleanup shape.
fn is_removable_residue(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => is_literal_true(cond) && then_body.is_empty() && else_body.is_empty(),
        Stmt::Sequence { pins, .. } => pins.iter().all(|pin| pin.is_empty()),
        _ => false,
    }
}

/// Return `true` when `expr` is `Expr::Literal("true")`. The inliner
/// substitutes DoOnce gate variables for their literal `"true"` values
/// once the variable has only one use, leaving this exact shape behind
/// in scaffold Branch conditions.
fn is_literal_true(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(text) if text == "true")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    fn lit_true() -> Expr {
        Expr::Literal("true".to_string())
    }

    fn call(name: &str) -> Stmt {
        Stmt::Call {
            func: Expr::Var(name.to_string()),
            args: vec![],
            offset: 0,
        }
    }

    #[test]
    fn removes_empty_constant_true_branch() {
        let mut body = vec![
            call("Foo"),
            Stmt::Branch {
                cond: lit_true(),
                then_body: vec![],
                else_body: vec![],
                offset: 0,
            },
            call("Bar"),
        ];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 2);
        assert!(matches!(&body[0], Stmt::Call { .. }));
        assert!(matches!(&body[1], Stmt::Call { .. }));
    }

    #[test]
    fn collapses_constant_true_wrapping_empty_sequence() {
        let mut body = vec![Stmt::Branch {
            cond: lit_true(),
            then_body: vec![Stmt::Sequence {
                pins: vec![vec![], vec![]],
                offset: 0,
            }],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert!(body.is_empty());
    }

    #[test]
    fn collapses_nested_constant_true_wrappers() {
        let mut body = vec![Stmt::Branch {
            cond: lit_true(),
            then_body: vec![Stmt::Sequence {
                pins: vec![
                    vec![Stmt::Branch {
                        cond: lit_true(),
                        then_body: vec![],
                        else_body: vec![],
                        offset: 0,
                    }],
                    vec![],
                ],
                offset: 0,
            }],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert!(body.is_empty());
    }

    #[test]
    fn preserves_constant_true_branch_with_real_content() {
        let mut body = vec![Stmt::Branch {
            cond: lit_true(),
            then_body: vec![call("Foo")],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
    }

    #[test]
    fn preserves_non_true_constant_branch_even_when_empty() {
        let mut body = vec![Stmt::Branch {
            cond: Expr::Literal("false".to_string()),
            then_body: vec![],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn preserves_variable_cond_branch_even_when_empty() {
        let mut body = vec![Stmt::Branch {
            cond: Expr::Var("Gate".to_string()),
            then_body: vec![],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn preserves_sequence_with_real_content_in_any_pin() {
        let mut body = vec![Stmt::Sequence {
            pins: vec![vec![call("Foo")], vec![]],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Sequence { pins, .. } = &body[0] else {
            panic!("expected Sequence");
        };
        assert_eq!(pins.len(), 2);
        assert_eq!(pins[0].len(), 1);
    }

    #[test]
    fn cleans_residue_inside_branch_arms() {
        let mut body = vec![Stmt::Branch {
            cond: Expr::Var("UserCond".to_string()),
            then_body: vec![
                call("Real"),
                Stmt::Branch {
                    cond: lit_true(),
                    then_body: vec![],
                    else_body: vec![],
                    offset: 0,
                },
            ],
            else_body: vec![],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
    }

    #[test]
    fn cleans_residue_inside_sequence_pins() {
        let mut body = vec![Stmt::Sequence {
            pins: vec![
                vec![
                    call("Real"),
                    Stmt::Branch {
                        cond: lit_true(),
                        then_body: vec![],
                        else_body: vec![],
                        offset: 0,
                    },
                ],
                vec![call("RealToo")],
            ],
            offset: 0,
        }];
        strip_scaffold_residue(&mut body);
        let Stmt::Sequence { pins, .. } = &body[0] else {
            panic!("expected Sequence");
        };
        assert_eq!(pins[0].len(), 1);
        assert_eq!(pins[1].len(), 1);
    }
}
