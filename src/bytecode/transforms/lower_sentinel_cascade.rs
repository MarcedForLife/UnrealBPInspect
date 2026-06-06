//! Sentinel `!=` cascade lowering for the IR.
//!
//! The Blueprint compiler emits enum-switch dispatch as a temp-driven
//! cascade rather than a direct `==` chain. The text shape is:
//! ```text
//! $SwitchEnum_CmpSuccess = (Status != 0)
//! if ($SwitchEnum_CmpSuccess) {
//!     $SwitchEnum_CmpSuccess = (Status != 1)
//!     if ($SwitchEnum_CmpSuccess) {
//!         ...
//!     } else {
//!         // case 1 body
//!     }
//! } else {
//!     // case 0 body
//! }
//! ```
//! In the IR this lands as `Stmt::Assignment` (rhs is `BinaryOp::Ne`)
//! immediately followed by `Stmt::Branch` whose condition is the same temp.
//! The downstream `cascade_fold` matcher only accepts direct `==` chains,
//! so it never fires on this real-fixture shape.
//!
//! This pass canonicalises the pattern: when a single-use temp is
//! assigned an `Ne` and then branched on, the assignment is dropped and
//! the branch becomes `if (X == N) <original_else> else <original_then>`
//! (then/else swapped because we negated the condition). After lowering,
//! `cascade_fold` sees a clean `==` chain and folds it to `Stmt::Switch`.
//!
//! The recognition is structural, never name-based. The single-use
//! invariant prevents rewriting cases where the temp carries semantics
//! beyond the immediate branch.

use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{
    resolve_expr_chain, resolve_var_chain, walk_bodies_with_ancestors_mut, walk_expr,
    walk_stmt_children_mut,
};

/// Walk a statement body, lowering `[Var = X != N; if (Var) A else B]`
/// pairs to `[if (X == N) B else A]` when `Var` is referenced exactly
/// once across the surrounding body. Recurses into every nested
/// `Vec<Stmt>` so the pattern lowers at every level.
pub fn lower_sentinel_cascade(body: &mut Vec<Stmt>) {
    lower_in_body(body, &[]);
}

/// `ancestors` is innermost-first: each slice is the preceding-siblings
/// view at one outer nesting level. Chain resolution at the current scope
/// starts with `body` itself and walks outward through `ancestors`.
fn lower_in_body(body: &mut Vec<Stmt>, ancestors: &[&[Stmt]]) {
    // Lower top-down at the current scope first so the rewritten branch
    // inherits the original adjacency. Then descend into every nested
    // body so a pattern hidden inside a then/else, case, loop body, etc.
    // also lowers.
    //
    // First pass: scan each Branch with a `Var($X)` cond and try the
    // chain-aware rewrite. The temp's defining `Ne` assignment can sit
    // anywhere in `body` (not just immediately above the Branch); the
    // matcher walks `resolve_var_chain` to find it. This subsumes the
    // adjacent shape: when the def is at `idx - 1`, chain resolution
    // returns the Ne directly.
    let mut idx = 0;
    while idx < body.len() {
        if try_lower_branch_via_chain(body, idx, ancestors) {
            // The rewrite removed the temp's def (anywhere in body) and
            // replaced the Branch in place. Don't advance: the rewritten
            // Branch could itself be the head of another sentinel chain
            // whose temp def now lives earlier in the (shrunken) body.
            continue;
        }
        idx += 1;
    }

    // Descend into nested bodies, threading preceding-siblings prefix as
    // the new innermost ancestor.
    walk_bodies_with_ancestors_mut(body, ancestors, &mut |stmt, child_ancestors| {
        walk_stmt_children_mut(stmt, &mut |sub_body| {
            lower_in_body(sub_body, child_ancestors)
        });
    });
}

/// Attempt to lower the Branch at `body[branch_idx]` when its cond is
/// `Var($temp)` and the temp's chain-resolved definition is `X != Y`.
/// Returns `true` if the rewrite fired (body shortened by one
/// statement, branch slot replaced with the canonical `Eq` form). The
/// temp's def can sit anywhere in `body` or in any of `ancestors`; the
/// matcher walks the full scope stack innermost-first.
fn try_lower_branch_via_chain(
    body: &mut Vec<Stmt>,
    branch_idx: usize,
    ancestors: &[&[Stmt]],
) -> bool {
    // Step 1: confirm the slot is a Branch whose cond is `Var($temp)`.
    let temp_name = match &body[branch_idx] {
        Stmt::Branch {
            cond: Expr::Var(name),
            ..
        } => name.clone(),
        _ => return false,
    };

    // Step 2: chain-resolve the temp across the scope stack. The terminal
    // must be `Binary{Ne, _, _}`. Intermediate `Var($Y) = $Z` aliases are
    // walked by `resolve_var_chain`; only the final non-Var expression
    // is inspected here.
    // Build the scope stack for chain resolution and capture the resolved
    // Ne operands as owned clones BEFORE any mutation of `body`. We need
    // to mutate `body` later (Step 5/6), and `resolved` borrows from one
    // of the scope slices including `body` itself, so the clone has to
    // happen up front.
    let resolved_ne_operands: Option<(Expr, Expr)> = {
        let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
        scopes.push(body.as_slice());
        scopes.extend(ancestors.iter().copied());
        match resolve_var_chain(&scopes, &temp_name) {
            Some(Expr::Binary {
                op: BinaryOp::Ne,
                lhs,
                rhs,
            }) => {
                // Deep-resolve operand sub-expressions: a chain hop may
                // expose `Ne(Var($Y), N)` where `$Y` further resolves to
                // a Call or FieldAccess. Without the deep walk, the
                // canonical Eq form would carry an opaque temp ref that
                // downstream cascade-fold can't structurally compare.
                let lhs_deep = resolve_expr_chain(lhs, &scopes);
                let rhs_deep = resolve_expr_chain(rhs, &scopes);
                Some((lhs_deep, rhs_deep))
            }
            _ => None,
        }
    };
    let resolved_ne_operands = match resolved_ne_operands {
        Some(operands) => operands,
        None => return false,
    };

    // Step 3: locate the FIRST top-level Assignment whose lhs is the
    // temp name in the current body. We only rewrite when the def lives
    // here, an ancestor-only def stays put (rewriting it would mutate a
    // parent body we don't own). If the chain has multiple hops
    // (`$X = $Y; $Y = $Z != N`), only the head alias `$X = $Y` is
    // removed; the deeper alias `$Y` remains. That is intentional: an
    // intermediate alias may have other uses, and resolving them is the
    // inliner's job. The single-use guard below ensures the head alias
    // has only one use (the Branch we're rewriting).
    let def_idx = body.iter().position(|stmt| {
        matches!(
            stmt,
            Stmt::Assignment {
                lhs: Expr::Var(name),
                ..
            } if *name == temp_name,
        )
    });
    let def_idx = match def_idx {
        Some(i) => i,
        None => return false,
    };

    // Step 4: single-use guard. The temp must appear exactly once at
    // the CURRENT scope level (the Branch's cond). Counts do not
    // recurse into nested sub-bodies: each cascade level reuses the
    // same temp name and operates in its own scope, safe regardless of
    // the outer rewrite. The Assignment lhs is a def, not a use.
    if count_var_uses_at_top_level(body, &temp_name) != 1 {
        return false;
    }

    // Step 5: chain-aware rewrite path. We need the cloned `Eq` operands
    // for the new Branch cond. If the def is a direct `Ne` assignment
    // (the common case, including the original adjacent shape), we move
    // the operands out by replacing the assignment in place. If the def
    // is a `Var($Y)` alias, we clone the resolved Ne operands instead;
    // the def slot is still removed but the chain target is left intact
    // for the inliner (or other passes) to clean up later.
    let direct_ne = matches!(
        &body[def_idx],
        Stmt::Assignment {
            rhs: Expr::Binary {
                op: BinaryOp::Ne,
                ..
            },
            ..
        }
    );
    let (eq_lhs, eq_rhs) = if direct_ne {
        let placeholder = Stmt::Unknown {
            reason: String::new(),
            raw_bytes: Vec::new(),
            offset: 0,
            length: 0,
        };
        match std::mem::replace(&mut body[def_idx], placeholder) {
            Stmt::Assignment {
                rhs: Expr::Binary { lhs, rhs, .. },
                ..
            } => (*lhs, *rhs),
            _ => return false,
        }
    } else {
        // Alias hop. Use the pre-cloned resolved Ne operands.
        resolved_ne_operands
    };

    // Step 6: take the Branch fields and build the canonical
    // `if (X == N) <original_else> else <original_then>` shape.
    let placeholder_branch = Stmt::Unknown {
        reason: String::new(),
        raw_bytes: Vec::new(),
        offset: 0,
        length: 0,
    };
    let original_branch = std::mem::replace(&mut body[branch_idx], placeholder_branch);

    let (then_body, else_body, branch_offset) = match original_branch {
        Stmt::Branch {
            then_body,
            else_body,
            offset,
            ..
        } => (then_body, else_body, offset),
        _ => return false,
    };

    let new_branch = Stmt::Branch {
        cond: Expr::Binary {
            op: BinaryOp::Eq,
            lhs: Box::new(eq_lhs),
            rhs: Box::new(eq_rhs),
        },
        then_body: else_body,
        else_body: then_body,
        offset: branch_offset,
    };

    // Remove the def slot (now a placeholder Unknown) and overwrite the
    // branch slot. Order matters: removing first shifts indices; the
    // branch index adjusts when the def sat before it.
    body.remove(def_idx);
    let adjusted_branch_idx = if def_idx < branch_idx {
        branch_idx - 1
    } else {
        branch_idx
    };
    body[adjusted_branch_idx] = new_branch;
    true
}

/// Count `Expr::Var(name)` occurrences at the CURRENT scope level only,
/// without recursing into nested `Vec<Stmt>` slots (Branch then/else,
/// Loop body, Switch cases, Latch init/body, Sequence pins). Assignment
/// lhs positions are defs, not uses.
///
/// This is deliberately narrower than `expr_transforms::count_var_uses`.
/// The cascade compiler reuses one temp name across nested levels:
/// the outer Branch's then-body re-assigns the same `$SwitchEnum_CmpSuccess`
/// before reading it. Each level is a fresh def-use chain in its own scope,
/// so the outer rewrite stays safe regardless of inner uses.
///
/// What the counter still walks at the current scope:
/// - Assignment rhs (`t = X`, where `X` may reference `name`)
/// - Call func and args, Return value
/// - Branch cond (the use we expect to see)
/// - Loop cond and ForEach array expression (current-scope reads)
/// - Switch expr and case values (current-scope reads)
fn count_var_uses_at_top_level(body: &[Stmt], name: &str) -> usize {
    body.iter()
        .map(|stmt| count_var_uses_in_stmt_top_level(stmt, name))
        .sum()
}

fn count_var_uses_in_stmt_top_level(stmt: &Stmt, name: &str) -> usize {
    match stmt {
        Stmt::Assignment { rhs, .. } => count_var_uses_in_expr(rhs, name),
        Stmt::Call { func, args, .. } => {
            let mut total = count_var_uses_in_expr(func, name);
            for arg in args {
                total += count_var_uses_in_expr(arg, name);
            }
            total
        }
        Stmt::Return { value, .. } => value
            .as_ref()
            .map(|expr| count_var_uses_in_expr(expr, name))
            .unwrap_or(0),
        Stmt::Branch { cond, .. } => count_var_uses_in_expr(cond, name),
        Stmt::Loop { cond, kind, .. } => {
            let mut total = cond
                .as_ref()
                .map(|expr| count_var_uses_in_expr(expr, name))
                .unwrap_or(0);
            if let crate::bytecode::stmt::LoopKind::ForEach { array, .. } = kind {
                total += count_var_uses_in_expr(array, name);
            }
            total
        }
        Stmt::Switch { expr, cases, .. } => {
            let mut total = count_var_uses_in_expr(expr, name);
            for case in cases {
                for value in &case.values {
                    total += count_var_uses_in_expr(value, name);
                }
            }
            total
        }
        Stmt::Sequence { .. }
        | Stmt::Latch { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => 0,
    }
}

fn count_var_uses_in_expr(expr: &Expr, name: &str) -> usize {
    let mut count = 0;
    walk_expr(expr, &mut |node| {
        if matches!(node, Expr::Var(other) if other == name) {
            count += 1;
        }
    });
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::BinaryOp;
    use crate::bytecode::stmt::{Stmt, SwitchCase};
    use crate::bytecode::transforms::cascade_fold::fold_switch_cascades;
    use crate::bytecode::transforms::test_fixtures::{call, lit, var};

    fn ne(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Ne,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn eq(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Eq,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn assign_ne(temp: &str, lhs: Expr, rhs: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: var(temp),
            rhs: ne(lhs, rhs),
            offset: 0,
        }
    }

    fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: 0x42,
        }
    }

    #[test]
    fn simple_sentinel_lowers() {
        // [t = X != 5; if (t) A else B] -> [if (X == 5) B else A]
        let mut body = vec![
            assign_ne("t", var("X"), lit("5")),
            branch(var("t"), vec![call("A", vec![])], vec![call("B", vec![])]),
        ];

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), 1, "pair should collapse to one branch");
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset,
        } = &body[0]
        else {
            panic!("expected Stmt::Branch");
        };
        assert_eq!(cond, &eq(var("X"), lit("5")));
        assert_eq!(*offset, 0x42, "branch offset preserved");
        // then/else swapped: original-else (B) is now the then-body.
        assert_eq!(then_body.len(), 1);
        assert!(matches!(&then_body[0], Stmt::Call { func, .. } if func == &var("B")));
        assert_eq!(else_body.len(), 1);
        assert!(matches!(&else_body[0], Stmt::Call { func, .. } if func == &var("A")));
    }

    #[test]
    fn multi_use_temp_does_not_lower() {
        // Temp `t` referenced in the branch AND a later return statement.
        // Lowering would silently drop the assignment that the return depends on.
        let mut body = vec![
            assign_ne("t", var("X"), lit("0")),
            branch(var("t"), vec![call("A", vec![])], vec![]),
            Stmt::Return {
                value: Some(var("t")),
                offset: 0x99,
            },
        ];
        let original_len = body.len();

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), original_len, "body should be unchanged");
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Branch { .. }));
        assert!(matches!(body[2], Stmt::Return { .. }));
    }

    #[test]
    fn non_ne_assignment_does_not_lower() {
        // Assignment is `==`, not `!=`. Already in canonical form.
        let mut body = vec![
            Stmt::Assignment {
                lhs: var("t"),
                rhs: eq(var("X"), lit("0")),
                offset: 0,
            },
            branch(var("t"), vec![call("A", vec![])], vec![]),
        ];

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Branch { .. }));
    }

    #[test]
    fn branch_uses_different_var_does_not_lower() {
        // Assignment writes `t`, branch reads `u`.
        let mut body = vec![
            assign_ne("t", var("X"), lit("0")),
            branch(var("u"), vec![call("A", vec![])], vec![]),
        ];

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Branch { .. }));
    }

    #[test]
    fn non_adjacent_assignment_lowers_via_chain() {
        // An unrelated call separates the assignment from the Branch.
        // The chain-aware matcher walks `resolve_var_chain` to locate
        // the temp's defining `Ne` assignment regardless of position,
        // so the rewrite still fires. Single-use guard remains in
        // force; the call here doesn't reference `t`.
        let mut body = vec![
            assign_ne("t", var("X"), lit("0")),
            call("Unrelated", vec![]),
            branch(var("t"), vec![call("A", vec![])], vec![call("B", vec![])]),
        ];

        lower_sentinel_cascade(&mut body);

        // Body shortens by one: [Call, Branch{Eq, swapped arms}].
        assert_eq!(body.len(), 2);
        assert!(matches!(&body[0], Stmt::Call { func, .. } if func == &var("Unrelated")));
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } = &body[1]
        else {
            panic!("expected Stmt::Branch");
        };
        assert_eq!(cond, &eq(var("X"), lit("0")));
        // then/else swapped: original-else (B) now is the then-body.
        assert!(matches!(&then_body[0], Stmt::Call { func, .. } if func == &var("B")));
        assert!(matches!(&else_body[0], Stmt::Call { func, .. } if func == &var("A")));
    }

    #[test]
    fn non_adjacent_with_other_use_does_not_lower() {
        // Same shape as `non_adjacent_assignment_lowers_via_chain` but
        // an extra Return references `t`, so the single-use guard rejects
        // the rewrite. Mirrors `multi_use_temp_does_not_lower` but with
        // the assign + branch separated by an unrelated statement.
        let mut body = vec![
            assign_ne("t", var("X"), lit("0")),
            call("Unrelated", vec![]),
            branch(var("t"), vec![call("A", vec![])], vec![]),
            Stmt::Return {
                value: Some(var("t")),
                offset: 0x99,
            },
        ];
        let original_len = body.len();

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), original_len, "body should be unchanged");
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Call { .. }));
        assert!(matches!(body[2], Stmt::Branch { .. }));
        assert!(matches!(body[3], Stmt::Return { .. }));
    }

    #[test]
    fn non_adjacent_def_below_branch_lowers() {
        // Cond's defining assignment sits AFTER the Branch (an unusual
        // shape but resolve_var_chain doesn't care about order). The
        // chain-aware path still finds the def by name and rewrites.
        // This shape is unlikely in real Blueprint output but locks in
        // the lookup-by-name behavior.
        let mut body = vec![
            branch(var("t"), vec![call("A", vec![])], vec![call("B", vec![])]),
            assign_ne("t", var("X"), lit("0")),
        ];

        lower_sentinel_cascade(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Branch { cond, .. } = &body[0] else {
            panic!("expected Stmt::Branch");
        };
        assert_eq!(cond, &eq(var("X"), lit("0")));
    }

    #[test]
    fn nested_sentinel_lowers_recursively() {
        // Outer Branch's else_body contains a sentinel pair. Both should
        // lower (the outer is itself unaffected at the top level, but its
        // inner pair collapses).
        let inner_pair = vec![
            assign_ne("t", var("Status"), lit("1")),
            branch(
                var("t"),
                vec![call("Inner1", vec![])],
                vec![call("Inner0", vec![])],
            ),
        ];
        let outer = Stmt::Branch {
            cond: var("OuterFlag"),
            then_body: vec![call("Outer", vec![])],
            else_body: inner_pair,
            offset: 0x10,
        };
        let mut body = vec![outer];

        lower_sentinel_cascade(&mut body);

        // Outer Branch unchanged. Its else_body now holds a single Branch
        // (the lowered pair) instead of [Assignment, Branch].
        assert_eq!(body.len(), 1);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("outer expected to remain a Branch");
        };
        assert_eq!(else_body.len(), 1, "inner pair should have collapsed");
        let Stmt::Branch {
            cond,
            then_body,
            else_body: inner_else,
            ..
        } = &else_body[0]
        else {
            panic!("inner expected to be a Branch");
        };
        assert_eq!(cond, &eq(var("Status"), lit("1")));
        assert!(matches!(&then_body[0], Stmt::Call { func, .. } if func == &var("Inner0")));
        assert!(matches!(&inner_else[0], Stmt::Call { func, .. } if func == &var("Inner1")));
    }

    #[test]
    fn feeds_cascade_fold() {
        // A 3-arm sentinel cascade in the shape the Blueprint compiler
        // emits for an enum switch. After lowering + cascade_fold, the
        // result should be a single Stmt::Switch with three cases.
        //
        // Source shape:
        //   t = Status != 0
        //   if (t) {
        //       t = Status != 1
        //       if (t) {
        //           t = Status != 2
        //           if (t) { Default }
        //           else    { Case2  }
        //       } else      { Case1  }
        //   } else          { Case0  }
        let inner3 = vec![
            assign_ne("t", var("Status"), lit("2")),
            branch(
                var("t"),
                vec![call("Default", vec![])],
                vec![call("Case2", vec![])],
            ),
        ];
        let inner2 = vec![
            assign_ne("t", var("Status"), lit("1")),
            branch(var("t"), inner3, vec![call("Case1", vec![])]),
        ];
        let mut body = vec![
            assign_ne("t", var("Status"), lit("0")),
            branch(var("t"), inner2, vec![call("Case0", vec![])]),
        ];

        lower_sentinel_cascade(&mut body);
        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1, "cascade should collapse to one Switch");
        let Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } = &body[0]
        else {
            panic!("expected Stmt::Switch");
        };
        assert_eq!(expr, &var("Status"));
        assert_eq!(cases.len(), 3, "expected three case arms (0, 1, 2)");
        let case_values: Vec<Vec<&Expr>> = cases
            .iter()
            .map(|c: &SwitchCase| c.values.iter().collect())
            .collect();
        assert_eq!(
            case_values,
            vec![vec![&lit("0")], vec![&lit("1")], vec![&lit("2")]],
        );
        let default_body = default.as_ref().expect("default expected");
        assert_eq!(default_body.len(), 1);
        assert!(matches!(&default_body[0], Stmt::Call { func, .. } if func == &var("Default")));
    }
}
