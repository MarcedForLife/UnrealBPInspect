//! Shared variable-reference primitives for the IR transforms.
//!
//! Several passes count how often a `Var(name)` is used or rename one variable
//! to another. Those operations were re-implemented per pass with subtly
//! different, unstated scope policies. This module spells the policy out as
//! arguments and delegates to the canonical `visit.rs` walkers, so the
//! counters share one exhaustive `Stmt`/`Expr` arm list instead of each
//! carrying its own.
//!
//! Two orthogonal policy axes:
//! - [`VarScope`]: `Deep` walks the whole subtree; `CurrentLevel` reads only
//!   the expressions a top-level statement owns directly, never entering a
//!   nested body (Branch arms, Loop body, Switch case bodies, Latch init/body,
//!   Sequence pins).
//! - [`Defs`]: `SkipLhs` ignores `Assignment` left-hand sides (a write is a
//!   def, not a use); `VisitLhs` counts them, so a `Var(name)` inside an
//!   `Assignment` lhs `FieldAccess` (a field-write back into the temp) counts
//!   as a use of that temp.
//!
//! Deliberately OUT of scope, with their own helpers: the common
//! subexpression elimination (CSE) family in `cse_projections.rs` (it needs a
//! third lhs policy, visiting the lhs sub-expressions but not the lhs root)
//! and `flipflop_naming`'s rename (`SkipLhs`, and it intentionally leaves the
//! `ForEach` item slot alone).

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit::{
    walk_body_exprs, walk_body_exprs_visit_lhs, walk_expr, walk_stmt_exprs_mut_visit_lhs, Action,
};
use std::collections::BTreeMap;

/// How far a var-ref query descends.
pub(crate) enum VarScope {
    /// The whole subtree, recursing into every nested statement body.
    Deep,
    /// Only the expressions each top-level statement owns directly; nested
    /// bodies are not entered.
    CurrentLevel,
}

/// Whether an `Assignment` left-hand side counts as a reference.
pub(crate) enum Defs {
    /// Skip the lhs; only true uses are counted.
    SkipLhs,
    /// Count the lhs too (a `Var` inside an lhs `FieldAccess` is a use of the
    /// receiver).
    VisitLhs,
}

/// Count occurrences of `Expr::Var(name)` in `body` under the given scope and
/// lhs policy.
///
/// `Deep` delegates to the shared `visit.rs` walkers. `CurrentLevel`
/// reproduces the per-statement read set the sentinel-cascade single-use
/// guard relies on: it must NOT recurse, because the cascade compiler reuses
/// one temp name across nested levels and a recursive count would conflate
/// them. At `CurrentLevel` the `Defs` argument has no effect, the dispatch
/// reads only use positions (`Assignment` rhs, never lhs), so `SkipLhs` and
/// `VisitLhs` coincide.
pub(crate) fn count_var(body: &[Stmt], name: &str, scope: VarScope, defs: Defs) -> usize {
    match scope {
        VarScope::Deep => {
            let mut count = 0usize;
            let mut tally = |node: &Expr| {
                if matches!(node, Expr::Var(other) if other == name) {
                    count += 1;
                }
            };
            match defs {
                Defs::SkipLhs => walk_body_exprs(body, &mut tally),
                Defs::VisitLhs => walk_body_exprs_visit_lhs(body, &mut tally),
            }
            count
        }
        VarScope::CurrentLevel => body
            .iter()
            .map(|stmt| count_in_stmt_current_level(stmt, name))
            .sum(),
    }
}

/// Count every distinct `Var` name used across `body` (`Deep` + `SkipLhs`) in
/// a single pass. Map form of [`count_var`] for callers that screen many
/// candidate names at once (the single-use temp inliner, struct-fold read
/// counts).
pub(crate) fn count_all_var_uses(body: &[Stmt]) -> BTreeMap<String, usize> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    walk_body_exprs(body, &mut |expr| {
        if let Expr::Var(name) = expr {
            *counts.entry(name.clone()).or_insert(0) += 1;
        }
    });
    counts
}

/// The current-scope read set of one statement: the expressions it owns
/// directly, never a nested body. Mirrors the sentinel-cascade guard's
/// hand-match exactly (Assignment rhs; Call func + args; Return value; Branch
/// cond; Loop cond + `ForEach` array; Switch expr + case values). Everything
/// else contributes nothing at this level.
fn count_in_stmt_current_level(stmt: &Stmt, name: &str) -> usize {
    match stmt {
        Stmt::Assignment { rhs, .. } => count_in_expr(rhs, name),
        Stmt::Call { func, args, .. } => {
            let mut total = count_in_expr(func, name);
            for arg in args {
                total += count_in_expr(arg, name);
            }
            total
        }
        Stmt::Return { value, .. } => value
            .as_ref()
            .map(|expr| count_in_expr(expr, name))
            .unwrap_or(0),
        Stmt::Branch { cond, .. } => count_in_expr(cond, name),
        Stmt::Loop { cond, kind, .. } => {
            let mut total = cond
                .as_ref()
                .map(|expr| count_in_expr(expr, name))
                .unwrap_or(0);
            if let LoopKind::ForEach { array, .. } = kind {
                total += count_in_expr(array, name);
            }
            total
        }
        Stmt::Switch { expr, cases, .. } => {
            let mut total = count_in_expr(expr, name);
            for case in cases {
                for value in &case.values {
                    total += count_in_expr(value, name);
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

/// Count `Var(name)` nodes anywhere inside a single expression tree.
fn count_in_expr(expr: &Expr, name: &str) -> usize {
    let mut count = 0;
    walk_expr(expr, &mut |node| {
        if matches!(node, Expr::Var(other) if other == name) {
            count += 1;
        }
    });
    count
}

/// Rename every `Expr::Var(old)` to `new` in a single statement, including
/// nested sub-bodies and the `LoopKind::ForEach::item` slot (a `String`
/// outside the `Expr` tree, so the visitor cannot reach it). Visits
/// `Assignment` left-hand sides, so a loop counter's `i = i + 1` increment is
/// renamed on both the read and the write.
///
/// This is the universal rename. `flipflop_naming`'s rename deliberately
/// diverges (it skips the lhs and the item slot to preserve the gate-var
/// alias definition) and keeps its own helper.
pub(crate) fn rename_var_in_stmt(stmt: &mut Stmt, old: &str, new: &str) {
    if let Stmt::Loop {
        kind: LoopKind::ForEach { item, .. },
        ..
    } = stmt
    {
        if item == old {
            *item = new.to_string();
        }
    }
    walk_stmt_exprs_mut_visit_lhs(stmt, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == old {
                *name = new.to_string();
            }
        }
        Action::Continue
    });
}

/// A structural key for `expr`, used by the CSE (common subexpression
/// elimination) passes to bucket equal subexpressions in a `BTreeMap`/`BTreeSet`
/// of `String`. `None` (a swallowed serialize error) means "not a CSE
/// candidate", matching the prior `serde_json::to_string(..).ok()` behaviour.
/// `Expr` derives only `PartialEq` (no `Eq`/`Hash`), so keying is string-based.
pub(crate) fn expr_key(expr: &Expr) -> Option<String> {
    serde_json::to_string(expr).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::BinaryOp;
    use crate::bytecode::stmt::SwitchCase;
    use crate::bytecode::transforms::test_fixtures::{assign, assign_expr, call, lit, var};

    fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: 0,
        }
    }

    fn ne(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Ne,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn field(recv_name: &str, field: &str) -> Expr {
        Expr::FieldAccess {
            recv: Box::new(var(recv_name)),
            field: field.to_string(),
        }
    }

    #[test]
    fn deep_skiplhs_counts_uses_not_defs() {
        // a = x; if (x) { f(x) }
        let body = vec![
            assign("a", var("x")),
            branch(var("x"), vec![call("f", vec![var("x")])], vec![]),
        ];
        // x: assign rhs (1) + branch cond (1) + call arg inside then-body (1).
        assert_eq!(count_var(&body, "x", VarScope::Deep, Defs::SkipLhs), 3);
        // `a` appears only as an Assignment lhs (a def), skipped under SkipLhs.
        assert_eq!(count_var(&body, "a", VarScope::Deep, Defs::SkipLhs), 0);
    }

    #[test]
    fn deep_visitlhs_counts_lhs_that_skiplhs_misses() {
        // $t.Field = 1  -- a field-write back into temp t. The lhs receiver
        // Var(t) is a use under VisitLhs (this is what blocks struct-fold),
        // and invisible under SkipLhs.
        let body = vec![assign_expr(field("t", "Field"), lit("1"))];
        assert_eq!(count_var(&body, "t", VarScope::Deep, Defs::SkipLhs), 0);
        assert_eq!(count_var(&body, "t", VarScope::Deep, Defs::VisitLhs), 1);
    }

    #[test]
    fn current_level_skips_def_lhs_and_nested_bodies() {
        // The sentinel-cascade single-use guard's exact shape:
        //   t = (X != 0)     // lhs t is a def; rhs uses X, not t
        //   if (t) A else B  // cond is the one real current-level use of t
        let body = vec![
            assign("t", ne(var("X"), lit("0"))),
            branch(var("t"), vec![call("A", vec![])], vec![call("B", vec![])]),
        ];
        // Exactly one: the branch cond. The Assignment lhs is a def and the
        // branch arms are nested bodies, neither counted. An over-count here
        // would flip the guard's `!= 1` and suppress every cascade lowering.
        assert_eq!(
            count_var(&body, "t", VarScope::CurrentLevel, Defs::SkipLhs),
            1
        );
    }

    #[test]
    fn current_level_reads_case_values_not_case_bodies() {
        // switch (t) { case t: g(t)  default: h(t) }
        let body = vec![Stmt::Switch {
            expr: var("t"),
            cases: vec![SwitchCase {
                values: vec![var("t")],
                body: vec![call("g", vec![var("t")])],
            }],
            default: Some(vec![call("h", vec![var("t")])]),
            offset: 0,
        }];
        // Current level: switch expr (1) + case value (1). The case body and
        // default body are nested, not entered.
        assert_eq!(
            count_var(&body, "t", VarScope::CurrentLevel, Defs::SkipLhs),
            2
        );
        // Deep: all four occurrences.
        assert_eq!(count_var(&body, "t", VarScope::Deep, Defs::SkipLhs), 4);
    }

    #[test]
    fn rename_var_in_stmt_covers_lhs_and_foreach_item() {
        // `i = i` -- both the lhs and rhs occurrences must rename, or a
        // renamed loop counter would read a different name than it writes.
        let mut stmt = assign("i", var("i"));
        rename_var_in_stmt(&mut stmt, "i", "Index");
        assert_eq!(
            count_var(
                std::slice::from_ref(&stmt),
                "i",
                VarScope::Deep,
                Defs::VisitLhs
            ),
            0
        );
        assert_eq!(
            count_var(
                std::slice::from_ref(&stmt),
                "Index",
                VarScope::Deep,
                Defs::VisitLhs
            ),
            2
        );

        // The ForEach item slot is a String outside the Expr tree; rename it.
        let mut loop_stmt = Stmt::Loop {
            kind: LoopKind::ForEach {
                item: "Elem".to_string(),
                array: var("arr"),
            },
            cond: None,
            body: vec![],
            completion: None,
            offset: 0,
        };
        rename_var_in_stmt(&mut loop_stmt, "Elem", "Renamed");
        let Stmt::Loop {
            kind: LoopKind::ForEach { item, .. },
            ..
        } = &loop_stmt
        else {
            panic!("expected ForEach loop");
        };
        assert_eq!(item, "Renamed");
    }
}
