//! Common-subexpression elimination for pure Blueprint node calls.
//!
//! The Blueprint compiler emits each pure-node call at every consumer
//! site, so a single editor-graph node like `BreakHitResult` can appear
//! multiple times in the bytecode stream. The editor treats these as one
//! cached node whose outputs feed all consumers. This pass collapses the
//! duplicates so the emitter matches that mental model.
//!
//! The IR is typed, so we pattern-match on `Stmt::Assignment` /
//! `Stmt::Call`.
//!
//! Two pure-call statement shapes are recognised:
//! - **Assignment**: `$<Call>_<Param> = <Call>(args, ...)`. The lhs name
//!   matches the decoder's `$<Call>_*` convention, which links the
//!   variable to a specific pure-node output pin.
//! - **Bare call**: `<Call>(args, out $<Call>_<Param>, ...)`. The
//!   outputs live entirely in `$<Call>_*` out-param vars.
//!
//! For duplicate assignments, the RHS rewrites to `Expr::Var(keeper_lhs)`.
//! The existing `inline_single_use_temps` pass collapses the resulting
//! `$X = $keeper` chain.
//!
//! For duplicate bare calls, the statement is deleted in place. The
//! keeper has already populated the shared `$<Call>_*` out-param vars
//! consumers reference.
//!
//! The pass walks the entire body cross-scope: the first occurrence in
//! a DFS in-order traversal is the keeper, and every later duplicate
//! (anywhere in the tree, including inside nested Branch arms or
//! Sequence pins) collapses against it. The pass runs after structuring,
//! so a cross-scope visitor is required to collapse a single pure node
//! whose duplicates land in different Branch arms.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::var_refs;
use crate::bytecode::transforms::visit::{walk_stmt_children, walk_stmt_children_mut};

/// Entry point. Walks the entire body cross-scope, picks the first
/// occurrence (DFS in-order) of each canonical pure-call as the keeper,
/// then rewrites every later duplicate. The first occurrence is the
/// outermost / earliest in source order.
pub fn cse_pure_calls(body: &mut Vec<Stmt>) {
    // First pass: scan in-order, record keeper info per canonical key.
    let mut keepers: BTreeMap<String, KeeperInfo> = BTreeMap::new();
    collect_keepers(body, &mut keepers);

    // Second pass: rewrite every duplicate using the keeper map.
    rewrite_duplicates(body, &keepers);
}

/// Keeper metadata for a canonical pure-call key. The shape determines
/// how duplicates are collapsed (assignment rewrites RHS, bare call gets
/// deleted).
struct KeeperInfo {
    shape: PureShape,
    /// Lhs var name for assignment shape; `None` for bare-call shape.
    lhs: Option<String>,
}

/// First pass. DFS in-order over the statement tree; the first
/// pure-call statement with a given canonical key registers as the
/// keeper. Subsequent matching statements are left alone here — the
/// second pass rewrites them.
fn collect_keepers(body: &[Stmt], keepers: &mut BTreeMap<String, KeeperInfo>) {
    for stmt in body.iter() {
        if let Some((shape, key, lhs)) = classify_pure(stmt) {
            keepers.entry(key).or_insert(KeeperInfo { shape, lhs });
        }
        // Recurse into sub-bodies after recording this statement so the
        // outermost occurrence wins as the keeper.
        walk_stmt_children(stmt, &mut |sub_body| collect_keepers(sub_body, keepers));
    }
}

/// Second pass. DFS over every scope; for each statement that classifies
/// as pure, check if it matches the keeper map. If it does AND it is not
/// itself the keeper (compared by lhs name for assignments, or by being
/// the first encountered for bare calls — handled via a per-key "seen
/// keeper" flag), rewrite or delete.
fn rewrite_duplicates(body: &mut Vec<Stmt>, keepers: &BTreeMap<String, KeeperInfo>) {
    let mut seen_keeper_keys: BTreeSet<String> = BTreeSet::new();
    rewrite_in_scope(body, keepers, &mut seen_keeper_keys);
}

/// Rewrite duplicates in one flat scope, then recurse into nested
/// scopes. `seen_keeper_keys` tracks which canonical keys have already
/// had their keeper visited, so the first occurrence in DFS order stays
/// untouched and all subsequent matches collapse.
fn rewrite_in_scope(
    body: &mut Vec<Stmt>,
    keepers: &BTreeMap<String, KeeperInfo>,
    seen_keeper_keys: &mut BTreeSet<String>,
) {
    // Indices of bare-call duplicates to delete after the loop. Assignment
    // dups rewrite in place so their indices stay valid.
    let mut bare_call_dups: Vec<usize> = Vec::new();

    for (idx, stmt) in body.iter_mut().enumerate() {
        if let Some((_shape, key, _dup_lhs)) = classify_pure(stmt) {
            let Some(keeper) = keepers.get(&key) else {
                continue;
            };
            if !seen_keeper_keys.contains(&key) {
                // This is the keeper — leave it alone, mark seen.
                seen_keeper_keys.insert(key);
            } else {
                // Duplicate — rewrite or delete.
                match keeper.shape {
                    PureShape::Assignment => {
                        let Some(keeper_lhs) = keeper.lhs.as_ref() else {
                            continue;
                        };
                        // Rewrite RHS to a Var ref to the keeper's lhs. If
                        // the duplicate's own lhs equals the keeper's lhs
                        // the result is a `$X = $X` self-assignment, which
                        // the second `inline_single_use_temps` / dead-stmt
                        // pass downstream will sweep when the slot has no
                        // remaining users.
                        if let Stmt::Assignment { rhs, .. } = &mut *stmt {
                            *rhs = Expr::Var(keeper_lhs.clone());
                        }
                    }
                    PureShape::BareCall => bare_call_dups.push(idx),
                }
            }
        }
        // Recurse into children so DFS order matches keeper collection.
        walk_stmt_children_mut(stmt, &mut |sub_body| {
            rewrite_in_scope(sub_body, keepers, seen_keeper_keys);
        });
    }

    if !bare_call_dups.is_empty() {
        bare_call_dups.sort_unstable();
        bare_call_dups.dedup();
        for idx in bare_call_dups.into_iter().rev() {
            body.remove(idx);
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum PureShape {
    /// `$<Call>_<Param> = <Call>(args)` — lhs name matches the decoder's
    /// `$<Call>_*` convention.
    Assignment,
    /// `<Call>(args, out $<Call>_<Param>, ...)` — outputs live in
    /// `$<Call>_*` out-param vars.
    BareCall,
}

/// Classify a statement as a pure-call shape.
///
/// Returns `Some((shape, key, lhs_if_assignment))` for pure-node shapes,
/// `None` otherwise. The key is the canonical JSON serialisation of the
/// call expression — for assignments the RHS, for bare calls a synthetic
/// `Call` expression rebuilt from the statement's func + args. Two pure
/// calls collapse iff their canonical keys match.
fn classify_pure(stmt: &Stmt) -> Option<(PureShape, String, Option<String>)> {
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => classify_assignment(lhs, rhs),
        Stmt::Call { func, args, .. } => classify_bare_call(func, args),
        _ => None,
    }
}

/// Classify an assignment as a pure-call shape. The lhs must be a `Var`
/// whose name matches `$<call>_*` for some `Call { name: call, .. }` rhs.
fn classify_assignment(lhs: &Expr, rhs: &Expr) -> Option<(PureShape, String, Option<String>)> {
    let Expr::Var(lhs_name) = lhs else {
        return None;
    };
    let Expr::Call {
        name: call_name, ..
    } = rhs
    else {
        return None;
    };
    if !lhs_is_pure_shape(lhs_name, call_name) {
        return None;
    }
    let key = var_refs::expr_key(rhs)?;
    Some((PureShape::Assignment, key, Some(lhs_name.clone())))
}

/// Classify a bare call as a pure-call shape. At least one argument must
/// be either an `Out`-wrapped `Var` or a plain `Var` whose name matches
/// `$<call>_*`. The match ignores the `out` prefix because the `out`
/// marker isn't always preserved into the IR for pure-node callees (the
/// BP-emitted out-param vars are the real identity signal).
fn classify_bare_call(func: &Expr, args: &[Expr]) -> Option<(PureShape, String, Option<String>)> {
    let Expr::Var(call_name) = func else {
        return None;
    };
    if !args.iter().any(|arg| is_pure_out_arg(arg, call_name)) {
        return None;
    }
    // Canonicalise as a synthetic `Call` expression so the key shape
    // mirrors the assignment-shape key (both serialise an `Expr::Call`).
    // Two bare calls collapse iff their func + arg sequence match.
    let canon = Expr::Call {
        name: call_name.clone(),
        args: args.to_vec(),
    };
    let key = var_refs::expr_key(&canon)?;
    Some((PureShape::BareCall, key, None))
}

/// True if `lhs_name` matches the decoder's pure-output naming
/// convention for `call`, e.g. `$BreakHitResult_HitActor` for a
/// `BreakHitResult` call.
fn lhs_is_pure_shape(lhs_name: &str, call: &str) -> bool {
    let prefix = format!("${}_", call);
    lhs_name.starts_with(&prefix)
}

/// True if `arg` references a `$<call>_*` out-param var (the decoder's
/// pure-node output naming convention). Accepts both `Out(Var)` and bare
/// `Var` forms — pure-node callees in real Blueprints (`BreakHitResult`,
/// `MakeVector`, etc.) emit out-param vars as plain `Var` in the IR.
fn is_pure_out_arg(arg: &Expr, call_name: &str) -> bool {
    let inner = match arg {
        Expr::Out(boxed) => boxed.as_ref(),
        other => other,
    };
    let Expr::Var(var_name) = inner else {
        return false;
    };
    lhs_is_pure_shape(var_name, call_name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign, call, lit, var};

    fn pure_assign(lhs: &str, call_name: &str, args: Vec<Expr>) -> Stmt {
        assign(
            lhs,
            Expr::Call {
                name: call_name.to_string(),
                args,
            },
        )
    }

    fn out_var(name: &str) -> Expr {
        Expr::Out(Box::new(var(name)))
    }

    #[test]
    fn empty_body_is_noop() {
        let mut body: Vec<Stmt> = Vec::new();
        cse_pure_calls(&mut body);
        assert!(body.is_empty());
    }

    #[test]
    fn single_assignment_is_noop() {
        let mut body = vec![pure_assign(
            "$GetVel_Velocity",
            "GetVel",
            vec![var("Wheel")],
        )];
        cse_pure_calls(&mut body);
        match &body[0] {
            Stmt::Assignment { rhs, .. } => match rhs {
                Expr::Call { name, args } => {
                    assert_eq!(name, "GetVel");
                    assert_eq!(args.len(), 1);
                }
                _ => panic!("rhs should still be a Call"),
            },
            other => panic!(
                "unexpected stmt shape: {:?}",
                super::super::test_fixtures::stmt_kind(other)
            ),
        }
    }

    #[test]
    fn two_identical_pure_assignments_collapse() {
        let mut body = vec![
            pure_assign("$GetVel_Velocity", "GetVel", vec![var("Wheel")]),
            pure_assign("$GetVel_Velocity_1", "GetVel", vec![var("Wheel")]),
        ];
        cse_pure_calls(&mut body);
        // First stays as the call.
        match &body[0] {
            Stmt::Assignment {
                rhs: Expr::Call { .. },
                ..
            } => {}
            _ => panic!("keeper should remain a Call"),
        }
        // Second rewrites to `Var(keeper_lhs)`.
        match &body[1] {
            Stmt::Assignment {
                rhs: Expr::Var(name),
                ..
            } => assert_eq!(name, "$GetVel_Velocity"),
            _ => panic!("duplicate should rewrite RHS to Var"),
        }
    }

    #[test]
    fn four_identical_pure_assignments_collapse_three() {
        let mut body = vec![
            pure_assign("$Foo_R", "Foo", vec![var("x")]),
            pure_assign("$Foo_R_1", "Foo", vec![var("x")]),
            pure_assign("$Foo_R_2", "Foo", vec![var("x")]),
            pure_assign("$Foo_R_3", "Foo", vec![var("x")]),
        ];
        cse_pure_calls(&mut body);
        match &body[0] {
            Stmt::Assignment {
                rhs: Expr::Call { .. },
                ..
            } => {}
            _ => panic!("first should be the keeper Call"),
        }
        for (idx, stmt) in body.iter().enumerate().take(4).skip(1) {
            match stmt {
                Stmt::Assignment {
                    rhs: Expr::Var(name),
                    ..
                } => assert_eq!(name, "$Foo_R"),
                _ => panic!("duplicate {} should rewrite RHS to Var", idx),
            }
        }
    }

    #[test]
    fn different_args_do_not_collapse() {
        let mut body = vec![
            pure_assign("$Foo_R", "Foo", vec![var("LeftHand")]),
            pure_assign("$Foo_R_1", "Foo", vec![var("RightHand")]),
        ];
        cse_pure_calls(&mut body);
        // Both stay as Call expressions.
        for (idx, stmt) in body.iter().enumerate().take(2) {
            match stmt {
                Stmt::Assignment {
                    rhs: Expr::Call { .. },
                    ..
                } => {}
                _ => panic!("stmt {} should remain a Call (different args)", idx),
            }
        }
    }

    #[test]
    fn lhs_not_matching_call_name_skipped() {
        // lhs `$Other_X` does not match call `Foo`, so this isn't a
        // pure-node output.
        let mut body = vec![
            pure_assign("$Other_X", "Foo", vec![var("x")]),
            pure_assign("$Other_X_1", "Foo", vec![var("x")]),
        ];
        let before: Vec<_> = body
            .iter()
            .map(|s| {
                matches!(
                    s,
                    Stmt::Assignment {
                        rhs: Expr::Call { .. },
                        ..
                    }
                )
            })
            .collect();
        cse_pure_calls(&mut body);
        let after: Vec<_> = body
            .iter()
            .map(|s| {
                matches!(
                    s,
                    Stmt::Assignment {
                        rhs: Expr::Call { .. },
                        ..
                    }
                )
            })
            .collect();
        assert_eq!(before, after);
    }

    #[test]
    fn bare_call_duplicates_deleted() {
        let make_call = || Stmt::Call {
            func: var("BreakHitResult"),
            args: vec![var("$Hit"), out_var("$BreakHitResult_HitActor")],
            offset: 0,
        };
        let mut body = vec![
            make_call(),
            call("OtherStmt", vec![]),
            make_call(),
            make_call(),
        ];
        cse_pure_calls(&mut body);
        // Only the keeper + the unrelated stmt should remain.
        assert_eq!(body.len(), 2);
        match &body[0] {
            Stmt::Call {
                func: Expr::Var(name),
                ..
            } => assert_eq!(name, "BreakHitResult"),
            _ => panic!("first should be the keeper bare call"),
        }
        match &body[1] {
            Stmt::Call {
                func: Expr::Var(name),
                ..
            } => assert_eq!(name, "OtherStmt"),
            _ => panic!("second should be the unrelated call"),
        }
    }

    #[test]
    fn bare_call_with_plain_var_out_args_collapses() {
        // Real BP shape: BreakHitResult's out-param vars surface as plain
        // `Expr::Var` (no `Out` wrapper) in the IR. The classifier still
        // needs to recognise them via the `$<Call>_*` naming convention.
        let make_call = || Stmt::Call {
            func: var("BreakHitResult"),
            args: vec![var("$Hit"), var("$BreakHitResult_HitActor")],
            offset: 0,
        };
        let mut body = vec![make_call(), make_call(), make_call()];
        cse_pure_calls(&mut body);
        assert_eq!(body.len(), 1);
    }

    #[test]
    fn bare_call_different_args_not_collapsed() {
        let mut body = vec![
            Stmt::Call {
                func: var("BreakHitResult"),
                args: vec![var("$HitA"), out_var("$BreakHitResult_HitActor")],
                offset: 0,
            },
            Stmt::Call {
                func: var("BreakHitResult"),
                args: vec![var("$HitB"), out_var("$BreakHitResult_HitActor")],
                offset: 0,
            },
        ];
        cse_pure_calls(&mut body);
        assert_eq!(body.len(), 2);
    }

    #[test]
    fn bare_call_without_pure_out_arg_skipped() {
        // `SetHealth(100)` has no `$SetHealth_*` out-param so the bare-call
        // classifier rejects it. Duplicates are not collapsed even though
        // they appear twice.
        let mut body = vec![
            call("SetHealth", vec![lit("100")]),
            call("SetHealth", vec![lit("100")]),
        ];
        cse_pure_calls(&mut body);
        assert_eq!(body.len(), 2);
    }

    #[test]
    fn nested_scope_duplicates_collapse() {
        // Duplicates inside a Branch then-body collapse independently of
        // anything in the outer scope.
        let mut body = vec![Stmt::Branch {
            cond: lit("true"),
            then_body: vec![
                pure_assign("$Foo_R", "Foo", vec![var("x")]),
                pure_assign("$Foo_R_1", "Foo", vec![var("x")]),
            ],
            else_body: vec![],
            offset: 0,
        }];
        cse_pure_calls(&mut body);
        match &body[0] {
            Stmt::Branch { then_body, .. } => {
                assert_eq!(then_body.len(), 2);
                match &then_body[1] {
                    Stmt::Assignment {
                        rhs: Expr::Var(name),
                        ..
                    } => assert_eq!(name, "$Foo_R"),
                    _ => panic!("nested duplicate should collapse"),
                }
            }
            _ => panic!("outer should remain a Branch"),
        }
    }
}
