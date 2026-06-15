//! Contextual rename of out-param temps from `$<Call>_<Param>` to `$<Param>`.
//!
//! The decoder names pure-call out-param temps as `$<CallName>_<OutParam>`
//! (e.g. `$GetActor_OutActor`). That's unambiguous
//! machine-readable output, but noisy for pseudocode. When the short form
//! `$<OutParam>` is unambiguous within the function scope, we prefer it.
//!
//! This pass runs late in the per-function pipeline, after common-
//! subexpression elimination (CSE), inlining, and dead-statement removal,
//! so the surviving out-param temps are the ones consumers actually
//! reference. It operates directly on
//! the typed statement IR, so rename is inherently whole-token and there
//! are no text-boundary concerns.
//!
//! ## Collection
//!
//! Over the whole statement tree:
//! - `call_names`: every name appearing in `Expr::Call` or
//!   `Expr::MethodCall`.
//! - `var_names`: every `$<...>` name appearing in `Expr::Var`, on both
//!   read and assignment-lhs positions.
//!
//! ## Rename rules
//!
//! For each `$<Call>_<Rest>` var whose `<Call>` matches a collected call
//! name (longest prefix wins, since some call names contain underscores),
//! the candidate short form is `$<Rest>`. A candidate is promoted only
//! when:
//! - `$<Rest>` is not already in `var_names` (no shadowing), AND
//! - no other `$<OtherCall>_<Rest>` produces the same `$<Rest>`.
//!
//! Pure-digit remainders (`$Foo_1`, a CSE dedup marker) are rejected, as
//! is an empty remainder. Collisions stay as their full form.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;

use super::visit::{walk_body_exprs_mut_visit_lhs, walk_body_exprs_visit_lhs, Action};

/// Rename unambiguous `$<Call>_<Param>` out-param temps to `$<Param>`
/// across `body`. Collects call and var names from the whole tree, builds
/// the `full -> short` map under the collision rules, then rewrites every
/// matching `Expr::Var` (read or lhs) in place.
pub fn rename_outparam_temps(body: &mut [Stmt]) {
    let mut call_names: BTreeSet<String> = BTreeSet::new();
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    collect_names(body, &mut call_names, &mut var_names);

    let rename_map = build_rename_map(&call_names, &var_names);
    if rename_map.is_empty() {
        return;
    }

    walk_body_exprs_mut_visit_lhs(body, &mut |expr| {
        if let Expr::Var(name) = expr {
            if let Some(short) = rename_map.get(name) {
                *name = short.clone();
            }
        }
        Action::Continue
    });
}

/// Collect call names and `$`-prefixed var names across the whole tree.
///
/// Two sources feed `call_names`:
/// - `Expr::Call` / `Expr::MethodCall` names (pure calls embedded in
///   expressions), gathered through the shared expression walker.
/// - The callee of a `Stmt::Call`. The IR models a standalone
///   (void / out-param-only) call as `Stmt::Call { func, .. }` whose
///   `func` is an `Expr::Var(name)` (free function) or
///   `Expr::FieldAccess { field, .. }` (method). The producing call for
///   most out-param temps (e.g. `Query(out $Query_Result)`) takes
///   this shape, so its name must be harvested here, not just from
///   `Expr::Call`.
fn collect_names(
    body: &[Stmt],
    call_names: &mut BTreeSet<String>,
    var_names: &mut BTreeSet<String>,
) {
    walk_body_exprs_visit_lhs(body, &mut |expr| match expr {
        Expr::Var(name) if name.starts_with('$') => {
            var_names.insert(name.clone());
        }
        Expr::Call { name, .. } | Expr::MethodCall { name, .. } => {
            call_names.insert(name.clone());
        }
        _ => {}
    });
    collect_stmt_call_callees(body, call_names);
}

/// Recurse the statement tree, adding the callee name of every
/// `Stmt::Call` to `call_names`. Children are reached through the same
/// sub-body slots `walk_stmt_children_mut` knows about.
fn collect_stmt_call_callees(body: &[Stmt], call_names: &mut BTreeSet<String>) {
    for stmt in body {
        if let Stmt::Call { func, .. } = stmt {
            if let Some(name) = callee_name(func) {
                call_names.insert(name);
            }
        }
        for_each_child_body(stmt, &mut |child| {
            collect_stmt_call_callees(child, call_names)
        });
    }
}

/// Extract the callable name from a `Stmt::Call` callee expression.
/// Handles the free-function (`Expr::Var`), method
/// (`Expr::FieldAccess`/`Expr::MethodCall`), and embedded
/// (`Expr::Call`) shapes the decoder produces for the func slot.
fn callee_name(func: &Expr) -> Option<String> {
    match func {
        Expr::Var(name) | Expr::Call { name, .. } | Expr::MethodCall { name, .. } => {
            Some(name.clone())
        }
        Expr::FieldAccess { field, .. } => Some(field.clone()),
        _ => None,
    }
}

/// Apply `visit` to each direct sub-body of `stmt`. Read-only counterpart
/// of `walk_stmt_children_mut`, kept local because no other module needs
/// the immutable variant.
fn for_each_child_body<F: FnMut(&[Stmt])>(stmt: &Stmt, visit: &mut F) {
    use crate::bytecode::stmt::LoopKind;
    match stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            visit(then_body);
            visit(else_body);
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter() {
                visit(pin_body);
            }
        }
        Stmt::Loop {
            body,
            completion,
            kind,
            ..
        } => {
            visit(body);
            if let Some(comp) = completion {
                visit(comp);
            }
            if let LoopKind::ForC { init, increment } = kind {
                visit(init);
                visit(increment);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for case in cases.iter() {
                visit(&case.body);
            }
            if let Some(default_body) = default {
                visit(default_body);
            }
        }
        Stmt::Latch { init, body, .. } => {
            visit(init);
            visit(body);
        }
        Stmt::Assignment { .. }
        | Stmt::Call { .. }
        | Stmt::Return { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
}

/// Build the final `full -> short` rename map, applying the collision
/// rules described in the module header.
fn build_rename_map(
    call_names: &BTreeSet<String>,
    var_names: &BTreeSet<String>,
) -> BTreeMap<String, String> {
    // For every `$<Call>_<Rest>` var, compute its candidate short form
    // `$<Rest>` using the longest matching call-name prefix. Group
    // candidates by short form so collisions are detectable.
    let mut candidates: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for var in var_names {
        let Some(rest) = var.strip_prefix('$') else {
            continue;
        };
        let Some(short_rest) = longest_call_prefix_strip(rest, call_names) else {
            continue;
        };
        if short_rest.is_empty() {
            continue;
        }
        // Reject pure-digit remainders. `$Foo_1` is the CSE-chained
        // duplicate disambiguator, not an out-param; renaming to `$1`
        // would produce an invalid identifier.
        if short_rest.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        let short = format!("${}", short_rest);
        candidates.entry(short).or_default().push(var.clone());
    }

    let mut map: BTreeMap<String, String> = BTreeMap::new();
    for (short, sources) in candidates {
        if sources.len() != 1 {
            // Two full-form vars would collapse to the same short form.
            continue;
        }
        if var_names.contains(&short) {
            // Short form already exists as its own var, keep the full
            // form to avoid aliasing.
            continue;
        }
        map.insert(sources.into_iter().next().unwrap(), short);
    }
    map
}

/// Strip the longest call-name prefix of the form `Call_` from `rest`.
/// Returns the remainder (the candidate short name) or `None` if no known
/// call prefixes `rest`. Call names can contain underscores, so the
/// longest match wins.
fn longest_call_prefix_strip(rest: &str, call_names: &BTreeSet<String>) -> Option<String> {
    let best_call = call_names
        .iter()
        .filter(|call| rest.starts_with(&format!("{}_", call)))
        .max_by_key(|call| call.len())?;
    rest.strip_prefix(&format!("{}_", best_call))
        .map(str::to_owned)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::transforms::test_fixtures::{assign, call, var};
    use crate::bytecode::transforms::visit::walk_body_exprs_visit_lhs;

    fn call_expr(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            name: name.to_string(),
            args,
        }
    }

    /// Collect every `$`-prefixed `Expr::Var` name in document order. The
    /// rename pass only mutates var-name strings, so comparing the
    /// in-order list of `$`-vars precisely captures what the pass did
    /// without needing `Stmt: PartialEq`.
    fn dollar_vars(body: &[Stmt]) -> Vec<String> {
        let mut names = Vec::new();
        walk_body_exprs_visit_lhs(body, &mut |expr| {
            if let Expr::Var(name) = expr {
                if name.starts_with('$') {
                    names.push(name.clone());
                }
            }
        });
        names
    }

    /// Single-occurrence out-param temp collapses to the short form.
    /// The producing pure call surfaces as `Expr::Call` in an assignment
    /// rhs (the shape for embedded out-param calls).
    #[test]
    fn single_occurrence_is_renamed() {
        let mut body = vec![
            assign(
                "discard",
                call_expr(
                    "GetInteractableActor",
                    vec![
                        var("Hand"),
                        Expr::Out(Box::new(var("$GetInteractableActor_InteractableActor"))),
                    ],
                ),
            ),
            assign("self.X", var("$GetInteractableActor_InteractableActor")),
        ];
        rename_outparam_temps(&mut body);
        assert_eq!(
            dollar_vars(&body),
            vec!["$InteractableActor", "$InteractableActor"]
        );
    }

    /// Short form already in use as a standalone var: keep the full form.
    #[test]
    fn short_form_collision_keeps_full_form() {
        let mut body = vec![
            assign("self.Y", var("$InteractableActor")),
            assign(
                "discard",
                call_expr(
                    "GetInteractableActor",
                    vec![Expr::Out(Box::new(var(
                        "$GetInteractableActor_InteractableActor",
                    )))],
                ),
            ),
            assign("self.X", var("$GetInteractableActor_InteractableActor")),
        ];
        let before = dollar_vars(&body);
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), before);
    }

    /// Two different calls both producing `$Actor` collide: neither renames.
    #[test]
    fn two_call_prefix_collision_keeps_full_form() {
        let mut body = vec![
            assign(
                "discardA",
                call_expr("FooA", vec![Expr::Out(Box::new(var("$FooA_Actor")))]),
            ),
            assign(
                "discardB",
                call_expr("FooB", vec![Expr::Out(Box::new(var("$FooB_Actor")))]),
            ),
            assign("self.X", var("$FooA_Actor")),
            assign("self.Y", var("$FooB_Actor")),
        ];
        let before = dollar_vars(&body);
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), before);
    }

    /// Pure-digit remainder (`$Foo_1`, a CSE marker) is rejected.
    #[test]
    fn short_form_digit_only_rejected() {
        let mut body = vec![
            call("Foo", vec![var("x")]),
            assign("$Foo", call_expr("Foo", vec![var("a")])),
            assign("$Foo_1", call_expr("Foo", vec![var("b")])),
        ];
        let before = dollar_vars(&body);
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), before);
    }

    /// `$Cast_AsActor` uses the dynamic-cast temp convention. With no
    /// `Cast(...)` call in scope, `Cast` is not a collected call name and
    /// the var is left untouched.
    #[test]
    fn dollar_cast_class_not_renamed() {
        let mut body = vec![assign(
            "$Cast_AsActor",
            Expr::Cast {
                kind: crate::bytecode::expr::CastKind::Class {
                    target: "Actor".to_string(),
                },
                inner: Box::new(var("$Foo")),
            },
        )];
        let before = dollar_vars(&body);
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), before);
    }

    /// Two distinct full forms produce two distinct short forms; both
    /// rename and the Stmt-level rename is inherently whole-token, so
    /// `$Foo_Bar` does not partially match inside `$Foo_Bar_Baz`.
    #[test]
    fn word_boundary_respected() {
        let mut body = vec![assign(
            "discard",
            call_expr(
                "Foo",
                vec![
                    Expr::Out(Box::new(var("$Foo_Bar"))),
                    Expr::Out(Box::new(var("$Foo_Bar_Baz"))),
                ],
            ),
        )];
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), vec!["$Bar", "$Bar_Baz"]);
    }

    /// Both `Do` and `DoThing` are call names; `$DoThing_Result` strips
    /// the longer prefix, yielding `$Result` not `$Thing_Result`.
    #[test]
    fn longest_call_prefix_wins() {
        let mut body = vec![
            assign("discardDo", call_expr("Do", vec![var("x")])),
            assign(
                "discardDoThing",
                call_expr(
                    "DoThing",
                    vec![var("y"), Expr::Out(Box::new(var("$DoThing_Result")))],
                ),
            ),
            assign("self.X", var("$DoThing_Result")),
        ];
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), vec!["$Result", "$Result"]);
    }

    /// Call name not in scope: `$Foo_Bar` is left untouched.
    #[test]
    fn call_name_not_in_scope_skipped() {
        let mut body = vec![assign("self.X", var("$Foo_Bar"))];
        let before = dollar_vars(&body);
        rename_outparam_temps(&mut body);
        assert_eq!(dollar_vars(&body), before);
    }

    /// Empty body is a no-op.
    #[test]
    fn empty_is_noop() {
        let mut body: Vec<Stmt> = Vec::new();
        rename_outparam_temps(&mut body);
        assert!(body.is_empty());
    }
}
