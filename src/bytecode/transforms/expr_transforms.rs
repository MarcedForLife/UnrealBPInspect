//! Expression-level transforms for the IR.
//!
//! Operates on `Vec<Stmt>` bodies (one per function or event). Bodies are
//! per-function/event so no scope crossing between transforms.
//!
//! Pipeline position: runs AFTER recognition (`refine_loops`,
//! `latch_recognition`, `cascade_fold`, etc.). Loops here may be any
//! `LoopKind` (While / ForC / ForEach), the walkers below recurse via
//! `walk_stmt_children_mut` which handles all nested-body slots
//! including ForC init/increment.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::name_shape::is_compiler_temp_name;
use crate::bytecode::transforms::var_refs;
use crate::bytecode::transforms::visit::{
    expr_contains_unknown, walk_body_exprs, walk_body_exprs_mut, walk_stmt_children,
    walk_stmt_children_mut, walk_stmt_exprs_mut, Action,
};

// Maximum fixed-point iterations before giving up, to guard against
// pathological inputs that would otherwise loop indefinitely.
const MAX_INLINE_ITERATIONS: usize = 16;

/// Inline single-use temporary assignments in a statement body.
///
/// Finds `Stmt::Assignment { lhs: Expr::Var(name), rhs, .. }` where `name`
/// appears exactly once as a use (not the assignment lhs itself). Replaces
/// that use with `rhs` and removes the assignment statement.
///
/// Skips inlining when:
/// - `rhs` contains any `Expr::Unknown` node (untrusted operand).
/// - `rhs` is `Expr::Out(..)` (ABI-significant out-parameter marker).
///
/// Candidate names: any `Var` name that is not `Self` or `None` and is not a
/// bare loop-counter name (single lowercase letter). In practice this matches
/// the `K2Node_*`, `Temp_*`, `CallFunc_*`, and `SomeName_N` patterns that
/// the Blueprint compiler produces for temporaries.
///
/// Iterates to fixed point (chained temps inline in successive passes). Caps
/// at [`MAX_INLINE_ITERATIONS`] passes and logs a warning if the cap is hit.
///
/// Recurses bottom-up through every nested statement body (Branch arms,
/// Loop body/completion/ForC init/increment, Switch case bodies/default,
/// Sequence pin bodies, Latch init/body) via `walk_stmt_children_mut` so
/// temps scoped inside any inner body inline within their own scope
/// before the outer scope runs. Recognition (`refine_loops`,
/// `latch_recognition`, `cascade_fold`, `demote_invariant_loops`) runs
/// upstream and is chain-aware against the un-inlined IR, so the inliner
/// no longer needs to preserve specific cond/increment shapes for
/// recognizers.
pub fn inline_single_use_temps(body: &mut Vec<Stmt>) {
    inline_at_scope(body);
}

fn inline_at_scope(body: &mut Vec<Stmt>) {
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut inline_at_scope);
    }
    for iteration in 0..MAX_INLINE_ITERATIONS {
        if !inline_pass(body) {
            // Method-handle binding pass runs after the single-use fixed
            // point so the use-count check above doesn't gate it.
            inline_method_handles_at_scope(body);
            return;
        }
        let _ = iteration; // consumed by range, satisfies the loop bound
    }
    eprintln!(
        "transform: inline_single_use_temps hit {}-iteration cap; \
         body may contain oscillating temporaries",
        MAX_INLINE_ITERATIONS
    );
}

/// Inline method-handle bindings of the shape
/// `$X = recv.MethodName` followed by zero or more `$X(args)` call sites.
///
/// The right-hand side is a pure method reference (FieldAccess or
/// FieldAccess-chain over a `Var`), so substituting every call-handle use
/// is safe even when the global use count is greater than one, which the
/// single-use inliner rejects. The alt-path emitter duplicates the same
/// call across convergence arms, leaving two call-handle uses at the same
/// bytecode offset, this pass collapses both back to direct method calls.
///
/// Operates on a single scope's slice. The caller (`inline_at_scope`) has
/// already recursed into every nested body, so substitutions reach call
/// sites in inner Branch arms, Sequence pins, Loop bodies, etc.
///
/// Conservatism: the pass skips the binding when any `Var($X)` appears
/// outside a `Stmt::Call::func` position (for example, passed as an
/// argument or stored into a field), since inlining there would change
/// observable behaviour.
fn inline_method_handles_at_scope(body: &mut Vec<Stmt>) {
    // Collect candidate (idx, name, rhs_clone) tuples, then mutate in
    // reverse so removal indices stay valid.
    let candidates: Vec<(usize, String, Expr)> = body
        .iter()
        .enumerate()
        .filter_map(|(idx, stmt)| {
            let (name, rhs) = match stmt {
                Stmt::Assignment {
                    lhs: Expr::Var(name),
                    rhs,
                    ..
                } => (name, rhs),
                _ => return None,
            };
            if !is_inline_candidate_name(name) {
                return None;
            }
            if !is_method_handle_rhs(rhs) {
                return None;
            }
            if expr_contains_unknown(rhs) {
                return None;
            }
            Some((idx, name.clone(), rhs.clone()))
        })
        .collect();

    for (assign_idx, var_name, rhs_clone) in candidates.into_iter().rev() {
        if !all_uses_are_call_handles(body, &var_name, assign_idx) {
            continue;
        }
        replace_call_handles(body, &var_name, &rhs_clone, assign_idx);
        body.remove(assign_idx);
    }
}

/// Returns `true` when `rhs` is a method-handle reference: a `FieldAccess`
/// rooted in a `Var` chain. The receiver chain may have multiple field hops
/// (e.g. `self.A.B.Method`). Anything containing a call, arithmetic, or
/// other compound expression is rejected, those have side effects or
/// observable evaluation order that direct inlining would change.
fn is_method_handle_rhs(expr: &Expr) -> bool {
    match expr {
        Expr::FieldAccess { recv, .. } => is_method_handle_recv(recv),
        _ => false,
    }
}

fn is_method_handle_recv(expr: &Expr) -> bool {
    match expr {
        Expr::Var(_) => true,
        Expr::FieldAccess { recv, .. } => is_method_handle_recv(recv),
        _ => false,
    }
}

/// Returns `true` when every `Var(name)` use in `body` (excluding the
/// def at `skip_idx`) sits in `Stmt::Call::func` position. The check is
/// "total uses == call-handle uses", any mismatch means at least one use
/// is in an argument, condition, or other expression position and the
/// pass must not fire.
fn all_uses_are_call_handles(body: &[Stmt], name: &str, skip_idx: usize) -> bool {
    let mut total_uses = 0usize;
    walk_body_exprs(body, &mut |expr| {
        if let Expr::Var(other) = expr {
            if other == name {
                total_uses += 1;
            }
        }
    });
    let handle_uses = count_call_handle_uses(body, name, skip_idx);
    handle_uses > 0 && handle_uses == total_uses
}

/// Recursively count `Stmt::Call { func: Var(name), .. }` occurrences in
/// `body`. Skips `body[skip_idx]` (the assignment itself).
fn count_call_handle_uses(body: &[Stmt], name: &str, skip_idx: usize) -> usize {
    body.iter()
        .enumerate()
        .map(|(idx, stmt)| {
            if idx == skip_idx {
                0
            } else {
                count_call_handle_uses_in_stmt(stmt, name)
            }
        })
        .sum()
}

fn count_call_handle_uses_in_stmt(stmt: &Stmt, name: &str) -> usize {
    let mut total = match stmt {
        Stmt::Call {
            func: Expr::Var(handle),
            ..
        } if handle == name => 1,
        _ => 0,
    };
    walk_stmt_children(stmt, &mut |inner| {
        total += count_call_handle_uses(inner, name, usize::MAX);
    });
    total
}

/// Replace every `Stmt::Call::func` that is `Var(name)` with a clone of
/// `replacement`. Recurses through every nested body slot. `skip_idx`
/// (the assignment stmt) is left untouched.
fn replace_call_handles(body: &mut [Stmt], name: &str, replacement: &Expr, skip_idx: usize) {
    for (idx, stmt) in body.iter_mut().enumerate() {
        if idx == skip_idx {
            continue;
        }
        replace_call_handles_in_stmt(stmt, name, replacement);
    }
}

fn replace_call_handles_in_stmt(stmt: &mut Stmt, name: &str, replacement: &Expr) {
    if let Stmt::Call { func, .. } = stmt {
        if matches!(func, Expr::Var(handle) if handle == name) {
            *func = replacement.clone();
        }
    }
    walk_stmt_children_mut(stmt, &mut |inner_body| {
        for inner_stmt in inner_body.iter_mut() {
            replace_call_handles_in_stmt(inner_stmt, name, replacement);
        }
    });
}

/// Single inlining sweep over `body`. Returns `true` if any substitution was
/// made (caller should re-run for chained temps).
fn inline_pass(body: &mut Vec<Stmt>) -> bool {
    let use_counts = var_refs::count_all_var_uses(body);

    // Collect candidates: indices of Assignment stmts whose lhs Var has
    // exactly one use (RHS-only count; LHS is the def, not a use) and a
    // trustworthy rhs.
    let candidates: Vec<(usize, String)> = body
        .iter()
        .enumerate()
        .filter_map(|(idx, stmt)| {
            let (name, rhs) = match stmt {
                Stmt::Assignment {
                    lhs: Expr::Var(name),
                    rhs,
                    ..
                } => (name, rhs),
                _ => return None,
            };
            if !is_inline_candidate_name(name) {
                return None;
            }
            if use_counts.get(name).copied().unwrap_or(0) != 1 {
                return None;
            }
            if expr_contains_unknown(rhs) {
                return None;
            }
            if matches!(rhs, Expr::Out(_)) {
                return None;
            }
            Some((idx, name.clone()))
        })
        .collect();

    if candidates.is_empty() {
        return false;
    }

    let mut changed = false;

    // Process candidates from the end so removal indices stay valid.
    for (assign_idx, var_name) in candidates.into_iter().rev() {
        // Clone the rhs out of the assignment before mutating the body.
        let rhs_clone = match &body[assign_idx] {
            Stmt::Assignment { rhs, .. } => rhs.clone(),
            _ => continue,
        };

        // Find and replace the single use site in the body (excluding the
        // assignment stmt itself at assign_idx).
        let substituted = substitute_var_in_body(body, &var_name, &rhs_clone, assign_idx);
        if substituted {
            body.remove(assign_idx);
            changed = true;
        }
    }

    changed
}

/// Replace the first occurrence of `Expr::Var(var_name)` (as a use, not
/// a def) in `body`, skipping the statement at `skip_idx` (the
/// assignment statement itself). Returns `true` if a substitution was
/// made. Walks via the shared visitor so Assignment lhs is never
/// substituted, that would corrupt the assignment shape.
fn substitute_var_in_body(
    body: &mut [Stmt],
    var_name: &str,
    replacement: &Expr,
    skip_idx: usize,
) -> bool {
    for (idx, stmt) in body.iter_mut().enumerate() {
        if idx == skip_idx {
            continue;
        }
        let mut substituted = false;
        walk_stmt_exprs_mut(stmt, &mut |expr| {
            if substituted {
                return Action::Stop;
            }
            if let Expr::Var(name) = expr {
                if name == var_name {
                    *expr = replacement.clone();
                    substituted = true;
                    return Action::Stop;
                }
            }
            Action::Continue
        });
        if substituted {
            return true;
        }
    }
    false
}

/// Inline a Blueprint-rematerialised scratch temp: a compiler temp with
/// two or more definitions that ALL assign the same read-only source
/// variable (a parameter or local that is never itself assigned anywhere
/// in the body).
///
/// The Blueprint compiler re-emits a select condition as
/// `Temp_bool_Variable_N = LeftHand` immediately before each use. When CSE
/// (`hoist_repeated_projections`) later consolidates the repeated uses into
/// a single `$Cse` temp, only one use of the scratch temp survives (the
/// `$Cse` condition) while several defs remain; the single-use inliner
/// rejects the multi-def shape, then dead-statement removal sweeps every
/// def, leaving a use of an undefined variable. Substituting the uniform
/// source into every use and dropping the defs is safe precisely because
/// the source is never reassigned: its value is identical at every program
/// point, so there is no use-before-def hazard (the source is a function
/// parameter, always in scope). Gated on >= 2 defs so single-def temps stay
/// on the ordinary single-use inliner.
pub fn inline_uniform_multidef_param_temps(body: &mut Vec<Stmt>) {
    let assigned = collect_assigned_names(body);
    // temp -> Some(src) while every def agrees on the same source Var;
    // None once a def disagrees or is not a uniform read-only source.
    let mut src_of: BTreeMap<String, Option<String>> = BTreeMap::new();
    let mut def_counts: BTreeMap<String, usize> = BTreeMap::new();
    collect_uniform_param_defs(body, &assigned, &mut src_of, &mut def_counts);

    let targets: BTreeMap<String, String> = src_of
        .into_iter()
        .filter_map(|(temp, src)| {
            let src = src?;
            (def_counts.get(&temp).copied().unwrap_or(0) >= 2).then_some((temp, src))
        })
        .collect();

    for (temp, src) in &targets {
        walk_body_exprs_mut(body, &mut |expr: &mut Expr| {
            if let Expr::Var(name) = expr {
                if name == temp {
                    *name = src.clone();
                }
            }
            Action::Continue
        });
        remove_var_defs(body, temp);
    }
}

/// Every variable name that appears as an assignment lhs anywhere in
/// `body` (recursing into nested bodies). A name in this set is not a
/// stable source for [`inline_uniform_multidef_param_temps`].
fn collect_assigned_names(body: &[Stmt]) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = BTreeSet::new();
    for stmt in body {
        if let Stmt::Assignment {
            lhs: Expr::Var(name),
            ..
        } = stmt
        {
            names.insert(name.clone());
        }
        walk_stmt_children(stmt, &mut |children| {
            names.extend(collect_assigned_names(children));
        });
    }
    names
}

/// Accumulate, per compiler-temp lhs, its def count and (while they all
/// agree) the single read-only source Var its defs assign. A def whose rhs
/// is not a bare read-only parameter/local Var, or that disagrees with an
/// earlier def, marks the temp's source `None` (disqualified).
fn collect_uniform_param_defs(
    body: &[Stmt],
    assigned: &BTreeSet<String>,
    src_of: &mut BTreeMap<String, Option<String>>,
    def_counts: &mut BTreeMap<String, usize>,
) {
    for stmt in body {
        if let Stmt::Assignment {
            lhs: Expr::Var(temp),
            rhs,
            ..
        } = stmt
        {
            if is_compiler_temp_name(temp) {
                *def_counts.entry(temp.clone()).or_insert(0) += 1;
                let candidate = match rhs {
                    Expr::Var(src)
                        if !is_compiler_temp_name(src)
                            && !src.contains('.')
                            && !assigned.contains(src) =>
                    {
                        Some(src.clone())
                    }
                    _ => None,
                };
                match src_of.get(temp) {
                    None => {
                        src_of.insert(temp.clone(), candidate);
                    }
                    Some(Some(existing)) if candidate.as_deref() != Some(existing.as_str()) => {
                        src_of.insert(temp.clone(), None);
                    }
                    _ => {}
                }
            }
        }
        walk_stmt_children(stmt, &mut |children| {
            collect_uniform_param_defs(children, assigned, src_of, def_counts);
        });
    }
}

/// Remove every `Stmt::Assignment` whose lhs is `Var(name)`, at any nesting
/// depth.
fn remove_var_defs(body: &mut Vec<Stmt>, name: &str) {
    body.retain(
        |stmt| !matches!(stmt, Stmt::Assignment { lhs: Expr::Var(lhs), .. } if lhs == name),
    );
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut |children| remove_var_defs(children, name));
    }
}

/// Returns `true` if `name` is a candidate for inlining.
///
/// The Blueprint compiler emits temporaries with recognisable shapes:
/// `$`-prefixed compute/cast/CSE slots (`$Subtract_FloatFloat_2`, `$Cse_1`,
/// `$Cast_AsPlayer`), `Temp_*` / `K2Node_*` / `CallFunc_*` prefixes, and
/// `<Name>_<N>` numeric-suffixed slots (`Tmp_3`). Only those shapes are
/// inline candidates.
///
/// Persistent Blueprint variables (member graph variables and function
/// locals) render as bare `Var("RotationDifference")` with NO `self.`
/// prefix (see `decode/expr_decode.rs::on_field_path_var`, where only
/// instance/default/sparse variables get a qualifying receiver). A
/// writeback like `RotationDifference = $Subtract_FloatFloat_2` is an
/// observable member write, not a temp def. The earlier deny-list let
/// such bare names through, so the inliner folded the writeback's RHS
/// into the earlier `RotationDifference` read and deleted the writeback,
/// dropping the field write and producing a self-referencing assignment.
///
/// Excludes well-known non-temporary names (`Self`, `None`), dotted
/// names (instance/default/sparse field writes render as
/// `Var("self.Field")`, inlining the LHS would drop the field write),
/// bare single-lowercase-letter loop counters (`i`, `j`), and any name
/// that is not a compiler-temp shape (a persistent member/local variable
/// writeback, which is observable and must not be folded away).
fn is_inline_candidate_name(name: &str) -> bool {
    if matches!(name, "Self" | "None") {
        return false;
    }
    if name.contains('.') {
        return false;
    }
    // Single lowercase letter: conventional loop-counter, skip.
    if name.len() == 1 && name.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
        return false;
    }
    is_compiler_temp_name(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::{BinaryOp, Expr};
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign, lit, var};

    fn make_call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            name: name.to_string(),
            args,
        }
    }

    fn call_stmt(func_name: &str, args: Vec<Expr>) -> Stmt {
        Stmt::Call {
            func: Expr::Var(func_name.to_string()),
            args,
            offset: 0,
        }
    }

    #[test]
    fn single_use_temp_inlines() {
        // Tmp_3 = Foo(); Bar(Tmp_3)  =>  Bar(Foo())
        let mut body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        match &body[0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], make_call("Foo", vec![]));
            }
            _ => panic!("expected Call statement after inlining"),
        }
    }

    #[test]
    fn multi_use_temp_does_not_inline() {
        // Tmp_3 = Foo(); Bar(Tmp_3); Baz(Tmp_3)  =>  unchanged
        let mut body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
            call_stmt("Baz", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(
            body.len(),
            original_len,
            "multi-use temp must not be inlined"
        );
    }

    #[test]
    fn chain_inlines_to_fixed_point() {
        // Temp_a = 1; Temp_b = Temp_a; Bar(Temp_b)  =>  Bar(1)
        // Temp_-prefixed so both names are compiler-temp-shaped under the
        // shared allow-list (`Tmp_` is not a recognised prefix).
        let mut body = vec![
            assign("Temp_a", lit("1")),
            assign("Temp_b", var("Temp_a")),
            call_stmt("Bar", vec![var("Temp_b")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        match &body[0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], lit("1"));
            }
            _ => panic!("expected Call statement after chain inlining"),
        }
    }

    #[test]
    fn unknown_rhs_does_not_inline() {
        let unknown_expr = Expr::Unknown {
            reason: "test".into(),
            raw_bytes: vec![0xff],
            offset: 0,
        };
        let mut body = vec![
            assign("Tmp_3", unknown_expr),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), original_len, "Unknown rhs must not be inlined");
    }

    #[test]
    fn out_param_does_not_inline() {
        let mut body = vec![
            assign("Tmp_3", Expr::Out(Box::new(var("X")))),
            call_stmt("Foo", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), original_len, "Out rhs must not be inlined");
    }

    #[test]
    fn dotted_name_does_not_inline() {
        // Field writes render as Var("self.Field") (see decode/expr_decode.rs:286).
        // Inlining `self.Hunger = $FClamp` into `(self.Hunger + ...)` would drop
        // the observable field write and produce a self-referencing assignment.
        // Regression captured during the recursive-into-Sequence-pin landing.
        let mut body = vec![
            assign(
                "$Add",
                Expr::Binary {
                    op: BinaryOp::Add,
                    lhs: Box::new(var("self.Hunger")),
                    rhs: Box::new(lit("1")),
                },
            ),
            assign("$FClamp", make_call("FClamp", vec![var("$Add")])),
            assign("self.Hunger", var("$FClamp")),
        ];
        inline_single_use_temps(&mut body);
        // Field write must survive.
        let last = body.last().expect("non-empty body");
        let Stmt::Assignment { lhs, .. } = last else {
            panic!("expected trailing field write assignment");
        };
        assert!(
            matches!(lhs, Expr::Var(name) if name == "self.Hunger"),
            "field write self.Hunger must remain"
        );
    }

    #[test]
    fn sequence_pin_temps_inline() {
        // P2 unblock: temps defined inside a Sequence pin body should
        // inline like top-level temps within their pin scope.
        use crate::bytecode::stmt::Stmt;
        let pin_body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        let mut body = vec![Stmt::Sequence {
            pins: vec![pin_body],
            offset: 0,
        }];
        inline_single_use_temps(&mut body);
        let Stmt::Sequence { pins, .. } = &body[0] else {
            panic!("expected Sequence");
        };
        assert_eq!(pins[0].len(), 1, "pin scope inlining should drop the temp");
        match &pins[0][0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], make_call("Foo", vec![]));
            }
            _ => panic!("expected pin-body Call after inlining"),
        }
    }

    #[test]
    fn reassigned_temp_does_not_corrupt_lhs() {
        // Regression: `Temp_X = 0; Temp_X = counter` previously got
        // `count_var_uses(Temp_X) == 2` (both lhs hits), then qualified for
        // inlining and substituted `0` into the second lhs, producing
        // `0 = counter`. With lhs no longer counted as a use, the dead
        // first assignment has count 0 (never read), and the second has
        // count 0 too, so neither inlines.
        let mut body = vec![assign("Temp_X", lit("0")), assign("Temp_X", var("counter"))];
        inline_single_use_temps(&mut body);
        // Whatever the outcome, must NOT contain `0 = counter`.
        for stmt in &body {
            if let Stmt::Assignment { lhs, rhs, .. } = stmt {
                assert!(
                    !matches!((lhs, rhs), (Expr::Literal(literal), Expr::Var(_)) if literal == "0"),
                    "must not produce literal-on-lhs corruption"
                );
            }
        }
    }

    fn field_access(recv_name: &str, field: &str) -> Expr {
        Expr::FieldAccess {
            recv: Box::new(var(recv_name)),
            field: field.to_string(),
        }
    }

    #[test]
    fn method_handle_single_use_inlines() {
        // $Play = self.Comp.Play; $Play(0.0)  =>  self.Comp.Play(0.0)
        let mut body = vec![
            assign("$Play", field_access("self.Comp", "Play")),
            call_stmt("$Play", vec![lit("0.0")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1, "binding should be dropped");
        let Stmt::Call { func, .. } = &body[0] else {
            panic!("expected Call");
        };
        assert_eq!(func, &field_access("self.Comp", "Play"));
    }

    #[test]
    fn method_handle_multi_use_inlines_all_call_sites() {
        // Duplicated-convergence case: $X bound once, called twice. The
        // single-use inliner rejects this (count != 1), but a method-ref
        // rhs is pure so substituting every call-handle position is safe.
        let mut body = vec![
            assign("$Stop", field_access("self.Comp", "Stop")),
            call_stmt("$Stop", vec![]),
            call_stmt("$Stop", vec![]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 2, "binding should be dropped");
        for stmt in &body {
            let Stmt::Call { func, .. } = stmt else {
                panic!("expected Call");
            };
            assert_eq!(func, &field_access("self.Comp", "Stop"));
        }
    }

    #[test]
    fn method_handle_value_use_inlined_only_by_single_use_path() {
        // $X = self.A.B; $X is passed as a value arg (not a call handle).
        // The method-handle pass must NOT fire, but the single-use inliner
        // will substitute the FieldAccess into the arg position because
        // count == 1. Either way the binding is gone, never with the
        // FieldAccess wrongly placed as a func.
        let mut body = vec![
            assign("$Ref", field_access("self.Obj", "Field")),
            call_stmt("Bar", vec![var("$Ref")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Call { func, args, .. } = &body[0] else {
            panic!("expected Call");
        };
        // The outer call's func must remain `Var("Bar")` — the
        // method-handle pass should not have grabbed it.
        assert_eq!(func, &var("Bar"));
        assert_eq!(args[0], field_access("self.Obj", "Field"));
    }

    #[test]
    fn method_handle_branch_arms_share_binding() {
        // $X bound once at outer scope, called from inside both branch
        // arms. Each arm gets the FieldAccess inlined; binding is dropped.
        let mut body = vec![
            assign("$Set", field_access("self.Move", "SetMode")),
            Stmt::Branch {
                cond: lit("true"),
                then_body: vec![call_stmt("$Set", vec![lit("true")])],
                else_body: vec![call_stmt("$Set", vec![lit("false")])],
                offset: 0,
            },
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1, "binding should be dropped");
        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        for arm in [then_body, else_body] {
            assert_eq!(arm.len(), 1);
            let Stmt::Call { func, .. } = &arm[0] else {
                panic!("expected Call");
            };
            assert_eq!(func, &field_access("self.Move", "SetMode"));
        }
    }

    #[test]
    fn method_handle_rhs_with_non_var_recv_skipped() {
        // rhs is FieldAccess { recv: Call(...), .. } — a method-on-call.
        // The receiver Call has side effects, so inlining at multiple
        // sites would change evaluation count. Pass must skip.
        let rhs = Expr::FieldAccess {
            recv: Box::new(Expr::Call {
                name: "GetThing".to_string(),
                args: vec![],
            }),
            field: "DoIt".to_string(),
        };
        let mut body = vec![
            assign("$X", rhs),
            call_stmt("$X", vec![]),
            call_stmt("$X", vec![]),
        ];
        inline_single_use_temps(&mut body);
        // Binding must survive at index 0; the call-handle uses must
        // remain `Var("$X")` rather than the inlined FieldAccess.
        assert_eq!(body.len(), 3, "binding with side-effect recv must stay");
        let Stmt::Assignment { lhs, .. } = &body[0] else {
            panic!("expected Assignment at index 0");
        };
        assert_eq!(lhs, &var("$X"));
        for stmt in &body[1..] {
            let Stmt::Call { func, .. } = stmt else {
                panic!("expected Call");
            };
            assert_eq!(func, &var("$X"));
        }
    }

    #[test]
    fn iteration_cap_warns_does_not_panic() {
        // Construct a body where a temp is genuinely used twice so no
        // inlining happens — the pass should terminate cleanly at the
        // fixed-point check after the first no-change pass, never hitting
        // the cap. This test verifies the function doesn't panic on such
        // a body.
        let mut body = vec![
            assign(
                "Tmp_3",
                Expr::Binary {
                    op: BinaryOp::Add,
                    lhs: Box::new(lit("1")),
                    rhs: Box::new(lit("2")),
                },
            ),
            call_stmt("Bar", vec![var("Tmp_3"), var("Tmp_3")]),
        ];
        // Should return quickly (no change on first pass) and not panic.
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 2);
    }
}
