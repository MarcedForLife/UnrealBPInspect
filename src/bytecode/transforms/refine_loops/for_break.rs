use super::{inline_body_temps_into_increment, lhs_matches_var, resolve_cond_chain};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit;

/// Promote a ForLoopWithBreak `While` to `LoopKind::ForC`, recovering the
/// index increment from the trailing break-flag-guard region.
///
/// The Blueprint ForLoopWithBreak macro compiles to a While whose head cond is
/// `Binary(And, !break_flag, counter <= last)` (the break flag short-circuits
/// the loop when a `break` fired) and whose trailing body statement is a
/// guard region `if (!break_flag) { counter = counter + 1 }` that advances the
/// index only while no break has been hit. Unlike a plain ForC, the increment
/// is wrapped in that guard Branch rather than sitting as a bare trailing
/// assignment, so `extract_increment` does not fire and the loop falls to the
/// "stays While" path.
///
/// Fingerprint (chain-resolved against `body` + `ancestors`):
///
/// 1. The cond resolves to `Binary(And, X, Y)` where one operand is a
///    break-flag negation and the OTHER resolves to
///    `Binary(Le|Lt, Var(counter), bound)` (the index bound, NOT an
///    `Array_Length` ForEach bound).
/// 2. The last body statement is `Branch { cond = <break-flag negation of the
///    same flag>, then_body = [.. ending in `counter = <expr>`], else_body =
///    [] }`, optionally immediately preceded by a `$temp = Not_PreBool(flag)`
///    re-eval assignment.
///
/// On match it:
///
/// - sets `*cond` to the bound operand reference (the un-resolved
///   `Var($LessEqual_IntInt)` so the later inliner folds it into the header,
///   mirroring plain ForC, and so the dead-`$`-temp sweep keeps the bound
///   alive while dropping the `$BooleanAND` And-leak),
/// - moves the increment statements out of the guard region into
///   `LoopKind::ForC { init: vec![], increment }`,
/// - drops the trailing guard Branch and its optional `$`-temp re-eval from
///   the body, leaving the real break-test if/else as the loop body.
///
/// The dead pre-loop `$BooleanAND` And-leak (and the break-flag scaffolding it
/// fed) is dropped by the absorb loop in [`refine_loops_vec`], reusing the
/// transitive `$`-temp sweep.
pub(super) fn try_promote_for_loop_with_break(
    kind: &mut LoopKind,
    cond: &mut Option<Expr>,
    body: &mut Vec<Stmt>,
    ancestors: &[&[Stmt]],
) -> bool {
    let Some(cond_expr) = cond.as_ref() else {
        return false;
    };
    // Snapshot the body for the read-only chain-resolution scope so the live
    // `body` can be borrowed mutably by `extract_break_guard_increment` below.
    // The guard's `Var($Not_PreBool)` cond resolves through the in-body re-eval
    // assignment, so the body must be in the scope stack.
    let body_snapshot: Vec<Stmt> = body.clone();
    let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
    scopes.push(body_snapshot.as_slice());
    scopes.extend(ancestors.iter().copied());

    // The head cond must be the And-guarded `(!break_flag && (counter <= last))`
    // shape. Resolve the cond and its And operands, peel the break-flag
    // negation, and confirm the surviving operand is an index bound over a
    // counter. `bound_operand` is the ORIGINAL (un-resolved) operand reference
    // so it can become the loop's new cond.
    let Some((counter_name, bound_operand)) = match_for_break_bound(cond_expr, &scopes) else {
        return false;
    };

    // The trailing body must be the break-flag-guard increment region.
    let Some(increment) = extract_break_guard_increment(body, &counter_name, &scopes) else {
        return false;
    };

    *cond = Some(bound_operand);
    *kind = LoopKind::ForC {
        init: vec![],
        increment,
    };
    true
}

/// Match the ForLoopWithBreak head cond: resolve `cond` to `Binary(And, A, B)`,
/// peel the break-flag negation, and confirm the surviving operand is an index
/// bound `Binary(Le|Lt, Var(counter), bound)`. Returns the counter name and the
/// ORIGINAL (un-resolved) bound operand so the caller can install it as the
/// loop's cond (letting the inliner fold the `$`-temp into the header).
///
/// Distinct from [`match_foreach_cond`]: this requires a plain index bound, NOT
/// an `Array_Length` ForEach bound, so it never fires on a ForEach-with-break.
fn match_for_break_bound(cond: &Expr, scopes: &[&[Stmt]]) -> Option<(String, Expr)> {
    let resolved = resolve_cond_chain(cond, scopes);
    let Expr::Binary {
        op: crate::bytecode::expr::BinaryOp::And,
        lhs,
        rhs,
    } = resolved
    else {
        return None;
    };
    // The And operands may themselves be opaque `Var($X)` references; resolve
    // each before testing for the break-flag negation, but keep the original
    // operand reference for the surviving (bound) side.
    let lhs_resolved = resolve_cond_chain(lhs, scopes);
    let rhs_resolved = resolve_cond_chain(rhs, scopes);
    let bound_operand = if is_break_flag_not(lhs_resolved) {
        rhs.as_ref()
    } else if is_break_flag_not(rhs_resolved) {
        lhs.as_ref()
    } else {
        return None;
    };
    let counter_name = match_index_bound_counter(bound_operand, scopes)?;
    Some((counter_name, bound_operand.clone()))
}

/// When `expr` resolves to `Binary(Le|Lt, Var(counter), bound)` whose bound is
/// NOT an `Array_Length` call, return the counter name. The non-`Array_Length`
/// gate keeps this from accepting a ForEach-with-break bound (which the ForEach
/// path owns).
fn match_index_bound_counter(expr: &Expr, scopes: &[&[Stmt]]) -> Option<String> {
    let resolved = resolve_cond_chain(expr, scopes);
    let Expr::Binary { op, lhs, rhs } = resolved else {
        return None;
    };
    if !matches!(
        op,
        crate::bytecode::expr::BinaryOp::Le | crate::bytecode::expr::BinaryOp::Lt
    ) {
        return None;
    }
    let counter_name = match lhs.as_ref() {
        Expr::Var(name) => name.clone(),
        Expr::FieldAccess { field, .. } => field.clone(),
        _ => return None,
    };
    // Reject the ForEach bound shape (`counter < Array_Length(arr)`); that is
    // the ForEach-with-break path's territory.
    let rhs_resolved = resolve_cond_chain(rhs, scopes);
    let is_array_bound = match rhs_resolved {
        Expr::Call { name, args } => is_array_length_name(name) && args.len() == 1,
        Expr::MethodCall { name, args, .. } => is_array_length_name(name) && args.is_empty(),
        _ => false,
    };
    if is_array_bound {
        return None;
    }
    Some(counter_name)
}

/// If the trailing body statement is the break-flag-guard increment region,
/// remove it (and an optional preceding `$temp = Not_PreBool(flag)` re-eval)
/// from `body` and return the increment statements.
///
/// The region is `Branch { cond = <break-flag negation>, then_body = [.. ending
/// in `counter = <expr>`], else_body = [] }`. The then-arm holds the recovered
/// increment (`$Add_IntInt = counter + 1; counter = $Add_IntInt`); its final
/// assignment must target `counter`. The else-arm must be empty.
fn extract_break_guard_increment(
    body: &mut Vec<Stmt>,
    counter_name: &str,
    scopes: &[&[Stmt]],
) -> Option<Vec<Stmt>> {
    // Inspect the last statement non-destructively first.
    let last = body.last()?;
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = last
    else {
        return None;
    };
    if !else_body.is_empty() {
        return None;
    }
    if !is_break_flag_not(resolve_cond_chain(cond, scopes)) {
        return None;
    }
    // The then-arm must be a non-empty increment block whose final statement
    // assigns the counter.
    let last_assign_targets_counter = matches!(
        then_body.last(),
        Some(Stmt::Assignment { lhs, .. }) if lhs_matches_var(lhs, counter_name)
    );
    if then_body.is_empty() || !last_assign_targets_counter {
        return None;
    }

    // Commit: take the increment out of the guard, drop the guard Branch, and
    // drop an immediately-preceding `$temp = Not_PreBool(flag)` re-eval.
    let Some(Stmt::Branch { then_body, .. }) = body.pop() else {
        return None;
    };
    if matches!(body.last(), Some(stmt) if is_break_flag_reeval(stmt)) {
        body.pop();
    }

    // The guard then-arm is the un-inlined increment block
    // `[$Add_IntInt = (counter + 1), counter = $Add_IntInt]`. The plain-ForC
    // path keeps only the trailing `counter = <expr>` in the increment slot and
    // inlines the `$`-temp defs into it (`counter = counter + 1`) via
    // `inline_body_temps_into_increment`, so the slot is self-contained and the
    // later global inliner does not mis-fold the orphaned `$`-temp. Mirror that:
    // keep the final counter assignment, fold the preceding defs into it.
    let mut defs = then_body;
    let counter_assign = defs.pop()?;
    let mut increment = vec![counter_assign];
    inline_body_temps_into_increment(&mut increment, &mut defs);
    Some(increment)
}

/// True when `stmt` is a `$temp = Not_PreBool(flag)` / `$temp = !flag`
/// break-flag re-evaluation assignment (the in-body recompute that feeds the
/// trailing guard Branch's cond).
fn is_break_flag_reeval(stmt: &Stmt) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    matches!(lhs, Expr::Var(name) if name.starts_with('$')) && is_break_flag_not(rhs)
}

/// True when `stmt` is the dead `$temp = Binary(And, !break_flag, bound)`
/// head-cond leak that precedes a ForLoopWithBreak-promoted ForC loop.
///
/// Blueprint emits the And-guarded head cond as a sibling before the loop. The
/// loop now renders `for (counter = init to bound)` and carries the bound in
/// its own cond, so the And-leak (and the break-flag scaffolding it fed) is
/// dead. Mirrors [`is_foreach_bound_expr_leak`] for the index-bound ForC shape.
pub(super) fn is_for_break_bound_leak(stmt: &Stmt, scopes: &[&[Stmt]]) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    if !matches!(lhs, Expr::Var(name) if name.starts_with('$')) {
        return false;
    }
    let Expr::Binary {
        op: crate::bytecode::expr::BinaryOp::And,
        ..
    } = rhs
    else {
        return false;
    };
    match_for_break_bound(rhs, scopes).is_some()
}

/// If `cond` is `Binary(And, A, B)` where one operand is a break-flag negation,
/// return the other operand. Order-insensitive. Returns `None` otherwise.
pub(super) fn peel_break_flag_and(cond: &Expr) -> Option<&Expr> {
    let Expr::Binary {
        op: crate::bytecode::expr::BinaryOp::And,
        lhs,
        rhs,
    } = cond
    else {
        return None;
    };
    if is_break_flag_not(lhs) {
        return Some(rhs.as_ref());
    }
    if is_break_flag_not(rhs) {
        return Some(lhs.as_ref());
    }
    None
}

/// True when `expr` is a logical negation of a single leaf operand. The
/// leaf restriction (Var, FieldAccess, or Literal) keeps `!(a < b)` from
/// matching and being conflated with the break-flag pattern.
fn is_break_flag_not(expr: &Expr) -> bool {
    visit::negated_operand(expr).is_some_and(is_break_flag_leaf)
}

/// True for leaves we accept inside a break-flag-not wrapper.
fn is_break_flag_leaf(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Var(_) | Expr::FieldAccess { .. } | Expr::Literal(_)
    )
}

/// True for any function name that represents `Array_Length(array)`.
pub(super) fn is_array_length_name(name: &str) -> bool {
    matches!(name, "Array_Length" | "Length")
}
