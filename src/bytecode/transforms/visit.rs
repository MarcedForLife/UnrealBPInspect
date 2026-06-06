//! Shared tree-walk helpers for IR transforms.
//!
//! These helpers exist to deduplicate near-identical traversals that
//! several transform passes share: peeling transparent expression
//! wrappers, visiting every direct sub-body of a statement, and
//! scanning expressions for `Expr::Unknown` markers.

use std::collections::BTreeSet;

use crate::bytecode::expr::{Expr, SwitchExprCase, UnaryOp};
use crate::bytecode::stmt::{LoopKind, Stmt};

/// Strip `Out` / `Interface` / `Persistent` wrappers so structural
/// equality and other inspectors see the inner storage.
pub(crate) fn peel_transparent(expr: &Expr) -> &Expr {
    let mut cursor = expr;
    while let Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) = cursor {
        cursor = inner.as_ref();
    }
    cursor
}

/// Return the negated operand when `expr` is a logical-not in either of
/// the two shapes the IR carries: `Unary { Not, operand }` (post-inline)
/// or `Call { name: "Not_PreBool", args: [operand] }` (pre-inline). The
/// `Not_PreBool` form survives whenever the Blueprint compiler emits a
/// `Not_PreBool` node and no later pass inlines it. Returns `None` for any
/// other expression shape.
pub(crate) fn negated_operand(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
        } => Some(operand.as_ref()),
        Expr::Call { name, args } if name == "Not_PreBool" && args.len() == 1 => Some(&args[0]),
        _ => None,
    }
}

/// Apply `visit` to every direct sub-body inside `stmt`. Sub-bodies are
/// the `Vec<Stmt>` slots a statement owns: branch then/else, sequence
/// pins, loop body/completion, ForC init/increment, switch case
/// bodies/default, latch init/body. Leaf variants (Assignment, Call,
/// Return, EventCall, Unknown) have no sub-bodies and are no-ops.
///
/// `stmt` itself is NOT visited; callers handle their own statement
/// before or after invoking this helper.
pub(crate) fn walk_stmt_children_mut<F: FnMut(&mut Vec<Stmt>)>(stmt: &mut Stmt, visit: &mut F) {
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
            for pin_body in pins.iter_mut() {
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
            // ForC carries init and increment sub-bodies. Pre-`refine_loops`
            // passes never observe ForC by pipeline construction, so the
            // recursion is dormant for them. Post-refine passes
            // (`inline_single_use_temps`, `dead_stmt`) need the slots visited.
            if let LoopKind::ForC { init, increment } = kind {
                visit(init);
                visit(increment);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for case in cases.iter_mut() {
                visit(&mut case.body);
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

/// Read-only counterpart of [`walk_stmt_children_mut`]. Applies `visit`
/// to every direct sub-body inside `stmt` with the same variant coverage
/// and child order: branch then/else, sequence pins, loop
/// body/completion/ForC-init/increment, switch case bodies/default, latch
/// init/body. `stmt` itself is NOT visited; leaf variants are no-ops.
pub(crate) fn walk_stmt_children<F: FnMut(&[Stmt])>(stmt: &Stmt, visit: &mut F) {
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

/// Walk each statement of `body` in order, building the per-statement
/// ancestor scope stack and handing `(stmt, child_ancestors)` to `visit`.
///
/// `child_ancestors` is innermost-first: the statement's preceding
/// siblings (`body[..i]`) as the innermost slice, then `ancestors`
/// unchanged. This captures the `split_at_mut` borrow-split that several
/// chain-resolving transforms (cascade_fold, demote_invariant_loops,
/// latch_recognition, lower_sentinel_cascade, refine_loops) share so a
/// rewrite at one statement can resolve `Var` chains through every outer
/// scope. The immutable prefix and the mutable current-statement borrow
/// do not alias.
pub(crate) fn walk_bodies_with_ancestors_mut<F: FnMut(&mut Stmt, &[&[Stmt]])>(
    body: &mut [Stmt],
    ancestors: &[&[Stmt]],
    visit: &mut F,
) {
    let len = body.len();
    for i in 0..len {
        let (head, tail) = body.split_at_mut(i);
        let head_immut: &[Stmt] = head;
        let stmt = &mut tail[0];
        let mut child_ancestors: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
        child_ancestors.push(head_immut);
        child_ancestors.extend(ancestors.iter().copied());
        visit(stmt, &child_ancestors);
    }
}

/// Returns `true` if any node in the expression tree is `Expr::Unknown`.
/// Used by transforms (inliner, dead-stmt, struct-fold, ternary-fold) to
/// reject candidates whose RHS contains an unrecognised opcode.
pub(crate) fn expr_contains_unknown(expr: &Expr) -> bool {
    if matches!(expr, Expr::Unknown { .. }) {
        return true;
    }
    match expr {
        Expr::Call { args, .. } => args.iter().any(expr_contains_unknown),
        Expr::MethodCall { recv, args, .. } => {
            expr_contains_unknown(recv) || args.iter().any(expr_contains_unknown)
        }
        Expr::FieldAccess { recv, .. } => expr_contains_unknown(recv),
        Expr::Index { recv, idx } => expr_contains_unknown(recv) || expr_contains_unknown(idx),
        Expr::Binary { lhs, rhs, .. } => expr_contains_unknown(lhs) || expr_contains_unknown(rhs),
        Expr::Unary { operand, .. } => expr_contains_unknown(operand),
        Expr::Cast { inner, .. } => expr_contains_unknown(inner),
        Expr::ArrayLit(items) => items.iter().any(expr_contains_unknown),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_contains_unknown(cond)
                || expr_contains_unknown(then_expr)
                || expr_contains_unknown(else_expr)
        }
        Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
            expr_contains_unknown(inner)
        }
        Expr::Resume { inner, .. } => expr_contains_unknown(inner),
        Expr::StructConstruct { fields, .. } => {
            fields.iter().any(|(_, value)| expr_contains_unknown(value))
        }
        Expr::Switch {
            index,
            cases,
            default,
        } => {
            expr_contains_unknown(index)
                || cases.iter().any(|case| {
                    expr_contains_unknown(&case.value) || expr_contains_unknown(&case.body)
                })
                || expr_contains_unknown(default)
        }
        Expr::Literal(_) | Expr::Var(_) | Expr::Unknown { .. } => false,
    }
}

/// Walk `Var($X)` through one or more `$X = $Y; $Y = $Z; ...` temp-assignment
/// hops across `scopes` and return the final non-`Var` expression. Returns
/// `None` when the chain dead-ends (no matching assignment in any scope) or
/// hits a cycle.
///
/// Intended for recognizers that need to inspect the underlying shape of a
/// cond / arg / body marker that the inliner has not yet resolved. The
/// returned reference is into one of the slices in `scopes`; callers must
/// hold those slices immutable while using it.
///
/// `scopes` is innermost-first. For a name referenced from inside a loop's
/// body, `scopes[0]` is typically the loop body's preceding siblings (or the
/// loop body itself), `scopes[1]` is the parent body's preceding siblings,
/// and so on. Within a single name lookup the walk searches each scope in
/// order: it scans `scopes[0]` for a top-level `Stmt::Assignment` whose lhs
/// is `Expr::Var(name)`, then `scopes[1]`, and so on. The first match wins.
/// Only top-level assignments in each scope are consulted; assignments in
/// nested sub-bodies (Branch arms, Sequence pins, Loop bodies, etc.) are
/// NOT consulted. Blueprint-compiler temps live in the same scope as their
/// use or in an enclosing scope, and crossing into nested sub-bodies risks
/// false matches.
///
/// When a name has multiple matching assignments within a single scope, the
/// FIRST in scope order wins. Blueprint rarely emits multiple assignments
/// to a temp, first-wins is the simplest deterministic choice.
///
/// If the resolved expression is itself `Var($Y)`, the walk recurses on `$Y`
/// (still searching the FULL scope stack from innermost-first on each hop)
/// until it finds a non-`Var` expression or runs out of chain. A
/// `BTreeSet<&str>` of visited names guards against cycles.
pub(crate) fn resolve_var_chain<'a>(scopes: &[&'a [Stmt]], name: &str) -> Option<&'a Expr> {
    // Owned `String` for cycle tracking sidesteps the lifetime tangle that
    // arises when `current` migrates between scopes mid-walk. Chain walks are
    // short (single-digit hops in practice), so the allocation cost is
    // negligible.
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut current = name.to_string();
    loop {
        if !visited.insert(current.clone()) {
            return None;
        }
        let rhs = find_top_level_var_assignment(scopes, &current)?;
        match rhs {
            Expr::Var(next) => current = next.clone(),
            other => return Some(other),
        }
    }
}

/// Recursively normalize `Var($X)` references inside `expr` by resolving
/// each through `scopes`. Returns an owned [`Expr`] where every inner `Var`
/// that has a chain definition is replaced with its terminal expression,
/// recursively normalized in turn. `Var` references whose chain dead-ends
/// in the scope stack are left as-is.
///
/// Sibling helper of [`resolve_var_chain`]. Where `resolve_var_chain` walks
/// one chain to its terminal and returns a borrow to the underlying `Expr`,
/// `resolve_expr_chain` keeps walking after the chain hits its terminal,
/// recursing into the terminal's sub-expressions so that any inner `Var`
/// references also resolve through the same scope stack. The owned return
/// type is necessary because the result combines multiple resolved subtrees
/// that don't share storage with the input.
///
/// Cycle guard: a per-name visited set passed down through recursion. A
/// name already on the stack is left as a bare `Var` rather than re-entered.
///
/// Intended for recognizers whose structural match needs the FULL shape of
/// the resolved expression. Example: a loop cond that pre-inline reads as
/// `Var($Less_IntInt)` resolves to `Binary{Lt, counter, Var($Array_Length)}`
/// after one chain hop, and the inner `Var($Array_Length)` resolves further
/// to `Call("Array_Length", [arr])`. Without the deep walk, the matcher
/// would see `rhs: Var($Array_Length)` and reject. With it, the matcher
/// sees `rhs: Call("Array_Length", [arr])` and matches.
pub(crate) fn resolve_expr_chain(expr: &Expr, scopes: &[&[Stmt]]) -> Expr {
    let mut visited: BTreeSet<String> = BTreeSet::new();
    walk_expr_chain(expr, scopes, &mut visited)
}

fn walk_expr_chain(expr: &Expr, scopes: &[&[Stmt]], visited: &mut BTreeSet<String>) -> Expr {
    match expr {
        Expr::Var(name) => {
            if visited.contains(name) {
                return expr.clone();
            }
            match resolve_var_chain(scopes, name) {
                Some(resolved) => {
                    visited.insert(name.clone());
                    let walked = walk_expr_chain(resolved, scopes, visited);
                    visited.remove(name);
                    walked
                }
                None => expr.clone(),
            }
        }
        Expr::Literal(_) | Expr::Unknown { .. } => expr.clone(),
        Expr::Call { name, args } => Expr::Call {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| walk_expr_chain(arg, scopes, visited))
                .collect(),
        },
        Expr::MethodCall { recv, name, args } => Expr::MethodCall {
            recv: Box::new(walk_expr_chain(recv, scopes, visited)),
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| walk_expr_chain(arg, scopes, visited))
                .collect(),
        },
        Expr::FieldAccess { recv, field } => Expr::FieldAccess {
            recv: Box::new(walk_expr_chain(recv, scopes, visited)),
            field: field.clone(),
        },
        Expr::Index { recv, idx } => Expr::Index {
            recv: Box::new(walk_expr_chain(recv, scopes, visited)),
            idx: Box::new(walk_expr_chain(idx, scopes, visited)),
        },
        Expr::Binary { op, lhs, rhs } => Expr::Binary {
            op: *op,
            lhs: Box::new(walk_expr_chain(lhs, scopes, visited)),
            rhs: Box::new(walk_expr_chain(rhs, scopes, visited)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: *op,
            operand: Box::new(walk_expr_chain(operand, scopes, visited)),
        },
        Expr::Cast { kind, inner } => Expr::Cast {
            kind: kind.clone(),
            inner: Box::new(walk_expr_chain(inner, scopes, visited)),
        },
        Expr::ArrayLit(items) => Expr::ArrayLit(
            items
                .iter()
                .map(|item| walk_expr_chain(item, scopes, visited))
                .collect(),
        ),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(walk_expr_chain(cond, scopes, visited)),
            then_expr: Box::new(walk_expr_chain(then_expr, scopes, visited)),
            else_expr: Box::new(walk_expr_chain(else_expr, scopes, visited)),
        },
        Expr::Out(inner) => Expr::Out(Box::new(walk_expr_chain(inner, scopes, visited))),
        Expr::Interface(inner) => {
            Expr::Interface(Box::new(walk_expr_chain(inner, scopes, visited)))
        }
        Expr::Persistent(inner) => {
            Expr::Persistent(Box::new(walk_expr_chain(inner, scopes, visited)))
        }
        Expr::Resume { inner, target } => Expr::Resume {
            inner: Box::new(walk_expr_chain(inner, scopes, visited)),
            target: *target,
        },
        Expr::StructConstruct { type_name, fields } => Expr::StructConstruct {
            type_name: type_name.clone(),
            fields: fields
                .iter()
                .map(|(name, value)| (name.clone(), walk_expr_chain(value, scopes, visited)))
                .collect(),
        },
        Expr::Switch {
            index,
            cases,
            default,
        } => Expr::Switch {
            index: Box::new(walk_expr_chain(index, scopes, visited)),
            cases: cases
                .iter()
                .map(|case| SwitchExprCase {
                    value: walk_expr_chain(&case.value, scopes, visited),
                    body: walk_expr_chain(&case.body, scopes, visited),
                })
                .collect(),
            default: Box::new(walk_expr_chain(default, scopes, visited)),
        },
    }
}

/// Action returned by a mutable expression visitor. Lets the visitor
/// abort the walk early after the first match.
pub(crate) enum Action {
    Continue,
    Stop,
}

/// Walk every Expr reachable from a Stmt subtree, calling `visit` on
/// each. Skips `Stmt::Assignment::lhs` because lhs is a def, not a use,
/// and substituting/renaming there would corrupt the assignment shape.
/// Recurses through every owned sub-body via the existing
/// `walk_stmt_children_mut` pattern. Visitor returning `Action::Stop`
/// halts the entire walk; remaining siblings/children are not visited.
pub(crate) fn walk_body_exprs_mut<F>(body: &mut [Stmt], visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    for stmt in body.iter_mut() {
        if matches!(walk_stmt_exprs_mut(stmt, visit), Action::Stop) {
            return Action::Stop;
        }
    }
    Action::Continue
}

/// Read-only counterpart. Same shape and lhs-skip semantics. No early
/// termination since most read-only callers want every node visited
/// (counting, presence checks).
pub(crate) fn walk_body_exprs<F>(body: &[Stmt], visit: &mut F)
where
    F: FnMut(&Expr),
{
    for stmt in body.iter() {
        walk_stmt_exprs(stmt, visit);
    }
}

/// Single-Stmt mutable walker. Visits every Expr the statement owns
/// (skipping Assignment lhs) and recurses into every owned sub-body.
pub(crate) fn walk_stmt_exprs_mut<F>(stmt: &mut Stmt, visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    match stmt {
        Stmt::Assignment { rhs, .. } => walk_expr_mut(rhs, visit),
        Stmt::Call { func, args, .. } => {
            if matches!(walk_expr_mut(func, visit), Action::Stop) {
                return Action::Stop;
            }
            for arg in args.iter_mut() {
                if matches!(walk_expr_mut(arg, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Stmt::Return { value, .. } => match value {
            Some(inner) => walk_expr_mut(inner, visit),
            None => Action::Continue,
        },
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if matches!(walk_expr_mut(cond, visit), Action::Stop) {
                return Action::Stop;
            }
            if matches!(walk_body_exprs_mut(then_body, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_body_exprs_mut(else_body, visit)
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter_mut() {
                if matches!(walk_body_exprs_mut(pin_body, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            ..
        } => {
            if let LoopKind::ForC { init, increment } = kind {
                if matches!(walk_body_exprs_mut(init, visit), Action::Stop) {
                    return Action::Stop;
                }
                if matches!(walk_body_exprs_mut(increment, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if let LoopKind::ForEach { array, .. } = kind {
                if matches!(walk_expr_mut(array, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if let Some(cond_expr) = cond {
                if matches!(walk_expr_mut(cond_expr, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if matches!(walk_body_exprs_mut(body, visit), Action::Stop) {
                return Action::Stop;
            }
            if let Some(comp) = completion {
                return walk_body_exprs_mut(comp, visit);
            }
            Action::Continue
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            if matches!(walk_expr_mut(expr, visit), Action::Stop) {
                return Action::Stop;
            }
            for case in cases.iter_mut() {
                for value in case.values.iter_mut() {
                    if matches!(walk_expr_mut(value, visit), Action::Stop) {
                        return Action::Stop;
                    }
                }
                if matches!(walk_body_exprs_mut(&mut case.body, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if let Some(default_body) = default {
                return walk_body_exprs_mut(default_body, visit);
            }
            Action::Continue
        }
        Stmt::Latch { init, body, .. } => {
            if matches!(walk_body_exprs_mut(init, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_body_exprs_mut(body, visit)
        }
        Stmt::Break { .. } | Stmt::EventCall { .. } | Stmt::Unknown { .. } => Action::Continue,
    }
}

/// Read-only single-Stmt walker. Mirrors `walk_stmt_exprs_mut` shape
/// and lhs-skip semantics; no early termination.
pub(crate) fn walk_stmt_exprs<F>(stmt: &Stmt, visit: &mut F)
where
    F: FnMut(&Expr),
{
    match stmt {
        Stmt::Assignment { rhs, .. } => walk_expr(rhs, visit),
        Stmt::Call { func, args, .. } => {
            walk_expr(func, visit);
            for arg in args.iter() {
                walk_expr(arg, visit);
            }
        }
        Stmt::Return { value, .. } => {
            if let Some(inner) = value {
                walk_expr(inner, visit);
            }
        }
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            walk_expr(cond, visit);
            walk_body_exprs(then_body, visit);
            walk_body_exprs(else_body, visit);
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter() {
                walk_body_exprs(pin_body, visit);
            }
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            ..
        } => {
            if let LoopKind::ForC { init, increment } = kind {
                walk_body_exprs(init, visit);
                walk_body_exprs(increment, visit);
            }
            if let LoopKind::ForEach { array, .. } = kind {
                walk_expr(array, visit);
            }
            if let Some(cond_expr) = cond {
                walk_expr(cond_expr, visit);
            }
            walk_body_exprs(body, visit);
            if let Some(comp) = completion {
                walk_body_exprs(comp, visit);
            }
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            walk_expr(expr, visit);
            for case in cases.iter() {
                for value in case.values.iter() {
                    walk_expr(value, visit);
                }
                walk_body_exprs(&case.body, visit);
            }
            if let Some(default_body) = default {
                walk_body_exprs(default_body, visit);
            }
        }
        Stmt::Latch { init, body, .. } => {
            walk_body_exprs(init, visit);
            walk_body_exprs(body, visit);
        }
        Stmt::Break { .. } | Stmt::EventCall { .. } | Stmt::Unknown { .. } => {}
    }
}

/// Mutable single-Expr walker. Visits `expr` itself first (pre-order)
/// so callers that mutate the root in-place see the new node when
/// recursing into children of the replacement. Walks every Expr
/// variant; `Switch` covers nested cases and default.
pub(crate) fn walk_expr_mut<F>(expr: &mut Expr, visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    if matches!(visit(expr), Action::Stop) {
        return Action::Stop;
    }
    walk_expr_children_mut(expr, visit)
}

/// Walk only the immediate children of `expr` with the full
/// [`walk_expr_mut`] (so each child subtree is visited pre-order),
/// skipping a visit of `expr` itself. This holds the single exhaustive
/// `Expr` arm list for the mutable direction; `walk_expr_mut` is the
/// visit-root-then-children wrapper over it. Used directly when the root
/// is a definition site (e.g. an `Assignment::lhs`) whose sub-expressions
/// are still reads that should be walked.
pub(crate) fn walk_expr_children_mut<F>(expr: &mut Expr, visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    match expr {
        Expr::Literal(_) | Expr::Var(_) | Expr::Unknown { .. } => Action::Continue,
        Expr::Call { args, .. } => {
            for arg in args.iter_mut() {
                if matches!(walk_expr_mut(arg, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Expr::MethodCall { recv, args, .. } => {
            if matches!(walk_expr_mut(recv, visit), Action::Stop) {
                return Action::Stop;
            }
            for arg in args.iter_mut() {
                if matches!(walk_expr_mut(arg, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Expr::FieldAccess { recv, .. } => walk_expr_mut(recv, visit),
        Expr::Index { recv, idx } => {
            if matches!(walk_expr_mut(recv, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_expr_mut(idx, visit)
        }
        Expr::Binary { lhs, rhs, .. } => {
            if matches!(walk_expr_mut(lhs, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_expr_mut(rhs, visit)
        }
        Expr::Unary { operand, .. } => walk_expr_mut(operand, visit),
        Expr::Cast { inner, .. } => walk_expr_mut(inner, visit),
        Expr::ArrayLit(items) => {
            for item in items.iter_mut() {
                if matches!(walk_expr_mut(item, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            if matches!(walk_expr_mut(cond, visit), Action::Stop) {
                return Action::Stop;
            }
            if matches!(walk_expr_mut(then_expr, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_expr_mut(else_expr, visit)
        }
        Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
            walk_expr_mut(inner, visit)
        }
        Expr::Resume { inner, .. } => walk_expr_mut(inner, visit),
        Expr::StructConstruct { fields, .. } => {
            for (_, value) in fields.iter_mut() {
                if matches!(walk_expr_mut(value, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Expr::Switch {
            index,
            cases,
            default,
        } => {
            if matches!(walk_expr_mut(index, visit), Action::Stop) {
                return Action::Stop;
            }
            for case in cases.iter_mut() {
                if matches!(walk_expr_mut(&mut case.value, visit), Action::Stop) {
                    return Action::Stop;
                }
                if matches!(walk_expr_mut(&mut case.body, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            walk_expr_mut(default, visit)
        }
    }
}

/// Variant of [`walk_body_exprs_mut`] that ALSO visits `Stmt::Assignment::lhs`.
///
/// SkipUses semantics (the default walker) is correct for transforms that
/// rewrite uses without touching defs (substitution, dead-stmt scans). A
/// minority of transforms must rewrite the lhs too: var_names renames the
/// ForC counter on both sides of `i = i + 1`, and struct_fold's use-count
/// must observe `Var(temp)` appearing inside an `Assignment::lhs`'s
/// `FieldAccess { recv, .. }` to detect remaining writes that would
/// invalidate a fold. Those callers use this variant instead.
///
/// Identical semantics to `walk_body_exprs_mut` otherwise: pre-order
/// traversal, `Action::Stop` halts the entire walk.
pub(crate) fn walk_body_exprs_mut_visit_lhs<F>(body: &mut [Stmt], visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    for stmt in body.iter_mut() {
        if matches!(walk_stmt_exprs_mut_visit_lhs(stmt, visit), Action::Stop) {
            return Action::Stop;
        }
    }
    Action::Continue
}

/// Read-only counterpart of [`walk_body_exprs_mut_visit_lhs`].
pub(crate) fn walk_body_exprs_visit_lhs<F>(body: &[Stmt], visit: &mut F)
where
    F: FnMut(&Expr),
{
    for stmt in body.iter() {
        walk_stmt_exprs_visit_lhs(stmt, visit);
    }
}

/// Single-Stmt mutable walker that visits both `Assignment::lhs` and `rhs`.
/// Companion of [`walk_body_exprs_mut_visit_lhs`]. Recurses via the
/// visit-lhs variants so nested Assignments inside Branch arms, Sequence
/// pins, Loop bodies, etc. also have their lhs visited.
pub(crate) fn walk_stmt_exprs_mut_visit_lhs<F>(stmt: &mut Stmt, visit: &mut F) -> Action
where
    F: FnMut(&mut Expr) -> Action,
{
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            if matches!(walk_expr_mut(lhs, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_expr_mut(rhs, visit)
        }
        Stmt::Call { func, args, .. } => {
            if matches!(walk_expr_mut(func, visit), Action::Stop) {
                return Action::Stop;
            }
            for arg in args.iter_mut() {
                if matches!(walk_expr_mut(arg, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Stmt::Return { value, .. } => match value {
            Some(inner) => walk_expr_mut(inner, visit),
            None => Action::Continue,
        },
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            if matches!(walk_expr_mut(cond, visit), Action::Stop) {
                return Action::Stop;
            }
            if matches!(
                walk_body_exprs_mut_visit_lhs(then_body, visit),
                Action::Stop
            ) {
                return Action::Stop;
            }
            walk_body_exprs_mut_visit_lhs(else_body, visit)
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter_mut() {
                if matches!(walk_body_exprs_mut_visit_lhs(pin_body, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            Action::Continue
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            ..
        } => {
            if let LoopKind::ForC { init, increment } = kind {
                if matches!(walk_body_exprs_mut_visit_lhs(init, visit), Action::Stop) {
                    return Action::Stop;
                }
                if matches!(
                    walk_body_exprs_mut_visit_lhs(increment, visit),
                    Action::Stop
                ) {
                    return Action::Stop;
                }
            }
            if let LoopKind::ForEach { array, .. } = kind {
                if matches!(walk_expr_mut(array, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if let Some(cond_expr) = cond {
                if matches!(walk_expr_mut(cond_expr, visit), Action::Stop) {
                    return Action::Stop;
                }
            }
            if matches!(walk_body_exprs_mut_visit_lhs(body, visit), Action::Stop) {
                return Action::Stop;
            }
            if let Some(comp) = completion {
                return walk_body_exprs_mut_visit_lhs(comp, visit);
            }
            Action::Continue
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            if matches!(walk_expr_mut(expr, visit), Action::Stop) {
                return Action::Stop;
            }
            for case in cases.iter_mut() {
                for value in case.values.iter_mut() {
                    if matches!(walk_expr_mut(value, visit), Action::Stop) {
                        return Action::Stop;
                    }
                }
                if matches!(
                    walk_body_exprs_mut_visit_lhs(&mut case.body, visit),
                    Action::Stop
                ) {
                    return Action::Stop;
                }
            }
            if let Some(default_body) = default {
                return walk_body_exprs_mut_visit_lhs(default_body, visit);
            }
            Action::Continue
        }
        Stmt::Latch { init, body, .. } => {
            if matches!(walk_body_exprs_mut_visit_lhs(init, visit), Action::Stop) {
                return Action::Stop;
            }
            walk_body_exprs_mut_visit_lhs(body, visit)
        }
        Stmt::Break { .. } | Stmt::EventCall { .. } | Stmt::Unknown { .. } => Action::Continue,
    }
}

/// Read-only single-Stmt walker that visits both `Assignment::lhs` and `rhs`.
/// Companion of [`walk_body_exprs_visit_lhs`].
pub(crate) fn walk_stmt_exprs_visit_lhs<F>(stmt: &Stmt, visit: &mut F)
where
    F: FnMut(&Expr),
{
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            walk_expr(lhs, visit);
            walk_expr(rhs, visit);
        }
        Stmt::Call { func, args, .. } => {
            walk_expr(func, visit);
            for arg in args.iter() {
                walk_expr(arg, visit);
            }
        }
        Stmt::Return { value, .. } => {
            if let Some(inner) = value {
                walk_expr(inner, visit);
            }
        }
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            walk_expr(cond, visit);
            walk_body_exprs_visit_lhs(then_body, visit);
            walk_body_exprs_visit_lhs(else_body, visit);
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter() {
                walk_body_exprs_visit_lhs(pin_body, visit);
            }
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            ..
        } => {
            if let LoopKind::ForC { init, increment } = kind {
                walk_body_exprs_visit_lhs(init, visit);
                walk_body_exprs_visit_lhs(increment, visit);
            }
            if let LoopKind::ForEach { array, .. } = kind {
                walk_expr(array, visit);
            }
            if let Some(cond_expr) = cond {
                walk_expr(cond_expr, visit);
            }
            walk_body_exprs_visit_lhs(body, visit);
            if let Some(comp) = completion {
                walk_body_exprs_visit_lhs(comp, visit);
            }
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            walk_expr(expr, visit);
            for case in cases.iter() {
                for value in case.values.iter() {
                    walk_expr(value, visit);
                }
                walk_body_exprs_visit_lhs(&case.body, visit);
            }
            if let Some(default_body) = default {
                walk_body_exprs_visit_lhs(default_body, visit);
            }
        }
        Stmt::Latch { init, body, .. } => {
            walk_body_exprs_visit_lhs(init, visit);
            walk_body_exprs_visit_lhs(body, visit);
        }
        Stmt::Break { .. } | Stmt::EventCall { .. } | Stmt::Unknown { .. } => {}
    }
}

/// Read-only single-Expr walker. Pre-order, every Expr variant. No
/// early termination.
pub(crate) fn walk_expr<F>(expr: &Expr, visit: &mut F)
where
    F: FnMut(&Expr),
{
    visit(expr);
    walk_expr_children(expr, visit);
}

/// Walk only the immediate children of `expr` with the full [`walk_expr`]
/// (so each child subtree is visited pre-order), skipping a visit of
/// `expr` itself. This holds the single exhaustive `Expr` arm list for the
/// read-only direction; `walk_expr` is the visit-root-then-children wrapper
/// over it. Used directly when the root is a definition site (e.g. an
/// `Assignment::lhs`) whose sub-expressions are still reads that should be
/// walked.
pub(crate) fn walk_expr_children<F>(expr: &Expr, visit: &mut F)
where
    F: FnMut(&Expr),
{
    match expr {
        Expr::Literal(_) | Expr::Var(_) | Expr::Unknown { .. } => {}
        Expr::Call { args, .. } => {
            for arg in args.iter() {
                walk_expr(arg, visit);
            }
        }
        Expr::MethodCall { recv, args, .. } => {
            walk_expr(recv, visit);
            for arg in args.iter() {
                walk_expr(arg, visit);
            }
        }
        Expr::FieldAccess { recv, .. } => walk_expr(recv, visit),
        Expr::Index { recv, idx } => {
            walk_expr(recv, visit);
            walk_expr(idx, visit);
        }
        Expr::Binary { lhs, rhs, .. } => {
            walk_expr(lhs, visit);
            walk_expr(rhs, visit);
        }
        Expr::Unary { operand, .. } => walk_expr(operand, visit),
        Expr::Cast { inner, .. } => walk_expr(inner, visit),
        Expr::ArrayLit(items) => {
            for item in items.iter() {
                walk_expr(item, visit);
            }
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            walk_expr(cond, visit);
            walk_expr(then_expr, visit);
            walk_expr(else_expr, visit);
        }
        Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
            walk_expr(inner, visit)
        }
        Expr::Resume { inner, .. } => walk_expr(inner, visit),
        Expr::StructConstruct { fields, .. } => {
            for (_, value) in fields.iter() {
                walk_expr(value, visit);
            }
        }
        Expr::Switch {
            index,
            cases,
            default,
        } => {
            walk_expr(index, visit);
            for case in cases.iter() {
                walk_expr(&case.value, visit);
                walk_expr(&case.body, visit);
            }
            walk_expr(default, visit);
        }
    }
}

/// Search each slice in `scopes` (innermost-first) for the first top-level
/// `Stmt::Assignment { lhs: Var(name), rhs }` and return `&rhs`. Returns
/// `None` when no scope contains a matching definition.
fn find_top_level_var_assignment<'a>(scopes: &[&'a [Stmt]], name: &str) -> Option<&'a Expr> {
    for scope in scopes {
        let hit = scope.iter().find_map(|stmt| match stmt {
            Stmt::Assignment {
                lhs: Expr::Var(lhs_name),
                rhs,
                ..
            } if lhs_name == name => Some(rhs),
            _ => None,
        });
        if let Some(rhs) = hit {
            return Some(rhs);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{resolve_expr_chain, resolve_var_chain};
    use crate::bytecode::expr::{BinaryOp, Expr};
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign, call, lit, var};

    fn binary_add(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn scopes_of(body: &[Stmt]) -> Vec<&[Stmt]> {
        vec![body]
    }

    #[test]
    fn direct_hit_returns_rhs_expr() {
        let body = vec![
            assign("X", binary_add(var("a"), lit("1"))),
            call("Other", vec![]),
        ];
        let scopes = scopes_of(&body);
        let resolved = resolve_var_chain(&scopes, "X").expect("direct hit");
        assert!(matches!(
            resolved,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn single_hop_follows_temp_alias() {
        let body = vec![
            assign("X", var("Y")),
            assign("Y", binary_add(var("a"), lit("1"))),
        ];
        let scopes = scopes_of(&body);
        let resolved = resolve_var_chain(&scopes, "X").expect("single hop");
        assert!(matches!(
            resolved,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn multi_hop_walks_to_terminal_call() {
        let body = vec![
            assign("X", var("Y")),
            assign("Y", var("Z")),
            assign(
                "Z",
                Expr::Call {
                    name: "Compute".to_string(),
                    args: vec![var("a")],
                },
            ),
        ];
        let scopes = scopes_of(&body);
        let resolved = resolve_var_chain(&scopes, "X").expect("multi hop");
        match resolved {
            Expr::Call { name, .. } => assert_eq!(name, "Compute"),
            other => panic!("expected Expr::Call, got {other:?}"),
        }
    }

    #[test]
    fn missing_name_returns_none() {
        let body = vec![assign("X", lit("1"))];
        let scopes = scopes_of(&body);
        assert!(resolve_var_chain(&scopes, "Y").is_none());
    }

    #[test]
    fn cycle_is_detected_without_infinite_loop() {
        let body = vec![assign("X", var("Y")), assign("Y", var("X"))];
        let scopes = scopes_of(&body);
        assert!(resolve_var_chain(&scopes, "X").is_none());
    }

    #[test]
    fn first_assignment_wins_when_name_repeats() {
        let body = vec![assign("X", lit("first")), assign("X", lit("second"))];
        let scopes = scopes_of(&body);
        let resolved = resolve_var_chain(&scopes, "X").expect("first wins");
        match resolved {
            Expr::Literal(text) => assert_eq!(text, "first"),
            other => panic!("expected first literal, got {other:?}"),
        }
    }

    #[test]
    fn nested_sub_body_assignments_are_not_consulted() {
        // Assignment to X is inside a Branch arm, not at top level.
        let body = vec![Stmt::Branch {
            cond: lit("true"),
            then_body: vec![assign("X", lit("hidden"))],
            else_body: vec![],
            offset: 0,
        }];
        let scopes = scopes_of(&body);
        assert!(resolve_var_chain(&scopes, "X").is_none());
    }

    #[test]
    fn outer_scope_resolves_when_inner_scope_misses() {
        // Inner scope has no def for X. Outer scope (next slice) does.
        let outer = vec![assign("X", binary_add(var("a"), lit("1")))];
        let inner: Vec<Stmt> = vec![call("Inner", vec![])];
        let scopes: Vec<&[Stmt]> = vec![&inner, &outer];
        let resolved = resolve_var_chain(&scopes, "X").expect("outer scope hit");
        assert!(matches!(
            resolved,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn inner_scope_shadows_outer_when_both_define() {
        // Both scopes define X. Inner scope wins.
        let outer = vec![assign("X", lit("outer"))];
        let inner = vec![assign("X", lit("inner"))];
        let scopes: Vec<&[Stmt]> = vec![&inner, &outer];
        let resolved = resolve_var_chain(&scopes, "X").expect("inner wins");
        match resolved {
            Expr::Literal(text) => assert_eq!(text, "inner"),
            other => panic!("expected inner literal, got {other:?}"),
        }
    }

    #[test]
    fn chain_hops_across_scopes() {
        // X = $Y in inner scope, $Y = Add(a, 1) in outer scope.
        // The chain walk follows X -> $Y; resolution of $Y must search
        // the full scope stack and find it in the outer scope.
        let outer = vec![assign("$Y", binary_add(var("a"), lit("1")))];
        let inner = vec![assign("X", var("$Y"))];
        let scopes: Vec<&[Stmt]> = vec![&inner, &outer];
        let resolved = resolve_var_chain(&scopes, "X").expect("chain across scopes");
        assert!(matches!(
            resolved,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
    }

    /// `resolve_expr_chain` walks Var sub-expressions inside structural
    /// shapes. A two-level chain inside an `Add` exposes both inner Vars'
    /// terminal definitions in one call.
    #[test]
    fn deep_resolve_expands_inner_vars() {
        // Add(Var("X"), Var("$Y")), with X = lit("3"), $Y = lit("4").
        let body = vec![assign("X", lit("3")), assign("$Y", lit("4"))];
        let scopes: Vec<&[Stmt]> = vec![&body];
        let input = binary_add(var("X"), var("$Y"));
        let resolved = resolve_expr_chain(&input, &scopes);
        let Expr::Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
        } = resolved
        else {
            panic!("expected Binary Add");
        };
        assert!(matches!(*lhs, Expr::Literal(ref text) if text == "3"));
        assert!(matches!(*rhs, Expr::Literal(ref text) if text == "4"));
    }

    /// `resolve_expr_chain` follows a multi-hop chain inside a
    /// sub-expression. `Add(Var("X"), Var("Y"))`, X = $Z, $Z = lit("5").
    /// Result: `Add(Literal("5"), Var("Y"))` because Y dead-ends.
    #[test]
    fn deep_resolve_walks_var_chain_then_continues() {
        let body = vec![assign("X", var("$Z")), assign("$Z", lit("5"))];
        let scopes: Vec<&[Stmt]> = vec![&body];
        let input = binary_add(var("X"), var("Y"));
        let resolved = resolve_expr_chain(&input, &scopes);
        let Expr::Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
        } = resolved
        else {
            panic!("expected Binary Add");
        };
        assert!(matches!(*lhs, Expr::Literal(ref text) if text == "5"));
        assert!(matches!(*rhs, Expr::Var(ref name) if name == "Y"));
    }

    /// Cycle guard: `X = $Y; $Y = X` should not loop forever. The cycle
    /// detection drops the recursion when a name is already on the stack
    /// and leaves the bare Var in place.
    #[test]
    fn deep_resolve_cycle_terminates() {
        let body = vec![assign("X", var("$Y")), assign("$Y", var("X"))];
        let scopes: Vec<&[Stmt]> = vec![&body];
        let resolved = resolve_expr_chain(&var("X"), &scopes);
        // Cycle detected; the walk leaves a Var in place rather than looping.
        assert!(matches!(resolved, Expr::Var(_)));
    }
}
