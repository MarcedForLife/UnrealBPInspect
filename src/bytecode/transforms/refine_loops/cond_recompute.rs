use super::{lhs_var_name, stmt_assignment_lhs_name};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{
    scope_stack, walk_expr, walk_stmt_exprs, walk_stmt_exprs_mut, Action,
};

/// Strip the trailing run of cond-recomputation statements from `body`.
///
/// Blueprint emits a tail-of-iteration cond recomputation at the end of every
/// Loop body so the back-edge `JumpIfNot` reads a fresh value. The canonical
/// (un-inlined) shape is:
///
/// ```text
/// function body:
///   $cond = Lt(counter, Array_Length(arr))      <-- canonical cond def (ancestor scope)
///   Loop[While]
///     cond: Var($cond)
///     body:
///       ... user code ...
///       counter = counter + 1                    <-- counter increment
///       $cond = Lt(counter, Array_Length(arr))   <-- TAIL recomputation
/// ```
///
/// The recomputation has no editor-graph counterpart; the user sees a single
/// `for (item in arr)` node with no explicit recomputation. Discarding it
/// matches the pre-cutover effective behaviour (where the inliner collapsed
/// the recomputation into the cond before refine_loops saw the body).
///
/// Identification rule: a trailing stmt `$X = <rhs>` is a cond-recomputation
/// iff
///
/// 1. `$X` is a name reachable from the loop cond either directly (the cond
///    chain walks through `$X`) or indirectly (a chain-terminal expression
///    references `$X` as a sub-expression temp), AND
/// 2. `<rhs>` structurally equals the CANONICAL definition of `$X`, the
///    `rhs` recorded in `name_canonical_rhs`. Canonical = first matching
///    top-level assignment encountered when walking `scopes` innermost-first;
///    Blueprint emits the head and tail recomputations with byte-identical
///    bytecode, so canonical equality is a direct `Expr` `==`.
///
/// Both gates must hold; the second protects against false-firing on
/// one-shot trailing stmts (notably the counter increment, where the rhs
/// differs from the canonical Lt def).
pub(crate) fn strip_trailing_cond_recomputation(
    body: &mut Vec<Stmt>,
    cond: &Expr,
    ancestors: &[&[Stmt]],
) {
    loop {
        if body.is_empty() {
            break;
        }
        // Resolve the cond chain against the body MINUS its trailing stmt
        // plus the ancestors. Excluding the candidate from the canonical
        // lookup makes the rule self-consistent: the trailing stmt counts as
        // a recomputation only when an EARLIER scope (body head or an
        // ancestor) already defines the same name with the same rhs. A
        // one-shot tail assignment whose canonical lookup would resolve to
        // itself simply produces no entry, so the strip can't fire on it.
        let head_len = body.len() - 1;
        let head_slice: &[Stmt] = &body[..head_len];
        let scopes = scope_stack(head_slice, ancestors);
        let recomp = collect_cond_recomputation_defs(cond, &scopes);
        if recomp.is_empty() {
            break;
        }
        let stmt = &body[head_len];
        let Stmt::Assignment { lhs, rhs, .. } = stmt else {
            break;
        };
        let Some(lhs_name) = lhs_var_name(lhs) else {
            break;
        };
        let canonical = match recomp.iter().find(|(name, _)| name == lhs_name) {
            Some((_, def_rhs)) => def_rhs,
            None => break,
        };
        if rhs != canonical {
            break;
        }
        body.pop();
    }
}

/// Build the `(name, canonical_rhs)` table covering every name reachable from
/// the loop cond. Reachability covers two paths:
///
/// 1. The chain walk: each `Var(X)` resolves to its canonical rhs via the
///    scope stack, and if that rhs is itself `Var(Y)` the walk continues at
///    `Y`. Each visited name is added with its canonical rhs.
/// 2. Sub-expression temps: once the chain reaches a non-Var terminal, every
///    free `Var(Z)` inside the terminal whose canonical rhs is also defined
///    in scopes is added to the table (transitively, so a chain hop hidden
///    behind a sub-expression still gets covered).
///
/// Canonical lookups walk `scopes` innermost-first, first match wins. A name
/// with no canonical def in any scope is dropped from the table.
fn collect_cond_recomputation_defs(cond: &Expr, scopes: &[&[Stmt]]) -> Vec<(String, Expr)> {
    let mut visited: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut entries: Vec<(String, Expr)> = Vec::new();
    let mut frontier: Vec<String> = Vec::new();

    if let Expr::Var(name) = cond {
        frontier.push(name.clone());
    }

    // Walk the cond's chain. After the chain reaches a non-Var terminal, the
    // terminal's free vars feed the sub-expr exploration below.
    let mut chain_terminal: Option<Expr> = None;
    while let Some(name) = frontier.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(rhs) = canonical_rhs_for(scopes, &name) else {
            continue;
        };
        entries.push((name.clone(), rhs.clone()));
        match rhs {
            Expr::Var(next) => frontier.push(next.clone()),
            other => {
                if chain_terminal.is_none() {
                    chain_terminal = Some(other.clone());
                }
                let mut deeper: Vec<String> = Vec::new();
                collect_var_refs_in_expr(other, &mut deeper);
                frontier.extend(deeper);
            }
        }
    }

    // Cond is already structural (no Var-ref entry point): the terminal IS
    // the cond expression itself, walk its sub-expr temps.
    if chain_terminal.is_none() {
        let mut sub_refs: Vec<String> = Vec::new();
        collect_var_refs_in_expr(cond, &mut sub_refs);
        let mut sub_frontier: Vec<String> = sub_refs;
        while let Some(name) = sub_frontier.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            let Some(rhs) = canonical_rhs_for(scopes, &name) else {
                continue;
            };
            entries.push((name.clone(), rhs.clone()));
            let mut deeper: Vec<String> = Vec::new();
            collect_var_refs_in_expr(rhs, &mut deeper);
            sub_frontier.extend(deeper);
        }
    }
    entries
}

/// Look up the canonical rhs of `name`: the FIRST top-level
/// `Stmt::Assignment { lhs: Var(name), rhs }` in any scope, walking
/// `scopes` innermost-first. Mirrors the first-wins rule used by
/// `resolve_var_chain`.
fn canonical_rhs_for<'a>(scopes: &[&'a [Stmt]], name: &str) -> Option<&'a Expr> {
    scopes
        .iter()
        .find_map(|slice| body_top_level_assignment_rhs(slice, name))
}

/// Find the FIRST top-level `Stmt::Assignment { lhs: Var(name), rhs }` in
/// `body` and return `&rhs`.
fn body_top_level_assignment_rhs<'a>(body: &'a [Stmt], name: &str) -> Option<&'a Expr> {
    body.iter().find_map(|stmt| match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(lhs_name),
            rhs,
            ..
        } if lhs_name == name => Some(rhs),
        _ => None,
    })
}

/// Substitute body-local single-use temp definitions into the increment
/// statements, removing the def from body once substituted. Repeats until no
/// further substitution is possible. Each substitution clones the body def's
/// rhs into the increment, then removes the def. Multi-use temps (still
/// referenced elsewhere in body) are skipped to avoid dropping observable
/// uses.
pub(super) fn inline_body_temps_into_increment(increment: &mut [Stmt], body: &mut Vec<Stmt>) {
    // Bound the chain depth so a malformed cycle can't loop forever. Real
    // chains are 1-2 hops in practice.
    const MAX_HOPS: u32 = 16;
    for _ in 0..MAX_HOPS {
        let candidate = pick_substitution_candidate(increment, body);
        let Some(name) = candidate else {
            return;
        };
        let def_idx = match body
            .iter()
            .position(|stmt| stmt_assignment_lhs_name(stmt) == Some(name.as_str()))
        {
            Some(idx) => idx,
            None => return,
        };
        let rhs_clone = match &body[def_idx] {
            Stmt::Assignment { rhs, .. } => rhs.clone(),
            _ => return,
        };
        for stmt in increment.iter_mut() {
            substitute_var_in_stmt_local(stmt, &name, &rhs_clone);
        }
        body.remove(def_idx);
    }
}

/// Find a temp name referenced by `Var(name)` in `increment` that has a
/// matching body-local def AND no other uses in `body`. Only inline-candidate
/// names are considered. Returns the name to substitute; `None` when no safe
/// substitution exists.
fn pick_substitution_candidate(increment: &[Stmt], body: &[Stmt]) -> Option<String> {
    let mut referenced: Vec<String> = Vec::new();
    for stmt in increment {
        collect_var_refs_in_stmt(stmt, &mut referenced);
    }
    referenced.sort();
    referenced.dedup();
    for name in referenced {
        if !is_intermediate_temp_name(&name) {
            continue;
        }
        let def_present = body
            .iter()
            .any(|stmt| stmt_assignment_lhs_name(stmt) == Some(name.as_str()));
        if !def_present {
            continue;
        }
        // Count uses of `name` across body (def and non-def stmts). If the
        // def line is the only stmt mentioning the name, the body has no
        // remaining consumers, the original consumer was the increment use.
        let body_uses = count_body_var_uses(body, &name);
        if body_uses == 0 {
            return Some(name);
        }
    }
    None
}

/// Count occurrences of `Var(name)` as a use across `body`, including inside
/// nested sub-bodies. Assignment lhs positions count as defs and are skipped.
/// Used to decide whether substituting a temp is safe (zero remaining uses
/// means the only consumer was the just-extracted increment).
pub(super) fn count_body_var_uses(body: &[Stmt], name: &str) -> usize {
    let mut count = 0;
    for stmt in body {
        count += count_var_uses_in_stmt(stmt, name);
    }
    count
}

fn count_var_uses_in_stmt(stmt: &Stmt, name: &str) -> usize {
    let mut count = 0usize;
    walk_stmt_exprs(stmt, &mut |expr: &Expr| {
        if let Expr::Var(other) = expr {
            if other == name {
                count += 1;
            }
        }
    });
    count
}

/// Collect every `Var(name)` reference appearing inside `stmt` into `out`.
/// Assignment lhs positions are skipped (they are defs, not uses).
fn collect_var_refs_in_stmt(stmt: &Stmt, out: &mut Vec<String>) {
    walk_stmt_exprs(stmt, &mut |expr: &Expr| {
        if let Expr::Var(name) = expr {
            out.push(name.clone());
        }
    });
}

/// Expression-level counterpart of [`collect_var_refs_in_stmt`]. Used by the
/// recomputation-defs collector when walking a chain-terminal expression
/// outside a Stmt context.
pub(super) fn collect_var_refs_in_expr(expr: &Expr, out: &mut Vec<String>) {
    walk_expr(expr, &mut |inner: &Expr| {
        if let Expr::Var(name) = inner {
            out.push(name.clone());
        }
    });
}

/// Replace every `Var(name)` in `stmt` with a clone of `replacement`. Used by
/// the chain-substitution pass when inlining a body-local temp def into the
/// increment slot. Assignment lhs is skipped (def, not a use; substituting
/// there would corrupt the assignment shape).
fn substitute_var_in_stmt_local(stmt: &mut Stmt, name: &str, replacement: &Expr) {
    walk_stmt_exprs_mut(stmt, &mut |expr: &mut Expr| {
        if let Expr::Var(other) = expr {
            if other == name {
                *expr = replacement.clone();
            }
        }
        Action::Continue
    });
}

/// True for names that are intermediate compiler-generated temp aliases the
/// init-absorption scan should skip past, and the increment-slot chain
/// substitution should consider for inlining. Excludes the conventional
/// non-temp names so the scan halts on real variable assignments.
///
/// Mirrors the criteria the inliner uses (`is_inline_candidate_name` in
/// `expr_transforms`), kept local to avoid coupling.
pub(super) fn is_intermediate_temp_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    if matches!(name, "Self" | "None") {
        return false;
    }
    if name.contains('.') {
        return false;
    }
    if name.len() == 1 && name.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
        return false;
    }
    true
}
