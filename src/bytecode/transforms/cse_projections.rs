//! Common-subexpression hoisting for pure projections.
//!
//! Many Blueprint graphs duplicate the same pure-projection sub-expression
//! across several call sites that span multiple nested scopes. The motivating
//! shape is a ternary projection like
//! `(Temp_bool_Variable_1 ? self.LeftTarget : self.RightTarget)`
//! appearing once in a Branch cond and three more times inside that Branch's
//! then-body. After `inline_single_use_temps` has resolved the Blueprint
//! compiler's per-pin temporaries, those duplicates are visible at the IR
//! level and can be hoisted into a single synthetic `let` at the deepest
//! common ancestor (DCA) scope.
//!
//! The pass is deliberately conservative. Only structurally-pure variants
//! participate (Var, FieldAccess, Index, Ternary, Binary, Unary, Cast,
//! StructConstruct, Switch). Any expression containing a Call, MethodCall,
//! Out, Resume, Persistent, Interface, or Unknown anywhere in its tree is
//! skipped because hoisting could change observable side-effect ordering.
//! Bare `Var` is skipped because a single-name reference is already the
//! canonical "named slot".
//!
//! Naming uses a three-tier heuristic:
//! - Tier 1: Left/Right suffix on Ternary/Switch arms, e.g. `self.LeftHand`
//!   vs `self.RightHand` derives `$Hand`.
//! - Tier 2: trailing dot-component when the expression ends in a
//!   `FieldAccess`, e.g. `expr.SocketName` derives `$SocketName`.
//! - Tier 3: deterministic body-wide counter `$Cse_1`, `$Cse_2`, ...
//!
//! The threshold is hybrid: 2+ uses if a tier-1 or tier-2 name is derivable,
//! 3+ uses for the fallback `$Cse_N` form. Naming-collision with an existing
//! `Var` reference anywhere in the body falls back to `$Cse_N`.
//!
//! Algorithm: collect every eligible sub-expression's `(expr_key, scope_path)`
//! across the entire body, group by key, compute the deepest common ancestor
//! scope per group via the longest common scope_path prefix, and hoist at
//! that DCA. After each successful hoist the body is re-scanned because
//! the inserted Assignment changes the shape of any larger expression that
//! contained the just-hoisted sub-expression. A hard iteration cap
//! (`MAX_ITERATIONS`) bounds the walk so a pathological fixture cannot
//! infinite-loop.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit::{
    any_expr, descend_mut, descend_ref, for_each_sub_body, walk_expr, walk_expr_children,
    walk_expr_children_mut, walk_expr_mut, Action, ScopeSlot, ScopeStep,
};

/// Hard iteration cap for the cross-scope hoist fixpoint. Mirrors the
/// inliner's `MAX_INLINE_ITERATIONS`; in practice every observed fixture
/// converges in single-digit iterations, the cap is a safety net for
/// pathological inputs.
const MAX_ITERATIONS: usize = 64;

/// Threshold for hoisting when a tier-1 / tier-2 name is derivable. Two
/// uses with a clean derived name yield a clear readability win.
const HOIST_NAMED_THRESHOLD: usize = 2;

/// Threshold for hoisting under the `$Cse_N` fallback. Synthetic names are
/// less readable, so require at least three uses to justify the new line.
const HOIST_FALLBACK_THRESHOLD: usize = 3;

/// Cross-scope CSE entry point. Collects every eligible sub-expression in
/// the function/event body, groups by canonical key, and hoists each
/// qualifying group at its deepest common ancestor scope.
///
/// Iterates to a fixpoint or `MAX_ITERATIONS`, whichever comes first. Each
/// iteration may hoist at most one group, after which the body is
/// re-collected so subsequent iterations observe the post-substitution
/// shape (e.g. an outer `(cond ? L : R).Field` whose key changes once the
/// inner `(cond ? L : R)` is hoisted to a Var).
pub fn hoist_repeated_projections(body: &mut Vec<Stmt>) {
    let mut cse_counter: usize = 0;
    let mut hoisted_names: BTreeSet<String> = BTreeSet::new();
    let mut rejected_keys: BTreeSet<String> = BTreeSet::new();

    for _ in 0..MAX_ITERATIONS {
        let groups = collect_groups(body);
        let existing_names = collect_var_names_deep(body);

        let next = pick_next_hoist(&groups, &rejected_keys);
        let Some(group) = next else {
            return;
        };

        let derivable_name = derive_name(&group.sample);
        let chosen_name = pick_name(
            derivable_name,
            &existing_names,
            &hoisted_names,
            &mut cse_counter,
        );

        if !apply_hoist(body, group, &chosen_name) {
            rejected_keys.insert(group.key.clone());
            continue;
        }
        hoisted_names.insert(chosen_name);
    }
}

/// Pick the next group to hoist. Returns `None` when no group meets its
/// threshold, indicating the fixpoint has converged.
fn pick_next_hoist<'groups>(
    groups: &'groups [Group],
    rejected: &BTreeSet<String>,
) -> Option<&'groups Group> {
    groups.iter().find(|group| {
        if rejected.contains(&group.key) {
            return false;
        }
        let needs = if derive_name(&group.sample).is_some() {
            HOIST_NAMED_THRESHOLD
        } else {
            HOIST_FALLBACK_THRESHOLD
        };
        group.uses.len() >= needs
    })
}

/// One CSE candidate group across the whole body.
struct Group {
    /// Canonical structural-equality key (serde JSON serialisation).
    key: String,
    /// Every recorded use site of the expression, in document order.
    uses: Vec<UseLocation>,
    /// One representative copy of the matching expression.
    sample: Expr,
}

/// Where a single use of a candidate expression lives.
#[derive(Clone)]
struct UseLocation {
    /// Path from the root body down to the scope containing this use.
    /// Empty path means the use is in the root scope itself.
    scope_path: Vec<ScopeStep>,
}

/// Walk the entire body and tally every eligible sub-expression's uses
/// across all nested scopes. The returned `Vec` is ordered by canonical
/// JSON key so iteration is deterministic.
///
/// Skips Assignment::rhs occurrences whose lhs is a `Var(name)` that has
/// multiple defs in the body. Those Assignments are Blueprint-compiler
/// temp-slot reuse (`$Add_IntInt = ...; ...; $Add_IntInt = ...`), where
/// substituting the rhs creates a `$X = $Cse_N` chain artifact that the
/// post-CSE inliner cannot collapse (the slot's reuse blocks single-use
/// inlining). True uses of those slots at downstream read sites still
/// count, so a hoist that has 2+ true uses still fires.
fn collect_groups(body: &[Stmt]) -> Vec<Group> {
    let multi_def_names = collect_multi_def_var_names(body);
    let mut buckets: BTreeMap<String, (Expr, Vec<UseLocation>)> = BTreeMap::new();
    collect_in_body(body, &[], &multi_def_names, &mut buckets);
    buckets
        .into_iter()
        .map(|(key, (sample, uses))| Group { key, uses, sample })
        .collect()
}

/// Set of `Var(name)` names appearing as Assignment lhs more than once
/// in the body (including nested sub-bodies). These are Blueprint-temp
/// slots reused across the function, whose defining Assignment's rhs
/// must NOT be a counted CSE use site, otherwise substitution creates a
/// chain alias the inliner cannot collapse.
fn collect_multi_def_var_names(body: &[Stmt]) -> BTreeSet<String> {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    count_var_lhs_in_body(body, &mut counts);
    counts
        .into_iter()
        .filter_map(|(name, count)| if count > 1 { Some(name) } else { None })
        .collect()
}

fn count_var_lhs_in_body(body: &[Stmt], counts: &mut BTreeMap<String, usize>) {
    for stmt in body.iter() {
        if let Stmt::Assignment { lhs, .. } = stmt {
            if let Some(name) = assignment_var_lhs_name(lhs) {
                *counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
        for_each_sub_body(stmt, |_slot, sub_body| {
            count_var_lhs_in_body(sub_body, counts);
        });
    }
}

/// Extract the underlying var name from an Assignment lhs that is either
/// a bare `Var(name)` or an out-parameter `Out(Var(name))`. The Out
/// wrapper is the ABI marker preserved through the pipeline; for CSE
/// multi-def accounting an `out X = ...` write is semantically the same
/// as a bare `X = ...` write at this scope.
fn assignment_var_lhs_name(lhs: &Expr) -> Option<&str> {
    match lhs {
        Expr::Var(name) => Some(name.as_str()),
        Expr::Out(inner) => match inner.as_ref() {
            Expr::Var(name) => Some(name.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Recursive worker for `collect_groups`. Visits each statement's own
/// scope-root expressions (statement-level operands) and recurses into
/// every owned sub-body with the matching `ScopeStep` appended.
///
/// `multi_def_names` is the BP-temp-slot-reuse exclusion set documented
/// on `collect_groups`. Assignment::rhs of a multi-def Var lhs is skipped
/// from counting.
///
/// Assignment::lhs is a definition position, not a use. The root lhs
/// expression itself is excluded from counting (otherwise two arms that
/// each write `self.foo.bar` would form a 2-use group that hoists the
/// projection to a temp and erases the original writes). Sub-expressions
/// inside compound lhs shapes (e.g. `FieldAccess { recv: Ternary {..} }`)
/// are still walked, since their `recv` positions are reads that should
/// participate in CSE.
fn collect_in_body(
    body: &[Stmt],
    parent_path: &[ScopeStep],
    multi_def_names: &BTreeSet<String>,
    buckets: &mut BTreeMap<String, (Expr, Vec<UseLocation>)>,
) {
    for (stmt_idx, stmt) in body.iter().enumerate() {
        let skip_rhs = match stmt {
            Stmt::Assignment { lhs, .. } => {
                assignment_var_lhs_name(lhs).is_some_and(|name| multi_def_names.contains(name))
            }
            _ => false,
        };
        for (expr, role) in scope_root_exprs_tagged(stmt) {
            // Skip the rhs slot of a multi-def-Var Assignment: counting
            // it produces chain artifacts post-substitution.
            if skip_rhs && matches!(role, ExprRole::AssignmentRhs) {
                continue;
            }
            let mut visit = |node: &Expr| {
                if !is_eligible(node) {
                    return;
                }
                let Ok(key) = serde_json::to_string(node) else {
                    return;
                };
                let entry = buckets
                    .entry(key)
                    .or_insert_with(|| (node.clone(), Vec::new()));
                entry.1.push(UseLocation {
                    scope_path: parent_path.to_vec(),
                });
            };
            if matches!(role, ExprRole::AssignmentLhs) {
                // Lhs root is a def, not a use. Walk only its sub-expressions
                // so nested projections (e.g. recv in `<projection>.Field`)
                // still participate.
                walk_expr_children(expr, &mut visit);
            } else {
                walk_expr(expr, &mut visit);
            }
        }
        for_each_sub_body(stmt, |slot, sub_body| {
            let mut child_path = parent_path.to_vec();
            child_path.push(ScopeStep { stmt_idx, slot });
            collect_in_body(sub_body, &child_path, multi_def_names, buckets);
        });
    }
}

/// Role tag a scope-root expression plays inside its owning statement.
/// Lets the collector and substituter distinguish Assignment lhs (a
/// definition site) from rhs (a use site) without re-matching on `Stmt`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprRole {
    AssignmentLhs,
    AssignmentRhs,
    Other,
}

/// Top-level expressions a single statement contributes to its OWN scope.
/// Returns the expressions that belong to this statement itself, excluding
/// every Vec<Stmt> sub-body (those are nested scopes).
///
/// Branch::cond, Loop::cond, Switch::expr, and ForEach's array expression
/// are part of the enclosing scope because they execute before any nested
/// body. Switch case-value expressions are also single-evaluation and
/// belong to the enclosing scope.
///
/// Assignment lhs is included because compound lhs shapes
/// (`FieldAccess { recv: <projection>, .. }`, `Index { recv: <projection>, .. }`)
/// host pure projections at their `recv` position, and those projections
/// must participate in CSE counting and substitution. Bare `Var` lhs is
/// not matched anyway because bare `Var` is not eligible for hoisting.
fn scope_root_exprs(stmt: &Stmt) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        Stmt::Call { func, args, .. } => {
            out.push(func);
            out.extend(args.iter());
        }
        Stmt::Return { value, .. } => {
            if let Some(expr) = value {
                out.push(expr);
            }
        }
        Stmt::Branch { cond, .. } => out.push(cond),
        Stmt::Loop { kind, cond, .. } => {
            if let Some(cond_expr) = cond {
                out.push(cond_expr);
            }
            if let LoopKind::ForEach { array, .. } = kind {
                out.push(array);
            }
        }
        Stmt::Switch { expr, cases, .. } => {
            out.push(expr);
            for case in cases.iter() {
                out.extend(case.values.iter());
            }
        }
        Stmt::Sequence { .. }
        | Stmt::Latch { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
    out
}

/// Like [`scope_root_exprs`] but tags each entry with the [`ExprRole`] it
/// plays in its owning statement. Lets callers distinguish Assignment lhs
/// (a def, walked excluding the root) from rhs (a use, walked normally).
fn scope_root_exprs_tagged(stmt: &Stmt) -> Vec<(&Expr, ExprRole)> {
    let mut out: Vec<(&Expr, ExprRole)> = Vec::new();
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            out.push((lhs, ExprRole::AssignmentLhs));
            out.push((rhs, ExprRole::AssignmentRhs));
        }
        Stmt::Call { func, args, .. } => {
            out.push((func, ExprRole::Other));
            for arg in args.iter() {
                out.push((arg, ExprRole::Other));
            }
        }
        Stmt::Return { value, .. } => {
            if let Some(expr) = value {
                out.push((expr, ExprRole::Other));
            }
        }
        Stmt::Branch { cond, .. } => out.push((cond, ExprRole::Other)),
        Stmt::Loop { kind, cond, .. } => {
            if let Some(cond_expr) = cond {
                out.push((cond_expr, ExprRole::Other));
            }
            if let LoopKind::ForEach { array, .. } = kind {
                out.push((array, ExprRole::Other));
            }
        }
        Stmt::Switch { expr, cases, .. } => {
            out.push((expr, ExprRole::Other));
            for case in cases.iter() {
                for value in case.values.iter() {
                    out.push((value, ExprRole::Other));
                }
            }
        }
        Stmt::Sequence { .. }
        | Stmt::Latch { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
    out
}

/// Mutable counterpart of [`scope_root_exprs_tagged`].
fn scope_root_exprs_tagged_mut(stmt: &mut Stmt) -> Vec<(&mut Expr, ExprRole)> {
    let mut out: Vec<(&mut Expr, ExprRole)> = Vec::new();
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            out.push((lhs, ExprRole::AssignmentLhs));
            out.push((rhs, ExprRole::AssignmentRhs));
        }
        Stmt::Call { func, args, .. } => {
            out.push((func, ExprRole::Other));
            for arg in args.iter_mut() {
                out.push((arg, ExprRole::Other));
            }
        }
        Stmt::Return { value, .. } => {
            if let Some(expr) = value {
                out.push((expr, ExprRole::Other));
            }
        }
        Stmt::Branch { cond, .. } => out.push((cond, ExprRole::Other)),
        Stmt::Loop { kind, cond, .. } => {
            if let Some(cond_expr) = cond {
                out.push((cond_expr, ExprRole::Other));
            }
            if let LoopKind::ForEach { array, .. } = kind {
                out.push((array, ExprRole::Other));
            }
        }
        Stmt::Switch { expr, cases, .. } => {
            out.push((expr, ExprRole::Other));
            for case in cases.iter_mut() {
                for value in case.values.iter_mut() {
                    out.push((value, ExprRole::Other));
                }
            }
        }
        Stmt::Sequence { .. }
        | Stmt::Latch { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
    out
}

/// True if `expr` is in the CSE allowlist (variant) AND its tree contains
/// no disallowed variant. Bare `Var(_)` is rejected because hoisting it is
/// dead, the value is already a single-token reference.
fn is_eligible(expr: &Expr) -> bool {
    if matches!(expr, Expr::Var(_)) {
        return false;
    }
    let allowlisted = matches!(
        expr,
        Expr::FieldAccess { .. }
            | Expr::Index { .. }
            | Expr::Ternary { .. }
            | Expr::Binary { .. }
            | Expr::Unary { .. }
            | Expr::Cast { .. }
            | Expr::StructConstruct { .. }
            | Expr::Switch { .. }
    );
    if !allowlisted {
        return false;
    }
    !contains_disallowed(expr)
}

/// True if any node in `expr`'s tree is a disallowed variant. Disallowed:
/// Call, MethodCall, Out, Resume, Persistent, Interface, Unknown. `Literal`
/// and `ArrayLit` are inert leaves and may appear inside an allowlisted
/// host (e.g. `Binary { lhs: Var, rhs: Literal }` is fine).
fn contains_disallowed(expr: &Expr) -> bool {
    any_expr(expr, &mut |node| {
        matches!(
            node,
            Expr::Call { .. }
                | Expr::MethodCall { .. }
                | Expr::Out(_)
                | Expr::Resume { .. }
                | Expr::Persistent(_)
                | Expr::Interface(_)
                | Expr::Unknown { .. }
        )
    })
}

/// Three-tier name derivation. Returns `None` when no clean name can be
/// derived (caller falls back to `$Cse_N`).
fn derive_name(expr: &Expr) -> Option<String> {
    if let Some(name) = derive_left_right_name(expr) {
        return Some(name);
    }
    derive_trailing_field_name(expr)
}

/// Tier 1: detect a Left/Right paired-arm projection and return the common
/// suffix as the derived name. Applies to `Ternary` and `Switch` shapes.
fn derive_left_right_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Ternary {
            then_expr,
            else_expr,
            ..
        } => left_right_suffix(field_chain_tail(then_expr)?, field_chain_tail(else_expr)?),
        Expr::Switch { cases, .. } if cases.len() >= 2 => {
            // Take the first two case bodies as representatives. Real
            // Blueprint Left/Right switches are 2-case (bool-coded) or
            // 2-case-plus-default; checking the first pair covers both.
            let first = field_chain_tail(&cases[0].body)?;
            let second = field_chain_tail(&cases[1].body)?;
            left_right_suffix(first, second)
        }
        _ => None,
    }
}

/// Trailing identifier of a `FieldAccess` / `Var` chain. For
/// `self.TargetActor` returns `TargetActor`. For
/// `expr.Foo.Bar` returns `Bar`. Returns `None` for non-projection arms.
fn field_chain_tail(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::FieldAccess { field, .. } => Some(field.as_str()),
        Expr::Var(name) => {
            if let Some(suffix) = name.strip_prefix("self.") {
                Some(suffix)
            } else {
                Some(name.as_str())
            }
        }
        _ => None,
    }
}

/// Match `Left<X>` against `Right<X>` (or vice-versa) and return `<X>`
/// when the suffixes are equal and form a valid identifier.
fn left_right_suffix(first: &str, second: &str) -> Option<String> {
    let suffix = match (first.strip_prefix("Left"), second.strip_prefix("Right")) {
        (Some(left_tail), Some(right_tail)) if left_tail == right_tail => left_tail,
        _ => match (first.strip_prefix("Right"), second.strip_prefix("Left")) {
            (Some(right_tail), Some(left_tail)) if right_tail == left_tail => right_tail,
            _ => return None,
        },
    };
    if suffix.is_empty() || !is_valid_identifier(suffix) {
        return None;
    }
    Some(suffix.to_string())
}

/// Tier 2: trailing dot-component on a `FieldAccess` chain.
fn derive_trailing_field_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::FieldAccess { field, .. } if is_valid_identifier(field) => Some(field.clone()),
        _ => None,
    }
}

/// True if `text` is a non-empty identifier (alphanumeric or `_`,
/// no leading digit).
fn is_valid_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    // Empty string has no first char; treat as not-an-identifier.
    let Some(first) = chars.next() else {
        return false;
    };
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

/// Pick the final name for a hoist. Prefers the derived tier-1/2 name
/// when one was found AND it does not collide with an existing `Var`
/// anywhere in the body or a name we've already hoisted. Falls back to
/// `$Cse_N` otherwise.
fn pick_name(
    derived: Option<String>,
    existing: &BTreeSet<String>,
    hoisted: &BTreeSet<String>,
    counter: &mut usize,
) -> String {
    if let Some(base) = derived {
        let candidate = format!("${}", base);
        if !existing.contains(&base)
            && !existing.contains(&candidate)
            && !hoisted.contains(&candidate)
        {
            return candidate;
        }
    }
    next_cse_name(existing, hoisted, counter)
}

/// Allocate the next `$Cse_N` name that does not collide with an existing
/// `Var` reference or a previously-hoisted synthetic.
fn next_cse_name(
    existing: &BTreeSet<String>,
    hoisted: &BTreeSet<String>,
    counter: &mut usize,
) -> String {
    loop {
        *counter += 1;
        let candidate = format!("$Cse_{}", counter);
        if !existing.contains(&candidate) && !hoisted.contains(&candidate) {
            return candidate;
        }
    }
}

/// Collect every `Var(name)` reference reachable from any statement in
/// `body`, including nested sub-bodies. Used as the global collision set
/// for the naming heuristic (CSE hoist naming and ForEach item naming).
pub(crate) fn collect_var_names_deep(body: &[Stmt]) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = BTreeSet::new();
    collect_var_names_in_body(body, &mut names);
    names
}

fn collect_var_names_in_body(body: &[Stmt], names: &mut BTreeSet<String>) {
    for stmt in body.iter() {
        for expr in scope_root_exprs(stmt) {
            walk_expr(expr, &mut |node| {
                if let Expr::Var(name) = node {
                    names.insert(name.clone());
                }
            });
        }
        for_each_sub_body(stmt, |_slot, sub_body| {
            collect_var_names_in_body(sub_body, names);
        });
    }
}

/// Apply one hoist: insert the synthetic Assignment at the deepest common
/// ancestor scope and substitute every match in that scope's subtree.
/// Returns `false` when the DCA descent failed (defensive, shouldn't
/// happen with well-formed scope_paths).
fn apply_hoist(body: &mut Vec<Stmt>, group: &Group, chosen_name: &str) -> bool {
    let dca_path = longest_common_prefix(&group.uses);
    let multi_def_names = collect_multi_def_var_names(body);

    // First-use offset: the offset of whichever stmt holds the earliest
    // occurrence after descending to the DCA scope.
    let first_use_offset = first_use_offset_at(body, &dca_path, &group.key).unwrap_or(0);

    let synthetic = Stmt::Assignment {
        lhs: Expr::Var(chosen_name.to_string()),
        rhs: group.sample.clone(),
        offset: first_use_offset,
    };

    let Some(dca_body) = descend_mut(body, &dca_path) else {
        return false;
    };
    let Some(insert_idx) = first_use_idx_in_scope(dca_body, &group.key) else {
        return false;
    };
    dca_body.insert(insert_idx, synthetic);

    // Substitute deep across the DCA subtree, but skip the freshly-inserted
    // Assignment itself; otherwise its rhs (the canonical expression) would
    // collapse to `Var(chosen_name)` referencing its own def. Also skip
    // multi-def-Var Assignment rhs slots, which represent BP-temp-slot
    // reuse (collection symmetry, see `collect_groups`).
    substitute_after_index(
        dca_body,
        insert_idx,
        &group.key,
        chosen_name,
        &multi_def_names,
    );
    true
}

/// Longest common prefix of every use's scope_path. The result IS the
/// DCA scope path (descend `body` along it to reach the scope where the
/// hoist lands).
fn longest_common_prefix(uses: &[UseLocation]) -> Vec<ScopeStep> {
    if uses.is_empty() {
        return Vec::new();
    }
    let first = &uses[0].scope_path;
    let mut prefix_len = first.len();
    for other in &uses[1..] {
        prefix_len = prefix_len.min(other.scope_path.len());
        let mut matched = 0;
        while matched < prefix_len && first[matched] == other.scope_path[matched] {
            matched += 1;
        }
        prefix_len = matched;
        if prefix_len == 0 {
            break;
        }
    }
    first[..prefix_len].to_vec()
}

/// Locate the earliest top-level `stmt_idx` within the DCA scope that
/// contains the key in any of its scope-root expressions OR anywhere in
/// its sub-bodies. Insertion goes BEFORE that statement so the synthetic
/// def dominates every occurrence.
fn first_use_idx_in_scope(scope_body: &[Stmt], key: &str) -> Option<usize> {
    scope_body
        .iter()
        .position(|stmt| stmt_subtree_contains_key(stmt, key))
}

/// True if `stmt` or any of its nested sub-bodies contains a sub-expression
/// whose canonical key equals `key`.
fn stmt_subtree_contains_key(stmt: &Stmt, key: &str) -> bool {
    if scope_root_contains_key(stmt, key) {
        return true;
    }
    let mut found = false;
    for_each_sub_body(stmt, |_slot, sub_body| {
        if found {
            return;
        }
        if sub_body
            .iter()
            .any(|child| stmt_subtree_contains_key(child, key))
        {
            found = true;
        }
    });
    found
}

/// True if any scope-root expression of `stmt` contains a sub-expression
/// whose canonical key equals `key`.
fn scope_root_contains_key(stmt: &Stmt, key: &str) -> bool {
    let mut hit = false;
    for expr in scope_root_exprs(stmt) {
        walk_expr(expr, &mut |node| {
            if hit {
                return;
            }
            if let Ok(node_key) = serde_json::to_string(node) {
                if node_key == key {
                    hit = true;
                }
            }
        });
        if hit {
            return true;
        }
    }
    false
}

/// Find the bytecode offset of the earliest occurrence of `key` once
/// descended into the DCA scope. Returns `None` if no occurrence is
/// found (defensive).
fn first_use_offset_at(body: &[Stmt], dca_path: &[ScopeStep], key: &str) -> Option<usize> {
    let scope = descend_ref(body, dca_path)?;
    let idx = scope
        .iter()
        .position(|stmt| stmt_subtree_contains_key(stmt, key))?;
    Some(scope[idx].offset())
}

/// Substitute every sub-expression matching `key` with `Var(replacement)`
/// across every statement at index `from + 1` onward in `scope_body`,
/// recursively descending into nested sub-bodies.
///
/// The `from + 1` skip is the infinite-loop guard, the inserted Assignment
/// at index `from` carries the canonical expression in its rhs and must
/// NOT be re-substituted, otherwise the rhs would collapse to
/// `Var(replacement)` referencing itself.
///
/// `multi_def_names` is the BP-temp-slot exclusion set: an Assignment whose
/// lhs is a `Var(name)` in this set has its rhs left untouched. Symmetric
/// with the collection-side skip in `collect_in_body`.
fn substitute_after_index(
    scope_body: &mut [Stmt],
    from: usize,
    key: &str,
    replacement: &str,
    multi_def_names: &BTreeSet<String>,
) {
    let after_insert = &mut scope_body[from + 1..];
    for stmt in after_insert.iter_mut() {
        substitute_in_stmt_subtree(stmt, key, replacement, multi_def_names);
    }
}

/// Substitute every sub-expression matching `key` in `stmt`'s scope-root
/// expressions and, recursively, in every nested sub-body. Skips the rhs
/// slot of any Assignment whose lhs is a multi-def Var. The Assignment
/// lhs root itself is never substituted (def position); only its sub-
/// expressions are walked, mirroring the collection-side exclusion in
/// `collect_in_body`.
fn substitute_in_stmt_subtree(
    stmt: &mut Stmt,
    key: &str,
    replacement: &str,
    multi_def_names: &BTreeSet<String>,
) {
    let skip_rhs = match stmt {
        Stmt::Assignment { lhs, .. } => {
            assignment_var_lhs_name(lhs).is_some_and(|name| multi_def_names.contains(name))
        }
        _ => false,
    };
    for (expr, role) in scope_root_exprs_tagged_mut(stmt) {
        if skip_rhs && matches!(role, ExprRole::AssignmentRhs) {
            // BP-temp-slot defining value: leave alone to avoid a
            // `$Slot = $Cse_N` chain artifact.
            continue;
        }
        let mut visit = |node: &mut Expr| {
            if let Ok(node_key) = serde_json::to_string(node) {
                if node_key == key {
                    *node = Expr::Var(replacement.to_string());
                    return Action::Continue;
                }
            }
            Action::Continue
        };
        if matches!(role, ExprRole::AssignmentLhs) {
            // Lhs root is a def. Walk only sub-expressions so nested
            // projections under it still get substituted.
            walk_expr_children_mut(expr, &mut visit);
        } else {
            walk_expr_mut(expr, &mut visit);
        }
    }
    for_each_sub_body_mut(stmt, |_slot, sub_body| {
        for child in sub_body.iter_mut() {
            substitute_in_stmt_subtree(child, key, replacement, multi_def_names);
        }
    });
}

/// Mutable counterpart of `for_each_sub_body`.
fn for_each_sub_body_mut<F: FnMut(ScopeSlot, &mut Vec<Stmt>)>(stmt: &mut Stmt, mut visit: F) {
    match stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            visit(ScopeSlot::BranchThen, then_body);
            visit(ScopeSlot::BranchElse, else_body);
        }
        Stmt::Sequence { pins, .. } => {
            for (pin_idx, pin_body) in pins.iter_mut().enumerate() {
                visit(ScopeSlot::SequencePin(pin_idx), pin_body);
            }
        }
        Stmt::Loop {
            body,
            completion,
            kind,
            ..
        } => {
            visit(ScopeSlot::LoopBody, body);
            if let Some(comp) = completion {
                visit(ScopeSlot::LoopCompletion, comp);
            }
            if let LoopKind::ForC { init, increment } = kind {
                visit(ScopeSlot::LoopForcInit, init);
                visit(ScopeSlot::LoopForcIncrement, increment);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for (case_idx, case) in cases.iter_mut().enumerate() {
                visit(ScopeSlot::SwitchCase(case_idx), &mut case.body);
            }
            if let Some(default_body) = default {
                visit(ScopeSlot::SwitchDefault, default_body);
            }
        }
        Stmt::Latch { init, body, .. } => {
            visit(ScopeSlot::LatchInit, init);
            visit(ScopeSlot::LatchBody, body);
        }
        Stmt::Assignment { .. }
        | Stmt::Call { .. }
        | Stmt::Return { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
}
