//! FlipFlop recognition: detects the self-toggling boolean + branch shape
//! the Blueprint compiler emits for a FlipFlop macro and rewrites it to a
//! `Stmt::Latch::FlipFlop`. Covers post-inline, pre-inline (alias-chained),
//! embedded, shared-arms, and trailing-toggle variants.

use super::shared::FLIPFLOP_TOGGLE_PREFIX;
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::visit::{self, resolve_var_chain};
use std::collections::BTreeSet;

/// FlipFlop recognition.
///
/// The Blueprint compiler emits a FlipFlop as a self-toggling boolean
/// followed by a branch on the same boolean. The toggle update can be
/// direct (post-inline) or routed through one or more temp aliases
/// (pre-inline / alias-chained). All shapes share the same essential
/// structure: a Branch on `Var(toggle_var)` immediately preceded by an
/// assignment to `toggle_var` whose right-hand side resolves, through
/// any number of `Var($temp)` chain hops, to `!Var(toggle_var)`.
///
/// Pre-inlining shape (3 stmts):
/// ```text
/// $Not_PreBool       = !Temp_bool_Variable_<N>;
/// Temp_bool_Variable_<N> = $Not_PreBool;
/// if (Temp_bool_Variable_<N>) { A } else { B }
/// ```
///
/// Post-inlining shape (2 stmts):
/// ```text
/// Temp_bool_Variable_<N> = !Temp_bool_Variable_<N>;
/// if (Temp_bool_Variable_<N>) { A } else { B }
/// ```
///
/// Latch recognition runs before single-use inlining, so the 3-stmt shape
/// is the common case in production. The 2-stmt shape becomes reachable
/// after the inliner is moved post-recognition.
///
/// `Stmt` is not `Clone`, so detection is split from construction:
/// [`detect_flipflop_at`] decides whether `body[idx]` is a FlipFlop
/// branch, and [`build_flipflop_latch`] consumes the branch in-place
/// (via `mem::take` on its arms) once the caller has confirmed match.
/// Result of FlipFlop detection at a single body index.
pub(super) enum FlipFlopMatch {
    /// Standard shape: preceding sibling assignments encode the toggle.
    /// Value is the number of stmts to drain before the branch index.
    Standard(usize),
    /// Embedded-flip shape: toggle update lives inside the else arm.
    /// Value is the number of preceding consumer stmts to absorb into the latch body.
    Embedded(usize),
    /// Address-split shared-arms shape: the preceding sibling chain encodes
    /// the toggle (standard shape), the Branch's then / else arms hold no
    /// user content (only the toggle update scaffold the BP compiler routed
    /// through the JIN), and the user content lives as following siblings
    /// that read the toggle var. Renders as `FlipFlop(<name>) { A|B: { ... } }`.
    /// `consumed_before` is the preceding-toggle-chain drain count and
    /// `consumed_after` is the trailing-sibling absorb count.
    SharedArms {
        consumed_before: usize,
        consumed_after: usize,
    },
    /// Trailing-toggle shape: the Branch arms hold no user content, and the
    /// toggle update chain sits as trailing siblings (the BP compiler placed
    /// the toggle preamble's block after the JIN's block on disk). User body
    /// content, if any, lives between the Branch and the toggle chain.
    /// `user_body_count` is the count of stmts between the Branch and the
    /// toggle chain (absorbed into the FlipFlop body), and `toggle_drain`
    /// is the trailing toggle-chain length to drop. Renders as
    /// `FlipFlop(<name>) { A|B: { ... } }`.
    TrailingToggle {
        user_body_count: usize,
        toggle_drain: usize,
    },
}

pub(super) fn detect_flipflop_at(
    body: &[Stmt],
    idx: usize,
    ancestors: &[&[Stmt]],
) -> Option<FlipFlopMatch> {
    let Stmt::Branch { cond, .. } = &body[idx] else {
        return None;
    };

    let toggle_var = match_flipflop_branch_cond(cond)?;
    if let Some(consumed_before) = matches_toggle_update(body, idx, toggle_var, ancestors) {
        if let Some(consumed_after) = detect_shared_arms_sibling_absorb(body, idx, toggle_var) {
            return Some(FlipFlopMatch::SharedArms {
                consumed_before,
                consumed_after,
            });
        }
        return Some(FlipFlopMatch::Standard(consumed_before));
    }
    if let Some((user_body_count, toggle_drain)) =
        matches_trailing_toggle_update(body, idx, toggle_var)
    {
        return Some(FlipFlopMatch::TrailingToggle {
            user_body_count,
            toggle_drain,
        });
    }
    detect_embedded_toggle_flip(body, idx, toggle_var).map(FlipFlopMatch::Embedded)
}

/// Address-split shared-arms detection.
///
/// Fires only when standard `matches_toggle_update` already succeeded,
/// the Branch's arms hold no user content (only the BP-emitted toggle
/// update scaffold or nothing), and the user content lives as following
/// siblings that transitively read the toggle var. Returns the number
/// of trailing siblings to absorb into the FlipFlop body.
///
/// The BP compiler emits this shape when the FlipFlop macro's gate JIN
/// dispatches to two tracepoint-only arms that converge on a shared
/// downstream body. The shared body executes regardless of which branch
/// fires, so the FlipFlop semantically wraps the shared body, not the
/// arms. This renders as `FlipFlop(name) { A|B: { <shared> } }`.
///
/// Returns `None` when:
/// - The Branch arms are NOT scaffold-only (the standard fold is correct).
/// - No trailing siblings read the toggle var or any forward-alias of it.
/// - The alias forward-walk exceeds [`ALIAS_LIMIT`].
fn detect_shared_arms_sibling_absorb(body: &[Stmt], idx: usize, toggle_var: &str) -> Option<usize> {
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[idx]
    else {
        return None;
    };
    if !then_body.is_empty() {
        return None;
    }
    if !else_body.is_empty() && !else_body_is_toggle_flip(else_body, toggle_var) {
        return None;
    }

    let consumed_after = count_following_alias_consumers(body, idx, toggle_var);
    if consumed_after == 0 {
        None
    } else {
        Some(consumed_after)
    }
}

/// Walk forward through statements after `body[idx]`, counting consecutive
/// flat statements that participate in the toggle-var's data-flow tree.
///
/// Two-pass algorithm:
/// 1. Forward closure: scan flat stmts (Assignment / Call) until a
///    structured stmt (Branch / Sequence / Loop / Switch / Latch / Return /
///    EventCall) or end of body. For each flat stmt, mark whether it
///    references any existing alias. Grow the alias set with any `Var(lhs)`
///    whose rhs touches an alias.
/// 2. Backward shim closure: a flat stmt that didn't ref any alias forward
///    still counts as part of the data-flow tree if its `Var(lhs)` name
///    is referenced by a later flat stmt that IS in the closure (e.g. UE5's
///    `$SelectFloat_B_1 = self.X` temp feeding `SelectFloat(..., $SelectFloat_B_1)`).
///
/// Returns the count of contiguous trailing flat stmts to absorb. The
/// closure is bounded by [`ALIAS_LIMIT`] to keep heuristics in check, and
/// must contain at least one stmt that directly references the toggle var.
fn count_following_alias_consumers(body: &[Stmt], idx: usize, toggle_var: &str) -> usize {
    let mut aliases: BTreeSet<String> = BTreeSet::new();
    aliases.insert(toggle_var.to_string());

    let mut window_end = idx + 1;
    while window_end < body.len() && is_flat_stmt(&body[window_end]) {
        window_end += 1;
    }
    if window_end == idx + 1 {
        return 0;
    }

    let mut in_closure = vec![false; window_end - (idx + 1)];
    let mut any_direct_ref = false;
    let toggle_ref_set: BTreeSet<String> = {
        let mut single = BTreeSet::new();
        single.insert(toggle_var.to_string());
        single
    };

    for relative_pos in 0..in_closure.len() {
        let stmt = &body[idx + 1 + relative_pos];
        let refs_alias = stmt_refs_any_alias(stmt, &aliases);
        if refs_alias {
            in_closure[relative_pos] = true;
            if stmt_refs_any_alias(stmt, &toggle_ref_set) {
                any_direct_ref = true;
            }
            if let Stmt::Assignment {
                lhs: Expr::Var(lhs_name),
                rhs,
                ..
            } = stmt
            {
                if expr_refs_any_alias(rhs, &aliases) && !aliases.contains(lhs_name) {
                    aliases.insert(lhs_name.clone());
                    if aliases.len() > ALIAS_LIMIT {
                        return 0;
                    }
                }
            }
        }
    }

    if !any_direct_ref {
        return 0;
    }

    // Backward shim closure: a flat temp-def whose lhs is consumed by a
    // later in-closure stmt joins the closure too.
    let mut changed = true;
    while changed {
        changed = false;
        for relative_pos in (0..in_closure.len()).rev() {
            if in_closure[relative_pos] {
                continue;
            }
            let stmt = &body[idx + 1 + relative_pos];
            let Stmt::Assignment {
                lhs: Expr::Var(lhs_name),
                ..
            } = stmt
            else {
                continue;
            };
            // Is the lhs name referenced by any LATER in-closure stmt?
            let consumed_later = ((relative_pos + 1)..in_closure.len())
                .any(|later| in_closure[later] && stmt_refs_var(&body[idx + 1 + later], lhs_name));
            if consumed_later {
                in_closure[relative_pos] = true;
                changed = true;
            }
        }
    }

    // Count the longest contiguous prefix of in_closure stmts starting at 0.
    let mut count = 0;
    for &included in in_closure.iter() {
        if included {
            count += 1;
        } else {
            break;
        }
    }
    count
}

/// Return `true` when `stmt` is a flat assignment or call (no nested
/// control-flow body). Branch / Sequence / Loop / Switch / Latch / Return /
/// EventCall / Unknown are NOT flat: absorbing past them risks pulling in
/// content that doesn't belong to the FlipFlop body.
fn is_flat_stmt(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Assignment { .. } | Stmt::Call { .. })
}

/// Return `true` when `stmt` references `target` (treating `target` as a
/// single-name alias set). Used by the backward shim closure to find
/// temp-defs whose lhs is later consumed.
fn stmt_refs_var(stmt: &Stmt, target: &str) -> bool {
    let mut single = BTreeSet::new();
    single.insert(target.to_string());
    stmt_refs_any_alias(stmt, &single)
}

/// Match a `toggle_var = ...` update that, after walking through any
/// `Var($temp)` aliases, resolves to `!Var(toggle_var)`.
///
/// Returns the number of preceding statements to drain when the match
/// succeeds: 1 for the post-inline shape, 2 for the pre-inline shape, and
/// `1 + chain_length` for any longer alias chain. Returns `None` when no
/// matching update precedes the branch or the chain doesn't terminate at
/// the toggle's negation.
///
/// `resolve_var_chain(&body[..idx], toggle_var)` does the chain walk:
/// `toggle_var`'s defining assignment is `body[idx - 1]`, and
/// `resolve_var_chain` follows `Var($temp)` rhss through the rest of
/// `body[..idx]` until it hits a non-`Var` expression. The matcher
/// accepts the match when that terminal expression is `!Var(toggle_var)`.
///
/// Drain extent is computed separately by walking the chain through
/// statements immediately preceding the branch. The Blueprint compiler
/// emits the toggle and its temp defs as a contiguous run; non-contiguous
/// chain links are rejected to keep the drain conservative.
fn matches_toggle_update(
    body: &[Stmt],
    idx: usize,
    toggle_var: &str,
    ancestors: &[&[Stmt]],
) -> Option<usize> {
    if idx == 0 {
        return None;
    }

    // Build the chain-resolution scope stack. Innermost is the body's
    // preceding siblings (`body[..idx]`), then the outer ancestors.
    let prefix: &[Stmt] = &body[..idx];
    let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
    scopes.push(prefix);
    scopes.extend(ancestors.iter().copied());
    let resolved = resolve_var_chain(&scopes, toggle_var)?;
    if !is_negation_of(resolved, toggle_var) {
        return None;
    }

    contiguous_chain_length(body, idx, toggle_var)
}

/// Detect a trailing toggle-update chain after the gate Branch at `body[idx]`.
///
/// Mirrors `matches_toggle_update` for the case where the BP compiler placed
/// the toggle preamble's block after the JIN's block on disk, so the toggle
/// update chain emits as siblings after the gate Branch rather than before it.
/// The chain is required to sit at the tail of `body` (no stmts after it),
/// the Branch's arms must be empty (scaffold-only), and any user body content
/// must live as flat stmts between the Branch and the chain.
///
/// Returns `(user_body_count, toggle_drain)` when the trailing chain is found:
/// - `user_body_count` is the count of stmts in `body[idx+1..chain_start]`
///   absorbed as the FlipFlop body.
/// - `toggle_drain` is the chain length (`body[chain_start..]`) to drop.
///
/// The chain shape is either the 1-stmt post-inline form (`toggle = !toggle`)
/// or the 2-stmt pre-inline form (`$Tmp = !toggle; toggle = $Tmp`), generalised
/// to any longer `Var($temp)` alias chain via [`resolve_var_chain`].
fn matches_trailing_toggle_update(
    body: &[Stmt],
    idx: usize,
    toggle_var: &str,
) -> Option<(usize, usize)> {
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[idx]
    else {
        return None;
    };
    if !then_body.is_empty() || !else_body.is_empty() {
        return None;
    }
    if idx + 1 >= body.len() {
        return None;
    }

    let toggle_drain = trailing_chain_length(body, toggle_var)?;
    let chain_start = body.len() - toggle_drain;
    if chain_start <= idx {
        return None;
    }
    let user_body_count = chain_start - (idx + 1);
    Some((user_body_count, toggle_drain))
}

/// Forward analogue of [`contiguous_chain_length`]: walk the tail of `body`
/// for a contiguous run of assignments that defines `toggle_var` from
/// `!toggle_var` (directly or via `Var($temp)` alias hops). The chain is
/// expected at the very tail of `body`; the terminal `Var = !toggle_var`
/// assignment sits earliest in the chain and the `toggle_var = ...` definition
/// sits last (at `body.len() - 1`).
///
/// Returns the chain length when the walk terminates at `!Var(toggle_var)`,
/// `None` otherwise (no toggle-assignment at the tail, chain isn't contiguous,
/// or a cycle is detected).
fn trailing_chain_length(body: &[Stmt], toggle_var: &str) -> Option<usize> {
    if body.is_empty() {
        return None;
    }
    let mut consumed = 0;
    let mut current = toggle_var;
    let mut visited: BTreeSet<&str> = BTreeSet::new();
    loop {
        if !visited.insert(current) {
            return None;
        }
        let successor_index = body.len().checked_sub(consumed + 1)?;
        let next_rhs = assignment_rhs_of(&body[successor_index], current)?;
        consumed += 1;
        match next_rhs {
            Expr::Var(next_name) => current = next_name.as_str(),
            other if is_negation_of(other, toggle_var) => return Some(consumed),
            _ => return None,
        }
    }
}

/// Walk back through immediately-preceding `lhs = rhs` assignments,
/// starting from `body[idx - 1]` whose lhs is `toggle_var`, following
/// `Var($temp)` rhss to their definitions. Returns the number of
/// statements consumed (the toggle update itself plus each chain hop's
/// defining statement) when the walk terminates at `!Var(toggle_var)`.
///
/// Returns `None` if the chain isn't contiguous (a hop's defining stmt
/// isn't directly above the previous one), if a name's defining
/// assignment is missing, or if a cycle is detected.
fn contiguous_chain_length(body: &[Stmt], idx: usize, toggle_var: &str) -> Option<usize> {
    let mut consumed = 0;
    let mut current = toggle_var;
    let mut visited: BTreeSet<&str> = BTreeSet::new();
    loop {
        if !visited.insert(current) {
            return None;
        }
        let predecessor_index = idx.checked_sub(consumed + 1)?;
        let next_rhs = assignment_rhs_of(&body[predecessor_index], current)?;
        consumed += 1;
        match next_rhs {
            Expr::Var(next_name) => current = next_name.as_str(),
            other if is_negation_of(other, toggle_var) => return Some(consumed),
            _ => return None,
        }
    }
}

/// If `stmt` is `Assignment { lhs: Var(target), rhs }`, return `&rhs`.
fn assignment_rhs_of<'a>(stmt: &'a Stmt, target: &str) -> Option<&'a Expr> {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return None;
    };
    let Expr::Var(lhs_name) = lhs else {
        return None;
    };
    if lhs_name == target {
        Some(rhs)
    } else {
        None
    }
}

/// Return `true` if `expr` is a logical negation of `Var(target)` in
/// either of the two negation forms the IR carries
/// (see `visit::negated_operand`).
fn is_negation_of(expr: &Expr, target: &str) -> bool {
    matches!(visit::negated_operand(expr), Some(Expr::Var(name)) if name == target)
}

/// Build a FlipFlop `Stmt::Latch` wrapping an inner `Stmt::Branch`.
/// `toggle_var` becomes both the latch's `gate_var` and the inner branch's
/// cond. Used by both the standard and embedded-flip recognizer arms.
fn make_flipflop_latch(
    toggle_var: String,
    then_body: Vec<Stmt>,
    else_body: Vec<Stmt>,
    offset: usize,
) -> Stmt {
    Stmt::Latch {
        kind: LatchKind::FlipFlop {
            gate_var: toggle_var.clone(),
            names: None,
        },
        init: vec![],
        body: vec![Stmt::Branch {
            cond: Expr::Var(toggle_var),
            then_body,
            else_body,
            offset,
        }],
        offset,
    }
}

/// Convert a confirmed FlipFlop `Stmt::Branch` in place into the equivalent
/// `Stmt::Latch`. Caller must have already validated the shape via
/// [`detect_flipflop_at`].
pub(super) fn build_flipflop_latch(branch: &mut Stmt) -> Stmt {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        offset,
    } = branch
    else {
        unreachable!("build_flipflop_latch called on non-Branch");
    };
    let toggle_var = match_flipflop_branch_cond(cond)
        .expect("FlipFlop cond must be Expr::Var with toggle prefix")
        .to_string();
    make_flipflop_latch(
        toggle_var,
        std::mem::take(then_body),
        std::mem::take(else_body),
        *offset,
    )
}

/// Return the toggle variable name if `cond` is `Expr::Var(<flipflop_var>)`.
fn match_flipflop_branch_cond(cond: &Expr) -> Option<&str> {
    let Expr::Var(name) = cond else {
        return None;
    };
    if name.starts_with(FLIPFLOP_TOGGLE_PREFIX) {
        Some(name)
    } else {
        None
    }
}

/// Embedded toggle flip: the toggle self-assignment lives inside the branch's
/// else arm rather than as a preceding sibling.
///
/// The Blueprint compiler emits this shape when the FlipFlop macro's internal
/// toggle update is not lifted out as a preceding assignment. Two else-body
/// shapes are recognised:
///
/// ```text
/// // Single-stmt: <lhs> = !toggle_var  (Unary::Not OR Not_PreBool Call)
/// // The lhs need not be `toggle_var` itself: post-inline shapes can land
/// // any temp on the lhs as long as the rhs negates the toggle.
/// <lhs> = !toggle_var
///
/// // Two-stmt canonical chain: `$tmp = !toggle_var; toggle_var = $tmp`.
/// // This is the pre-inline shape where the Not_PreBool result is routed
/// // through an intermediate temp before being written back to the toggle.
/// $tmp = !toggle_var
/// toggle_var = $tmp
/// ```
///
/// Surrounding context required:
/// - `then_body` is empty (guard against collapsing a real branch).
/// - At least one preceding sibling reads `toggle_var` directly OR via the
///   alias-aware walk (forward def-use chains let `self.X = Var(toggle_var)`
///   then later reads of `self.X` count as toggle consumers).
///
/// Returns the number of preceding consumer stmts to absorb. Zero consumers
/// means we can't form a FlipFlop body, so the match aborts.
fn detect_embedded_toggle_flip(body: &[Stmt], idx: usize, toggle_var: &str) -> Option<usize> {
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = &body[idx]
    else {
        return None;
    };

    if !then_body.is_empty() {
        return None;
    }

    if !else_body_is_toggle_flip(else_body, toggle_var) {
        return None;
    }

    // Walk back through preceding siblings collecting those that reference
    // toggle_var, threading reads through any forward-defined aliases.
    let consumer_count = count_preceding_alias_consumers(body, idx, toggle_var);
    if consumer_count == 0 {
        return None;
    }

    Some(consumer_count)
}

/// Maximum number of distinct alias names tracked during the forward def-use
/// pass. Real BP-emitted FlipFlop bodies stay well under this; an explosion
/// past 16 indicates the heuristic is wandering into unrelated code.
const ALIAS_LIMIT: usize = 16;

/// Return `true` when `else_body` matches one of the recognised toggle-flip
/// shapes: a single assignment whose rhs negates `toggle_var`, or the
/// canonical two-stmt chain `$tmp = !toggle_var; toggle_var = $tmp`.
fn else_body_is_toggle_flip(else_body: &[Stmt], toggle_var: &str) -> bool {
    match else_body.len() {
        1 => is_assignment_with_negation_rhs(&else_body[0], toggle_var),
        2 => is_two_stmt_toggle_flip_chain(&else_body[0], &else_body[1], toggle_var),
        _ => false,
    }
}

/// Return `true` when `stmt` is `Assignment { rhs: <negation_of(toggle_var)>, .. }`.
/// The lhs is not constrained: post-inline shapes can land any name on the
/// lhs as long as the rhs is the negation form.
fn is_assignment_with_negation_rhs(stmt: &Stmt, toggle_var: &str) -> bool {
    let Stmt::Assignment { rhs, .. } = stmt else {
        return false;
    };
    is_negation_of(rhs, toggle_var)
}

/// Return `true` when `(first, second)` form the canonical two-stmt toggle
/// flip chain `$tmp = !toggle_var; toggle_var = $tmp`. The intermediate
/// temp's name is whatever the compiler picked (`$Not_PreBool`, etc.), so
/// the check is structural: first defines a name from the negation, second
/// assigns `toggle_var` from that same name via `Var($tmp)`.
fn is_two_stmt_toggle_flip_chain(first: &Stmt, second: &Stmt, toggle_var: &str) -> bool {
    let Stmt::Assignment {
        lhs: first_lhs,
        rhs: first_rhs,
        ..
    } = first
    else {
        return false;
    };
    let Expr::Var(temp_name) = first_lhs else {
        return false;
    };
    if !is_negation_of(first_rhs, toggle_var) {
        return false;
    }
    let Stmt::Assignment {
        lhs: second_lhs,
        rhs: second_rhs,
        ..
    } = second
    else {
        return false;
    };
    let Expr::Var(second_lhs_name) = second_lhs else {
        return false;
    };
    if second_lhs_name != toggle_var {
        return false;
    }
    matches!(second_rhs, Expr::Var(name) if name == temp_name)
}

/// Walk backward through preceding siblings, counting consecutive statements
/// that read any name in the alias set seeded with `toggle_var`.
///
/// The alias set is grown by a forward def-use pre-pass over `body[..idx]`:
/// each assignment whose rhs references an existing alias contributes its
/// lhs to the set. This lets a forward-aliasing setup like
/// `self.Field = Var(toggle)` followed by reads of `self.Field`
/// (or temp chains derived from it) count as preceding consumers.
///
/// Bounds and abort conditions:
/// - Returns 0 when the alias set grows past `ALIAS_LIMIT` (signal that
///   the heuristic is overreaching).
/// - A re-bind (assignment to a name already in the alias set with an rhs
///   that does NOT reference any alias) aborts the forward pass at that
///   point. The backward count then runs over the alias set as built up
///   to the abort.
fn count_preceding_alias_consumers(body: &[Stmt], idx: usize, toggle_var: &str) -> usize {
    let aliases = match build_alias_set(body, idx, toggle_var) {
        Some(aliases) => aliases,
        None => return 0,
    };

    let mut count = 0;
    for pos in (0..idx).rev() {
        if stmt_refs_any_alias(&body[pos], &aliases) {
            count += 1;
        } else {
            break;
        }
    }
    count
}

/// Forward def-use over `body[..idx]` building the set of names that
/// transitively carry `toggle_var`'s value. Returns `None` if the set
/// exceeds `ALIAS_LIMIT`. Aborts on re-bind (an existing alias overwritten
/// with an unrelated rhs) without growing the set further.
fn build_alias_set(body: &[Stmt], idx: usize, toggle_var: &str) -> Option<BTreeSet<String>> {
    let mut aliases: BTreeSet<String> = BTreeSet::new();
    aliases.insert(toggle_var.to_string());

    for stmt in body.iter().take(idx) {
        let Stmt::Assignment { lhs, rhs, .. } = stmt else {
            continue;
        };
        let Expr::Var(lhs_name) = lhs else {
            continue;
        };
        let rhs_touches_alias = expr_refs_any_alias(rhs, &aliases);
        if aliases.contains(lhs_name) {
            // Re-bind: the existing alias gets overwritten. If the new rhs
            // still references an alias, the binding stays; otherwise the
            // forward walk is done and we keep the set as-is.
            if !rhs_touches_alias {
                break;
            }
            continue;
        }
        if rhs_touches_alias {
            aliases.insert(lhs_name.clone());
            if aliases.len() > ALIAS_LIMIT {
                return None;
            }
        }
    }

    Some(aliases)
}

/// Return `true` when `stmt` references any name in `aliases` at the top
/// level of its expressions (lhs or rhs of Assignment, func/args of Call,
/// cond of Branch).
fn stmt_refs_any_alias(stmt: &Stmt, aliases: &BTreeSet<String>) -> bool {
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            expr_refs_any_alias(lhs, aliases) || expr_refs_any_alias(rhs, aliases)
        }
        Stmt::Call { func, args, .. } => {
            expr_refs_any_alias(func, aliases)
                || args.iter().any(|arg| expr_refs_any_alias(arg, aliases))
        }
        Stmt::Branch { cond, .. } => expr_refs_any_alias(cond, aliases),
        _ => false,
    }
}

/// Return `true` when `expr` contains any `Var(name)` matching a member of
/// `aliases`. Walks the full expression tree via the shared `walk_expr`,
/// so every variant is covered, including Cast, Ternary, StructConstruct,
/// Switch, ArrayLit, and the transparent Out/Interface/Persistent/Resume
/// wrappers. The previous hand-rolled walk stopped at `_ => false` and
/// silently missed an alias referenced through any of those, undercounting
/// alias consumers.
fn expr_refs_any_alias(expr: &Expr, aliases: &BTreeSet<String>) -> bool {
    let mut found = false;
    visit::walk_expr(expr, &mut |node| {
        if let Expr::Var(name) = node {
            if aliases.contains(name) {
                found = true;
            }
        }
    });
    found
}

/// Build a FlipFlop `Stmt::Latch` from an embedded-flip branch.
///
/// The branch has an empty `then_body` and an `else_body` whose stmts hold
/// only the toggle update scaffold (one or two assignments, all discarded).
/// The `consumers` are the preceding siblings that read the toggle (directly
/// or via aliases) and form the latch body. They become the then arm of the
/// inner Branch (the A side, meaning they run when `toggle_var` is true
/// after the flip).
pub(super) fn build_embedded_flipflop_latch(branch: &mut Stmt, consumers: Vec<Stmt>) -> Stmt {
    let Stmt::Branch { cond, offset, .. } = branch else {
        unreachable!("build_embedded_flipflop_latch called on non-Branch");
    };
    let toggle_var = match_flipflop_branch_cond(cond)
        .expect("FlipFlop cond must be Expr::Var with toggle prefix")
        .to_string();
    make_flipflop_latch(toggle_var, consumers, vec![], *offset)
}

/// Build a FlipFlop `Stmt::Latch` for the address-split shared-arms shape.
///
/// The branch arms are scaffold-only (empty THEN, ELSE holds only the
/// toggle update). `absorbed` is the following-siblings list that the
/// detector identified as the FlipFlop's shared body. The arms get
/// discarded; `absorbed` becomes the then arm of the inner Branch with
/// an empty else, which the summary emitter renders as `A|B: { ... }`.
pub(super) fn build_shared_arms_flipflop_latch(branch: &mut Stmt, absorbed: Vec<Stmt>) -> Stmt {
    let Stmt::Branch { cond, offset, .. } = branch else {
        unreachable!("build_shared_arms_flipflop_latch called on non-Branch");
    };
    let toggle_var = match_flipflop_branch_cond(cond)
        .expect("FlipFlop cond must be Expr::Var with toggle prefix")
        .to_string();
    make_flipflop_latch(toggle_var, absorbed, vec![], *offset)
}

#[cfg(test)]
mod tests {
    use super::expr_refs_any_alias;
    use crate::bytecode::expr::{CastKind, Expr};
    use crate::bytecode::transforms::test_fixtures::{lit, var};
    use std::collections::BTreeSet;

    fn alias_set(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|name| name.to_string()).collect()
    }

    /// Regression: the previous hand-rolled walk stopped at `_ => false`
    /// and silently missed an alias referenced through a Cast, Ternary, or
    /// other non-arithmetic wrapper, undercounting alias consumers. Routing
    /// through the shared `walk_expr` covers every variant.
    #[test]
    fn alias_seen_through_cast_and_ternary_wrappers() {
        let aliases = alias_set(&["X"]);

        let cast = Expr::Cast {
            kind: CastKind::ToBool,
            inner: Box::new(var("X")),
        };
        assert!(
            expr_refs_any_alias(&cast, &aliases),
            "alias inside a Cast must be seen"
        );

        // Cast nested inside a Ternary condition exercises the deep walk.
        let ternary = Expr::Ternary {
            cond: Box::new(cast),
            then_expr: Box::new(lit("1")),
            else_expr: Box::new(lit("0")),
        };
        assert!(
            expr_refs_any_alias(&ternary, &aliases),
            "alias inside a Ternary must be seen"
        );

        // A non-alias var through the same wrapper stays false.
        let other = Expr::Cast {
            kind: CastKind::ToBool,
            inner: Box::new(var("Y")),
        };
        assert!(
            !expr_refs_any_alias(&other, &aliases),
            "non-alias var must not match"
        );
    }
}
