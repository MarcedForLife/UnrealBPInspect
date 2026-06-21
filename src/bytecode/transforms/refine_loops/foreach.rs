use super::{
    collect_var_refs_in_expr, count_body_var_uses, exprs_equivalent, idx_matches_counter,
    is_array_length_name, is_one_literal, lhs_matches_var, lhs_var_name, peel_break_flag_and,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{
    resolve_var_chain, scope_stack, walk_stmt_exprs, walk_stmt_exprs_mut, Action,
};

/// Check if the ForC shape (cond + increment + body) matches the canonical
/// `counter < Array_Length(array)` pattern, returning `(item_name, array_expr)`
/// on success.
///
/// The condition (`counter < Array_Length(array)`) plus a matching increment
/// is the ForEach signature: an `Array_Length`-bounded counter loop. A real
/// index-`for` over a numeric param (`counter < TraceSockets - 1`) never
/// produces this shape, so the array-bound gate alone cannot fire on a plain
/// ForC.
///
/// When the body reads `array[counter]` the item name comes from the fetch's
/// lhs. When the iterated element is UNUSED (the Blueprint compiler emits no
/// element fetch at all), the name is synthesized from the array via
/// [`var_names::derive_foreach_item_name`] so the loop still renders as a
/// ForEach rather than an index-`for`. The unused-element path is gated by
/// [`body_indexes_with_counter`]: a counter that feeds a parallel-array fetch
/// (`Other[counter]` while the cond bounds a different array) keeps the loop an
/// index-`for`, since the ForEach rendering cannot expose the iteration index.
pub(super) fn match_foreach_shape(
    cond: &Expr,
    increment: &[Stmt],
    body: &[Stmt],
    ancestors: &[&[Stmt]],
) -> Option<(String, Expr)> {
    let (counter_name, array_expr) = match_foreach_cond(cond, body, ancestors)?;
    if !match_foreach_increment(increment, &counter_name, body, ancestors) {
        return None;
    }
    let item = match find_foreach_item(body, &counter_name, &array_expr, ancestors) {
        Some(name) => name,
        None => {
            // No fetch reads the bound array. Promote to a no-element ForEach
            // ONLY when the counter is dead scaffolding. If the body indexes any
            // array with the counter (a parallel-array access whose cond bounds a
            // different array), keep it an index-`for`: the ForEach rendering
            // hides the iteration index, so promoting would orphan that fetch.
            if body_indexes_with_counter(body, &counter_name) {
                return None;
            }
            crate::bytecode::transforms::var_names::derive_foreach_item_name(&array_expr, body)
        }
    };
    Some((item, array_expr))
}

/// True when the body fetches an array element indexed by the loop counter (or
/// one of its index-mirror aliases) anywhere: `arr[counter]` /
/// `Array_Get(arr, counter)` for ANY array, including nested bodies. An
/// index-mirror def (`alias = counter`) is a `Var` rhs, not an index fetch, so
/// it does not count.
///
/// Used to gate the unused-element ForEach promotion (`match_foreach_shape`): a
/// loop whose counter feeds a parallel-array fetch is a genuine index-`for`, not
/// a ForEach, because the ForEach rendering does not expose the iteration index.
fn body_indexes_with_counter(body: &[Stmt], counter_name: &str) -> bool {
    let aliases = collect_index_aliases(body, counter_name);
    let mut found = false;
    for stmt in body {
        walk_stmt_exprs(stmt, &mut |expr: &Expr| {
            let idx = match expr {
                Expr::Index { idx, .. } => Some(idx.as_ref()),
                Expr::Call { name, args } if is_array_get_name(name) && args.len() == 2 => {
                    Some(&args[1])
                }
                _ => None,
            };
            if let Some(idx) = idx {
                if aliases.iter().any(|alias| idx_matches_counter(idx, alias)) {
                    found = true;
                }
            }
        });
    }
    found
}

/// Remove the index-fetch line (and any preceding index-mirror lines) from the
/// body, in preparation for `LoopKind::ForEach` promotion.
///
/// Mirrors `find_foreach_item`: index-mirror collection is scoped to the body
/// head (the mirror is always first when present), and the fetch lookup walks
/// the full body. The `array_expr` match in `index_fetch_matches` ensures
/// only the matching fetch is removed, not unrelated `Array_Get` calls inside
/// nested loops.
pub(super) fn strip_foreach_boilerplate(
    body: &mut Vec<Stmt>,
    _item: &str,
    array_expr: &Expr,
    cond: &Expr,
    ancestors: &[&[Stmt]],
) {
    let (counter_name, _) = match match_foreach_cond(cond, body, ancestors) {
        Some(pair) => pair,
        None => return,
    };
    let alias_names = collect_index_aliases(body, &counter_name);
    let scopes = scope_stack(body.as_slice(), ancestors);

    let fetch_idx = body.iter().position(|stmt| {
        let Stmt::Assignment { rhs, .. } = stmt else {
            return false;
        };
        alias_names
            .iter()
            .any(|alias| index_fetch_matches(rhs, array_expr, alias, &scopes))
    });
    let fetch_idx = match fetch_idx {
        Some(idx) => idx,
        None => return,
    };
    // Drop the fetch line plus every index-mirror sitting before it. The
    // mirror is dead once we promote the loop to ForEach, regardless of
    // whether it's adjacent to the fetch or further up the body.
    let mut drop_indices: Vec<usize> = body
        .iter()
        .take(fetch_idx)
        .enumerate()
        .filter_map(|(idx, stmt)| {
            if is_index_mirror(stmt, &counter_name) {
                Some(idx)
            } else {
                None
            }
        })
        .collect();
    drop_indices.push(fetch_idx);
    drop_indices.sort_unstable();
    for idx in drop_indices.into_iter().rev() {
        body.remove(idx);
    }
}

/// True when the loop-body subtree contains a `Stmt::Break`. A `break`
/// only appears on a multi-break loop (the break-guard recovery emits
/// it), so this scopes the nested index-fetch substitution to that shape
/// and leaves plain ForEach loops byte-identical. Recurses into nested
/// Branch / Loop / Switch / Latch / Sequence bodies.
pub(super) fn body_contains_break(body: &[Stmt]) -> bool {
    body.iter().any(|stmt| match stmt {
        Stmt::Break { .. } => true,
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => body_contains_break(then_body) || body_contains_break(else_body),
        Stmt::Loop {
            body, completion, ..
        } => body_contains_break(body) || completion.as_deref().is_some_and(body_contains_break),
        Stmt::Switch { cases, default, .. } => {
            cases.iter().any(|case| body_contains_break(&case.body))
                || default.as_deref().is_some_and(body_contains_break)
        }
        Stmt::Latch { init, body, .. } => body_contains_break(init) || body_contains_break(body),
        Stmt::Sequence { pins, .. } => pins.iter().any(|pin| body_contains_break(pin)),
        _ => false,
    })
}

/// Recursively replace every `array[counter]` / `Array_Get(array, counter)`
/// index-fetch in the loop-body subtree with `Var(item)`. Scoped to the
/// loop body (and its nested Branch / Loop / Switch / Latch / Sequence
/// bodies), so a re-fetch nested inside a loop-break guard's branch
/// renders as the loop variable instead of the raw counter. The defining
/// fetch (`item = array[counter]`) is already removed by
/// `strip_foreach_boilerplate` before this runs, so only nested re-fetches
/// remain to rewrite.
pub(super) fn substitute_foreach_fetches(
    body: &mut Vec<Stmt>,
    array_expr: &Expr,
    counter_aliases: &[String],
    item: &str,
    ancestors: &[&[Stmt]],
) {
    // Snapshot the body for the read-only chain-resolution scope so the
    // matcher can hop an opaque `Var($X)` recv through body-local temp
    // definitions while the live body is borrowed mutably below.
    let body_snapshot: Vec<Stmt> = body.to_vec();
    let scopes = scope_stack(body_snapshot.as_slice(), ancestors);
    let replacement = Expr::Var(item.to_string());
    for stmt in body.iter_mut() {
        walk_stmt_exprs_mut(stmt, &mut |expr: &mut Expr| {
            if counter_aliases
                .iter()
                .any(|alias| index_fetch_matches(expr, array_expr, alias, &scopes))
            {
                *expr = replacement.clone();
            }
            Action::Continue
        });
    }
    // The substitution turns a nested re-fetch `item = array[counter]` into
    // the self-assignment `item = item` (a redundant reload of the loop
    // var). Drop those throughout the subtree.
    remove_item_self_assignments(body, item);
}

/// Recursively remove `item = item` self-assignments from the loop-body
/// subtree (introduced when [`substitute_foreach_fetches`] rewrites a
/// nested `item = array[counter]` re-fetch).
fn remove_item_self_assignments(body: &mut Vec<Stmt>, item: &str) {
    body.retain(|stmt| {
        !matches!(
            stmt,
            Stmt::Assignment { lhs: Expr::Var(lhs_name), rhs: Expr::Var(rhs_name), .. }
                if lhs_name == item && rhs_name == item
        )
    });
    for stmt in body.iter_mut() {
        match stmt {
            Stmt::Branch {
                then_body,
                else_body,
                ..
            } => {
                remove_item_self_assignments(then_body, item);
                remove_item_self_assignments(else_body, item);
            }
            Stmt::Loop {
                body, completion, ..
            } => {
                remove_item_self_assignments(body, item);
                if let Some(comp) = completion {
                    remove_item_self_assignments(comp, item);
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for case in cases.iter_mut() {
                    remove_item_self_assignments(&mut case.body, item);
                }
                if let Some(default_body) = default {
                    remove_item_self_assignments(default_body, item);
                }
            }
            Stmt::Latch { init, body, .. } => {
                remove_item_self_assignments(init, item);
                remove_item_self_assignments(body, item);
            }
            Stmt::Sequence { pins, .. } => {
                for pin in pins.iter_mut() {
                    remove_item_self_assignments(pin, item);
                }
            }
            _ => {}
        }
    }
}

/// Walk `body` looking for `item = array[counter]` or
/// `item = Array_Get(array, counter)`. Returns the item variable name on match.
///
/// The fetch may sit anywhere in the body, not just at the head: Blueprint
/// emits user code (e.g. `BreakHitResult(...)`) before the index-fetch when
/// the source graph executes statements before consuming the array element.
/// The `index_fetch_matches` check requires the array expression to match the
/// loop's array, which guards against picking up an inner-loop fetch.
///
/// The index-mirror form is still accepted: a leading `Temp_int_* = counter`
/// assignment makes that temp an alias the fetch can index through. Mirrors
/// are collected from the body head only (where Blueprint emits them).
///
/// Chain-aware: when the body fetch's recv is an opaque `Var($X)` and the
/// loop's `array_expr` is a structural shape (e.g. the cond's chain hop
/// already walked through), [`index_fetch_matches`] chain-walks the recv via
/// [`resolve_expr_chain`] so the structural comparison sees both sides at
/// the same canonical level.
fn find_foreach_item(
    body: &[Stmt],
    counter_name: &str,
    array_expr: &Expr,
    ancestors: &[&[Stmt]],
) -> Option<String> {
    let alias_names = collect_index_aliases(body, counter_name);
    let alias_refs: Vec<&str> = alias_names.iter().map(String::as_str).collect();
    let scopes = scope_stack(body, ancestors);

    if let Some(item) = find_item_binding_in_stmts(body, &alias_refs, array_expr, &scopes) {
        return Some(item);
    }

    // Fallback: the item-binding fetch can sit inside a nested body (the
    // DoOnce-in-ForEach shape wraps the `array[counter]` fetch in a Latch).
    // Aliases are collected from the OUTER body head (where Blueprint emits
    // the index mirror), so reuse `alias_refs` while descending into nested
    // statement bodies. Only reached when the top-level scan found nothing,
    // so plain top-level-fetch ForEach loops stay byte-identical.
    find_item_binding_nested(body, &alias_refs, array_expr, &scopes)
}

/// Scan `stmts` (one level) for an `Assignment` whose rhs is an index-fetch
/// of `array_expr` keyed by one of `alias_refs`. Returns the lhs item name.
pub(super) fn find_item_binding_in_stmts(
    stmts: &[Stmt],
    alias_refs: &[&str],
    array_expr: &Expr,
    scopes: &[&[Stmt]],
) -> Option<String> {
    stmts.iter().find_map(|stmt| {
        let Stmt::Assignment { lhs, rhs, .. } = stmt else {
            return None;
        };
        let matches_fetch = alias_refs
            .iter()
            .any(|alias| index_fetch_matches(rhs, array_expr, alias, scopes));
        if matches_fetch {
            lhs_var_name(lhs).map(str::to_string)
        } else {
            None
        }
    })
}

/// Recursively scan the nested statement bodies of `stmts` for the
/// item-binding fetch. Used as the [`find_foreach_item`] fallback for the
/// DoOnce-in-ForEach shape, where the fetch lives inside a `Latch` body.
fn find_item_binding_nested(
    stmts: &[Stmt],
    alias_refs: &[&str],
    array_expr: &Expr,
    scopes: &[&[Stmt]],
) -> Option<String> {
    for stmt in stmts {
        for child in stmt.child_bodies_structural() {
            if let Some(item) = find_item_binding_in_stmts(child, alias_refs, array_expr, scopes) {
                return Some(item);
            }
            if let Some(item) = find_item_binding_nested(child, alias_refs, array_expr, scopes) {
                return Some(item);
            }
        }
    }
    None
}

/// True when `expr` evaluates to `array_resolved[counter_name]` via the
/// `Index` opcode or an `Array_Get` call.
///
/// When the body fetch's recv is an opaque `Var($X)` and `array_resolved`
/// is a structural shape (because the cond's chain hop walked through),
/// the recv is chain-walked through `scopes` so the structural comparison
/// sees both sides at the same canonical level. The walk only fires on a
/// bare `Var` recv, leaving an already-inlined `arr[idx]` shape with its
/// user-facing array name intact. The idx is matched symbolically against
/// `counter_name` without resolution; resolving it would substitute the
/// counter's init definition from an ancestor scope.
fn index_fetch_matches(
    expr: &Expr,
    array_resolved: &Expr,
    counter_name: &str,
    scopes: &[&[Stmt]],
) -> bool {
    let (recv, idx) = match expr {
        Expr::Index { recv, idx } => (recv.as_ref(), idx.as_ref()),
        Expr::Call { name, args } if is_array_get_name(name) && args.len() == 2 => {
            (&args[0], &args[1])
        }
        _ => return false,
    };
    if !idx_matches_counter(idx, counter_name) {
        return false;
    }
    if exprs_equivalent(recv, array_resolved) {
        return true;
    }
    // recv and array_resolved didn't structurally match. If recv is an
    // opaque Var (the un-inlined IR shape) try a chain hop and re-compare.
    // Shallow walk only: we want to reach a non-Var terminal that compares
    // structurally with `array_resolved`, not deep-substitute through
    // every sub-Var.
    if matches!(recv, Expr::Var(_)) {
        let recv_resolved = resolve_cond_chain(recv, scopes);
        return exprs_equivalent(recv_resolved, array_resolved);
    }
    false
}

/// Collect names that the loop counter goes by inside the body: the counter
/// itself plus any leading `Temp_int_* = counter` index-mirror.
///
/// Mirrors only appear at the very top of the body, so a small head scan
/// (matches the depth Blueprint emits) is sufficient. Walking the full body
/// here would risk picking up unrelated `Temp_int_*` writes that happen to
/// reference the counter for non-mirror reasons.
pub(super) fn collect_index_aliases(body: &[Stmt], counter_name: &str) -> Vec<String> {
    const HEAD_SCAN_LIMIT: usize = 4;
    let mut aliases: Vec<String> = vec![counter_name.to_string()];
    for stmt in body.iter().take(HEAD_SCAN_LIMIT) {
        if is_index_mirror(stmt, counter_name) {
            if let Stmt::Assignment { lhs, .. } = stmt {
                if let Some(name) = lhs_var_name(lhs) {
                    aliases.push(name.to_string());
                }
            }
        }
    }
    aliases
}

/// Match `Binary(Lt, Var(counter), Array_Length(array))`, optionally wrapped
/// in `Binary(And, break_flag_not, canonical)` (either order).
///
/// The break-flag-not shape covers Blueprint's ForEach-with-break trampoline,
/// which AND-guards the loop with `!Temp_bool_True_if_break_was_hit` so a
/// `break` inside the body falls through. The flag toggles via body-level
/// assignments that stay as plain Stmt::Assignment after refinement.
///
/// Chain-aware: when `cond` is an opaque `Var($X)` produced by the un-inlined
/// IR shape (i.e. `inline_single_use_temps` has not yet run, or runs after
/// recognition), the matcher walks the temp chain through `body` via
/// `resolve_var_chain` before structural matching. The chain may include both
/// the outer break-flag wrapper temp (`$BooleanAND_*`) and the inner cond temp
/// (`$Less_IntInt_*`); the matcher peels through both layers. The Lt's rhs
/// (the array-length operand) is then deep-resolved through
/// [`resolve_expr_chain`] so a further chain hop into `Call(Array_Length, _)`
/// reaches the canonical shape. The Lt's lhs is intentionally NOT
/// deep-resolved: it is the loop counter, which has an init definition
/// (`counter = 0`) in an ancestor scope. Resolving through the counter
/// would substitute the init literal and break the structural counter match.
pub(crate) fn match_foreach_cond(
    cond: &Expr,
    body: &[Stmt],
    ancestors: &[&[Stmt]],
) -> Option<(String, Expr)> {
    let scopes = scope_stack(body, ancestors);
    let resolved = resolve_cond_chain(cond, &scopes);
    // When `resolved` is `Binary{And, ...}`, peel the break-flag wrapper.
    // The And operands may themselves be opaque `Var($X)` references that
    // need a chain walk so the break-flag predicate (`Call("Not_PreBool", _)`
    // / `Unary{Not, _}`) and the canonical `Lt(counter, Array_Length(_))`
    // reveal their structural shape. Var-aliasing hops only (via
    // `resolve_var_chain`); we deliberately do NOT recurse into the
    // terminal expression's sub-Vars, because that would expand the loop
    // counter through its init definition in an ancestor scope.
    let break_flag_resolved = match resolved {
        Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::And,
            lhs,
            rhs,
        } => Some(Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::And,
            lhs: Box::new(resolve_cond_chain(lhs, &scopes).clone()),
            rhs: Box::new(resolve_cond_chain(rhs, &scopes).clone()),
        }),
        _ => None,
    };
    if let Some(deep_and) = &break_flag_resolved {
        if let Some(canonical) = peel_break_flag_and(deep_and) {
            return match_canonical_foreach_cond(canonical, &scopes);
        }
    }
    if let Some(canonical) = peel_break_flag_and(resolved) {
        let canonical = resolve_cond_chain(canonical, &scopes);
        return match_canonical_foreach_cond(canonical, &scopes);
    }
    match_canonical_foreach_cond(resolved, &scopes)
}

/// Walk a `Var($X)` cond reference through any number of scope-level temp
/// assignments and return the underlying non-`Var` expression. Returns the
/// input unchanged when the cond is already structural or the chain
/// dead-ends.
pub(super) fn resolve_cond_chain<'a>(cond: &'a Expr, scopes: &[&'a [Stmt]]) -> &'a Expr {
    match cond {
        Expr::Var(name) => resolve_var_chain(scopes, name).unwrap_or(cond),
        _ => cond,
    }
}

/// Match the bare `Binary(Lt, Var(counter), Array_Length(array))` shape.
///
/// When the Lt's rhs is itself an opaque `Var($X)`, the matcher chain-walks
/// it through `scopes` to its terminal expression. This handles the
/// pre-inline shape where the cond's chain hop reveals
/// `Lt(counter, Var($Length))` and `$Length` separately resolves to
/// `Call(Array_Length, _)`. The walk only fires when the rhs is a bare
/// `Var`, so a fully-inlined rhs (`Call(Array_Length, [Var(arr)])`) is
/// returned unchanged, preserving the user-facing array name even when
/// `arr` itself has an aliasing definition in scope.
fn match_canonical_foreach_cond(cond: &Expr, scopes: &[&[Stmt]]) -> Option<(String, Expr)> {
    let Expr::Binary {
        op: crate::bytecode::expr::BinaryOp::Lt,
        lhs,
        rhs,
    } = cond
    else {
        return None;
    };
    let counter_name = match lhs.as_ref() {
        Expr::Var(name) => name.clone(),
        Expr::FieldAccess { field, .. } => field.clone(),
        _ => return None,
    };
    // Shallow chain walk only when the rhs is a bare Var: a chain hop
    // through `$X = $Y; $Y = Call(Array_Length, _)` reaches the canonical
    // shape, but a deeper walk into the Call's args would substitute the
    // array name through its own scope-level aliases (NestedActors -> ...)
    // and change the user-facing array reference in the rendered ForEach.
    let rhs_resolved = resolve_cond_chain(rhs, scopes);
    let array_expr = match rhs_resolved {
        Expr::Call { name, args } if is_array_length_name(name) && args.len() == 1 => {
            args[0].clone()
        }
        Expr::MethodCall { recv, name, args } if is_array_length_name(name) && args.is_empty() => {
            (**recv).clone()
        }
        _ => return None,
    };
    Some((counter_name, array_expr))
}

/// True when `stmt` is the canonical bound-expr leak that precedes a
/// ForEach-promoted loop: `$temp = (counter < Array_Length(arr))` where `arr`
/// structurally equals the loop's `array` field.
///
/// Blueprint emits the loop's head condition (`counter < Array_Length(arr)`)
/// as a sibling before the loop. For a real for-loop that line stays as the
/// head cond; for a ForEach the loop renders `for (item in arr)` with no
/// condition, so the sibling is dead and must be dropped.
///
/// At this pass's stage the leaked line is the un-inlined shape
/// `$temp = (Temp_int_*_Counter < $Array_Length)`, where `$Array_Length`
/// separately resolves to `Array_Length(arr)` (counter folding and array
/// resolution happen later, in `inline_single_use_temps`). [`match_foreach_cond`]
/// chain-walks the Lt's rhs to the canonical `Array_Length(arr)` and yields the
/// resolved array; the match is then gated on `arr` structurally equalling the
/// loop's own `array`.
///
/// Both head-cond shapes match: the bare `Lt` a plain ForEach leaks and
/// the `$BooleanAND = (!break && (counter < Array_Length(...)))` And-wrapped
/// form a ForEach-with-break leaks. `match_foreach_cond` peels the
/// break-flag negation before falling through to the canonical matcher, so a
/// ForEach-with-break's dead head cond is dropped just like a plain ForEach's.
pub(super) fn is_foreach_bound_expr_leak(stmt: &Stmt, array: &Expr, scopes: &[&[Stmt]]) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    if !matches!(lhs, Expr::Var(name) if name.starts_with('$')) {
        return false;
    }
    match match_foreach_cond(rhs, &[], scopes) {
        Some((_, bound_array)) => exprs_equivalent(&bound_array, array),
        None => false,
    }
}

/// Remove the canonical bound-expr leak at `leak_idx`, then sweep the
/// now-dead `$`-temp probe defs it fed, transitively.
///
/// A plain ForEach leaks a two-link chain (`$Less_IntInt = (counter <
/// $Array_Length)` fed by `$Array_Length = Array_Length(arr)`). A
/// ForEach-with-break leaks a deeper one: `$BooleanAND = ($Not_PreBool &&
/// $Less_IntInt)`, where `$Less_IntInt` in turn feeds off `$Array_Length` and
/// `$Not_PreBool` is a third sibling. Removing only the leak orphans every def
/// it (transitively) consumed as a fresh standalone sibling. So sweep the whole
/// dead-temp closure: seed it with the leak's own `$`-refs, then repeatedly drop
/// any preceding `$`-temp def the closure reached whose remaining use-count is
/// zero, expanding the closure with that def's own `$`-refs. Iterate to a
/// fixpoint, removing one consumer can zero out the def that fed it.
///
/// The use-count gate keeps a shared probe alive: a nested ForEach-with-break's
/// array def (`$GetComponentsByClass`) is still read by the inner `for`, so its
/// count stays positive and it is not swept. The counter/index init lines
/// (`Temp_int_*`) are not `$`-temps and are left for the later inliner and
/// dead-statement removal, which drop them once their consumers are gone.
pub(super) fn drop_foreach_bound_expr_leak(stmts: &mut Vec<Stmt>, leak_idx: usize) {
    let mut dead_temps: Vec<String> = Vec::new();
    if let Stmt::Assignment { rhs, .. } = &stmts[leak_idx] {
        collect_var_refs_in_expr(rhs, &mut dead_temps);
    }
    dead_temps.retain(|name| name.starts_with('$'));
    stmts.remove(leak_idx);

    // The loop now sits at `leak_idx`; only the preceding siblings (`0..boundary`)
    // are sweep candidates, so the loop body and post-loop statements are never
    // touched.
    let mut boundary = leak_idx;
    loop {
        let mut removed_any = false;
        let mut idx = 0;
        while idx < boundary {
            let dead_refs = match &stmts[idx] {
                Stmt::Assignment {
                    lhs: Expr::Var(name),
                    rhs,
                    ..
                } if name.starts_with('$') && dead_temps.iter().any(|dead| dead == name) => {
                    if count_body_var_uses(stmts, name) > 0 {
                        None
                    } else {
                        let mut refs = Vec::new();
                        collect_var_refs_in_expr(rhs, &mut refs);
                        Some(refs)
                    }
                }
                _ => None,
            };
            match dead_refs {
                Some(refs) => {
                    for fed in refs {
                        if fed.starts_with('$') && !dead_temps.contains(&fed) {
                            dead_temps.push(fed);
                        }
                    }
                    stmts.remove(idx);
                    boundary -= 1;
                    removed_any = true;
                    // The next statement shifted into this slot; re-check it.
                }
                None => idx += 1,
            }
        }
        if !removed_any {
            break;
        }
    }
}

/// Match `counter = counter + 1` in the first increment statement.
///
/// Chain-aware: when the rhs is an opaque `Var($X)` (the un-inlined IR
/// shape), the matcher walks the temp chain through `body` via
/// `resolve_var_chain` and matches against the resolved `Binary{Add, ...}`.
/// The Add's rhs operand (the literal `1` slot) is then deep-resolved via
/// [`resolve_expr_chain`] so a chain hop through a `Var($one)` temp reaches
/// the canonical literal. The Add's lhs is intentionally NOT deep-resolved:
/// it must structurally match the loop counter, and resolving it would
/// substitute the counter's init definition from an ancestor scope.
pub(crate) fn match_foreach_increment(
    increment: &[Stmt],
    counter_name: &str,
    body: &[Stmt],
    ancestors: &[&[Stmt]],
) -> bool {
    let Some(Stmt::Assignment { lhs, rhs, .. }) = increment.first() else {
        return false;
    };
    if !lhs_matches_var(lhs, counter_name) {
        return false;
    }
    let scopes = scope_stack(body, ancestors);
    let resolved = resolve_cond_chain(rhs, &scopes);
    let Expr::Binary {
        op: crate::bytecode::expr::BinaryOp::Add,
        lhs: inner_lhs,
        rhs: inner_rhs,
    } = resolved
    else {
        return false;
    };
    if !lhs_matches_var(inner_lhs, counter_name) {
        return false;
    }
    let inner_rhs_resolved = resolve_cond_chain(inner_rhs, &scopes);
    is_one_literal(inner_rhs_resolved)
}

/// True for `Array_Get` and canonical aliases.
fn is_array_get_name(name: &str) -> bool {
    matches!(name, "Array_Get" | "GetArrayItem")
}

/// True when `stmt` is `Temp_int_* = counter` (an index-mirror line).
fn is_index_mirror(stmt: &Stmt, counter_name: &str) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    let Some(lhs_name) = lhs_var_name(lhs) else {
        return false;
    };
    if !lhs_name.starts_with("Temp_int_") {
        return false;
    }
    matches!(rhs, Expr::Var(name) if name == counter_name)
        || matches!(rhs, Expr::FieldAccess { field, .. } if field == counter_name)
}
