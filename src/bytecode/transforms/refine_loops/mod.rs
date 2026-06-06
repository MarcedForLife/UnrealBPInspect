//! Loop refinement for the IR.
//!
//! At decode time every loop is classified as `LoopKind::While` because the
//! condition expression is often a temp-var reference (`Expr::Var($Less_IntInt)`)
//! rather than the expanded binary form.
//!
//! This pass runs BEFORE `inline_single_use_temps` (see the transform-stack
//! order in `decode::mod`), so the condition and increment still appear as
//! `Var` references to local temp definitions. The matchers are chain-aware:
//! they walk those `Var` references through the loop body and `ancestors`
//! scopes (via `resolve_var_chain` / `resolve_cond_chain`) to recover the
//! canonical `counter < Array_Length(array)` shape themselves, rather than
//! relying on inlining to have collapsed it.
//!
//! This pass walks the statement tree and refines `LoopKind::While` nodes into:
//!
//! - `LoopKind::ForC { increment }` — when the trailing body statement is an
//!   assignment whose lhs appears in the condition (counter increment pattern).
//! - `LoopKind::ForEach { item, array }` — when the condition matches
//!   `counter < Array_Length(array)` with a matching increment. The item name
//!   comes from the body's `array[counter]` fetch, or is synthesized from the
//!   array when the iterated element is unused (no fetch emitted).

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit::walk_bodies_with_ancestors_mut;

mod cond_recompute;
mod for_break;
mod foreach;
mod helpers;

use cond_recompute::*;
use for_break::*;
use foreach::*;
use helpers::*;

// Re-exported for the sibling `refine_loops_tests` module, which references
// these matchers as `refine_loops::X`.
#[cfg(test)]
pub(super) use cond_recompute::strip_trailing_cond_recomputation;
#[cfg(test)]
pub(super) use foreach::{match_foreach_cond, match_foreach_increment};
#[cfg(test)]
pub(super) use helpers::exprs_equivalent;

/// Walk a statement body, refining `LoopKind::While` nodes whose post-inline
/// condition reveals a ForC or ForEach pattern, and absorbing the
/// immediately-preceding counter assignment into each ForC's `init` field.
pub fn refine_loops(stmts: &mut Vec<Stmt>) {
    refine_loops_vec(stmts, &[]);
}

/// Walk a `Vec<Stmt>` body, refining While nodes and also absorbing the
/// immediately-preceding counter assignment into each ForC's `init` field.
///
/// `ancestors` is innermost-first: each slice is the preceding-siblings
/// view at one outer nesting level. Chain-resolution probes (cond, increment)
/// search the loop body plus `ancestors` so a temp def emitted in the
/// parent body still resolves.
pub(super) fn refine_loops_vec(stmts: &mut Vec<Stmt>, ancestors: &[&[Stmt]]) {
    // Two-pass: first collect (index, counter_var) for every ForC candidate,
    // then walk backwards absorbing predecessors, then recurse.
    //
    // We process all refinements first (so we know which loops become ForC),
    // then absorb predecessors by walking backwards through the index list.
    // Backwards traversal ensures that when we remove a predecessor, we don't
    // corrupt the indices of earlier absorptions.

    // Refine all statements in place. Each stmt sees a scope stack that
    // includes its preceding siblings as the innermost ancestor, then the
    // outer ancestors passed in.
    walk_bodies_with_ancestors_mut(stmts, ancestors, &mut |stmt, child_ancestors| {
        refine_one(stmt, child_ancestors);
    });

    // Collect indices of loops whose preceding sibling is an absorbable
    // pre-loop statement: ForC's counter-init line and ForEach's canonical
    // bound-expr leak. We scan from the end and process in reverse so that
    // removing a predecessor never shifts the index of a loop we haven't
    // processed yet.
    let absorb_indices: Vec<usize> = stmts
        .iter()
        .enumerate()
        .filter_map(|(idx, stmt)| {
            if matches!(
                stmt,
                Stmt::Loop {
                    kind: LoopKind::ForC { .. } | LoopKind::ForEach { .. },
                    ..
                }
            ) {
                Some(idx)
            } else {
                None
            }
        })
        .collect();

    for loop_idx in absorb_indices.into_iter().rev() {
        if loop_idx == 0 {
            continue; // No predecessor possible.
        }

        // ForEach drops its leaked canonical bound-expr sibling (the head
        // cond a real for-loop would keep; a ForEach has `cond = None` and no
        // editor-graph counterpart for it). The sibling is always the
        // immediate predecessor, gated on the loop's own `array` field.
        if matches!(
            &stmts[loop_idx],
            Stmt::Loop {
                kind: LoopKind::ForEach { .. },
                ..
            }
        ) {
            let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
            scopes.push(stmts.as_slice());
            scopes.extend(ancestors.iter().copied());
            let Stmt::Loop {
                kind: LoopKind::ForEach { array, .. },
                ..
            } = &stmts[loop_idx]
            else {
                unreachable!("guarded by the matches! above")
            };
            if is_foreach_bound_expr_leak(&stmts[loop_idx - 1], array, &scopes) {
                drop_foreach_bound_expr_leak(stmts, loop_idx - 1);
            }
            continue;
        }

        // A ForLoopWithBreak-promoted ForC leaks the And-guarded head cond
        // (`$BooleanAND = (!break_flag && (counter <= last))`) as a dead
        // sibling immediately before the loop (the loop now carries the bound
        // in its own cond). Drop it, transitively sweeping the break-flag
        // `$`-temps it fed, before the counter-init scan. The use-count gate in
        // the sweep keeps the surviving bound temp (`$LessEqual_IntInt`, now the
        // loop cond) alive. Reuses `drop_foreach_bound_expr_leak`, which is a
        // generic transitive `$`-temp closure sweep from `leak_idx`.
        let mut loop_idx = loop_idx;
        {
            let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
            scopes.push(stmts.as_slice());
            scopes.extend(ancestors.iter().copied());
            if is_for_break_bound_leak(&stmts[loop_idx - 1], &scopes) {
                let before = stmts.len();
                drop_foreach_bound_expr_leak(stmts, loop_idx - 1);
                // The sweep removed the leak plus any dead `$`-temps it fed,
                // all sitting before the loop. Shift the loop index down by the
                // number of removed statements so the counter-init scan below
                // operates on the post-sweep positions.
                loop_idx -= before - stmts.len();
            }
            if loop_idx == 0 {
                continue;
            }
        }

        // Extract the counter var name from the increment body.
        let counter_var = match forc_increment_counter(&stmts[loop_idx]) {
            Some(name) => name,
            None => continue,
        };

        // Scan backward from loop_idx - 1, skipping over intermediate
        // temp-alias assignments. The scan's intent is to find the counter
        // init line (e.g. `counter = 0`); intermediate temps may sit
        // between the init and the loop header in two shapes:
        //
        //   - `$Array_Length = MethodCall(...)` — Blueprint's pre-loop
        //     probes (dollar-prefixed compiler temps).
        //   - `$X = ...; Temp_int_Y = $X` — chain-aliased temps when the
        //     inliner has not yet collapsed them (they stay as siblings of
        //     the loop until the inliner cleans up).
        //
        // Skip past any inline-candidate-eligible name that isn't the
        // counter; halt on the counter init (absorb), an unrelated non-
        // candidate assignment, or any non-Assignment statement (give up).
        let mut scan = loop_idx - 1;
        let init_idx = loop {
            match &stmts[scan] {
                Stmt::Assignment { lhs, .. } => {
                    let lhs_name = stmt_lhs_name(lhs).unwrap_or("");
                    if lhs_name == counter_var {
                        break Some(scan);
                    }
                    if is_intermediate_temp_name(lhs_name) {
                        if scan == 0 {
                            break None;
                        }
                        scan -= 1;
                        continue;
                    }
                    // Non-temp, non-counter assignment — give up.
                    break None;
                }
                // Any non-assignment statement — give up.
                _ => break None,
            }
        };

        let init_idx = match init_idx {
            Some(idx) => idx,
            None => continue,
        };

        // Remove the counter-init statement and place it in the loop's init field.
        // Because we're iterating forc_indices in reverse, the loop's position
        // in `stmts` is still `loop_idx`. After removing init_idx (which is
        // before loop_idx), the loop shifts to loop_idx - 1.
        let init_stmt = stmts.remove(init_idx);
        let new_loop_idx = loop_idx - 1;
        if let Stmt::Loop {
            kind: LoopKind::ForC { init, .. },
            ..
        } = &mut stmts[new_loop_idx]
        {
            init.push(init_stmt);
        }
    }
}

fn refine_one(stmt: &mut Stmt, ancestors: &[&[Stmt]]) {
    match stmt {
        Stmt::Loop {
            kind: kind @ LoopKind::While,
            cond,
            body,
            completion,
            ..
        } => {
            // Try ForEach first — it's the more specific shape and subsumes ForC.
            let cond_expr = match cond {
                Some(expr) => expr,
                None => {
                    // No cond to inspect; recurse into body.
                    refine_loops_vec(body, ancestors);
                    if let Some(comp) = completion {
                        refine_loops_vec(comp, ancestors);
                    }
                    return;
                }
            };

            // Check if we can extract a counter increment from the trailing body.
            let increment = extract_increment(body, cond_expr, ancestors);

            if let Some(inc_stmts) = increment {
                // Try ForEach refinement on the resulting ForC shape.
                if let Some((item, array)) =
                    match_foreach_shape(cond_expr, &inc_stmts, body, ancestors)
                {
                    // Collect the counter aliases before stripping (which
                    // drops the defining fetch and may remove the
                    // index-mirror the alias scan reads).
                    let counter_aliases = match_foreach_cond(cond_expr, body, ancestors)
                        .map(|(counter, _)| collect_index_aliases(body, &counter));
                    // Whether the item-binding fetch sits at the TOP level of
                    // the body. When it does NOT, the binding was found by the
                    // nested fallback (the DoOnce-in-ForEach shape, where the
                    // fetch lives inside a Latch body that
                    // `strip_foreach_boilerplate`'s top-level scan cannot
                    // reach), so the leftover nested fetch needs substituting.
                    let item_binding_nested = counter_aliases
                        .as_ref()
                        .map(|aliases| {
                            let alias_refs: Vec<&str> =
                                aliases.iter().map(String::as_str).collect();
                            let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
                            scopes.push(body.as_slice());
                            scopes.extend(ancestors.iter().copied());
                            find_item_binding_in_stmts(body, &alias_refs, &array, &scopes).is_none()
                        })
                        .unwrap_or(false);
                    // Drop the index-fetch line from the body before mutating kind.
                    strip_foreach_boilerplate(body, &item, &array, cond_expr, ancestors);
                    // Substitute any remaining `array[counter]` index-fetch
                    // occurrences with the loop var. Two shapes need this:
                    //   - multi-break: a second fetch nested inside a
                    //     loop-break guard's branch body (the body carries a
                    //     `Stmt::Break`, which only that recovery emits).
                    //   - DoOnce-in-ForEach: the item-binding fetch is itself
                    //     nested inside a Latch body (`item_binding_nested`),
                    //     so the top-level strip left it.
                    // A plain ForEach whose PRIMARY fetch is at top level (even
                    // with an unrelated nested re-fetch) stays untouched: the
                    // strip removes the top-level fetch and neither gate fires.
                    if body_contains_break(body) || item_binding_nested {
                        if let Some(aliases) = &counter_aliases {
                            substitute_foreach_fetches(body, &array, aliases, &item, ancestors);
                        }
                    }
                    *kind = LoopKind::ForEach { item, array };
                    *cond = None;
                    refine_loops_vec(body, ancestors);
                    if let Some(comp) = completion {
                        refine_loops_vec(comp, ancestors);
                    }
                    return;
                }

                // A counter-only WHILE loop (body is nothing but the counter
                // increment) is a `while`, not a `for`. Promoting it to ForC
                // hoists its sole statement into the increment slot and leaves
                // an empty body, which the editor never shows. Keep it a While
                // and restore the increment as the body. Real ForC loops carry
                // user code beyond the increment, so extraction leaves a
                // non-empty body and this guard does not fire.
                if body.is_empty() {
                    *body = inc_stmts;
                    refine_loops_vec(body, ancestors);
                    if let Some(comp) = completion {
                        refine_loops_vec(comp, ancestors);
                    }
                    return;
                }

                // Plain ForC — put the increment into the kind.
                *kind = LoopKind::ForC {
                    init: vec![],
                    increment: inc_stmts,
                };
                refine_loops_vec(body, ancestors);
                if let Some(comp) = completion {
                    refine_loops_vec(comp, ancestors);
                }
            } else if try_promote_for_loop_with_break(kind, cond, body, ancestors) {
                // Promoted a ForLoopWithBreak (And-guarded head cond plus a
                // trailing break-flag-guard increment region) to ForC. The
                // helper rewrote `kind`, `cond`, and `body`; recurse into the
                // refined body and completion.
                refine_loops_vec(body, ancestors);
                if let Some(comp) = completion {
                    refine_loops_vec(comp, ancestors);
                }
            } else {
                // Stays While — recurse into body.
                refine_loops_vec(body, ancestors);
                if let Some(comp) = completion {
                    refine_loops_vec(comp, ancestors);
                }
            }
        }

        // For already-classified loops, just recurse into sub-bodies.
        Stmt::Loop {
            body, completion, ..
        } => {
            refine_loops_vec(body, ancestors);
            if let Some(comp) = completion {
                refine_loops_vec(comp, ancestors);
            }
        }

        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            refine_loops_vec(then_body, ancestors);
            refine_loops_vec(else_body, ancestors);
        }

        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter_mut() {
                refine_loops_vec(pin_body, ancestors);
            }
        }

        Stmt::Switch { cases, default, .. } => {
            for case in cases.iter_mut() {
                refine_loops_vec(&mut case.body, ancestors);
            }
            if let Some(default_body) = default {
                refine_loops_vec(default_body, ancestors);
            }
        }

        Stmt::Latch { init, body, .. } => {
            refine_loops_vec(init, ancestors);
            refine_loops_vec(body, ancestors);
        }

        // Leaves: no sub-bodies.
        Stmt::Assignment { .. }
        | Stmt::Call { .. }
        | Stmt::Return { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
}

/// If the last statement in `body` is an `Assignment` whose lhs name appears
/// in `cond`, drain it (and any further trailing assignments to the same var)
/// into a separate Vec and return it. Otherwise return `None`.
///
/// The "lhs referenced in cond" rule distinguishes While (no counter) from
/// ForC (counter increment at the trailing tail).
///
/// Chain-aware: when `cond` is an opaque `Var($X)` produced by the un-inlined
/// IR shape, the reference check walks each `Var` through the body's temp
/// chain via `expr_references_var_chain` so the orchestrator gate accepts
/// both pre-inline and post-inline cond shapes (including the multi-layer
/// break-flag-AND wrapper used by ForEach trampolines).
pub(super) fn extract_increment(
    body: &mut Vec<Stmt>,
    cond: &Expr,
    ancestors: &[&[Stmt]],
) -> Option<Vec<Stmt>> {
    // Blueprint emits a tail-of-iteration recomputation of the loop cond at
    // the end of every Loop body so the back-edge JumpIfNot can read a
    // fresh value. These assignments survive into refine_loops (the inliner
    // runs after). Strip the trailing run of cond recomputations before the
    // counter-increment extraction so this pass does not greedily absorb
    // plumbing into the increment slot.
    strip_trailing_cond_recomputation(body, cond, ancestors);

    let last_lhs_name = body
        .last()
        .and_then(stmt_assignment_lhs_name)
        .map(str::to_string)?;
    // Build the chain-resolution scope stack used by the cond reference
    // walk: loop body innermost, then ancestors. The chain may hop through
    // a temp def in the parent body (e.g. real for-loop scaffold emitting
    // `$Less_IntInt = i < n` as a sibling of the Loop).
    let mut scopes: Vec<&[Stmt]> = Vec::with_capacity(ancestors.len() + 1);
    scopes.push(body.as_slice());
    scopes.extend(ancestors.iter().copied());
    if !expr_references_var_chain(cond, &last_lhs_name, &scopes) {
        return None;
    }
    let mut increment = Vec::new();
    loop {
        let trailing_name = body.last().and_then(stmt_assignment_lhs_name);
        if trailing_name != Some(last_lhs_name.as_str()) {
            break;
        }
        if let Some(stmt) = body.pop() {
            increment.insert(0, stmt);
        } else {
            break;
        }
    }
    if increment.is_empty() {
        return None;
    }
    // Pre-inline shape: the increment use (`counter = $Add_IntInt_1`) just
    // moved into the increment slot, but the def (`$Add_IntInt_1 = Binary{Add,
    // counter, 1}`) is still in body. After this pass returns, dead-stmt's
    // body-scoped use scan would sweep the def out (the use moved to a sibling
    // slot, invisible to body-scoped scans), leaving the increment expression
    // referencing a deleted temp. Substitute body-local single-use temps into
    // the increment now and drop their defs from body so the increment slot is
    // self-contained.
    inline_body_temps_into_increment(&mut increment, body);
    Some(increment)
}
