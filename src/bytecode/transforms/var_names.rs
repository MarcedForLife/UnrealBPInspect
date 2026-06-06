//! Variable name normalisation for the IR.
//!
//! Renames synthetic variable names that the Blueprint compiler emits to
//! shorter, more readable alternatives. Two classes are handled:
//!
//! - **ForC counter variables**: the iteration counter in a
//!   `Stmt::Loop { kind: LoopKind::ForC { .. }, .. }` carries a name like
//!   `Temp_int_Loop_Counter_Variable_3` (real BP compiler) or `Temp_int_var_3`
//!   (synthetic test names). These are renamed to `i`, `j`, `k`, ... by
//!   nesting depth. The depth counter resets at each body boundary (per
//!   function or event), so the outermost loop always gets `i`.
//!
//! - **Struct-construction temporaries**: when a
//!   `Stmt::Assignment { lhs: Expr::Var(name), rhs: Expr::StructConstruct { type_name, .. } }`
//!   assigns into a var matching `Temp_struct_var_<N>`, the var is renamed to
//!   a short form derived from `type_name` (stripping a leading `F` for UE
//!   struct types, e.g. `FVector` -> `Vector`). All subsequent uses of the
//!   old name in the same body are updated. Skips when `type_name` is the
//!   `<unknown>` placeholder emitted by struct-fold before the decoder
//!   threads the originating type through.

use std::collections::BTreeMap;

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::cse_projections::collect_var_names_deep;
use crate::bytecode::transforms::visit::{peel_transparent, walk_stmt_exprs_mut_visit_lhs, Action};

/// Prefixes used by the Blueprint compiler for integer loop counter temporaries.
///
/// The real BP compiler emits `Temp_int_Loop_Counter_Variable_N`. The
/// synthetic `Temp_int_var_N` prefix is kept as a fallback for unit tests
/// that build loops with short names.
const TEMP_INT_PREFIXES: &[&str] = &["Temp_int_Loop_Counter_Variable_", "Temp_int_var_"];

/// Prefix used for struct-construction temporaries.
const TEMP_STRUCT_PREFIX: &str = "Temp_struct_var_";

/// Placeholder emitted by struct_fold when the struct type is not yet known.
pub(super) const UNKNOWN_TYPE_NAME: &str = "<unknown>";

/// Sequence of names assigned to ForC counter variables by nesting depth.
/// Depth 0 => "i", depth 1 => "j", depth 2 => "k", beyond => "loop_<N>".
pub(super) fn counter_name_at_depth(depth: usize) -> String {
    match depth {
        0 => "i".to_string(),
        1 => "j".to_string(),
        2 => "k".to_string(),
        other => format!("loop_{}", other),
    }
}

/// Derive a short name for a struct-construction temporary from `type_name`.
///
/// Strips a leading `F` when the name starts with an uppercase letter after it
/// (the UE naming convention for structs, e.g. `FVector` -> `Vector`).
/// If `type_name` is the unknown placeholder, returns `None`.
pub(super) fn struct_short_name(type_name: &str) -> Option<String> {
    if type_name == UNKNOWN_TYPE_NAME || type_name.is_empty() {
        return None;
    }
    let stripped = if let Some(after_f) = type_name.strip_prefix('F') {
        if after_f.starts_with(|c: char| c.is_ascii_uppercase()) {
            after_f
        } else {
            type_name
        }
    } else {
        type_name
    };
    Some(stripped.to_string())
}

/// Normalise synthetic variable names in a statement body.
///
/// Scoped per body: renames do not propagate outside. Should run last in the
/// transform pipeline (after all folding and inlining) so renamed vars don't
/// confuse earlier passes.
pub fn normalize_var_names(body: &mut [Stmt]) {
    let mut depth = 0usize;
    normalize_body(body, &mut depth);
}

fn normalize_body(body: &mut [Stmt], loop_depth: &mut usize) {
    // First collect struct-temp renames at this level so we can apply them
    // to the full body slice, then process individual statements for ForC
    // and nested bodies.
    let struct_renames = collect_struct_renames(body);
    if !struct_renames.is_empty() {
        apply_renames_to_body(body, &struct_renames);
    }

    let mut idx = 0;
    while idx < body.len() {
        match &body[idx] {
            Stmt::Loop {
                kind: LoopKind::ForC { .. },
                ..
            } => {
                // Extract the counter var from the increment body, rename it,
                // then recurse into the loop's sub-bodies at the next depth.
                let old_name = forc_counter_name(&body[idx]);
                let new_name = old_name
                    .as_deref()
                    .filter(|name| {
                        TEMP_INT_PREFIXES
                            .iter()
                            .any(|prefix| name.starts_with(prefix))
                    })
                    .map(|_| counter_name_at_depth(*loop_depth));

                if let Some(new) = new_name {
                    let old = old_name.unwrap();
                    // Rename within this loop statement only (scoped).
                    rename_in_stmt(&mut body[idx], &old, &new);
                }

                // Recurse into nested bodies at increased depth.
                *loop_depth += 1;
                recurse_stmt_bodies(&mut body[idx], loop_depth);
                *loop_depth -= 1;
            }
            Stmt::Loop {
                kind: LoopKind::ForEach { item, array },
                body: loop_body,
                ..
            } => {
                // The strip pass left the index-fetch lhs (Blueprint
                // compiler temp like `$Array_Get_Item`) as the loop item.
                // Derive a friendly singular name from the iterated array
                // (e.g. `NestedActors` -> `NestedActor`, hit-result arrays
                // -> `hit`), within this loop only.
                let old_name = item.clone();
                if old_name.starts_with('$') {
                    let new_name = derive_foreach_item_name(array, loop_body);
                    rename_in_stmt(&mut body[idx], &old_name, &new_name);
                }

                *loop_depth += 1;
                recurse_stmt_bodies(&mut body[idx], loop_depth);
                *loop_depth -= 1;
            }
            _ => {
                recurse_stmt_bodies(&mut body[idx], loop_depth);
            }
        }
        idx += 1;
    }
}

/// Derive a friendly ForEach item name from the iterated `array`:
///
/// - hit-result arrays (compiler temps ending `OutHits`/`Hits`) -> `hit`;
/// - a plain plural array variable (trailing lowercase `s`) -> de-pluralized
///   (`NestedActors` -> `NestedActor`);
/// - anything else -> `item`.
///
/// A leading `self.` qualifier on the array name is dropped before
/// de-pluralizing, so a member array like `self.OverlappingActors` yields the
/// unqualified `OverlappingActor` the editor shows, not `self.OverlappingActor`.
///
/// Falls back to `item` when the derived name already appears as a variable
/// in the loop body (collision), or when `array` is not a bare variable
/// (method-call / field-access sources have no clean singular form). The
/// decoder shortens method-call array sources to `$`-prefixed temps, so the
/// de-pluralize branch is gated to real (non-`$`) variable names to avoid
/// mangling temps like `$GetComponentsByClass`.
pub(super) fn derive_foreach_item_name(array: &Expr, loop_body: &[Stmt]) -> String {
    let item_fallback = || "item".to_string();
    let Expr::Var(raw) = peel_transparent(array) else {
        return item_fallback();
    };
    let had_dollar = raw.starts_with('$');
    let unqualified = raw.strip_prefix('$').unwrap_or(raw);
    let base = unqualified.strip_prefix("self.").unwrap_or(unqualified);

    let candidate = if had_dollar && (base.ends_with("OutHits") || base.ends_with("Hits")) {
        "hit".to_string()
    } else if !had_dollar
        && base.len() >= 4
        && base.ends_with('s')
        && base.as_bytes()[base.len() - 2].is_ascii_lowercase()
    {
        base[..base.len() - 1].to_string()
    } else {
        return item_fallback();
    };

    if collect_var_names_deep(loop_body).contains(&candidate) {
        return item_fallback();
    }
    candidate
}

/// Extract the counter variable name from a `Stmt::Loop { kind: ForC { .. } }`.
///
/// The counter is identified as the variable assigned in the increment body.
/// The increment body for a ForC loop contains `VAR = VAR + 1` (or similar).
/// Returns the lhs var name if exactly one assignment target appears in the
/// increment body. Returns `None` if the shape is ambiguous or absent.
fn forc_counter_name(stmt: &Stmt) -> Option<String> {
    let Stmt::Loop {
        kind: LoopKind::ForC { increment, .. },
        ..
    } = stmt
    else {
        return None;
    };

    // Collect all distinct vars assigned in the increment body.
    let mut assigned: Vec<String> = increment
        .iter()
        .filter_map(|inc_stmt| {
            if let Stmt::Assignment {
                lhs: Expr::Var(name),
                ..
            } = inc_stmt
            {
                Some(name.clone())
            } else {
                None
            }
        })
        .collect();
    assigned.dedup();
    assigned.sort();

    if assigned.len() == 1 {
        Some(assigned.into_iter().next().unwrap())
    } else {
        None
    }
}

/// Collect struct-temp renames from a body.
///
/// Scans for `Stmt::Assignment { lhs: Expr::Var(name), rhs: Expr::StructConstruct { type_name, .. } }`
/// where `name` starts with `Temp_struct_var_`. Returns a map from old name
/// to new name. When multiple temps derive the same base name, appends a
/// counter suffix to keep them distinct.
fn collect_struct_renames(body: &[Stmt]) -> BTreeMap<String, String> {
    let mut renames: BTreeMap<String, String> = BTreeMap::new();
    // Track how many times each base name has been used to avoid clashes.
    let mut base_counts: BTreeMap<String, usize> = BTreeMap::new();

    for stmt in body {
        let (old_name, type_name) = match stmt {
            Stmt::Assignment {
                lhs: Expr::Var(name),
                rhs: Expr::StructConstruct { type_name, .. },
                ..
            } if name.starts_with(TEMP_STRUCT_PREFIX) => (name, type_name),
            _ => continue,
        };

        let Some(base) = struct_short_name(type_name) else {
            continue;
        };

        let count = base_counts.entry(base.clone()).or_insert(0);
        let new_name = if *count == 0 {
            base.clone()
        } else {
            format!("{}_{}", base, count)
        };
        *count += 1;

        renames.insert(old_name.clone(), new_name);
    }

    renames
}

/// Apply a set of variable renames to every statement in a body slice.
fn apply_renames_to_body(body: &mut [Stmt], renames: &BTreeMap<String, String>) {
    for stmt in body.iter_mut() {
        for (old, new) in renames {
            rename_in_stmt(stmt, old, new);
        }
    }
}

/// Recurse into nested sub-bodies of a statement, calling `normalize_body`
/// on each, but skipping the ForC top-level handling (that's done by the
/// caller for the ForC statement itself).
fn recurse_stmt_bodies(stmt: &mut Stmt, loop_depth: &mut usize) {
    match stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            normalize_body(then_body, loop_depth);
            normalize_body(else_body, loop_depth);
        }
        Stmt::Sequence { pins, .. } => {
            for pin_body in pins.iter_mut() {
                normalize_body(pin_body, loop_depth);
            }
        }
        Stmt::Loop {
            kind,
            body,
            completion,
            ..
        } => {
            // ForC: the increment and init are handled by the caller (counter rename).
            // We still need to recurse into the loop body and completion.
            if let LoopKind::ForC { init, increment } = kind {
                normalize_body(init, loop_depth);
                normalize_body(increment, loop_depth);
            }
            normalize_body(body, loop_depth);
            if let Some(comp) = completion {
                normalize_body(comp, loop_depth);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for case in cases.iter_mut() {
                normalize_body(&mut case.body, loop_depth);
            }
            if let Some(default_body) = default {
                normalize_body(default_body, loop_depth);
            }
        }
        Stmt::Latch { init, body, .. } => {
            normalize_body(init, loop_depth);
            normalize_body(body, loop_depth);
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

/// Rename all `Expr::Var(old)` occurrences to `new` within a single statement,
/// including expressions and nested sub-bodies. Also renames the
/// `LoopKind::ForEach::item` slot (a String, not an Expr, so it isn't
/// reachable through the visitor).
fn rename_in_stmt(stmt: &mut Stmt, old: &str, new: &str) {
    if let Stmt::Loop {
        kind: LoopKind::ForEach { item, .. },
        ..
    } = stmt
    {
        if item == old {
            *item = new.to_string();
        }
    }
    walk_stmt_exprs_mut_visit_lhs(stmt, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == old {
                *name = new.to_string();
            }
        }
        Action::Continue
    });
}
