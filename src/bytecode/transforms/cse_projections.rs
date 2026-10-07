//! Common-subexpression elimination within one call's argument evaluation.
//!
//! A projection can read mutable fields even when it contains no calls.
//! Sharing it across statements or control-flow boundaries requires effects
//! and alias information that this IR does not carry.

use std::collections::BTreeSet;

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::name_shape::is_compiler_temp_name;
use crate::bytecode::transforms::visit::{
    any_expr, walk_body_exprs_visit_lhs, walk_stmt_children, walk_stmt_children_mut,
};

/// Cache repeated argument projections only when the first nonliteral
/// argument is the projection and every argument is free of calls and ABI
/// wrappers. The new read executes where its first original read did, and
/// no writes or calls can separate the remaining reads.
pub fn hoist_repeated_projections(body: &mut Vec<Stmt>) {
    let mut existing_names = collect_var_names_deep(body);
    let mut counter = 0;
    apply_hoist(body, &mut existing_names, &mut counter);
}

fn apply_hoist(body: &mut Vec<Stmt>, existing_names: &mut BTreeSet<String>, counter: &mut usize) {
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut |children| {
            apply_hoist(children, existing_names, counter);
        });
    }
    for stmt_idx in (0..body.len()).rev() {
        let Stmt::Call {
            func: Expr::Var(func),
            args,
            offset,
        } = &mut body[stmt_idx]
        else {
            continue;
        };
        if func.contains('.') || is_compiler_temp_name(func) || args.iter().any(contains_disallowed)
        {
            continue;
        }
        let Some(projection) = args.iter().find(|arg| !matches!(arg, Expr::Literal(_))) else {
            continue;
        };
        if !is_eligible(projection) {
            continue;
        }
        let derived = derive_name(projection);
        let threshold = if derived.is_some() { 2 } else { 3 };
        if args.iter().filter(|arg| *arg == projection).count() < threshold {
            continue;
        }
        let projection = projection.clone();
        let chosen_name = pick_name(derived, existing_names, &BTreeSet::new(), counter);
        existing_names.insert(chosen_name.clone());
        for arg in args {
            if *arg == projection {
                *arg = Expr::Var(chosen_name.clone());
            }
        }
        let synthetic = Stmt::Assignment {
            lhs: Expr::Var(chosen_name),
            rhs: projection,
            offset: *offset,
        };
        body.insert(stmt_idx, synthetic);
    }
}

fn is_eligible(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::FieldAccess { .. }
            | Expr::Index { .. }
            | Expr::Ternary { .. }
            | Expr::Binary { .. }
            | Expr::Unary { .. }
            | Expr::Cast { .. }
            | Expr::StructConstruct { .. }
            | Expr::Switch { .. }
    ) && !contains_disallowed(expr)
}

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

/// Collect references and definitions, including non-expression loop items,
/// so generated projection and loop names cannot shadow existing storage.
pub(crate) fn collect_var_names_deep(body: &[Stmt]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    walk_body_exprs_visit_lhs(body, &mut |expr| {
        if let Expr::Var(name) = expr {
            names.insert(name.clone());
        }
    });
    collect_var_names_in_body(body, &mut names);
    names
}

fn collect_var_names_in_body(body: &[Stmt], names: &mut BTreeSet<String>) {
    for stmt in body {
        if let Stmt::Loop {
            kind: LoopKind::ForEach { item, .. },
            ..
        } = stmt
        {
            names.insert(item.clone());
        }
        walk_stmt_children(stmt, &mut |children| {
            collect_var_names_in_body(children, names)
        });
    }
}
