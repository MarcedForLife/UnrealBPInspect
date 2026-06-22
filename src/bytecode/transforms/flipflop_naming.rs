//! FlipFlop display-name derivation pass.
//!
//! After `recognize_latches` has rewritten the FlipFlop shape into a
//! `Stmt::Latch { kind: FlipFlop { gate_var, names: None }, .. }`, this
//! pass scans each FlipFlop body for the user-visible alias-set
//! assignment that the Blueprint editor wires to the toggle's output pin
//! (`<lhs> = <gate_var>`). The lhs's identifier is the user-facing
//! display name.
//!
//! When a name is derived, every reference to `gate_var` inside the
//! FlipFlop body is rewritten to `$<name>_IsA`, the
//! `$FlipFlop_<name>_IsA` convention with the redundant `FlipFlop_`
//! segment dropped (the `$` prefix already marks the synthetic).
//!
//! When no alias-set is present, `names` stays `None` and the emitter
//! falls back to its legacy `FlipFlop("<gate_var>")` rendering.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::visit::{rewrite_stmts_postorder, walk_body_exprs_mut, Action};

/// Suffix appended to the derived display name when renaming gate-var
/// references inside a FlipFlop body. The `$FlipFlop_<name>_IsA`
/// convention with the redundant `FlipFlop_` segment dropped.
const IS_A_SUFFIX: &str = "_IsA";

/// Walk every `Stmt::Latch::FlipFlop` in `body`, deriving a display name
/// from any alias-set assignment in its body and rewriting `gate_var`
/// references to `$<name>_IsA`.
///
/// Recurses into every nested sub-body (Branch arms, Sequence pins, Loop
/// body/completion, ForC init/increment, Switch case bodies, Latch
/// init/body) so FlipFlops nested inside other constructs are handled
/// alongside top-level ones.
pub fn derive_flipflop_names(body: &mut [Stmt]) {
    // Bottom-up: name nested FlipFlops before their enclosing one, so a
    // FlipFlop's alias-set scan sees inner names already settled.
    rewrite_stmts_postorder(body, &mut |stmt| derive_in_stmt(stmt));
}

fn derive_in_stmt(stmt: &mut Stmt) {
    if let Stmt::Latch {
        kind: LatchKind::FlipFlop { gate_var, names },
        body,
        ..
    } = stmt
    {
        if names.is_some() {
            return;
        }
        if let Some(display_name) = derive_display_name(body, gate_var) {
            let renamed_var = format!("${}{}", display_name, IS_A_SUFFIX);
            rename_var_in_stmts(body, gate_var, &renamed_var);
            *names = Some((display_name.clone(), display_name));
        }
    }
}

/// Scan `body` for an alias-set assignment of the shape
/// `<lhs> = Var(gate_var)` and derive the display name from `<lhs>`.
///
/// The lhs may be `self.<field>` (FieldAccess on `self`), a bare
/// `Var(name)`, or a deeper `FieldAccess` chain. The name returned is
/// the trailing field segment for FieldAccess, the variable name for
/// Var.
///
/// Returns `None` when no alias-set assignment is found, which leaves
/// the FlipFlop's `names` slot at `None` so the emitter renders the
/// legacy `FlipFlop("<gate_var>")` form.
fn derive_display_name(body: &[Stmt], gate_var: &str) -> Option<String> {
    for stmt in body {
        if let Some(name) = alias_target_name(stmt, gate_var) {
            return Some(name);
        }
        // The recognizer wraps consumers in an inner Branch (then=consumers,
        // else=[]); the alias-set can live one level down.
        if let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = stmt
        {
            for inner in then_body.iter().chain(else_body.iter()) {
                if let Some(name) = alias_target_name(inner, gate_var) {
                    return Some(name);
                }
            }
        }
    }
    None
}

/// Return the derived display name when `stmt` is `<lhs> = Var(gate_var)`.
fn alias_target_name(stmt: &Stmt, gate_var: &str) -> Option<String> {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return None;
    };
    let Expr::Var(rhs_name) = rhs else {
        return None;
    };
    if rhs_name != gate_var {
        return None;
    }
    name_from_lhs(lhs)
}

/// Extract a display-name identifier from an assignment lhs.
///
/// - `Expr::FieldAccess { recv, field }` returns the trailing field name
///   (`self.<field>` -> `<field>`).
/// - `Expr::Var("self.<field>")` (the decoder's on-disk shape for an
///   `EX_INSTANCE_VARIABLE` lhs before any later FieldAccess folding)
///   returns `<field>`.
/// - `Expr::Var(name)` returns `name`.
/// - Anything else (Index, Cast, etc.) returns `None`.
fn name_from_lhs(lhs: &Expr) -> Option<String> {
    match lhs {
        Expr::FieldAccess { field, .. } => Some(field.clone()),
        Expr::Var(name) => {
            if let Some(field) = name.strip_prefix("self.") {
                Some(field.to_string())
            } else {
                Some(name.clone())
            }
        }
        _ => None,
    }
}

/// Replace every `Expr::Var(old)` use reference within `stmts` (and every
/// nested sub-statement / sub-expression) with `Expr::Var(new)`. Skips
/// Assignment lhs by virtue of the shared walker's lhs-skip semantics;
/// the callers here only ever rename a synthetic `gate_var` that is the
/// definition source for the alias-set, so its lhs occurrences (the
/// `<lhs> = Var(gate_var)` itself) are not consumers and preserving them
/// is intentional.
fn rename_var_in_stmts(stmts: &mut [Stmt], old: &str, new: &str) {
    walk_body_exprs_mut(stmts, &mut |expr: &mut Expr| {
        if let Expr::Var(name) = expr {
            if name == old {
                *name = new.to_string();
            }
        }
        Action::Continue
    });
}
