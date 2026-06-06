//! Init-check / scaffold-sequence cleanup passes. Peels the init/gate-check
//! `Branch` wrappers and `Sequence` scaffolding the region-decode path can
//! leave around a recognized `Stmt::Latch::DoOnce`, and strips phantom
//! init-guard latches.

use super::shared::{
    classify_doonce_role, is_doonce_latch, is_doonce_scaffold_assignment, is_reset_doonce_call,
    DoOnceRole, DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::visit::walk_stmt_children_mut;

/// Walk the body tree replacing `Branch{cond: Var(init/gate prefix),
/// then: [<Latch::DoOnce>...], else: [empty or scaffold-only]}` with
/// the then-arm's contents (and the mirror with then/else swapped).
///
/// This runs after all latch recognition has settled. The Branch is a
/// no-op wrapper at this point: BP's DoOnce macro lowered the init seed
/// into one arm and the second-call body (the recognized inner Latch)
/// into the other, but both arms produce the same observable state. The
/// inner Latch is what the user wrote in the editor.
pub(super) fn peel_init_check_around_doonce(body: &mut Vec<Stmt>) {
    let mut idx = 0;
    while idx < body.len() {
        walk_stmt_children_mut(&mut body[idx], &mut peel_init_check_around_doonce);
        if let Some(replacement) = unwrap_init_check_doonce_wrapper(&mut body[idx]) {
            body.splice(idx..idx + 1, replacement);
            continue;
        }
        idx += 1;
    }
}

/// If `stmt` is a `Branch{cond: Var(init/gate prefix), then|else:
/// [Latch::DoOnce...], other: scaffold-only-or-empty}`, return the
/// Latch arm's drained contents. Returns `None` otherwise.
fn unwrap_init_check_doonce_wrapper(stmt: &mut Stmt) -> Option<Vec<Stmt>> {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };
    let Expr::Var(cond_name) = cond else {
        return None;
    };
    if !cond_name.starts_with(DOONCE_INIT_PREFIX) && !cond_name.starts_with(DOONCE_GATE_PREFIX) {
        return None;
    }
    let body_has_doonce = |arm: &Vec<Stmt>| arm.iter().any(is_doonce_latch);
    let arm_is_pure_scaffold =
        |arm: &Vec<Stmt>| arm.is_empty() || arm.iter().all(is_doonce_scaffold_assignment);
    let (latch_arm, other_arm) = if body_has_doonce(then_body) && arm_is_pure_scaffold(else_body) {
        (then_body, else_body)
    } else if body_has_doonce(else_body) && arm_is_pure_scaffold(then_body) {
        (else_body, then_body)
    } else {
        return None;
    };
    let _ = other_arm; // dropped along with the Branch
    Some(std::mem::take(latch_arm))
}

/// Drop `Stmt::Latch::DoOnce` whose `gate_var` starts with the
/// `Has_Been_Initd_Variable` prefix.
///
/// A real DoOnce gate is always a `Temp_bool_IsClosed_Variable_<N>`
/// name. The Blueprint compiler also emits a `Has_Been_Initd_Variable_<N>`
/// for the macro's one-shot seed, but that variable is an init-check
/// guard, never a gate. The region-decode path can mis-wrap an init-check
/// `Branch` as `Latch::DoOnce`, producing a phantom latch whose body is
/// just the gate-set assignment.
///
/// Walks the entire body tree, so phantom init-doonce wrappers inside
/// branch arms / sequence pins / loop bodies all get removed.
pub(super) fn strip_phantom_init_doonce(body: &mut Vec<Stmt>) {
    let mut idx = 0;
    while idx < body.len() {
        if is_init_guard_latch(&body[idx]) {
            body.remove(idx);
            continue;
        }
        walk_stmt_children_mut(&mut body[idx], &mut strip_phantom_init_doonce);
        idx += 1;
    }
}

/// Return `true` when `stmt` is `Stmt::Latch { kind: DoOnce { gate_var, .. } }`
/// whose `gate_var` starts with [`DOONCE_INIT_PREFIX`] (the init-guard
/// prefix rather than the real gate prefix).
fn is_init_guard_latch(stmt: &Stmt) -> bool {
    let Stmt::Latch {
        kind: LatchKind::DoOnce { gate_var, .. },
        ..
    } = stmt
    else {
        return false;
    };
    gate_var.starts_with(DOONCE_INIT_PREFIX)
}

/// Lift a real `Latch::DoOnce` out of a `Stmt::Sequence` wrapper whose
/// other pins hold only DoOnce scaffolding.
///
/// The region-decode path can emit a DoOnce as
/// `Sequence{pins: [<scaffold>, [<Latch::DoOnce>]]}` instead of folding
/// the scaffold into the latch wrapper. When exactly one pin contains a
/// single `Latch::DoOnce` and every other pin is pure scaffold (init+gate-set
/// assignments with optional empty-arm init/gate-check Branches), replace
/// the Sequence with the inner latch.
///
/// Walks the entire body tree so wrapped latches in any nesting level
/// get unwrapped. Takes `&mut Vec<Stmt>` because it's threaded through
/// `walk_stmt_children_mut` which hands callers a `&mut Vec<Stmt>` slot.
#[allow(clippy::ptr_arg)]
pub(super) fn unwrap_scaffold_sequence_around_latch(body: &mut Vec<Stmt>) {
    let mut idx = 0;
    while idx < body.len() {
        walk_stmt_children_mut(&mut body[idx], &mut unwrap_scaffold_sequence_around_latch);
        if let Some(replacement) = sequence_to_inner_latch(&mut body[idx]) {
            body.splice(idx..=idx, replacement);
        }
        idx += 1;
    }
}

/// If `stmt` is a `Stmt::Sequence` whose pins partition into N-1 scaffold
/// pins plus one pin holding a single `Latch::DoOnce`, return the collapsed
/// replacement: any folded `ResetDoOnce` calls from scaffold pins (in pin
/// order) followed by the inner latch. Otherwise return `None`.
///
/// A scaffold pin is either pure DoOnce role pieces (gate/init check Branch
/// or set-to-true Assignment, which carry no surviving statement) or a single
/// folded `Call(ResetDoOnce)` (which must be preserved as a leading sibling).
/// The user-body pin must hold exactly one `Latch::DoOnce` so the unwrap
/// target is unambiguous.
fn sequence_to_inner_latch(stmt: &mut Stmt) -> Option<Vec<Stmt>> {
    let Stmt::Sequence { pins, .. } = stmt else {
        return None;
    };
    if pins.len() < 2 {
        return None;
    }
    let mut latch_pin: Option<usize> = None;
    let mut reset_pins: Vec<usize> = Vec::new();
    for (pin_index, pin) in pins.iter().enumerate() {
        if pin_is_pure_doonce_scaffold(pin) {
            continue;
        }
        // After partition recovery, a scaffold pin's gate-reset pair
        // folds to a single `Call(ResetDoOnce)` (via
        // `try_rewrite_reset_doonce_pair`), which `classify_doonce_role`
        // doesn't recognise. Accept it as a non-body scaffold pin and keep
        // the call as a leading sibling so the wrapper collapses without
        // dropping the reset (the else-arm scaffold-pin shape).
        if pin_is_reset_doonce_scaffold(pin) {
            reset_pins.push(pin_index);
            continue;
        }
        if pin.len() == 1
            && matches!(
                pin[0],
                Stmt::Latch {
                    kind: LatchKind::DoOnce { .. },
                    ..
                }
            )
        {
            if latch_pin.is_some() {
                return None;
            }
            latch_pin = Some(pin_index);
            continue;
        }
        return None;
    }
    let chosen = latch_pin?;
    if pins[chosen].len() != 1 {
        return None;
    }
    let mut replacement: Vec<Stmt> = Vec::new();
    for &reset_index in &reset_pins {
        replacement.append(&mut std::mem::take(&mut pins[reset_index]));
    }
    let mut latch = std::mem::take(&mut pins[chosen]);
    replacement.push(latch.remove(0));
    Some(replacement)
}

/// Return `true` when every stmt in `pin` is a DoOnce-scaffold piece
/// (gate/init check Branch with empty arms, or gate/init set-to-true
/// Assignment).
fn pin_is_pure_doonce_scaffold(pin: &[Stmt]) -> bool {
    if pin.is_empty() {
        return true;
    }
    pin.iter().all(|stmt| {
        matches!(
            classify_doonce_role(stmt),
            DoOnceRole::GateCheck(_)
                | DoOnceRole::GateSet(_)
                | DoOnceRole::InitCheck(_)
                | DoOnceRole::InitSet(_)
        )
    })
}

/// Return `true` when `pin` is a single `Call(ResetDoOnce, ...)` produced by
/// `try_rewrite_reset_doonce_pair`. Such a pin is the folded form of a
/// gate-reset scaffold (`IsClosed = false; Has_Been_Initd = true`), so it
/// counts as a non-body scaffold pin for wrapper collapse.
fn pin_is_reset_doonce_scaffold(pin: &[Stmt]) -> bool {
    matches!(
        pin,
        [Stmt::Call { func, .. }] if is_reset_doonce_call(func)
    )
}
