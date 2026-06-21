//! Cross-cutting helpers shared by the latch recognizer families: the
//! gate/init/toggle name prefixes, the DoOnce role classifier, and the
//! display-name derivation used for DoOnce / ResetDoOnce naming.

use super::doonce::{
    classify_doonce_sequence, doonce_var_suffix, is_synthetic_reset_doonce, DoOnceSequenceEvidence,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};

/// Variable-name prefix for the DoOnce gate (`true` once the gate has fired).
/// Shared with `k2node_byte_map::attribute_macro_scaffold_bytes` so scaffold
/// attribution and recognition agree on the gate spelling.
pub(crate) const DOONCE_GATE_PREFIX: &str = "Temp_bool_IsClosed_Variable";

/// Variable-name prefix for the DoOnce init guard. The Blueprint compiler
/// emits a one-shot init block alongside the gate to seed the gate variable
/// the first time the macro instance runs; `Has_Been_Initd_Variable_<N>`
/// is the boolean that flips true after the seed runs once.
/// Shared with `k2node_byte_map::attribute_macro_scaffold_bytes`.
pub(crate) const DOONCE_INIT_PREFIX: &str = "Temp_bool_Has_Been_Initd_Variable";

/// Variable-name prefix for the FlipFlop toggle. Note this also matches
/// `Temp_bool_IsClosed_Variable` and `Temp_bool_Has_Been_Initd_Variable`
/// by prefix — FlipFlop matching guards against that by requiring the
/// toggle pattern, not just the prefix.
/// Shared with `k2node_byte_map::attribute_macro_scaffold_bytes`.
pub(crate) const FLIPFLOP_TOGGLE_PREFIX: &str = "Temp_bool_Variable";

/// Display / call-target name for a recognized DoOnce latch. Also used as a
/// prefix (`DoOnce_<suffix>`) for fallback names derived from the gate suffix.
pub(crate) const DOONCE_CALL_NAME: &str = "DoOnce";

/// Call-target name for the synthetic gate-reset call paired with a DoOnce.
pub(crate) const RESET_DOONCE_CALL_NAME: &str = "ResetDoOnce";

/// Common UE library / math function prefixes that don't make good DoOnce
/// display names.
pub(crate) const LIBRARY_FUNC_PREFIXES: &[&str] = &[
    "Select",
    "Multiply_",
    "Add_",
    "Subtract_",
    "Divide_",
    "Abs",
    "FClamp",
    "MakeVector",
    "MakeRotator",
    "MakeTransform",
    "BreakVector",
    "BreakRotator",
    "ComposeRotators",
    "VSize",
    "Normalize",
    "GetPlayerController",
    "GetPlayerCameraManager",
    "GetWorldDeltaSeconds",
    "IsValid",
    "PrintString",
];

/// Return true when `stmt` is `Stmt::Latch { kind: DoOnce, .. }`.
pub(super) fn is_doonce_latch(stmt: &Stmt) -> bool {
    matches!(
        stmt,
        Stmt::Latch {
            kind: LatchKind::DoOnce { .. },
            ..
        }
    )
}

/// If `stmt` is `Var(name) = Literal(value)`, return `(name, offset)`.
pub(super) fn match_var_assigned_literal<'a>(
    stmt: &'a Stmt,
    value: &str,
) -> Option<(&'a str, usize)> {
    let Stmt::Assignment { lhs, rhs, offset } = stmt else {
        return None;
    };
    let Expr::Var(name) = lhs else {
        return None;
    };
    if !matches!(rhs, Expr::Literal(text) if text == value) {
        return None;
    }
    Some((name.as_str(), *offset))
}

/// Classification of a single statement's role in a DoOnce expansion.
///
/// `GateCheck`/`GateSet` carry the gate variable name (e.g. `Temp_bool_IsClosed_Variable_4`).
/// `InitCheck`/`InitSet` carry the init variable name (e.g. `Temp_bool_Has_Been_Initd_Variable_4`).
/// Knowing the var names lets the tail-acceptance rule distinguish "scaffold for the
/// outer DoOnce" (reject in tail) from "scaffold for a different macro nested inside
/// the user body" (accept in tail).
pub(super) enum DoOnceRole {
    None,
    GateCheck(String),
    GateSet(String),
    InitCheck(String),
    InitSet(String),
    DoOnceSequence(DoOnceSequenceEvidence),
}

impl DoOnceRole {
    /// True for the four flat gate/init scaffold roles. `None` and
    /// `DoOnceSequence` are not flat scaffold.
    pub(super) fn is_scaffold(&self) -> bool {
        matches!(
            self,
            DoOnceRole::GateCheck(_)
                | DoOnceRole::GateSet(_)
                | DoOnceRole::InitCheck(_)
                | DoOnceRole::InitSet(_)
        )
    }

    /// The trimmed DoOnce instance suffix this role carries (`""` for the
    /// first, unnumbered instance, `"4"` for `..._4`, etc.). Strips the gate
    /// prefix for gate roles and the init prefix for init roles, folding that
    /// gate-vs-init prefix choice into one place. `None` for `None` and
    /// `DoOnceSequence` (which carry no single gate/init variable).
    pub(super) fn suffix(&self) -> Option<&str> {
        match self {
            DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => {
                Some(doonce_var_suffix(name, DOONCE_GATE_PREFIX))
            }
            DoOnceRole::InitCheck(name) | DoOnceRole::InitSet(name) => {
                Some(doonce_var_suffix(name, DOONCE_INIT_PREFIX))
            }
            DoOnceRole::None | DoOnceRole::DoOnceSequence(_) => None,
        }
    }
}

pub(super) fn classify_doonce_role(stmt: &Stmt) -> DoOnceRole {
    if let Some(name) =
        match_empty_branch_var(stmt).or_else(|| match_scaffold_else_branch_var(stmt))
    {
        if name.starts_with(DOONCE_GATE_PREFIX) {
            return DoOnceRole::GateCheck(name.to_string());
        }
        if name.starts_with(DOONCE_INIT_PREFIX) {
            return DoOnceRole::InitCheck(name.to_string());
        }
    }
    if let Some(name) = match_var_set_to_true(stmt) {
        if name.starts_with(DOONCE_GATE_PREFIX) {
            return DoOnceRole::GateSet(name.to_string());
        }
        if name.starts_with(DOONCE_INIT_PREFIX) {
            return DoOnceRole::InitSet(name.to_string());
        }
    }
    if let Some(evidence) = classify_doonce_sequence(stmt) {
        return DoOnceRole::DoOnceSequence(evidence);
    }
    DoOnceRole::None
}

/// A single statement's role inside a DoOnce-expansion pin. Layers the three
/// scaffold tests the pin-purity predicates share so each predicate can spell
/// its own accept-set over one classification instead of re-deriving it.
/// Checked in order: scaffold no-op branch, then synthetic `ResetDoOnce` call,
/// then the statement's `DoOnceRole`; anything else is user body.
pub(super) enum PinClass {
    /// A DoOnce role (the inner role tells gate/init/sequence apart;
    /// `DoOnceSequence` is kept distinguishable and is not flat scaffold).
    Scaffold(DoOnceRole),
    /// A scaffold no-op `Branch { cond: true, [], [] }` from pop_flow collapse.
    Noop,
    /// The synthetic `Call(ResetDoOnce(DoOnce_*))` produced by reset-pair folding.
    SyntheticReset,
    /// Anything that is not DoOnce scaffold.
    UserBody,
}

/// Classify one statement's pin role (see [`PinClass`] for the layer order).
pub(super) fn classify_pin_stmt(stmt: &Stmt) -> PinClass {
    if is_scaffold_noop_branch(stmt) {
        return PinClass::Noop;
    }
    if is_synthetic_reset_doonce(stmt) {
        return PinClass::SyntheticReset;
    }
    match classify_doonce_role(stmt) {
        DoOnceRole::None => PinClass::UserBody,
        role => PinClass::Scaffold(role),
    }
}

/// Match `Branch{cond: Var(name), <arms pure DoOnce scaffold>}` where at
/// least one arm is non-empty and every arm contains nothing but DoOnce
/// scaffolding. Returns the cond `name`, which the caller maps to a
/// `GateCheck` or `InitCheck` role just like the `match_empty_branch_var`
/// case. BP's DoOnce macro lowers the first-call init seed into one arm of
/// an init-check Branch; the other arm is the no-op for already-initialised
/// calls.
///
/// The scaffold arm is not always a flat assignment run. When a latent call
/// splits the macro body the region-decoder keeps the init seed's duplicate
/// gate-check as a nested scaffold-only `Sequence` (and/or nested gate/init
/// Branches) inside one arm, and emits the other arm as init-set
/// assignments, so BOTH arms are non-empty pure scaffold. The recursive
/// [`is_pure_doonce_scaffold_stmt`] predicate accepts that shape; the flat
/// single-arm shape stays covered as a special case of it.
fn match_scaffold_else_branch_var(stmt: &Stmt) -> Option<&str> {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };
    let Expr::Var(name) = cond else {
        return None;
    };
    if !name.starts_with(DOONCE_INIT_PREFIX) && !name.starts_with(DOONCE_GATE_PREFIX) {
        return None;
    }
    // At least one arm must carry scaffold content (the truly-empty
    // both-arms case is `match_empty_branch_var`'s job).
    if then_body.is_empty() && else_body.is_empty() {
        return None;
    }
    if !then_body.iter().all(is_pure_doonce_scaffold_stmt)
        || !else_body.iter().all(is_pure_doonce_scaffold_stmt)
    {
        return None;
    }
    Some(name.as_str())
}

/// Return `true` when `stmt` is a `Stmt::Branch` with an empty `then_body`,
/// an empty `else_body`, and a `Var(name)` cond. Used to identify the
/// scaffold-shaped gate-check / init-check Branches the BP DoOnce
/// expansion leaves behind after pop_flow markers are absorbed.
pub(super) fn match_empty_branch_var(stmt: &Stmt) -> Option<&str> {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };
    if !then_body.is_empty() || !else_body.is_empty() {
        return None;
    }
    let Expr::Var(name) = cond else {
        return None;
    };
    Some(name.as_str())
}

/// Return `true` when `stmt` is a scaffold-noop Branch left behind by the
/// structurer's `pop_flow` handling: `Stmt::Branch { cond: Literal("true"),
/// then_body: [], else_body: [] }`. These appear inside Sequence pins at
/// scaffold positions when an outer compound DoOnce wraps an inner
/// scaffold and the pop_flow markers collapse to a Literal cond rather
/// than the gate Var. They carry no gate/init information, but they DO
/// belong to the scaffold (not the user body) and must not block the
/// prefix walk in `classify_doonce_sequence` or leak into the user body
/// during `apply_doonce_scaffold_rewrite`.
pub(super) fn is_scaffold_noop_branch(stmt: &Stmt) -> bool {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return false;
    };
    if !then_body.is_empty() || !else_body.is_empty() {
        return false;
    }
    matches!(cond, Expr::Literal(text) if text == "true")
}

/// Return `true` when `stmt` is a `Var(name) = Literal("true")` or
/// `Var(name) = Literal("false")` assignment whose lhs is a DoOnce
/// gate or init temp. Used by `match_scaffold_else_branch_var` to
/// decide whether a non-empty Branch arm is pure scaffold.
pub(super) fn is_doonce_scaffold_assignment(stmt: &Stmt) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    let Expr::Var(lhs_name) = lhs else {
        return false;
    };
    if !lhs_name.starts_with(DOONCE_INIT_PREFIX) && !lhs_name.starts_with(DOONCE_GATE_PREFIX) {
        return false;
    }
    matches!(rhs, Expr::Literal(text) if text == "true" || text == "false")
}

/// Return `true` when `stmt` is pure DoOnce scaffolding, recursively.
///
/// The init-block arm the BP compiler emits is not always a flat run of
/// `Var = true|false` assignments. When a latent call splits the macro
/// body, the region-decoder keeps the init seed's duplicate gate-check as
/// a nested scaffold-only `Sequence` (and/or nested gate/init Branches)
/// inside the init-check Branch's arm rather than flattening it to a
/// sibling. `is_doonce_scaffold_assignment` only recognises the flat-
/// assignment case, so this predicate generalises it: an arm is pure
/// scaffold when every stmt is a scaffold assignment, a scaffold-noop
/// `if (true) {}` Branch, a gate/init check Branch whose own non-empty
/// arms are themselves pure scaffold, or a `Sequence` whose every pin is
/// pure scaffold.
fn is_pure_doonce_scaffold_stmt(stmt: &Stmt) -> bool {
    if is_doonce_scaffold_assignment(stmt) || is_scaffold_noop_branch(stmt) {
        return true;
    }
    match stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            let Expr::Var(name) = cond else {
                return false;
            };
            if !name.starts_with(DOONCE_INIT_PREFIX) && !name.starts_with(DOONCE_GATE_PREFIX) {
                return false;
            }
            then_body.iter().all(is_pure_doonce_scaffold_stmt)
                && else_body.iter().all(is_pure_doonce_scaffold_stmt)
        }
        Stmt::Sequence { pins, .. } => pins
            .iter()
            .all(|pin| pin.iter().all(is_pure_doonce_scaffold_stmt)),
        _ => false,
    }
}

/// Return the lhs name when `stmt` is `Var(name) = Literal("true")`.
pub(super) fn match_var_set_to_true(stmt: &Stmt) -> Option<&str> {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return None;
    };
    let Expr::Var(name) = lhs else {
        return None;
    };
    if !matches!(rhs, Expr::Literal(text) if text == "true") {
        return None;
    }
    Some(name.as_str())
}

pub(super) fn first_user_call_name(body: &[Stmt]) -> Option<String> {
    let mut first_library: Option<String> = None;
    for stmt in body {
        let Some(call_name) = stmt_call_display_name(stmt) else {
            continue;
        };
        if is_library_func(&call_name) {
            if first_library.is_none() {
                first_library = Some(call_name);
            }
            continue;
        }
        return Some(call_name);
    }
    first_library
}

/// Extract a display function name from `Stmt::Call` or an `Stmt::Assignment`
/// whose rhs is a call. Strips method receivers (`obj.Foo` -> `Foo`).
///
/// The function/rhs path distinction matters: a `Stmt::Call` carries the
/// callee as `func`, which can legitimately be a bare `Expr::Var` (the
/// function name) or a `Expr::FieldAccess` (method-style call). A
/// `Stmt::Assignment` rhs only qualifies as a "call" when it is actually
/// call-shaped (`Expr::Call`/`Expr::MethodCall`); a bare `Var` rhs is a
/// value copy from a temp, not a callable. Accepting `Var`/`FieldAccess`
/// on the assignment-rhs path mis-identified a
/// `$Greater_FloatFloat_A = $InputAxisEvent_AxisValue_6` SelectFloat-cond
/// temp as the gated user call.
pub(crate) fn stmt_call_display_name(stmt: &Stmt) -> Option<String> {
    match stmt {
        Stmt::Call { func, .. } => expr_display_name(func),
        Stmt::Assignment { rhs, .. } => expr_display_name_for_assign_rhs(rhs),
        _ => None,
    }
}

fn expr_display_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call { name, .. } => Some(strip_method_recv(name)),
        Expr::MethodCall { name, .. } => Some(name.clone()),
        // `Stmt::Call` produced by `decode_call` carries `func: Expr::Var(name)`
        // for plain function calls (the inner `Expr::Call` from the expression
        // decoder is unwrapped at statement-construction time). Treat the bare
        // Var as the function name so the DoOnce naming heuristic finds it.
        Expr::Var(name) => Some(strip_method_recv(name)),
        Expr::FieldAccess { field, .. } => Some(field.clone()),
        _ => None,
    }
}

/// Variant of `expr_display_name` used for the rhs of `Stmt::Assignment`.
/// Only call-shaped expressions (`Call`/`MethodCall`) qualify; bare `Var`
/// and `FieldAccess` are value copies, not callables.
fn expr_display_name_for_assign_rhs(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call { name, .. } => Some(strip_method_recv(name)),
        Expr::MethodCall { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn strip_method_recv(call_name: &str) -> String {
    match call_name.rfind('.') {
        Some(pos) => call_name[pos + 1..].to_string(),
        None => call_name.to_string(),
    }
}

fn is_library_func(name: &str) -> bool {
    LIBRARY_FUNC_PREFIXES
        .iter()
        .any(|prefix| name.starts_with(prefix))
}

pub(super) fn fallback_name_from_gate(gate_name: &str) -> String {
    let suffix = gate_name
        .strip_prefix(DOONCE_GATE_PREFIX)
        .unwrap_or("")
        .trim_start_matches('_');
    if suffix.is_empty() {
        DOONCE_CALL_NAME.to_string()
    } else {
        format!("{}_{}", DOONCE_CALL_NAME, suffix)
    }
}

/// Return `true` when `func` is `Expr::Var("ResetDoOnce")`.
pub(super) fn is_reset_doonce_call(func: &Expr) -> bool {
    matches!(func, Expr::Var(name) if name == RESET_DOONCE_CALL_NAME)
}

/// Return `true` when `stmt` is exactly `Stmt::Call{ func: Var("ResetDoOnce"),
/// args: [_] }` (single-arg ResetDoOnce). Matches the synthetic shape produced
/// by `try_rewrite_reset_doonce_pair`.
pub(super) fn is_reset_doonce_call_stmt(stmt: &Stmt) -> bool {
    let Stmt::Call { func, args, .. } = stmt else {
        return false;
    };
    is_reset_doonce_call(func) && args.len() == 1
}
