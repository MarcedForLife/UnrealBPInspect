//! DoOnce recognition and the ResetDoOnce gate-reset rewrites: the
//! ResetDoOnce pair fold, post-chain reset absorption, the single-Branch /
//! compound / cross-arm DoOnce recognizers, the scaffold scanner, and the
//! `rewrite_reset_doonce_names` / `rewrite_asset_wide_reset_doonce_names`
//! display-name passes.

use super::shared::{
    classify_doonce_role, fallback_name_from_gate, first_user_call_name, is_doonce_latch,
    is_reset_doonce_call, is_scaffold_noop_branch, match_empty_branch_var,
    match_var_assigned_literal, match_var_set_to_true, DoOnceRole, DOONCE_CALL_NAME,
    DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX, RESET_DOONCE_CALL_NAME,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::visit::{self, walk_stmt_children_mut};
use std::collections::BTreeSet;

/// ResetDoOnce gate-reset recognition.
///
/// The Blueprint compiler expands `ResetDoOnce(<macro>)` as a contiguous
/// two-statement pair, one assignment to the gate (`IsClosed = false`)
/// and one assignment to the init guard (`Has_Been_Initd = true`).
/// The canonical shape is:
/// ```text
/// Temp_bool_IsClosed_Variable_<N>      = false;
/// Temp_bool_Has_Been_Initd_Variable_<N> = true;
/// ```
/// but the compiler also emits the pair in reverse order (init first,
/// gate second) and with mismatched suffixes when the two halves were
/// allocated from different temp slots (e.g. bare gate / `_2`-suffixed
/// init for a shared cross-event DoOnce). Both prefixes are dedicated
/// to DoOnce expansions, so any contiguous pair of one gate-prefix
/// `false` assignment and one init-prefix `true` assignment is a reset
/// regardless of suffix.
///
/// Without recognition the pair survives the transform pipeline but gets
/// wiped by `dead_stmt::remove_dead_assignments` because both right-hand
/// sides are pure literals and the names aren't read in the same body.
///
/// Rewrites each matched pair to a single `Stmt::Call` whose `func` is
/// `Expr::Var("ResetDoOnce")` and whose sole arg is the derived macro
/// name. `Stmt::Call` is opaque to dead-elim so the call survives.
///
/// Returns `true` when at least one pair was rewritten.
pub(super) fn try_rewrite_reset_doonce_pair(body: &mut Vec<Stmt>) -> bool {
    let mut rewrote = false;
    let mut idx = 0;
    while idx + 1 < body.len() {
        if let Some(call) = match_reset_doonce_pair(&body[idx], &body[idx + 1]) {
            body[idx] = call;
            body.remove(idx + 1);
            rewrote = true;
        }
        idx += 1;
    }
    rewrote
}

/// Post-chain `ResetDoOnce` absorption into a sibling Branch's else.
///
/// When the Blueprint compiler places a `DoOnce` macro inside an `if`-arm
/// it emits the gate-clear scaffolding (`IsClosed = false; Has_Been_Initd = true`)
/// at addresses that fall through past the gate's `pop_flow` but BEFORE
/// the user body. The structurer assigns those addresses to the outer
/// JIN's ELSE-flow direction, but because the addresses are above the
/// JIN's THEN range upper bound, they decode as siblings of the outer
/// `Stmt::Branch` (which gets an empty `else_body`) rather than as its
/// `else_body` content.
///
/// `try_rewrite_reset_doonce_pair` already folded the trailing
/// `IsClosed=false; Has_Been_Initd=true` pair into a single
/// `Stmt::Call(ResetDoOnce, DoOnce_<N>)`. This pass walks the parent body
/// for the structural pair `(Branch{empty else, DoOnce inside then},
/// Call(ResetDoOnce, ...))` and migrates the call into the Branch's
/// `else_body`.
///
/// The shape predicate is intentionally narrow:
///   - the Branch's `else_body` must be empty (avoids overwriting an
///     existing else such as the cases that already decoded their reset
///     into the proper position),
///   - the Branch's `then_body` must contain a `Stmt::Latch::DoOnce`
///     (proves the THEN arm holds a DoOnce expansion the trailing reset
///     is plausibly clearing),
///   - the trailing call must be the synthetic `ResetDoOnce(DoOnce_*)`
///     produced by `try_rewrite_reset_doonce_pair` (no other Call shape
///     qualifies).
pub(super) fn absorb_post_chain_reset_into_else(body: &mut Vec<Stmt>) {
    let mut idx = 0;
    while idx + 1 < body.len() {
        if branch_has_empty_else_with_doonce(&body[idx])
            && is_synthetic_reset_doonce(&body[idx + 1])
        {
            let reset_call = body.remove(idx + 1);
            if let Stmt::Branch { else_body, .. } = &mut body[idx] {
                else_body.push(reset_call);
            }
        }
        idx += 1;
    }
}

/// Return true when `stmt` is a `Stmt::Branch` whose `else_body` is empty
/// and whose `then_body` directly contains a `Stmt::Latch::DoOnce` (any
/// position). The DoOnce check guards against migrating resets into
/// arbitrary empty-else branches that don't originate from a DoOnce
/// gate scaffold.
fn branch_has_empty_else_with_doonce(stmt: &Stmt) -> bool {
    let Stmt::Branch {
        then_body,
        else_body,
        ..
    } = stmt
    else {
        return false;
    };
    if !else_body.is_empty() {
        return false;
    }
    then_body.iter().any(is_doonce_latch)
}

/// Return true when `stmt` is the synthetic `Stmt::Call` shape that
/// `match_reset_doonce_pair` produces: `Var("ResetDoOnce")` applied to a
/// single `Var("DoOnce*")` argument. The args check excludes user calls
/// that happen to be named `ResetDoOnce` but pass non-`Var` arguments.
pub(super) fn is_synthetic_reset_doonce(stmt: &Stmt) -> bool {
    let Stmt::Call { func, args, .. } = stmt else {
        return false;
    };
    let Expr::Var(func_name) = func else {
        return false;
    };
    if func_name != RESET_DOONCE_CALL_NAME || args.len() != 1 {
        return false;
    }
    matches!(&args[0], Expr::Var(name) if name.starts_with(DOONCE_CALL_NAME))
}

/// Return the gate suffix when `stmt` is a synthetic `Call(ResetDoOnce(DoOnce_<N>))`
/// produced by `try_rewrite_reset_doonce_pair`. Returns the bare empty string for `DoOnce` (no
/// numeric suffix). Used by the cross-Sequence inventory to credit init
/// evidence to the matching suffix without consuming the call itself.
pub(super) fn synthetic_reset_doonce_suffix(stmt: &Stmt) -> Option<String> {
    let Stmt::Call { func, args, .. } = stmt else {
        return None;
    };
    let Expr::Var(func_name) = func else {
        return None;
    };
    if func_name != RESET_DOONCE_CALL_NAME || args.len() != 1 {
        return None;
    }
    let Expr::Var(arg_name) = &args[0] else {
        return None;
    };
    let suffix = arg_name.strip_prefix(DOONCE_CALL_NAME)?;
    Some(suffix.trim_start_matches('_').to_string())
}

/// If `(first, second)` form a contiguous gate-reset pair, return the
/// equivalent `Stmt::Call(ResetDoOnce(<derived_name>))`.
///
/// Accepts either ordering (gate-then-init or init-then-gate) and does
/// not require matching suffixes between the two halves: both prefixes
/// are dedicated to the BP DoOnce macro expansion, so the pair shape
/// uniquely identifies a reset. The display name is derived from
/// whichever half carries the gate prefix, preserving the existing
/// `DoOnce_<gate_suffix>` form.
fn match_reset_doonce_pair(first: &Stmt, second: &Stmt) -> Option<Stmt> {
    let (gate_name, init_name, call_offset) =
        match_doonce_reset_halves(first, second).or_else(|| {
            match_doonce_reset_halves(second, first).map(|(g, i, _)| {
                // When the pair is in reverse order (init-then-gate), the
                // call still anchors at the first stmt's offset for stable
                // ordering with surrounding statements.
                let first_offset = first.offset();
                (g, i, first_offset)
            })
        })?;
    let _ = init_name;

    let display_name = fallback_name_from_gate(gate_name);
    Some(Stmt::Call {
        func: Expr::Var(RESET_DOONCE_CALL_NAME.to_string()),
        args: vec![Expr::Var(display_name)],
        offset: call_offset,
    })
}

/// If `(gate_stmt, init_stmt)` is a `(gate=false, init=true)` pair with
/// the dedicated DoOnce prefixes, return `(gate_name, init_name, gate_offset)`.
pub(super) fn match_doonce_reset_halves<'a>(
    gate_stmt: &'a Stmt,
    init_stmt: &'a Stmt,
) -> Option<(&'a str, &'a str, usize)> {
    let (gate_name, gate_offset) = match_var_assigned_literal(gate_stmt, "false")?;
    let (init_name, _) = match_var_assigned_literal(init_stmt, "true")?;
    if !gate_name.starts_with(DOONCE_GATE_PREFIX) {
        return None;
    }
    if !init_name.starts_with(DOONCE_INIT_PREFIX) {
        return None;
    }
    Some((gate_name, init_name, gate_offset))
}

/// Cross-arm compound DoOnce recognition.
///
/// Walks the top level of `body` for `Stmt::Branch` entries whose then
/// arm or else arm holds a partial DoOnce scaffold (gate-check + gate-set
/// for the same suffix) without local init proof, and whose sibling arm
/// supplies external init proof for the same suffix. When the pairing
/// holds the matching arm gets rewritten exactly as the single-body
/// compound recognizer would have.
///
/// Background on the shape: the Blueprint compiler can place a DoOnce
/// macro inside one arm of an `if`, with the gate-clear scaffolding
/// (`IsClosed = false; Has_Been_Initd = true`) routed through the
/// opposite arm via fall-through. After `try_rewrite_reset_doonce_pair`
/// folds the gate-clear pair into a synthetic `Call ResetDoOnce`, the
/// only surviving init evidence for that arm's gate suffix is the
/// sibling arm's `ResetDoOnce(DoOnce_<N>)` call. The standard compound
/// recognizer rejects the arm because it lacks an in-body init-check
/// Branch + init-set Assignment, leaving the user body unwrapped.
///
/// Init-proof sources accepted from the sibling arm:
/// - A `Call ResetDoOnce(Var("DoOnce_<suffix>"))` whose suffix matches
///   the gate variable's suffix. The synthetic ResetDoOnce only exists
///   when `try_rewrite_reset_doonce_pair` saw a gate-set + init-set pair
///   for that suffix, so the call functions as a strict proof of the
///   missing init evidence.
/// - An `InitCheck` or `InitSet` scaffold piece matching the suffix
///   (covers the spec-described shape where the init pieces literally
///   live across arms).
///
/// Returns `true` when at least one arm was rewritten.
pub(super) fn try_rewrite_cross_arm_doonce(body: &mut [Stmt]) -> bool {
    let mut rewrote = false;
    for stmt in body.iter_mut() {
        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = stmt
        else {
            continue;
        };
        if try_rewrite_arm_with_sibling_proof(then_body, else_body) {
            rewrote = true;
        }
        if try_rewrite_arm_with_sibling_proof(else_body, then_body) {
            rewrote = true;
        }
    }
    rewrote
}

/// Attempt the compound DoOnce rewrite on `target_arm` using `sibling_arm`
/// to satisfy the init-proof requirement. Returns `true` when rewritten.
fn try_rewrite_arm_with_sibling_proof(target_arm: &mut Vec<Stmt>, sibling_arm: &[Stmt]) -> bool {
    let scaffold = match scan_doonce_scaffold(target_arm) {
        Some(s) => s,
        None => return false,
    };
    if scaffold.has_init_proof {
        // The standard compound pass already handled this arm during the
        // child-recursion phase; nothing to do here.
        return false;
    }
    if scaffold.gate_var.is_empty() {
        return false;
    }
    let gate_suffix = doonce_var_suffix(&scaffold.gate_var, DOONCE_GATE_PREFIX);
    if !sibling_arm_supplies_init_proof(sibling_arm, gate_suffix) {
        return false;
    }
    apply_doonce_scaffold_rewrite(target_arm, scaffold)
}

/// Extract the numeric (or empty) suffix from a DoOnce gate or init
/// variable name. The Blueprint compiler emits the bare name without a
/// suffix for the first instance and `_<N>` for subsequent instances.
pub(super) fn doonce_var_suffix<'a>(var_name: &'a str, prefix: &str) -> &'a str {
    var_name
        .strip_prefix(prefix)
        .unwrap_or("")
        .trim_start_matches('_')
}

/// Return `true` when the sibling arm body contains an init-proof signal
/// for the DoOnce instance identified by `gate_suffix`.
fn sibling_arm_supplies_init_proof(sibling: &[Stmt], gate_suffix: &str) -> bool {
    sibling
        .iter()
        .any(|stmt| stmt_supplies_doonce_init_proof(stmt, gate_suffix))
}

/// Walk one statement and any nested bodies looking for init-proof for
/// `gate_suffix`. Recurses into Branch arms, Sequence pins, Loop body,
/// Switch case bodies, and Latch init/body so a sibling-arm scan finds
/// init evidence wherever the BP compiler routed it.
fn stmt_supplies_doonce_init_proof(stmt: &Stmt, gate_suffix: &str) -> bool {
    if is_reset_doonce_call_for_suffix(stmt, gate_suffix) {
        return true;
    }
    if let Some(name) = match_empty_branch_var(stmt) {
        if name.starts_with(DOONCE_INIT_PREFIX)
            && doonce_var_suffix(name, DOONCE_INIT_PREFIX) == gate_suffix
        {
            return true;
        }
    }
    if let Some(name) = match_var_set_to_true(stmt) {
        if name.starts_with(DOONCE_INIT_PREFIX)
            && doonce_var_suffix(name, DOONCE_INIT_PREFIX) == gate_suffix
        {
            return true;
        }
    }
    match stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            sibling_arm_supplies_init_proof(then_body, gate_suffix)
                || sibling_arm_supplies_init_proof(else_body, gate_suffix)
        }
        Stmt::Sequence { pins, .. } => pins
            .iter()
            .any(|pin| sibling_arm_supplies_init_proof(pin, gate_suffix)),
        Stmt::Loop {
            body, completion, ..
        } => {
            sibling_arm_supplies_init_proof(body, gate_suffix)
                || completion
                    .as_ref()
                    .is_some_and(|comp| sibling_arm_supplies_init_proof(comp, gate_suffix))
        }
        Stmt::Switch { cases, default, .. } => {
            cases
                .iter()
                .any(|case| sibling_arm_supplies_init_proof(&case.body, gate_suffix))
                || default
                    .as_ref()
                    .is_some_and(|body| sibling_arm_supplies_init_proof(body, gate_suffix))
        }
        Stmt::Latch { init, body, .. } => {
            sibling_arm_supplies_init_proof(init, gate_suffix)
                || sibling_arm_supplies_init_proof(body, gate_suffix)
        }
        _ => false,
    }
}

/// Return `true` when `stmt` is the synthetic
/// `Call ResetDoOnce(Var("DoOnce_<suffix>"))` produced by
/// `try_rewrite_reset_doonce_pair`. Suffix-matching uses the same trim
/// rule as the gate-var suffix extraction so bare-instance and
/// numbered-instance names compare equal.
pub(super) fn is_reset_doonce_call_for_suffix(stmt: &Stmt, gate_suffix: &str) -> bool {
    let Stmt::Call { func, args, .. } = stmt else {
        return false;
    };
    let Expr::Var(func_name) = func else {
        return false;
    };
    if func_name != RESET_DOONCE_CALL_NAME || args.len() != 1 {
        return false;
    }
    let Expr::Var(target) = &args[0] else {
        return false;
    };
    let Some(call_suffix) = target.strip_prefix(DOONCE_CALL_NAME) else {
        return false;
    };
    call_suffix.trim_start_matches('_') == gate_suffix
}

/// Compound DoOnce recognition.
///
/// The Blueprint compiler expands a `DoOnce` macro instance into a
/// scaffolding pattern that survives the decoder as several sibling
/// statements plus a scaffold-only `Stmt::Sequence`. The scaffolding pieces
/// are:
///
/// - **gate-check Branch**: `Stmt::Branch { cond: Var(IsClosed_*), then=empty, else=empty }`
///   guards the user body so it only runs when the gate is open. Empty
///   then/else because the JIN's body and post-body bytes (`pop_flow*`
///   markers) are dropped at decode time.
/// - **gate-set assignment**: `IsClosed_<N> = true` flips the gate closed
///   so subsequent invocations skip the body.
/// - **init-check Branch**: `Stmt::Branch { cond: Var(Has_Been_Initd_*), then=empty }`
///   gates the per-instance init block.
/// - **init-set assignment**: `Has_Been_Initd_<M> = true` marks the init
///   block as run.
/// - **scaffold-only Sequence**: a `Stmt::Sequence` whose pin bodies are
///   exclusively the scaffolding stmts above (or empty). One pin holds the
///   init block; the other (when present) holds a duplicate gate-check.
///
/// The user's body content is everything in the parent body that ISN'T
/// scaffolding, in document order.
///
/// Recognition strategy:
/// 1. Confirm the body contains a scaffold-only `Stmt::Sequence`.
/// 2. Confirm at least one init-check Branch + one init-set assignment
///    appears among (a) the body's siblings and (b) the Sequence's pin
///    contents combined. The init block proves this is a DoOnce, not a
///    bare gated assignment.
/// 3. Strip every scaffolding statement from the body (siblings and the
///    Sequence as a whole).
/// 4. Wrap the remaining (user-body) statements in `Stmt::Latch::DoOnce`
///    and replace the body's contents with the wrapped form.
///
/// Returns `true` when a compound DoOnce was recognised and rewritten.
pub(super) fn try_rewrite_compound_doonce(body: &mut Vec<Stmt>) -> bool {
    let scaffold = match scan_doonce_scaffold(body) {
        Some(s) => s,
        None => return false,
    };

    // Validate the init proof: at least one init-check + one init-set
    // anywhere in the matched scaffold. Without that proof the
    // gate-check + gate-set pattern alone would fold any "set this bool
    // and skip if it's true" sequence into a DoOnce.
    if !scaffold.has_init_proof {
        return false;
    }

    apply_doonce_scaffold_rewrite(body, scaffold)
}

/// Apply a confirmed DoOnce scaffold rewrite to `body`.
///
/// Splits `body` into a preamble (anything before the first scaffold
/// statement), strips scaffold pieces from the tail, pulls any embedded
/// user-body tail out of a scaffold-leading Sequence pin, and wraps the
/// remaining user-body statements in a `Stmt::Latch::DoOnce`. The Latch
/// replaces the tail; the preamble keeps its original ordering.
///
/// The caller is responsible for proving the scaffold represents a real
/// DoOnce, either via `scaffold.has_init_proof` or via an external
/// signal such as a cross-arm `ResetDoOnce` matching the gate suffix.
///
/// Returns `true` when the wrap was applied, `false` when the scaffold
/// covered the entire body with nothing left to wrap (no-op case).
fn apply_doonce_scaffold_rewrite(body: &mut Vec<Stmt>, scaffold: DoOnceScaffold) -> bool {
    let outer_offset = scaffold.outer_offset;

    // The user body comes from two sources:
    //   1. Non-scaffold sibling stmts in `body` (working DoOnce shape, e.g.
    //      the user body is a single `Call` and the Sequence is
    //      scaffold-only).
    //   2. Trailing non-scaffold stmts embedded inside one Sequence pin
    //      (the embedded-body shape, e.g. a pin that starts with
    //      gate-check + gate-set then continues with the user body via
    //      post-pop fall-through).
    //
    // When both are empty the body is entirely scaffold (e.g. an init pin
    // viewed in isolation) and we leave it alone, otherwise we'd hand back
    // an empty wrap.
    let embedded_present = scaffold.embedded_user_body.is_some();
    if scaffold.scaffold_indices.len() == body.len() && !embedded_present {
        return false;
    }

    let embedded = scaffold
        .embedded_user_body
        .as_ref()
        .map(|loc| extract_embedded_user_body(body, loc))
        .unwrap_or_default();

    // Stmts at indices < first_scaffold are preamble that ran BEFORE the
    // gate-check (e.g. an entry guard call + outer if/else routing into
    // the DoOnce body). They stay as siblings of the new latch. Only stmts
    // at indices >= first_scaffold count as user-body candidates.
    // A scaffold always has at least one index, but degrade to "no rewrite"
    // rather than panic if a malformed asset produced an empty index list.
    let Some(&first_scaffold) = scaffold.scaffold_indices.first() else {
        return false;
    };
    let owned = std::mem::take(body);
    let mut preamble: Vec<Stmt> = Vec::new();
    let mut tail_with_scaffold: Vec<Stmt> = Vec::with_capacity(owned.len());
    let mut scaffold_iter = scaffold.scaffold_indices.iter().copied().peekable();
    let mut adjusted_indices: Vec<usize> = Vec::with_capacity(scaffold.scaffold_indices.len());
    for (idx, stmt) in owned.into_iter().enumerate() {
        if scaffold_iter.peek().copied() == Some(idx) {
            scaffold_iter.next();
            adjusted_indices.push(tail_with_scaffold.len());
            tail_with_scaffold.push(stmt);
        } else if idx < first_scaffold {
            preamble.push(stmt);
        } else {
            tail_with_scaffold.push(stmt);
        }
    }

    let mut user_body = take_non_scaffold_stmts(&mut tail_with_scaffold, &adjusted_indices);
    user_body.extend(embedded);

    if user_body.is_empty() {
        // Defensive: the length check above should have ruled this out,
        // but if a future caller passes overlapping or out-of-order
        // indices we restore by leaving the body alone.
        *body = preamble;
        return false;
    }

    let name = derive_doonce_name(&user_body, &scaffold.gate_var);

    let latch = Stmt::Latch {
        kind: LatchKind::DoOnce {
            name,
            gate_var: scaffold.gate_var.clone(),
        },
        init: vec![],
        body: user_body,
        offset: outer_offset,
    };

    preamble.push(latch);
    *body = preamble;
    true
}

/// Description of the scaffolding found at one body level.
struct DoOnceScaffold {
    /// Indices in the parent body that are scaffolding (gate-check Branch,
    /// gate-set Assignment, init-check Branch, init-set Assignment, or a
    /// scaffold-only / scaffold-leading Sequence). All get removed during
    /// rewrite.
    scaffold_indices: Vec<usize>,
    /// When a matched Sequence is scaffold-leading (its pins start with
    /// scaffold but one pin trails into a user body), this records
    /// `(sequence_index, pin_index, scaffold_prefix_len)` so the rewriter
    /// can pull the trailing pin tail out as the user body. The BP compiler
    /// emits this shape when a DoOnce sits inside an outer if-arm: the
    /// gate scaffold + user body live in the same execution pin via
    /// post-pop fall-through, but the partitioner splits them across one
    /// pin's leading scaffold and trailing body.
    embedded_user_body: Option<EmbeddedBodyLocation>,
    /// Source-of-truth gate variable name for naming fallback.
    gate_var: String,
    /// True when the scan saw at least one init-check Branch + at least
    /// one init-set Assignment (proving this is a DoOnce expansion rather
    /// than a stray gate-set pattern).
    has_init_proof: bool,
    /// Bytecode offset to attach to the synthesised `Stmt::Latch`. Picks
    /// the first scaffolding stmt's offset as the macro's anchor.
    outer_offset: usize,
}

/// Coordinates of a user body embedded inside a scaffold-leading Sequence
/// pin. The rewriter splits `pins[pin_index]` at `prefix_len`, drops the
/// prefix as scaffold, and uses the tail as the DoOnce body.
struct EmbeddedBodyLocation {
    sequence_index: usize,
    pin_index: usize,
    prefix_len: usize,
}

/// Walk one body level looking for compound DoOnce scaffolding.
///
/// Examines every statement in `body`:
///
/// - If the statement is a sibling-level scaffold piece (gate/init check
///   Branch with empty arms, or gate/init set-to-true Assignment), record
///   its index.
/// - If the statement is a `Stmt::Sequence` whose pins are scaffold-only
///   or scaffold-leading-with-trailing-user-body, record its index AND
///   fold the pins' init-check / init-set evidence into the running proof.
///   When a pin trails into a user body, capture the location so the
///   rewriter can pull the tail out.
///
/// Stops short of confirming a match — `try_rewrite_compound_doonce`
/// applies the proof check.
fn scan_doonce_scaffold(body: &[Stmt]) -> Option<DoOnceScaffold> {
    let mut scaffold_indices = Vec::new();
    let mut embedded_user_body: Option<EmbeddedBodyLocation> = None;
    let mut gate_var: Option<String> = None;
    let mut has_init_check = false;
    let mut has_init_set = false;
    let mut outer_offset: Option<usize> = None;

    for (idx, stmt) in body.iter().enumerate() {
        let role = classify_doonce_role(stmt);
        match role {
            DoOnceRole::None => continue,
            DoOnceRole::DoOnceSequence(seq_evidence) => {
                // Only one Sequence per body level may carry an embedded
                // user body. A second Sequence with an embedded tail would
                // create an ambiguous wrap so we bail by not matching it.
                if seq_evidence.trailing_user_body.is_some() && embedded_user_body.is_some() {
                    continue;
                }
                scaffold_indices.push(idx);
                if seq_evidence.has_init_check {
                    has_init_check = true;
                }
                if seq_evidence.has_init_set {
                    has_init_set = true;
                }
                if let Some(name) = seq_evidence.gate_var {
                    gate_var.get_or_insert(name);
                }
                if let Some((pin_index, prefix_len)) = seq_evidence.trailing_user_body {
                    embedded_user_body = Some(EmbeddedBodyLocation {
                        sequence_index: idx,
                        pin_index,
                        prefix_len,
                    });
                }
                outer_offset.get_or_insert_with(|| stmt.offset());
            }
            DoOnceRole::GateCheck(name) => {
                scaffold_indices.push(idx);
                gate_var.get_or_insert(name);
                outer_offset.get_or_insert_with(|| stmt.offset());
            }
            DoOnceRole::GateSet(name) => {
                scaffold_indices.push(idx);
                gate_var.get_or_insert(name);
                outer_offset.get_or_insert_with(|| stmt.offset());
            }
            DoOnceRole::InitCheck(_) => {
                scaffold_indices.push(idx);
                has_init_check = true;
                outer_offset.get_or_insert_with(|| stmt.offset());
            }
            DoOnceRole::InitSet(_) => {
                scaffold_indices.push(idx);
                has_init_set = true;
                outer_offset.get_or_insert_with(|| stmt.offset());
            }
        }
    }

    if scaffold_indices.is_empty() {
        return None;
    }

    Some(DoOnceScaffold {
        scaffold_indices,
        embedded_user_body,
        gate_var: gate_var.unwrap_or_default(),
        has_init_proof: has_init_check && has_init_set,
        outer_offset: outer_offset.unwrap_or(0),
    })
}

/// Per-pin / per-Sequence evidence collected when classifying a Sequence
/// as a DoOnce expansion.
pub(super) struct DoOnceSequenceEvidence {
    has_init_check: bool,
    has_init_set: bool,
    gate_var: Option<String>,
    /// `Some((pin_index, scaffold_prefix_len))` when exactly one pin has
    /// trailing non-scaffold stmts after its scaffold prefix. The rewriter
    /// pulls those tail stmts as the DoOnce body. `None` for the canonical
    /// scaffold-only Sequence.
    trailing_user_body: Option<(usize, usize)>,
}

/// Return `Some(evidence)` when `stmt` is a `Stmt::Sequence` shaped like
/// a DoOnce expansion.
///
/// Two pin shapes are accepted:
///
/// - **Scaffold-only**: every stmt in every pin is a scaffold piece
///   (gate-check / gate-set / init-check / init-set). This is the
///   canonical shape emitted when the user body lives as a sibling of
///   the Sequence.
/// - **Scaffold-leading with one trailing user body**: every pin starts
///   with a scaffold prefix; at most one pin has a trailing tail of
///   stmts that contains NO further scaffolding for any DoOnce gate.
///   The tail is the user body (e.g. when the DoOnce is wrapped inside
///   an outer if and the user body falls through into the gate pin via
///   post-pop continuation).
///
/// Returns `None` for:
///   - Sequences with non-scaffold leading content in any pin.
///   - Sequences where any tail contains scaffold stmts for a DoOnce
///     gate (these are usually the cross-range-push shape where one
///     macro's user body bleeds into another macro's gate-clear).
///   - Multiple pins with trailing tails (ambiguous wrap target).
///   - Nested DoOnce Sequences.
///   - Sequences with no scaffold evidence at all (avoids classifying
///     stray empty/non-DoOnce Sequences as scaffolding).
pub(super) fn classify_doonce_sequence(stmt: &Stmt) -> Option<DoOnceSequenceEvidence> {
    let Stmt::Sequence { pins, .. } = stmt else {
        return None;
    };
    let mut has_init_check = false;
    let mut has_init_set = false;
    let mut gate_var: Option<String> = None;
    let mut trailing_user_body: Option<(usize, usize)> = None;
    let mut total_scaffold_stmts = 0;

    for (pin_index, pin) in pins.iter().enumerate() {
        let mut prefix_len = 0;
        let mut tail_started = false;
        for inner in pin {
            // Scaffold-noop Branches (`if (true) {}`) sit at scaffold
            // positions inside the Sequence pins but carry no role
            // evidence. Treat them as scaffold for prefix purposes and
            // skip the role dispatch entirely so they neither (a) reject
            // the Sequence by falling into the `None` arm with
            // `prefix_len == 0`, nor (b) satisfy init/gate proofs.
            if is_scaffold_noop_branch(inner) {
                if tail_started {
                    // A noop appearing AFTER the user body starts would
                    // be unusual residue. Refuse to fold so the broken
                    // shape surfaces in output rather than hiding behind
                    // a silent accept.
                    return None;
                }
                prefix_len += 1;
                total_scaffold_stmts += 1;
                continue;
            }
            let role = classify_doonce_role(inner);
            if tail_started {
                // The tail belongs to the user body. Reject only when the
                // tail contains scaffold for the SAME outer DoOnce
                // instance (a same-suffix gate-check/set or init-check/set
                // would indicate the outer scaffold itself leaked into the
                // tail, which is a different broken shape we still want to
                // surface). Tail roles for a different gate suffix are
                // user-body content (e.g. an inline ResetDoOnce of a
                // sibling macro), accept silently.
                if !is_tail_role_acceptable(&role, gate_var.as_deref()) {
                    return None;
                }
                continue;
            }
            match role {
                DoOnceRole::None => {
                    // First non-scaffold stmt marks the start of the user-
                    // body tail. Reject the Sequence if any other pin has
                    // already claimed the tail slot, or if this pin has no
                    // scaffold prefix at all (a pin with NO scaffold
                    // prefix isn't a recognised gate/init pin shape).
                    if trailing_user_body.is_some() || prefix_len == 0 {
                        return None;
                    }
                    trailing_user_body = Some((pin_index, prefix_len));
                    tail_started = true;
                }
                DoOnceRole::DoOnceSequence(_) => {
                    return None;
                }
                DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => {
                    gate_var.get_or_insert(name);
                    prefix_len += 1;
                    total_scaffold_stmts += 1;
                }
                DoOnceRole::InitCheck(_) => {
                    has_init_check = true;
                    prefix_len += 1;
                    total_scaffold_stmts += 1;
                }
                DoOnceRole::InitSet(_) => {
                    has_init_set = true;
                    prefix_len += 1;
                    total_scaffold_stmts += 1;
                }
            }
        }
    }

    // A Sequence with a trailing tail must carry its own scaffold
    // evidence to be considered a DoOnce match. Otherwise a Sequence
    // whose only "scaffold" is a non-existent prefix would falsely
    // capture the body as DoOnce. Empty / evidence-free Sequences (no
    // scaffold pieces, no tail) stay classified as ScaffoldOnly so they
    // remain droppable alongside a real adjacent scaffold; the canonical
    // shape pairs a real Sequence with leftover empty ones the partition
    // couldn't merge.
    if trailing_user_body.is_some() && total_scaffold_stmts == 0 {
        return None;
    }

    Some(DoOnceSequenceEvidence {
        has_init_check,
        has_init_set,
        gate_var,
        trailing_user_body,
    })
}

/// Decide whether a role found in the pin tail (after the user-body start)
/// is acceptable as user-body content rather than a sign that the outer
/// scaffold has bled into the wrong slot.
///
/// Acceptable in tail:
///   - `None` (regular user-body Stmt).
///   - `GateCheck`/`GateSet`/`InitCheck`/`InitSet` whose variable suffix
///     differs from `outer_gate_var`'s suffix. These are scaffold pieces
///     for a different DoOnce instance nested inside the user body
///     (e.g. an inline ResetDoOnce expansion of a sibling macro).
///
/// Rejected in tail:
///   - Same-suffix gate/init scaffold (means the outer DoOnce's own
///     scaffold leaked into the tail, a broken shape we want to surface
///     by refusing to fold).
///   - `DoOnceSequence` (a nested DoOnce Sequence inside the user body
///     would create ambiguous fold targets).
fn is_tail_role_acceptable(role: &DoOnceRole, outer_gate_var: Option<&str>) -> bool {
    let outer_suffix = outer_gate_var
        .and_then(|name| name.strip_prefix(DOONCE_GATE_PREFIX))
        .unwrap_or("");
    let role_suffix = match role {
        DoOnceRole::None => return true,
        DoOnceRole::DoOnceSequence(_) => return false,
        DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => {
            name.strip_prefix(DOONCE_GATE_PREFIX).unwrap_or("")
        }
        DoOnceRole::InitCheck(name) | DoOnceRole::InitSet(name) => {
            name.strip_prefix(DOONCE_INIT_PREFIX).unwrap_or("")
        }
    };
    role_suffix != outer_suffix
}

/// Drain the trailing non-scaffold tail out of a scaffold-leading Sequence
/// pin. The Sequence at `body[loc.sequence_index]` will be dropped by the
/// caller (its index is in `scaffold_indices`), so we only need to pull
/// the tail stmts before that drop happens.
///
/// Scaffold-noop Branches (`if (true) {}`) sometimes appear at the head of
/// the tail when the structurer's pop_flow residue lands just after a
/// recognised scaffold prefix but before the user calls. Drop them so the
/// returned user body is clean.
fn extract_embedded_user_body(body: &mut [Stmt], loc: &EmbeddedBodyLocation) -> Vec<Stmt> {
    let Some(Stmt::Sequence { pins, .. }) = body.get_mut(loc.sequence_index) else {
        return Vec::new();
    };
    let Some(pin) = pins.get_mut(loc.pin_index) else {
        return Vec::new();
    };
    if loc.prefix_len > pin.len() {
        return Vec::new();
    }
    let mut tail = pin.split_off(loc.prefix_len);
    while tail.first().is_some_and(is_scaffold_noop_branch) {
        tail.remove(0);
    }
    tail
}

/// Drain `body`, returning a new vector of statements at indices NOT in
/// `scaffold_indices`. `scaffold_indices` is expected to be in ascending
/// order (the scanner visits stmts left-to-right).
fn take_non_scaffold_stmts(body: &mut Vec<Stmt>, scaffold_indices: &[usize]) -> Vec<Stmt> {
    let owned = std::mem::take(body);
    let mut scaffold_iter = scaffold_indices.iter().copied().peekable();
    let mut user_body = Vec::with_capacity(owned.len());
    for (idx, stmt) in owned.into_iter().enumerate() {
        if scaffold_iter.peek().copied() == Some(idx) {
            scaffold_iter.next();
            continue;
        }
        user_body.push(stmt);
    }
    user_body
}

/// If `stmt` is a `Stmt::Branch` matching the DoOnce shape, return the
/// equivalent `Stmt::Latch`. Otherwise return `None`.
///
/// The DoOnce shape is:
/// ```text
/// if (!Temp_bool_IsClosed_Variable_<N>) {
///     Temp_bool_IsClosed_Variable_<N> = true;
///     <body>
/// }
/// ```
/// `else_body` is empty.
pub(super) fn try_rewrite_doonce(stmt: &mut Stmt) -> Option<Stmt> {
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        offset,
    } = stmt
    else {
        return None;
    };

    if !else_body.is_empty() {
        return None;
    }

    let gate_name = match_doonce_negated_gate(cond)?;

    if then_body.is_empty() {
        return None;
    }
    if !is_gate_self_assignment(&then_body[0], gate_name) {
        return None;
    }

    let body = then_body.split_off(1);
    let derived_name = derive_doonce_name(&body, gate_name);

    Some(Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: derived_name,
            gate_var: gate_name.to_string(),
        },
        init: vec![],
        body,
        offset: *offset,
    })
}

/// Return the gate variable name if `cond` is `!Temp_bool_IsClosed_Variable*`.
fn match_doonce_negated_gate(cond: &Expr) -> Option<&str> {
    let Expr::Var(name) = visit::negated_operand(cond)? else {
        return None;
    };
    if name.starts_with(DOONCE_GATE_PREFIX) {
        Some(name)
    } else {
        None
    }
}

/// Return `true` when `stmt` is `gate_name = true` (the DoOnce gate
/// self-close).
fn is_gate_self_assignment(stmt: &Stmt, gate_name: &str) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    let Expr::Var(lhs_name) = lhs else {
        return false;
    };
    if lhs_name != gate_name {
        return false;
    }
    matches!(rhs, Expr::Literal(text) if text == "true")
}

/// Derive a display name for a DoOnce from its body. Scans for the first
/// non-library function call; falls back to the gate variable suffix.
fn derive_doonce_name(body: &[Stmt], gate_name: &str) -> String {
    if let Some(name) = first_user_call_name(body) {
        return name;
    }
    fallback_name_from_gate(gate_name)
}

/// Rewrite synthetic `Stmt::Call(ResetDoOnce(DoOnce_<N>))` arguments to the
/// matching sibling `Stmt::Latch::DoOnce`'s display name.
///
/// `try_rewrite_reset_doonce_pair` produces ResetDoOnce calls whose argument
/// is the algorithmic fallback `DoOnce_<gate_suffix>`. When a Latch
/// reachable in the same body tree carries a meaningful display name (the
/// first user-call name in its body) for the same gate var, this pass
/// swaps the fallback for that name, e.g.
///
/// ```text
/// DoOnce("MyAction") { ... }
/// ...
/// ResetDoOnce(DoOnce_3)   ->   ResetDoOnce(MyAction)
/// ```
///
/// Two passes over the body tree: first collect every Latch's
/// `(fallback_name -> display_name)` mapping, then walk again to rewrite
/// matching `ResetDoOnce` arguments. Walking the whole body before
/// rewriting handles nested Latches correctly (a Latch nested inside
/// another Latch's body still contributes to the map). Earlier entries
/// win on key collisions, mirroring the spec's "take the first" rule.
pub fn rewrite_reset_doonce_names(body: &mut Vec<Stmt>) {
    let mut name_map: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();
    collect_doonce_names_in_body(body.as_mut_slice(), &mut name_map);
    if name_map.is_empty() {
        return;
    }
    rewrite_reset_calls_in_body(body.as_mut_slice(), &name_map);
}

fn collect_doonce_names_in_body(
    body: &mut [Stmt],
    name_map: &mut std::collections::BTreeMap<String, String>,
) {
    for stmt in body.iter_mut() {
        if let Stmt::Latch {
            kind: LatchKind::DoOnce { name, gate_var },
            ..
        } = stmt
        {
            let fallback = fallback_name_from_gate(gate_var);
            // Skip when the latch is itself a fallback (no improvement) or
            // when its display name is a compiler temp (`$Foo`, less
            // readable than `DoOnce_<N>`).
            if name != &fallback && !name.starts_with('$') {
                name_map.entry(fallback).or_insert_with(|| name.clone());
            }
        }
        walk_stmt_children_mut(stmt, &mut |children| {
            collect_doonce_names_in_body(children.as_mut_slice(), name_map)
        });
    }
}

fn rewrite_reset_calls_in_body(
    body: &mut [Stmt],
    name_map: &std::collections::BTreeMap<String, String>,
) {
    for stmt in body.iter_mut() {
        if let Stmt::Call { func, args, .. } = stmt {
            if is_reset_doonce_call(func) && args.len() == 1 {
                if let Expr::Var(target) = &mut args[0] {
                    if let Some(replacement) = name_map.get(target.as_str()) {
                        *target = replacement.clone();
                    }
                }
            }
        }
        walk_stmt_children_mut(stmt, &mut |children| {
            rewrite_reset_calls_in_body(children.as_mut_slice(), name_map)
        });
    }
}

/// Asset-wide ResetDoOnce display-name resolution.
///
/// The per-body `rewrite_reset_doonce_names` pass only resolves names
/// from Latches reachable from the same body it's invoked on. Synthetic
/// `Call(ResetDoOnce(DoOnce_<N>))` arguments whose gate variable's
/// canonical Latch wrap lives in another event/function stay as the
/// bare fallback after the per-body pass.
///
/// This pass walks every function + event body across the asset, builds
/// `gate_var -> display_name` from non-fallback `Stmt::Latch::DoOnce`
/// entries, applies an ambiguity guard (multiple display names for the
/// same gate_var excludes that gate_var), then rewrites surviving
/// fallback `Call(ResetDoOnce(DoOnce_<N>))` arguments. The per-body pass
/// runs first so locally-resolved calls aren't overridden by the
/// asset-wide map.
pub fn rewrite_asset_wide_reset_doonce_names(
    functions: &mut [crate::bytecode::asset::Function],
    events: &mut [crate::bytecode::asset::Event],
) {
    let mut name_options: std::collections::BTreeMap<String, BTreeSet<String>> =
        std::collections::BTreeMap::new();
    for function in functions.iter() {
        collect_asset_wide_doonce_names(&function.body, &mut name_options);
    }
    for event in events.iter() {
        collect_asset_wide_doonce_names(&event.body, &mut name_options);
    }

    let mut resolved: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();
    for (gate_var, candidates) in name_options {
        // Only a single unambiguous candidate resolves a name; `next()` is
        // Some here, but pattern-match instead of unwrap for robustness.
        if candidates.len() == 1 {
            if let Some(display) = candidates.into_iter().next() {
                resolved.insert(fallback_name_from_gate(&gate_var), display);
            }
        }
    }
    if resolved.is_empty() {
        return;
    }

    for function in functions.iter_mut() {
        rewrite_fallback_reset_calls(&mut function.body, &resolved);
    }
    for event in events.iter_mut() {
        rewrite_fallback_reset_calls(&mut event.body, &resolved);
    }
}

/// Walk `body` collecting every `Stmt::Latch::DoOnce` whose `name` is a
/// non-fallback display name. Each gate_var accumulates a `BTreeSet` of
/// observed display names so the caller can detect ambiguity.
fn collect_asset_wide_doonce_names(
    body: &[Stmt],
    out: &mut std::collections::BTreeMap<String, BTreeSet<String>>,
) {
    for stmt in body {
        if let Stmt::Latch {
            kind: LatchKind::DoOnce { name, gate_var },
            init,
            body: inner,
            ..
        } = stmt
        {
            let fallback = fallback_name_from_gate(gate_var);
            // Skip fallback names (no information to share) and `$temp`
            // compiler-emitted names (less readable than the fallback).
            if name != &fallback && !name.starts_with('$') {
                out.entry(gate_var.clone())
                    .or_default()
                    .insert(name.clone());
            }
            collect_asset_wide_doonce_names(init, out);
            collect_asset_wide_doonce_names(inner, out);
            continue;
        }
        // Recurse into every Vec<Stmt> sub-body. Manual descent (rather
        // than walk_stmt_children_mut) lets the immutable collect pass
        // borrow `body` shared.
        match stmt {
            Stmt::Branch {
                then_body,
                else_body,
                ..
            } => {
                collect_asset_wide_doonce_names(then_body, out);
                collect_asset_wide_doonce_names(else_body, out);
            }
            Stmt::Sequence { pins, .. } => {
                for pin in pins {
                    collect_asset_wide_doonce_names(pin, out);
                }
            }
            Stmt::Loop {
                body: loop_body,
                completion,
                ..
            } => {
                collect_asset_wide_doonce_names(loop_body, out);
                if let Some(comp) = completion {
                    collect_asset_wide_doonce_names(comp, out);
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for case in cases {
                    collect_asset_wide_doonce_names(&case.body, out);
                }
                if let Some(default_body) = default {
                    collect_asset_wide_doonce_names(default_body, out);
                }
            }
            _ => {}
        }
    }
}

/// Rewrite every `Call(ResetDoOnce(DoOnce_<N>))` whose argument matches
/// a fallback-name key in `name_map`. Recurses through every nested body
/// via `walk_stmt_children_mut`. The argument-side check `starts_with('$')`
/// guard isn't needed here: the rewrite key set never contains `$`-named
/// targets (collection already filtered them out).
///
/// Threaded through `walk_stmt_children_mut`, which hands callers a
/// `&mut Vec<Stmt>` slot; the Vec parameter type matches that contract.
#[allow(clippy::ptr_arg)]
fn rewrite_fallback_reset_calls(
    body: &mut Vec<Stmt>,
    name_map: &std::collections::BTreeMap<String, String>,
) {
    for stmt in body.iter_mut() {
        if let Stmt::Call { func, args, .. } = stmt {
            if is_reset_doonce_call(func) && args.len() == 1 {
                if let Expr::Var(target) = &mut args[0] {
                    if let Some(replacement) = name_map.get(target.as_str()) {
                        *target = replacement.clone();
                    }
                }
            }
        }
        walk_stmt_children_mut(stmt, &mut |children| {
            rewrite_fallback_reset_calls(children, name_map)
        });
    }
}
