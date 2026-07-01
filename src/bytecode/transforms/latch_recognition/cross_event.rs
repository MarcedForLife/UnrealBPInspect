//! Cross-Sequence / cross-event DoOnce folding: collapses the multi-pin
//! `Sequence` shapes the BP compiler emits when a DoOnce macro's scaffold
//! is split across sibling Sequences or across an event boundary.

use super::doonce::{
    doonce_var_suffix, is_reset_doonce_call_for_suffix, is_synthetic_reset_doonce,
    match_doonce_reset_halves, synthetic_reset_doonce_suffix,
};
use super::shared::{
    classify_doonce_role, classify_pin_stmt, fallback_name_from_gate, first_user_call_name,
    is_reset_doonce_call_stmt, is_scaffold_noop_branch, match_var_assigned_literal, DoOnceRole,
    PinClass, DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LatchKind, Stmt};
use std::collections::BTreeSet;

/// Cross-Sequence compound DoOnce recognition.
///
/// Handles the BP-emitted shape where the user-body-wrap DoOnce's
/// scaffold is split across multiple sibling Sequences (or between a
/// sibling stmt and a sibling Sequence) at the same body level.
///
/// The standard `try_rewrite_compound_doonce` rejects these shapes
/// because a single Sequence in isolation lacks one or more required
/// scaffold pieces (init-check Branch, init-set Assignment, in-Sequence
/// gate-set, etc.). Cross-Sequence reasoning closes that gap, with
/// suffix-matching so adjacent BP DoOnce macros with different gate
/// suffixes stay independent.
///
/// Two scaffold-distribution shapes are recognised:
///
/// 1. **Two-Sequence split (else-arm scaffold split)**: one Sequence's pin
///    holds the user body and at least one OTHER pin in the same or
///    sibling Sequence holds scaffold for the same suffix (or a
///    contiguous `gate=false; init=true` gate-clear pair that supplies
///    init-set evidence). A sibling pure-scaffold Sequence supplies the
///    remaining init-check / gate-set evidence.
/// 2. **Partial-prefix-with-tail (deeply-nested user call)**: one
///    Sequence pin holds `[Branch(gate)=empty, gate=true, <user body>]`
///    for a suffix `S`, but no in-Sequence init-proof for `S`. Init-set
///    for the same suffix sits as a sibling assignment at the parent
///    body or inside a sibling Sequence's pin.
///
/// Returns `true` when at least one fold landed.
pub(super) fn try_rewrite_multi_sequence_doonce(body: &mut Vec<Stmt>) -> bool {
    let mut rewrote = false;
    while let Some(plan) = build_multi_sequence_fold_plan(body) {
        apply_multi_sequence_fold(body, plan);
        rewrote = true;
    }
    rewrote
}

/// A planned fold for `try_rewrite_multi_sequence_doonce`. Built without
/// mutating `body` so the planner can scan freely and the applier can
/// drive a tight rewrite afterwards.
struct MultiSequenceFoldPlan {
    /// Suffix identifying the DoOnce instance being folded (empty string
    /// for the bare-suffix BP variant).
    suffix: String,
    /// Source-of-truth gate variable name for the latch.
    gate_var: String,
    /// Latch offset anchor: the user-body location's outer Sequence offset
    /// when known, falling back to the user-body Stmt's own offset.
    outer_offset: usize,
    /// Indices in `body` that should be dropped during the rewrite
    /// (pure-scaffold siblings, fully-scaffold Sequences). Sorted ascending.
    drop_indices: Vec<usize>,
    /// Where the user body lives.
    user_body_location: UserBodyLocation,
}

/// Coordinates describing where the user body lives for a `MultiSequenceFoldPlan`.
enum UserBodyLocation {
    /// User body is one pin of a Sequence at `body[seq_index]`. The pin
    /// at `user_pin_idx` starts with a `prefix_len`-stmt scaffold prefix
    /// (gate-check + gate-set when `prefix_len == 2`, or 0 for a pure
    /// user-body pin). The Sequence as a whole is consumed; pins other
    /// than `user_pin_idx` are dropped alongside their parent Sequence.
    SequencePin {
        seq_index: usize,
        user_pin_idx: usize,
        prefix_len: usize,
    },
    /// User body is a partial-prefix-with-tail pin inside a Sequence
    /// nested deeper than the outer body level. `outer_seq_index` is
    /// the index of the OUTER Sequence at body level. `nested_path` is
    /// the chain of `(pin_index, child_sequence_index_inside_pin)` hops
    /// needed to reach the user-body Sequence. `user_pin_idx` and
    /// `prefix_len` describe the partial-prefix-with-tail pin inside the
    /// deepest Sequence.
    NestedSequencePin {
        outer_seq_index: usize,
        nested_path: Vec<(usize, usize)>,
        user_pin_idx: usize,
        prefix_len: usize,
    },
}

/// Build a fold plan if `body` contains a recognisable cross-Sequence
/// DoOnce shape. Pure inspection, no mutation.
fn build_multi_sequence_fold_plan(body: &[Stmt]) -> Option<MultiSequenceFoldPlan> {
    let inventory = collect_body_scaffold_inventory(body);
    if inventory.is_empty() {
        return None;
    }
    // Try each suffix that has any scaffold evidence in the body. Earlier
    // suffixes win for stable behaviour when the body holds scaffold for
    // multiple DoOnces.
    let mut suffixes: Vec<&str> = inventory.keys().map(String::as_str).collect();
    suffixes.sort();
    for suffix in suffixes {
        if let Some(plan) = plan_fold_for_suffix(body, &inventory, suffix) {
            return Some(plan);
        }
    }
    None
}

/// Per-suffix inventory entry: counts and indices of stmts/sequences in
/// `body` that contribute scaffold evidence for one DoOnce gate suffix.
#[derive(Default)]
struct SuffixInventory {
    /// `body` indices of sibling stmts that are scaffold pieces for this
    /// suffix (gate/init check Branch with empty arms, or var-set-to-true
    /// assignment whose lhs has this suffix).
    sibling_scaffold_indices: Vec<usize>,
    /// `body` indices of Sequences whose pins are ALL pure scaffold for
    /// this suffix (no user-body content anywhere). Pure-scaffold Sequences
    /// are safe to drop wholesale when a fold lands.
    pure_scaffold_sequence_indices: Vec<usize>,
    /// `body` indices of sibling `Assignment(Var=Literal)` stmts that
    /// participate in a contiguous `gate=false; init=true` gate-clear
    /// pair for this suffix. Tracked separately from sibling_scaffold so
    /// only matching-suffix pairs get consumed.
    sibling_gate_clear_indices: Vec<usize>,
    /// Did the inventory see an init-check Branch for this suffix?
    has_init_check: bool,
    /// Did the inventory see an init-set Assignment for this suffix?
    has_init_set: bool,
    /// First gate-var name seen for this suffix (for naming fallback).
    gate_var: Option<String>,
}

/// Collect per-suffix scaffold inventory for `body`. Recurses into Sequence
/// pin contents so deeply-nested scaffold pieces also contribute. Stmts
/// inside Branch/Loop/Switch arms are NOT inspected: those carry their
/// own structural context and shouldn't be folded into a sibling DoOnce
/// at this body level.
fn collect_body_scaffold_inventory(
    body: &[Stmt],
) -> std::collections::BTreeMap<String, SuffixInventory> {
    let mut inventory: std::collections::BTreeMap<String, SuffixInventory> =
        std::collections::BTreeMap::new();
    for (idx, stmt) in body.iter().enumerate() {
        accumulate_inventory_for_sibling(&mut inventory, idx, stmt, body);
    }
    inventory
}

/// Record scaffold evidence for one body-level stmt into `inventory`.
fn accumulate_inventory_for_sibling(
    inventory: &mut std::collections::BTreeMap<String, SuffixInventory>,
    idx: usize,
    stmt: &Stmt,
    body: &[Stmt],
) {
    // Sibling-level scaffold roles (gate/init check Branch, gate/init set).
    // `participates_in_pair` means this stmt is one half of a Pass -1
    // gate-clear pair (`gate=false; init=true` in either order, possibly
    // mismatched suffixes). Pass -1 will later fold that pair into a
    // synthetic `Call ResetDoOnce`, and the cross-arm recogniser depends
    // on that call surviving. Such stmts contribute to init/gate proof
    // (read-only evidence) but never to drop indices.
    let participates_in_pair = sibling_participates_in_pass_minus_one_pair(body, idx);
    let sibling_role = classify_doonce_role(stmt);
    if let Some((suffix, gate_var)) = role_suffix_and_gate_var(&sibling_role) {
        let entry = inventory.entry(suffix).or_default();
        if !participates_in_pair {
            entry.sibling_scaffold_indices.push(idx);
        }
        if let Some(name) = gate_var {
            entry.gate_var.get_or_insert(name);
        }
        match &sibling_role {
            DoOnceRole::InitCheck(_) => entry.has_init_check = true,
            DoOnceRole::InitSet(_) => entry.has_init_set = true,
            _ => {}
        }
    }

    // Sibling gate-clear pair with MATCHING suffix on both halves. Pass -1
    // runs before this pass so raw pairs are normally already folded into
    // a synthetic `Call(ResetDoOnce(DoOnce_<N>))`; this branch only catches
    // pairs that bypassed Pass -1 (e.g. synthetic unit-test fixtures that
    // call into this codepath directly). Real BP-decoded bodies never
    // reach this with a raw pair after the reorder. Mismatched-suffix
    // pairs are not treated as scaffold to avoid over-consumption.
    if idx + 1 < body.len() {
        if let Some(suffix) = matching_gate_clear_pair_suffix(&body[idx], &body[idx + 1]) {
            let entry = inventory.entry(suffix).or_default();
            entry.sibling_gate_clear_indices.push(idx);
            entry.sibling_gate_clear_indices.push(idx + 1);
            entry.has_init_set = true;
        }
    }

    // Synthetic `Call(ResetDoOnce(DoOnce_<N>))` produced by Pass -1.
    // Supplies init-set evidence for the matching suffix so the wrap can
    // still fold when its own scaffold lives inside a Sequence pin and
    // the BP compiler placed the cross-macro reset at the sibling level.
    // The call itself is NOT added to drop indices, so it stays as a
    // leading sibling of the resulting Latch (the else-arm reset-then-call
    // shape).
    if let Some(suffix) = synthetic_reset_doonce_suffix(stmt) {
        let entry = inventory.entry(suffix).or_default();
        entry.has_init_set = true;
    }

    // Sequence: classify pin contents into "pure scaffold for one suffix"
    // or "mixed/user-body" and update inventory.
    if let Stmt::Sequence { pins, .. } = stmt {
        match summarise_sequence_pins(pins) {
            Some(SequenceSummary::PureScaffold {
                suffix,
                has_init_check,
                has_init_set,
                gate_var,
            }) => {
                let entry = inventory.entry(suffix).or_default();
                entry.pure_scaffold_sequence_indices.push(idx);
                if has_init_check {
                    entry.has_init_check = true;
                }
                if has_init_set {
                    entry.has_init_set = true;
                }
                if let Some(name) = gate_var {
                    entry.gate_var.get_or_insert(name);
                }
            }
            // A MIXED body-level Sequence (one pin pure user body, another
            // pin pure scaffold for one suffix) carries the scaffold
            // evidence the fold needs even though it isn't safe to drop
            // wholesale. A mixed else arm can have exactly this shape:
            // pin0 = synthetic `ResetDoOnce(DoOnce_4)`, pin1 = a user
            // call. Register the suffix + init evidence so
            // `match_user_body_sequence` (which already handles the mixed
            // shape) gets a chance to run. Do NOT add the index to
            // `pure_scaffold_sequence_indices`: the matcher, not a wholesale
            // drop, consumes the Sequence.
            None => register_mixed_sequence_evidence(inventory, pins),
        }
    }
}

/// Register fold evidence for a MIXED body-level Sequence: one whose pins
/// are not all pure scaffold. For each suffix that has BOTH a pin carrying
/// matching scaffold and a pure-user-body pin, credit the suffix's init
/// evidence and gate-var name into the inventory without recording any
/// drop index. This is the minimal enrichment that lets
/// `find_user_body_location_for_suffix` find the user body when the BP
/// compiler emitted the cross-macro reset and the user call as two pins of
/// a single Sequence (no separate pure-scaffold sibling Sequence to mine).
fn register_mixed_sequence_evidence(
    inventory: &mut std::collections::BTreeMap<String, SuffixInventory>,
    pins: &[Vec<Stmt>],
) {
    let has_user_body_pin = pins.iter().any(|pin| pin_is_pure_user_body(pin));
    if !has_user_body_pin {
        return;
    }
    for pin in pins {
        for stmt in pin {
            if let Some(suffix) = synthetic_reset_doonce_suffix(stmt) {
                inventory.entry(suffix).or_default().has_init_set = true;
                continue;
            }
            let role = classify_doonce_role(stmt);
            let Some((suffix, gate_var)) = role_suffix_and_gate_var(&role) else {
                continue;
            };
            let entry = inventory.entry(suffix).or_default();
            if let Some(name) = gate_var {
                entry.gate_var.get_or_insert(name);
            }
            match role {
                DoOnceRole::InitCheck(_) => entry.has_init_check = true,
                DoOnceRole::InitSet(_) => entry.has_init_set = true,
                _ => {}
            }
        }
    }
}

/// Return `true` when `body[idx]` is part of a Pass -1 gate-clear pair
/// (`gate=false; init=true` in either order, suffixes may mismatch).
/// Pass -1 folds such pairs into a synthetic `Call ResetDoOnce(DoOnce_<gate_suffix>)`,
/// and that synthesised call later supplies init-proof for the cross-arm
/// recogniser. The cross-Sequence pass therefore must not consume the
/// init-set half here, or the pair becomes unrecoverable downstream.
fn sibling_participates_in_pass_minus_one_pair(body: &[Stmt], idx: usize) -> bool {
    if idx > 0
        && (match_doonce_reset_halves(&body[idx - 1], &body[idx]).is_some()
            || match_doonce_reset_halves(&body[idx], &body[idx - 1]).is_some())
    {
        return true;
    }
    if idx + 1 < body.len()
        && (match_doonce_reset_halves(&body[idx], &body[idx + 1]).is_some()
            || match_doonce_reset_halves(&body[idx + 1], &body[idx]).is_some())
    {
        return true;
    }
    false
}

/// Extract `(suffix, optional gate_var_name)` from a sibling-stmt role.
/// Returns `None` for `DoOnceRole::None` and `DoOnceRole::DoOnceSequence`.
fn role_suffix_and_gate_var(role: &DoOnceRole) -> Option<(String, Option<String>)> {
    let suffix = role.suffix()?.to_string();
    let gate_var = match role {
        DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => Some(name.clone()),
        _ => None,
    };
    Some((suffix, gate_var))
}

/// Per-Sequence summary used by the inventory builder.
enum SequenceSummary {
    /// Every pin in the Sequence is pure scaffold for `suffix`.
    PureScaffold {
        suffix: String,
        has_init_check: bool,
        has_init_set: bool,
        gate_var: Option<String>,
    },
}

/// Classify a Sequence's pins. Returns `Some(PureScaffold)` only when all
/// pins are pure scaffold pieces that share a single gate suffix. Returns
/// `None` for mixed Sequences (user body somewhere, or multiple suffixes).
fn summarise_sequence_pins(pins: &[Vec<Stmt>]) -> Option<SequenceSummary> {
    let mut suffix: Option<String> = None;
    let mut has_init_check = false;
    let mut has_init_set = false;
    let mut gate_var: Option<String> = None;
    let mut saw_any = false;
    for pin in pins {
        if pin.is_empty() {
            continue;
        }
        for inner in pin {
            if is_scaffold_noop_branch(inner) {
                saw_any = true;
                continue;
            }
            let role = classify_doonce_role(inner);
            let (role_suffix, role_gate_var) = role_suffix_and_gate_var(&role)?;
            // All pins must share one suffix.
            match &suffix {
                None => suffix = Some(role_suffix.clone()),
                Some(existing) if existing == &role_suffix => {}
                _ => return None,
            }
            if let Some(name) = role_gate_var {
                gate_var.get_or_insert(name);
            }
            match role {
                DoOnceRole::InitCheck(_) => has_init_check = true,
                DoOnceRole::InitSet(_) => has_init_set = true,
                _ => {}
            }
            saw_any = true;
        }
    }
    let suffix = suffix?;
    if !saw_any {
        return None;
    }
    Some(SequenceSummary::PureScaffold {
        suffix,
        has_init_check,
        has_init_set,
        gate_var,
    })
}

/// If `(first, second)` is a contiguous `gate=false; init=true` (in any
/// order) where both halves share a gate suffix, return that suffix.
/// Mirrors `Pass -1`'s pair logic but only matches WHEN the suffixes
/// agree, so cross-suffix pairs (which `Pass -1` deliberately collapses
/// into a `ResetDoOnce` for the gate suffix) don't pollute the per-suffix
/// inventory used for fold-suffix matching.
fn matching_gate_clear_pair_suffix(first: &Stmt, second: &Stmt) -> Option<String> {
    let (gate_name, init_name, _) = match_doonce_reset_halves(first, second)
        .or_else(|| match_doonce_reset_halves(second, first))?;
    let gate_suffix = doonce_var_suffix(gate_name, DOONCE_GATE_PREFIX);
    let init_suffix = doonce_var_suffix(init_name, DOONCE_INIT_PREFIX);
    if gate_suffix == init_suffix {
        Some(gate_suffix.to_string())
    } else {
        None
    }
}

/// Plan a fold for the DoOnce gate suffix `target_suffix`. Returns `None`
/// when no user-body location matches or the init-proof check fails.
fn plan_fold_for_suffix(
    body: &[Stmt],
    inventory: &std::collections::BTreeMap<String, SuffixInventory>,
    target_suffix: &str,
) -> Option<MultiSequenceFoldPlan> {
    let entry = inventory.get(target_suffix)?;
    // Locate a user-body Sequence for this suffix.
    let location = find_user_body_location_for_suffix(body, target_suffix)?;
    if !entry.has_init_check && !entry.has_init_set {
        // No init evidence at all; refuse to fold (would conflate a
        // bare gate-check + gate-set with a DoOnce wrap).
        return None;
    }
    if !init_proof_sufficient(entry, &location) {
        return None;
    }
    // Refuse to synthesise a NEW DoOnce wrap when the only init evidence
    // is a synthetic `ResetDoOnce` call (a re-arm of an already-existing
    // gate) and the user-body Sequence itself holds no real DoOnce-OPEN
    // signal. A reset clears a gate; it never opens one, so a user call
    // sitting next to a bare reset is a plain sibling, not a fresh latch.
    // Legitimate folds keep their own open inside the user-body Sequence:
    // a recognised inner `Latch{DoOnce}`,
    // a gate-check/gate-set Branch, or an init-check/init-set assignment.
    if !entry.has_init_check
        && entry.sibling_scaffold_indices.is_empty()
        && entry.pure_scaffold_sequence_indices.is_empty()
        && entry.sibling_gate_clear_indices.is_empty()
        && entry.gate_var.is_none()
        && !user_body_sequence_has_open(body, &location)
    {
        return None;
    }

    let (outer_offset, gate_var) =
        derive_fold_anchors(body, &location, entry.gate_var.as_deref(), target_suffix)?;

    let drop_indices = build_drop_indices(entry, &location);
    Some(MultiSequenceFoldPlan {
        suffix: target_suffix.to_string(),
        gate_var,
        outer_offset,
        drop_indices,
        user_body_location: location,
    })
}

/// Return `true` when the user-body Sequence at `location` carries a real
/// DoOnce-OPEN signal in any pin: a recognised inner `Latch{DoOnce}`, a
/// gate-check/gate-set Branch, or an init-check/init-set assignment. A
/// gate-CLEAR (`gate = false`, the reset half) does NOT count: it re-arms
/// an existing gate rather than opening a new one. Used to reject phantom
/// folds whose only init evidence is a sibling-level synthetic ResetDoOnce.
///
/// `NestedSequencePin` locations always return `true`: the partial-prefix
/// matcher that produces them already required a gate-check + gate-set
/// prefix inside the deepest Sequence, so the open is proven by construction.
fn user_body_sequence_has_open(body: &[Stmt], location: &UserBodyLocation) -> bool {
    let UserBodyLocation::SequencePin { seq_index, .. } = location else {
        return true;
    };
    let Some(Stmt::Sequence { pins, .. }) = body.get(*seq_index) else {
        return false;
    };
    pins.iter().flatten().any(|stmt| {
        matches!(
            stmt,
            Stmt::Latch {
                kind: LatchKind::DoOnce { .. },
                ..
            }
        ) || matches!(classify_pin_stmt(stmt), PinClass::Scaffold(role) if role.is_scaffold())
    })
}

/// A user body must be paired with at least an init-set (the BP-compiler
/// signal that this is a DoOnce expansion rather than a stray gate-check).
/// When the user-body Sequence ALREADY supplies in-Sequence init evidence
/// the parent-body inventory only needs to back the missing half.
fn init_proof_sufficient(entry: &SuffixInventory, location: &UserBodyLocation) -> bool {
    // For a SequencePin location, the Sequence's other pins (drop_pins)
    // may carry their own init evidence beyond what the inventory recorded
    // as sibling scaffold; that evidence already flows into the inventory
    // via `summarise_sequence_pins` (when applicable) or via
    // `has_init_check_in_seq` / `has_init_set_in_seq`. Here we only need
    // to satisfy "at least init-set" using the inventory.
    let _ = location;
    entry.has_init_check || entry.has_init_set
}

/// Derive the latch's offset anchor and gate-var name. Prefers the gate
/// variable already discovered in the inventory; otherwise reconstructs
/// the canonical `Temp_bool_IsClosed_Variable[_<suffix>]` name from the
/// suffix.
fn derive_fold_anchors(
    body: &[Stmt],
    location: &UserBodyLocation,
    inventory_gate_var: Option<&str>,
    suffix: &str,
) -> Option<(usize, String)> {
    let outer_offset = match location {
        UserBodyLocation::SequencePin { seq_index, .. } => body.get(*seq_index)?.offset(),
        UserBodyLocation::NestedSequencePin {
            outer_seq_index, ..
        } => body.get(*outer_seq_index)?.offset(),
    };
    let gate_var = match inventory_gate_var {
        Some(name) => name.to_string(),
        None => {
            if suffix.is_empty() {
                DOONCE_GATE_PREFIX.to_string()
            } else {
                format!("{}_{}", DOONCE_GATE_PREFIX, suffix)
            }
        }
    };
    Some((outer_offset, gate_var))
}

/// Build the sorted list of body indices to drop during the fold. Includes
/// sibling scaffold indices, sibling gate-clear-pair indices, pure-scaffold
/// Sequence indices, plus the user-body Sequence index (the Sequence itself
/// is consumed and replaced by the latch).
fn build_drop_indices(entry: &SuffixInventory, location: &UserBodyLocation) -> Vec<usize> {
    let mut drop_set: BTreeSet<usize> = BTreeSet::new();
    drop_set.extend(&entry.sibling_scaffold_indices);
    drop_set.extend(&entry.sibling_gate_clear_indices);
    drop_set.extend(&entry.pure_scaffold_sequence_indices);
    let location_index = match location {
        UserBodyLocation::SequencePin { seq_index, .. } => *seq_index,
        UserBodyLocation::NestedSequencePin {
            outer_seq_index, ..
        } => *outer_seq_index,
    };
    drop_set.insert(location_index);
    drop_set.into_iter().collect()
}

/// Find a single user-body location at this body level whose gate suffix
/// matches `target_suffix`. Walks each Sequence in `body` (and one level
/// of nesting inside Sequence pins) looking for a pin with either
/// (a) pure user content alongside pure-scaffold sibling pins for the
///     matching suffix, or
/// (b) the partial-prefix-with-tail shape (gate-check + gate-set + user
///     body) for the matching suffix.
fn find_user_body_location_for_suffix(
    body: &[Stmt],
    target_suffix: &str,
) -> Option<UserBodyLocation> {
    for (idx, stmt) in body.iter().enumerate() {
        let Stmt::Sequence { pins, .. } = stmt else {
            continue;
        };
        if let Some(location) = match_user_body_sequence(pins, target_suffix, idx) {
            return Some(location);
        }
        // One-level nested search: BP can emit the user-body Sequence
        // inside a parent Sequence's pin (the bare-suffix else-arm shape).
        // The outer Sequence's other pins must be pure scaffold
        // or otherwise consumable.
        for (pin_idx, pin) in pins.iter().enumerate() {
            for (inner_idx, inner) in pin.iter().enumerate() {
                let Stmt::Sequence {
                    pins: inner_pins, ..
                } = inner
                else {
                    continue;
                };
                let Some(inner_location) = match_user_body_sequence(inner_pins, target_suffix, idx)
                else {
                    continue;
                };
                // Ensure the outer Sequence is consumable: its non-target
                // pins must be pure scaffold (any suffix; we just need
                // confidence the wrap is safe to peel), and the pin that
                // holds our inner Sequence must contain ONLY that inner
                // Sequence so we don't lose unrelated content.
                if pin.len() != 1 {
                    return None;
                }
                if !outer_sequence_consumable(pins, pin_idx) {
                    return None;
                }
                let UserBodyLocation::SequencePin {
                    user_pin_idx,
                    prefix_len,
                    ..
                } = inner_location
                else {
                    unreachable!("match_user_body_sequence returns SequencePin");
                };
                let _ = inner_idx;
                return Some(UserBodyLocation::NestedSequencePin {
                    outer_seq_index: idx,
                    nested_path: vec![(pin_idx, 0)],
                    user_pin_idx,
                    prefix_len,
                });
            }
        }
    }
    None
}

/// Return `true` when the outer Sequence's other pins (not `target_pin`)
/// are pure scaffold (any suffix) and therefore safe to drop alongside
/// the user-body wrap.
fn outer_sequence_consumable(pins: &[Vec<Stmt>], target_pin: usize) -> bool {
    for (pin_idx, pin) in pins.iter().enumerate() {
        if pin_idx == target_pin {
            continue;
        }
        if pin.is_empty() {
            continue;
        }
        if !pin_is_pure_scaffold_any_suffix(pin) {
            return false;
        }
    }
    true
}

/// Return `true` when every stmt in `pin` is a DoOnce-scaffold piece
/// (any suffix) or the synthetic `Call ResetDoOnce(DoOnce_*)` produced
/// by `Pass -1`. Used to validate that a sibling pin of the user-body
/// Sequence's container is safe to discard.
fn pin_is_pure_scaffold_any_suffix(pin: &[Stmt]) -> bool {
    // Roles + Noop + SyntheticReset. This WIDER accept-set (vs init_check's
    // roles-only pin_is_pure_doonce_scaffold) is the load-bearing divergence:
    // a discardable sibling pin may legitimately contain a folded ResetDoOnce
    // or a pop_flow no-op, which a pure-scaffold pin here is allowed to carry.
    pin.iter().all(|stmt| match classify_pin_stmt(stmt) {
        PinClass::Scaffold(role) => role.is_scaffold(),
        PinClass::Noop | PinClass::SyntheticReset => true,
        PinClass::UserBody => false,
    })
}

/// Match a Sequence's pins for a user-body candidate at suffix `target_suffix`.
/// `seq_index` is the body-level index of this Sequence (passed through to
/// the returned location for the rewriter).
fn match_user_body_sequence(
    pins: &[Vec<Stmt>],
    target_suffix: &str,
    seq_index: usize,
) -> Option<UserBodyLocation> {
    if pins.is_empty() {
        return None;
    }
    // First search for the partial-prefix-with-tail pin shape: any pin
    // beginning with `[Branch(gate)=empty, gate=true, ...]` for suffix
    // `target_suffix`. The remaining pins must be consumable. Single-pin
    // Sequences with this shape are accepted: the pin itself carries
    // gate-check + gate-set scaffold so no sibling pin is required.
    for (pin_idx, pin) in pins.iter().enumerate() {
        if let Some(prefix_len) = partial_prefix_with_tail_length(pin, target_suffix) {
            if !sibling_pins_consumable_for_suffix(pins, pin_idx, target_suffix) {
                continue;
            }
            return Some(UserBodyLocation::SequencePin {
                seq_index,
                user_pin_idx: pin_idx,
                prefix_len,
            });
        }
    }
    if pins.len() < 2 {
        return None;
    }
    // Otherwise look for a pure-user-body pin paired with pure-scaffold
    // siblings for `target_suffix`. The user-body pin must have no
    // scaffold prefix (entire pin is non-scaffold) and at least one
    // sibling pin must carry suffix-matching scaffold so the fold has
    // local evidence the wrap belongs here.
    for (pin_idx, pin) in pins.iter().enumerate() {
        if pin.is_empty() {
            continue;
        }
        if !pin_is_pure_user_body(pin) {
            continue;
        }
        if !sibling_pins_have_suffix_scaffold(pins, pin_idx, target_suffix) {
            continue;
        }
        if !sibling_pins_consumable_for_suffix(pins, pin_idx, target_suffix) {
            continue;
        }
        return Some(UserBodyLocation::SequencePin {
            seq_index,
            user_pin_idx: pin_idx,
            prefix_len: 0,
        });
    }
    None
}

/// Return `Some(prefix_len)` when `pin` begins with the partial-prefix
/// shape for `target_suffix`: a gate-check Branch (empty arms, cond
/// `Var(gate_<suffix>)`), followed by a gate-set assignment, followed
/// by at least one user-body stmt. Returns `None` otherwise.
fn partial_prefix_with_tail_length(pin: &[Stmt], target_suffix: &str) -> Option<usize> {
    if pin.len() < 3 {
        return None;
    }
    let DoOnceRole::GateCheck(first_name) = classify_doonce_role(&pin[0]) else {
        return None;
    };
    if doonce_var_suffix(&first_name, DOONCE_GATE_PREFIX) != target_suffix {
        return None;
    }
    let DoOnceRole::GateSet(second_name) = classify_doonce_role(&pin[1]) else {
        return None;
    };
    if doonce_var_suffix(&second_name, DOONCE_GATE_PREFIX) != target_suffix {
        return None;
    }
    // Tail must contain at least one non-scaffold stmt (the user body).
    if !pin
        .iter()
        .skip(2)
        .any(|stmt| matches!(classify_doonce_role(stmt), DoOnceRole::None))
    {
        return None;
    }
    Some(2)
}

/// Return `true` when every stmt in `pin` is genuine user-body content
/// (no DoOnce scaffold role and not the synthetic `Call ResetDoOnce(...)`
/// that `Pass -1` emits). Empty pins return `false`: an empty pin carries
/// no positive evidence of being the user-body slot.
fn pin_is_pure_user_body(pin: &[Stmt]) -> bool {
    if pin.is_empty() {
        return false;
    }
    pin.iter().all(|stmt| {
        !is_synthetic_reset_doonce(stmt) && matches!(classify_doonce_role(stmt), DoOnceRole::None)
    })
}

/// Return `true` when at least one sibling pin (not `user_pin_idx`)
/// carries scaffold pieces with `target_suffix`. Without this check a
/// pure-user-body pin could fold against unrelated noise in another pin.
fn sibling_pins_have_suffix_scaffold(
    pins: &[Vec<Stmt>],
    user_pin_idx: usize,
    target_suffix: &str,
) -> bool {
    pins.iter().enumerate().any(|(pin_idx, pin)| {
        if pin_idx == user_pin_idx {
            return false;
        }
        pin_carries_suffix_scaffold(pin, target_suffix)
    })
}

/// Sibling pins must be entirely scaffold for `target_suffix` (or empty,
/// or a gate-clear pair for `target_suffix`). Adjacent BP DoOnces with
/// different suffixes must not be lumped together here.
fn sibling_pins_consumable_for_suffix(
    pins: &[Vec<Stmt>],
    user_pin_idx: usize,
    target_suffix: &str,
) -> bool {
    for (pin_idx, pin) in pins.iter().enumerate() {
        if pin_idx == user_pin_idx {
            continue;
        }
        if !pin_is_consumable_for_suffix(pin, target_suffix) {
            return false;
        }
    }
    true
}

/// Return `true` when `pin` carries scaffold evidence for `target_suffix`
/// (gate/init check/set role with matching suffix, a matching gate-clear
/// pair, or a synthetic `Call ResetDoOnce(DoOnce_<suffix>)` produced by
/// `Pass -1`). Empty pins return `false`.
fn pin_carries_suffix_scaffold(pin: &[Stmt], target_suffix: &str) -> bool {
    if pin.is_empty() {
        return false;
    }
    // Direct scaffold role with matching suffix.
    if pin.iter().any(|stmt| {
        let role = classify_doonce_role(stmt);
        match role {
            DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => {
                doonce_var_suffix(&name, DOONCE_GATE_PREFIX) == target_suffix
            }
            DoOnceRole::InitCheck(name) | DoOnceRole::InitSet(name) => {
                doonce_var_suffix(&name, DOONCE_INIT_PREFIX) == target_suffix
            }
            _ => false,
        }
    }) {
        return true;
    }
    if pin
        .iter()
        .any(|stmt| is_reset_doonce_call_for_suffix(stmt, target_suffix))
    {
        return true;
    }
    // Matching gate-clear pair anywhere in the pin.
    pin.windows(2).any(|pair| {
        matching_gate_clear_pair_suffix(&pair[0], &pair[1]).as_deref() == Some(target_suffix)
    })
}

/// `pin` is consumable when every stmt is either a scaffold piece for
/// `target_suffix`, a `target_suffix` gate-clear pair, or a synthetic
/// `Call ResetDoOnce(DoOnce_<suffix>)` for `target_suffix`. Mixed pins
/// (other-suffix scaffold, or user-body content) fail.
fn pin_is_consumable_for_suffix(pin: &[Stmt], target_suffix: &str) -> bool {
    if pin.is_empty() {
        return true;
    }
    let mut idx = 0;
    while idx < pin.len() {
        if is_scaffold_noop_branch(&pin[idx]) {
            idx += 1;
            continue;
        }
        if is_reset_doonce_call_for_suffix(&pin[idx], target_suffix) {
            idx += 1;
            continue;
        }
        let role = classify_doonce_role(&pin[idx]);
        match role {
            DoOnceRole::GateCheck(name) | DoOnceRole::GateSet(name) => {
                if doonce_var_suffix(&name, DOONCE_GATE_PREFIX) != target_suffix {
                    return false;
                }
                idx += 1;
            }
            DoOnceRole::InitCheck(name) | DoOnceRole::InitSet(name) => {
                if doonce_var_suffix(&name, DOONCE_INIT_PREFIX) != target_suffix {
                    return false;
                }
                idx += 1;
            }
            DoOnceRole::DoOnceSequence(_) => return false,
            DoOnceRole::None => {
                // Allow a contiguous gate-clear pair for the target suffix.
                if idx + 1 < pin.len()
                    && matching_gate_clear_pair_suffix(&pin[idx], &pin[idx + 1]).as_deref()
                        == Some(target_suffix)
                {
                    idx += 2;
                    continue;
                }
                return false;
            }
        }
    }
    true
}

/// Apply a planned fold. Mutates `body` in place: drops scaffold stmts,
/// extracts the user-body Sequence pin tail, wraps it in `Stmt::Latch`.
fn apply_multi_sequence_fold(body: &mut Vec<Stmt>, plan: MultiSequenceFoldPlan) {
    let MultiSequenceFoldPlan {
        suffix,
        gate_var,
        outer_offset,
        drop_indices,
        user_body_location,
    } = plan;

    // Capture synthetic `Call(ResetDoOnce(DoOnce_*))` calls living in the
    // user-body Sequence's non-user-body pins BEFORE extraction. These
    // are cross-macro reset siblings the BP compiler emitted in a pin
    // adjacent to the user body. When the Sequence gets dropped wholesale,
    // the calls would be lost; we lift them as leading siblings of the
    // resulting Latch instead (the else-arm reset-then-call shape).
    //
    // Suffixes already represented at sibling level (via a raw gate-clear
    // pair Pass -1 will fold next, or via an existing synthetic call) are
    // excluded so the lift doesn't duplicate (the shape where the BP
    // compiler emits the same reset both at sibling level and inside the
    // wrap's adjacent pin).
    let suffixes_already_at_sibling =
        collect_sibling_level_reset_suffixes(body, &user_body_location);
    let lifted_resets: Vec<Stmt> = collect_lifted_resets(body, &user_body_location)
        .into_iter()
        .filter(|stmt| match synthetic_reset_doonce_suffix(stmt) {
            Some(suffix) => !suffixes_already_at_sibling.contains(&suffix),
            None => true,
        })
        .collect();

    // Extract the user body BEFORE draining other indices, since the
    // extraction reads from the Sequence that will be dropped.
    let user_body = extract_user_body(body, &user_body_location).unwrap_or_default();
    if user_body.is_empty() {
        return;
    }

    let name = derive_doonce_name_with_suffix(&user_body, &gate_var, &suffix);
    let latch = Stmt::Latch {
        kind: LatchKind::DoOnce { name, gate_var },
        init: vec![],
        body: user_body,
        offset: outer_offset,
    };

    // Compute the slot the latch should occupy after the drop sweep.
    // `location_index` shifts down by the count of dropped indices that
    // sit strictly before it.
    let location_index = match user_body_location {
        UserBodyLocation::SequencePin { seq_index, .. } => seq_index,
        UserBodyLocation::NestedSequencePin {
            outer_seq_index, ..
        } => outer_seq_index,
    };
    let mut to_drop: Vec<usize> = drop_indices
        .into_iter()
        .filter(|idx| *idx != location_index)
        .collect();
    to_drop.sort_unstable();
    let shift = to_drop.iter().filter(|idx| **idx < location_index).count();
    for idx in to_drop.into_iter().rev() {
        body.remove(idx);
    }
    // Replace the user-body Sequence at its post-shift slot with the latch,
    // splicing the lifted reset calls in BEFORE the latch.
    let target_index = location_index - shift;
    let lifted_count = lifted_resets.len();
    if target_index >= body.len() {
        body.extend(lifted_resets);
        body.push(latch);
    } else {
        // Replace the slot with the latch first, then insert the lifted
        // resets ahead of it. Using splice keeps the relative order.
        body[target_index] = latch;
        for (offset, call) in lifted_resets.into_iter().enumerate() {
            body.insert(target_index + offset, call);
        }
        let _ = lifted_count;
    }
}

/// Walk the user-body Sequence and capture every synthetic
/// `Call(ResetDoOnce(DoOnce_*))` living in pins other than the user-body
/// pin. The captures are returned in source-pin order so the lifted
/// siblings preserve the BP compiler's original sequencing.
///
/// For `NestedSequencePin` locations the inner pins live one Sequence
/// level deeper; the outer Sequence's other pins are walked too so
/// cross-macro resets at any nested level get preserved.
fn collect_lifted_resets(body: &[Stmt], location: &UserBodyLocation) -> Vec<Stmt> {
    let mut lifted = Vec::new();
    match location {
        UserBodyLocation::SequencePin {
            seq_index,
            user_pin_idx,
            ..
        } => {
            let Some(Stmt::Sequence { pins, .. }) = body.get(*seq_index) else {
                return lifted;
            };
            for (pin_idx, pin) in pins.iter().enumerate() {
                if pin_idx == *user_pin_idx {
                    continue;
                }
                collect_synthetic_resets_in_stmts(pin, &mut lifted);
            }
        }
        UserBodyLocation::NestedSequencePin {
            outer_seq_index,
            nested_path,
            user_pin_idx,
            ..
        } => {
            let Some(Stmt::Sequence { pins, .. }) = body.get(*outer_seq_index) else {
                return lifted;
            };
            // Outer pins: every pin except the one leading to the nested
            // user-body Sequence contributes.
            let outer_target_pin = nested_path.first().map(|(pin_idx, _)| *pin_idx);
            for (pin_idx, pin) in pins.iter().enumerate() {
                if Some(pin_idx) == outer_target_pin {
                    continue;
                }
                collect_synthetic_resets_in_stmts(pin, &mut lifted);
            }
            // Walk down the nested path, capturing resets in sibling pins
            // at each level. The deepest level's user-body pin gets the
            // user_pin_idx exclusion; intermediate levels have a single
            // target pin recorded in the path.
            let mut current_pins = pins;
            for (depth, (pin_idx, child_seq_idx)) in nested_path.iter().enumerate() {
                let Some(pin) = current_pins.get(*pin_idx) else {
                    return lifted;
                };
                let Some(child) = pin.get(*child_seq_idx) else {
                    return lifted;
                };
                let Stmt::Sequence {
                    pins: child_pins, ..
                } = child
                else {
                    return lifted;
                };
                // At the deepest level, exclude the user-body pin. At
                // intermediate levels, exclude the next nested-path pin.
                let exclude_pin = if depth + 1 == nested_path.len() {
                    *user_pin_idx
                } else {
                    nested_path[depth + 1].0
                };
                for (inner_pin_idx, inner_pin) in child_pins.iter().enumerate() {
                    if inner_pin_idx == exclude_pin {
                        continue;
                    }
                    collect_synthetic_resets_in_stmts(inner_pin, &mut lifted);
                }
                current_pins = child_pins;
            }
        }
    }
    lifted
}

/// Append every synthetic `Call(ResetDoOnce(DoOnce_*))` found at the top
/// level of `stmts` to `out`. Does not recurse into nested bodies; the
/// fold only lifts calls that lived as direct pin siblings of the
/// user-body Sequence's drop set.
fn collect_synthetic_resets_in_stmts(stmts: &[Stmt], out: &mut Vec<Stmt>) {
    for stmt in stmts {
        if is_synthetic_reset_doonce(stmt) {
            out.push(stmt.clone());
        }
    }
}

/// Collect suffixes whose reset is already represented at the body's
/// sibling level (i.e. NOT inside the user-body Sequence). Pre-Pass-1
/// raw gate-clear pairs count even with mismatched gate/init suffixes:
/// `match_reset_doonce_pair` synthesises `Call(ResetDoOnce(DoOnce_<gate_suffix>))`
/// using the gate side's suffix, so the lifted call duplicates regardless
/// of init suffix alignment. The body indices belonging to the user-body
/// Sequence are skipped so its internal pin contents don't contribute.
fn collect_sibling_level_reset_suffixes(
    body: &[Stmt],
    location: &UserBodyLocation,
) -> BTreeSet<String> {
    let location_index = match location {
        UserBodyLocation::SequencePin { seq_index, .. } => *seq_index,
        UserBodyLocation::NestedSequencePin {
            outer_seq_index, ..
        } => *outer_seq_index,
    };
    let mut suffixes: BTreeSet<String> = BTreeSet::new();
    for (idx, stmt) in body.iter().enumerate() {
        if idx == location_index {
            continue;
        }
        if let Some(suffix) = synthetic_reset_doonce_suffix(stmt) {
            suffixes.insert(suffix);
        }
        if idx + 1 < body.len() && idx + 1 != location_index {
            if let Some(suffix) = pass_minus_one_pair_gate_suffix(&body[idx], &body[idx + 1]) {
                suffixes.insert(suffix);
            }
        }
    }
    suffixes
}

/// Return the gate-side suffix of a Pass -1 gate-clear pair regardless
/// of init-side suffix alignment. Mirrors `match_reset_doonce_pair`'s
/// gate-suffix naming, so the result identifies the synthetic call Pass
/// -1 will emit for this pair.
fn pass_minus_one_pair_gate_suffix(first: &Stmt, second: &Stmt) -> Option<String> {
    let (gate_name, _, _) = match_doonce_reset_halves(first, second)
        .or_else(|| match_doonce_reset_halves(second, first))?;
    Some(doonce_var_suffix(gate_name, DOONCE_GATE_PREFIX).to_string())
}

/// Derive the latch's user-body content, draining it out of `body`'s
/// Sequence pin. The Sequence at `location_index` is left in place (the
/// caller drops it during the index sweep).
fn extract_user_body(body: &mut [Stmt], location: &UserBodyLocation) -> Option<Vec<Stmt>> {
    match location {
        UserBodyLocation::SequencePin {
            seq_index,
            user_pin_idx,
            prefix_len,
            ..
        } => extract_user_body_from_pin(body, *seq_index, *user_pin_idx, *prefix_len),
        UserBodyLocation::NestedSequencePin {
            outer_seq_index,
            nested_path,
            user_pin_idx,
            prefix_len,
        } => {
            let Some(Stmt::Sequence { pins, .. }) = body.get_mut(*outer_seq_index) else {
                return None;
            };
            let mut current_pins: &mut Vec<Vec<Stmt>> = pins;
            for (pin_idx, child_seq_idx) in nested_path {
                let pin = current_pins.get_mut(*pin_idx)?;
                let inner_stmt = pin.get_mut(*child_seq_idx)?;
                let Stmt::Sequence {
                    pins: inner_pins, ..
                } = inner_stmt
                else {
                    return None;
                };
                current_pins = inner_pins;
            }
            let pin = current_pins.get_mut(*user_pin_idx)?;
            if *prefix_len > pin.len() {
                return None;
            }
            let mut tail = pin.split_off(*prefix_len);
            while tail.first().is_some_and(is_scaffold_noop_branch) {
                tail.remove(0);
            }
            Some(tail)
        }
    }
}

/// Drain the user-body tail out of a Sequence pin at `body[seq_index]`.
fn extract_user_body_from_pin(
    body: &mut [Stmt],
    seq_index: usize,
    user_pin_idx: usize,
    prefix_len: usize,
) -> Option<Vec<Stmt>> {
    let Some(Stmt::Sequence { pins, .. }) = body.get_mut(seq_index) else {
        return None;
    };
    let pin = pins.get_mut(user_pin_idx)?;
    if prefix_len > pin.len() {
        return None;
    }
    let mut tail = pin.split_off(prefix_len);
    while tail.first().is_some_and(is_scaffold_noop_branch) {
        tail.remove(0);
    }
    Some(tail)
}

/// Name derivation that prefers the user body's first non-library call,
/// falling back to `DoOnce[_<suffix>]` from the gate suffix.
fn derive_doonce_name_with_suffix(body: &[Stmt], gate_var: &str, suffix: &str) -> String {
    if let Some(name) = first_user_call_name(body) {
        return name;
    }
    if suffix.is_empty() {
        // Bare suffix: prefer `DoOnce` (matches `fallback_name_from_gate`).
        let _ = gate_var;
        return "DoOnce".to_string();
    }
    fallback_name_from_gate(gate_var)
}

/// Cross-event inline DoOnce fold for the walker arm-decode path.
///
/// Matches the specific 2-pin Sequence shape the region walker emits
/// for a DoOnce whose scaffold lives across event boundaries (the gate
/// variable's init-check / init-set / outer suffix belong to a sibling
/// event's Latch, so the local arm only sees `gate-check + gate-set +
/// user-call`). The standard `try_rewrite_compound_doonce` rejects this
/// shape because pin0 has already folded to a `Call(ResetDoOnce(...))`
/// and pin1 wraps the user body in an extra Sequence layer.
///
/// Required shape (every component, no tolerance):
///   `Stmt::Sequence{ pins: [pin0, pin1] }` exactly 2 pins, where
///   - `pin0` = `[Stmt::Call{ func: Var("ResetDoOnce"), args: [_] }]`
///     (single statement, single call, exactly ResetDoOnce).
///   - `pin1` = `[Stmt::Sequence{ pins: [inner_pin] }]`
///     (single statement that is a single-pin Sequence).
///   - `inner_pin` = exactly 3 statements in this order:
///       1. `Stmt::Branch{ cond: Var(gate_var), then: empty, else: empty }`
///          where `gate_var` starts with `DOONCE_GATE_PREFIX`.
///       2. `Stmt::Assignment{ lhs: Var(gate_var), rhs: Literal("true") }`
///          with the same `gate_var` name.
///       3. `Stmt::Call{ ... }` (the user body call).
///
/// On match the outer Sequence is replaced by two flat siblings:
///   1. the `Call(ResetDoOnce(...))` from pin0 (verbatim).
///   2. `Stmt::Latch{ kind: DoOnce{ name, gate_var }, body: [user_call] }`
///      whose display name comes from `derive_doonce_name_with_suffix`
///      (preferring the first user-call name in the body) and whose
///      offset matches the outer Sequence.
///
/// Returns `true` when at least one replacement was made.
pub(super) fn try_rewrite_cross_event_doonce_in_sequence(body: &mut Vec<Stmt>) -> bool {
    let mut rewrote = false;
    let mut idx = 0;
    while idx < body.len() {
        if let Some(replacement) = match_cross_event_doonce_in_sequence(&body[idx]) {
            body.splice(idx..=idx, replacement);
            // The splice inserted 2 stmts (reset + latch); advance past both.
            idx += 2;
            rewrote = true;
            continue;
        }
        idx += 1;
    }
    rewrote
}

/// Validate the shape and return `[ResetDoOnce-call, Latch::DoOnce]`
/// when it holds. Returns `None` otherwise so the caller skips the slot.
fn match_cross_event_doonce_in_sequence(stmt: &Stmt) -> Option<Vec<Stmt>> {
    let Stmt::Sequence { pins, offset } = stmt else {
        return None;
    };
    if pins.len() != 2 {
        return None;
    }
    let pin0 = &pins[0];
    let pin1 = &pins[1];
    if pin0.len() != 1 || pin1.len() != 1 {
        return None;
    }
    // pin0 = [Call(ResetDoOnce, [_])]
    let reset_call = &pin0[0];
    if !is_reset_doonce_call_stmt(reset_call) {
        return None;
    }
    // pin1 = [Sequence{ pins: [inner_pin] }]
    let Stmt::Sequence {
        pins: inner_pins, ..
    } = &pin1[0]
    else {
        return None;
    };
    if inner_pins.len() != 1 {
        return None;
    }
    let inner_pin = &inner_pins[0];
    if inner_pin.len() != 3 {
        return None;
    }
    // inner_pin[0]: Branch(cond=Var(gate_var), then empty, else empty),
    //               gate_var starts with DOONCE_GATE_PREFIX.
    let Stmt::Branch {
        cond,
        then_body,
        else_body,
        ..
    } = &inner_pin[0]
    else {
        return None;
    };
    if !then_body.is_empty() || !else_body.is_empty() {
        return None;
    }
    let Expr::Var(branch_gate_var) = cond else {
        return None;
    };
    if !branch_gate_var.starts_with(DOONCE_GATE_PREFIX) {
        return None;
    }
    // inner_pin[1]: Assignment(Var(gate_var) = true) same gate_var name.
    let (assign_gate_var, _gate_set_offset) = match_var_assigned_literal(&inner_pin[1], "true")?;
    if assign_gate_var != branch_gate_var.as_str() {
        return None;
    }
    // inner_pin[2]: Stmt::Call (user body call).
    if !matches!(inner_pin[2], Stmt::Call { .. }) {
        return None;
    }

    // All shape checks passed. Build the replacement: reset call (cloned
    // from pin0) and a Latch::DoOnce wrapping the user call.
    let reset_clone = reset_call.clone();
    let user_call = inner_pin[2].clone();
    let gate_var = branch_gate_var.clone();
    // The suffix the recognizer uses for fallback naming follows the gate
    // variable's `Temp_bool_IsClosed_Variable[_N]` form. Bare prefix is
    // suffix-empty (matches `fallback_name_from_gate`).
    let suffix = gate_var
        .strip_prefix(DOONCE_GATE_PREFIX)
        .map(|raw| raw.trim_start_matches('_').to_string())
        .unwrap_or_default();
    let user_body = vec![user_call];
    let display_name = derive_doonce_name_with_suffix(&user_body, &gate_var, &suffix);
    let latch = Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: display_name,
            gate_var,
        },
        init: vec![],
        body: user_body,
        offset: *offset,
    };
    Some(vec![reset_clone, latch])
}
