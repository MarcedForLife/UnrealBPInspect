//! Graph-identity DoOnce wrap synthesis.
//!
//! The live consumer is `plan_doonce_wrap_synthesis` /
//! `apply_doonce_wrap_synthesis`: it resolves the cross-body-unreachable
//! DoOnce candidates the byte recognizer cannot reach (a guarded call in a
//! Branch arm whose gate scaffold lives in a sibling body) from the
//! flow-stack formation pass (`cfg::macro_region::form_event_macro_regions`)
//! and wraps the matching flat call after the transform stack runs.

use std::collections::BTreeSet;

use crate::bytecode::cfg::macro_region::{
    attribute_macro_gate, decode_macro_region_body, form_event_macro_regions, MacroRegionCandidate,
};
use crate::bytecode::cfg::ControlFlowGraph;
use crate::bytecode::decode::ctx::DecodeCtx;
use crate::bytecode::k2node_byte_map::K2NodeByteMap;
use crate::bytecode::names::MacroKind;
use crate::bytecode::partition::OpcodeGraph;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::latch_recognition::{
    DOONCE_CALL_NAME, LIBRARY_FUNC_PREFIXES, RESET_DOONCE_CALL_NAME,
};

/// The `Temp_bool_*` gate var named by the candidate's in-body `=false`
/// init-seed, when exactly one distinct such var sits in the body
/// geometry. Reads the locality-pass byte map and the CFG block extents
/// directly (the same maps `select_gate_set` reads); not inference.
/// `None` when no in-body seed exists or several distinct seed vars sit
/// in the body.
fn candidate_seed_gate_var(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> Option<String> {
    let body_spans: Vec<std::ops::Range<usize>> = candidate
        .member_blocks
        .iter()
        .filter_map(|&block_id| cfg.blocks.get(block_id))
        .filter(|block| !block.opcodes.is_empty() && block.end > block.start)
        .map(|block| block.start..block.end)
        .collect();
    let mut seed_vars: BTreeSet<String> = BTreeSet::new();
    for (&offset, &owner) in &map.gate_let_owner_by_offset {
        if owner != candidate.node_id {
            continue;
        }
        if map.gate_let_is_set_by_offset.get(&offset).copied() != Some(false) {
            continue;
        }
        if !body_spans.iter().any(|span| span.contains(&offset)) {
            continue;
        }
        if let Some(var) = map.gate_let_var_by_offset.get(&offset) {
            seed_vars.insert(var.clone());
        }
    }
    if seed_vars.len() == 1 {
        seed_vars.into_iter().next()
    } else {
        None
    }
}

/// Every `=true` gate-SET disk offset the locality pass attributed to
/// the node on `gate_var` (sorted). The attributed gate is one of these;
/// when ambiguous all of them are reported.
fn node_gate_sets_on_var(node_id: usize, map: &K2NodeByteMap, gate_var: &str) -> Vec<usize> {
    let mut offsets: Vec<usize> = map
        .gate_let_owner_by_offset
        .iter()
        .filter(|(_, &owner)| owner == node_id)
        .map(|(&offset, _)| offset)
        .filter(|offset| map.gate_let_is_set_by_offset.get(offset).copied() == Some(true))
        .filter(|offset| {
            map.gate_let_var_by_offset.get(offset).map(String::as_str) == Some(gate_var)
        })
        .collect();
    offsets.sort_unstable();
    offsets
}

/// The first user call inside a Latch body (recursing through nested
/// wrappers), as a display string. `None` when the body has no call.
fn first_body_call(body: &[Stmt]) -> Option<String> {
    for stmt in body {
        match stmt {
            Stmt::Call { func, args, .. } => return Some(render_call(func, args)),
            Stmt::Latch { body: inner, .. } => {
                if let Some(call) = first_body_call(inner) {
                    return Some(call);
                }
            }
            _ => {}
        }
    }
    None
}

/// Render a call expression as `Name(arg, arg)` for the diagnostic.
fn render_call(func: &crate::bytecode::expr::Expr, args: &[crate::bytecode::expr::Expr]) -> String {
    let name = match func {
        crate::bytecode::expr::Expr::Var(name) => name.clone(),
        other => format!("{:?}", other),
    };
    let arg_text = args
        .iter()
        .map(|arg| match arg {
            crate::bytecode::expr::Expr::Var(value) => value.clone(),
            crate::bytecode::expr::Expr::Literal(value) => value.clone(),
            other => format!("{:?}", other),
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}({})", name, arg_text)
}

/// Locate the `Latch{DoOnce}` for `gate_var` in `body`, returning the
/// enclosing Branch arm (`THEN(cond)` / `ELSE(cond)` / `top-level`) and
/// the first call in its body. Recurses through every container variant
/// so a nested gate is found. Returns `None` when no Latch for the var
/// exists (the flat / unwrapped case).
fn locate_doonce(
    body: &[Stmt],
    gate_var: &str,
    arm_label: &str,
) -> Option<(String, Option<String>)> {
    for stmt in body {
        if let Stmt::Latch {
            kind: LatchKind::DoOnce { gate_var: var, .. },
            body: latch_body,
            ..
        } = stmt
        {
            if var == gate_var {
                return Some((arm_label.to_string(), first_body_call(latch_body)));
            }
        }
        let found = match stmt {
            Stmt::Branch {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let cond_text = render_expr(cond);
                locate_doonce(then_body, gate_var, &format!("THEN({})", cond_text))
                    .or_else(|| locate_doonce(else_body, gate_var, &format!("ELSE({})", cond_text)))
            }
            Stmt::Sequence { pins, .. } => pins
                .iter()
                .find_map(|pin| locate_doonce(pin, gate_var, arm_label)),
            Stmt::Loop {
                body, completion, ..
            } => locate_doonce(body, gate_var, arm_label).or_else(|| {
                completion
                    .as_ref()
                    .and_then(|comp| locate_doonce(comp, gate_var, arm_label))
            }),
            Stmt::Switch { cases, default, .. } => cases
                .iter()
                .find_map(|case| locate_doonce(&case.body, gate_var, arm_label))
                .or_else(|| {
                    default
                        .as_ref()
                        .and_then(|def| locate_doonce(def, gate_var, arm_label))
                }),
            Stmt::Latch {
                init,
                body: latch_body,
                ..
            } => locate_doonce(init, gate_var, arm_label)
                .or_else(|| locate_doonce(latch_body, gate_var, arm_label)),
            _ => None,
        };
        if found.is_some() {
            return found;
        }
    }
    None
}

/// Render an expression as a compact condition string for the `arm`
/// column. Best-effort; falls back to debug for shapes the diagnostic
/// does not need to read precisely.
fn render_expr(expr: &crate::bytecode::expr::Expr) -> String {
    match expr {
        crate::bytecode::expr::Expr::Var(name) => name.clone(),
        crate::bytecode::expr::Expr::Literal(value) => value.clone(),
        other => format!("{:?}", other),
    }
}

/// A validated DoOnce-wrap candidate, resolved while the per-event
/// `DecodeCtx` is alive but before the transform stack runs. Holds only
/// owned data so the actual body rewrite (`apply_doonce_wrap_synthesis`)
/// can run later against the fully transform-stacked body, after the
/// per-event `DecodeCtx` and its borrows have been dropped.
///
/// The split keeps the pass output-neutral: every `ctx`/`cfg`/`map`
/// computation (gate-var resolution, the out-of-range discriminator, the
/// guarded-call-name decode, the sibling-reset-name decode) happens in
/// `plan_doonce_wrap_synthesis` while those borrows are valid; the body-only
/// rewrite (`locate_doonce` skip, `sole_other_doonce_latch_name` fallback,
/// `wrap_flat_doonce_anywhere`) happens in `apply_doonce_wrap_synthesis`. None
/// of the planning step reads the statement body, and none of the apply step
/// reads `ctx`.
pub(crate) struct SynthWrapPlan {
    gate_var: String,
    /// Display name of the guarded user call this wrap derives from, the
    /// flat call the apply step locates and wraps in the transformed body.
    target_name: String,
    /// Display name the captured trailing `ResetDoOnce(...)` should re-arm:
    /// the SIBLING DoOnce the wrap's reset targets, resolved from the
    /// candidate's own bytecode geometry (a disk-order partition decode that
    /// differs from `target_name`). `None` when no distinct sibling is
    /// recoverable at plan time, in which case the apply step falls back to a
    /// body `Latch{DoOnce}` scan.
    sibling_reset_name: Option<String>,
    /// A re-key directive instead of a wrap. The byte-shape fold provisionally
    /// bound an existing `Latch{DoOnce}` to a co-located sibling's gate (the
    /// only local scaffold being a gate-CLEAR reset-pair, not this call's own
    /// gate-open). When `Some(display_name)`, the apply step finds the
    /// top-level `Latch{DoOnce}` named `display_name` whose gate differs from
    /// `gate_var` and re-keys it onto `gate_var` (this node's real gate). This
    /// vacates the foreign gate so the genuine wrap (the displaced twin) can
    /// fire on it. This handles an else-arm cross-body reset whose fold bound
    /// it to a co-located sibling's gate rather than its own.
    rekey_latch_named: Option<String>,
}

/// The negative gate-set discriminator: every `=true` gate-SET the node
/// owns on the gate var must lie OUTSIDE the event's owned byte ranges. An
/// in-range gate-SET means the scaffold is reachable and the byte recognizer
/// owns it, so synthesis must not touch it (the named-guard zero-divergence
/// contract). An empty `gate_sets` is handled by the caller before this.
fn all_gate_sets_out_of_range(
    gate_sets: &[usize],
    owned_ranges: &[std::ops::Range<usize>],
) -> bool {
    gate_sets
        .iter()
        .all(|offset| !owned_ranges.iter().any(|range| range.contains(offset)))
}

/// The positive body-before-scaffold discriminator: the matching
/// POP/continuation must sit at a LOWER disk offset than the PUSH, the
/// genuine cross-body layout the synthesis targets (the gated body precedes
/// its gate scaffold in the byte stream). Required IN ADDITION to the
/// out-of-range gate-set check so a bare gate-LET mis-attribution cannot
/// fabricate a wrap on a normally-laid-out (`push <= pop`) node.
fn is_body_before_scaffold(pop_addr: usize, push_addr: usize) -> bool {
    pop_addr < push_addr
}

/// The per-candidate features the synthesis discriminator reads, resolved
/// once in a first pass so the survival decision can correlate sibling
/// candidates (the mis-decoder vs its displaced twin).
struct CandidateFeatures {
    gate_var: String,
    /// All the node's gate-SETs lie outside the event's owned ranges.
    out_of_range: bool,
    /// Body-before-scaffold layout (POP at lower disk offset than PUSH).
    bbs: bool,
    /// Flow-order guarded call name (the wrap's target).
    target_name: String,
    /// Disk-order sibling call name when it differs from `target_name`.
    sibling_reset_name: Option<String>,
    /// Flow-order and disk-order decodes agree (`sibling_reset_name` is
    /// `None`). When false the candidate's flow read crossed a shared flow
    /// frame into a co-located macro's body and mis-decoded its own call.
    flow_disk_agree: bool,
}

/// Resolve one candidate's discriminator features, or `None` when it has no
/// gate var, no gate-SET, or no guarded call (the early-continue cases the
/// old single-pass loop had).
fn candidate_features(
    candidate: &MacroRegionCandidate,
    cfg: &ControlFlowGraph,
    map: &K2NodeByteMap,
    ctx: &DecodeCtx,
    owned_ranges: &[std::ops::Range<usize>],
) -> Option<CandidateFeatures> {
    let gate_var = attribute_macro_gate(cfg, candidate, map)
        .map(|attr| attr.gate_var)
        .or_else(|| candidate_seed_gate_var(cfg, candidate, map))?;
    let gate_sets = node_gate_sets_on_var(candidate.node_id, map, &gate_var);
    if gate_sets.is_empty() {
        return None;
    }
    let out_of_range = all_gate_sets_out_of_range(&gate_sets, owned_ranges);
    let bbs = is_body_before_scaffold(candidate.pop_addr, candidate.push_addr);
    let target_name = candidate_guarded_call_name(cfg, candidate, ctx)?;
    let sibling_reset_name = candidate_sibling_reset_name(map, candidate, ctx, &target_name);
    let flow_disk_agree = sibling_reset_name.is_none();
    Some(CandidateFeatures {
        gate_var,
        out_of_range,
        bbs,
        target_name,
        sibling_reset_name,
        flow_disk_agree,
    })
}

/// Resolve the graph-identity DoOnce wrap candidates for one event, while
/// the per-event `DecodeCtx` is alive but BEFORE the transform stack runs.
///
/// Performs every `ctx`/`cfg`/`map` computation the synthesis needs: gate
/// candidate formation, gate-var resolution (attribution or in-body
/// init-seed), the out-of-range discriminator, and the guarded-call-name
/// decode (`candidate_guarded_call_name`, the only `ctx` consumer). Returns
/// an owned plan per validated candidate so the body rewrite can run later
/// against the fully transform-stacked body (`apply_doonce_wrap_synthesis`),
/// after `ctx` and its per-event borrows have been dropped. Touches no
/// statement body, so the split is output-neutral.
///
/// Derives its DoOnce candidates from `form_event_macro_regions` (the
/// always-available flow-stack formation pass), independent of any audit
/// env gate. Fires only on the cross-body-unreachable DoOnce shape (a
/// guarded call in a Branch arm whose gate scaffold lives elsewhere);
/// every in-range scaffold the byte recognizer already wrapped is excluded
/// by the discriminator.
pub(crate) fn plan_doonce_wrap_synthesis(
    cfg: &ControlFlowGraph,
    graph: &OpcodeGraph,
    map: &K2NodeByteMap,
    ctx: &DecodeCtx,
    event_name: &str,
) -> Vec<SynthWrapPlan> {
    let rows = form_event_macro_regions(cfg, graph, map, event_name);
    let owned_ranges = ctx.owned_ranges.unwrap_or(&[]);
    let candidates: Vec<MacroRegionCandidate> = rows
        .iter()
        .filter(|row| row.owner_event == event_name)
        .filter_map(|row| row.candidate())
        .filter(|candidate| candidate.macro_kind == MacroKind::DoOnce)
        .collect();

    // First pass: compute the per-candidate features the discriminator reads
    // (gate var, gate-SET locality, body-before-scaffold layout, flow-order
    // guarded-call name, disk-order sibling name). A candidate whose
    // flow-order and disk-order decodes DISAGREE is mis-decoding its own
    // guarded call: the flow-order read crossed a shared flow frame into a
    // co-located macro's body. A gate-collision event has exactly one such
    // mis-decoder (the shared macro instance: its flow-order and disk-order
    // calls differ, and its gate sits out of range).
    let features: Vec<CandidateFeatures> = candidates
        .iter()
        .filter_map(|candidate| candidate_features(candidate, cfg, map, ctx, owned_ranges))
        .collect();

    // A mis-decoder is an out-of-range body-before-scaffold candidate whose
    // flow/disk decodes disagree. The naive discriminator would synthesize a
    // wrap on its (wrong) flow-order call; this one rejects it and instead
    // promotes its genuine in-range same-target twin.
    let misdecoded_targets: BTreeSet<String> = features
        .iter()
        .filter(|feature| feature.out_of_range && feature.bbs && !feature.flow_disk_agree)
        .map(|feature| feature.target_name.clone())
        .collect();

    let mut plans = Vec::new();
    for feature in &features {
        // Discriminator.
        //
        // The base survivor is a body-before-scaffold candidate whose gate-SETs
        // all lie OUTSIDE the event's owned ranges (the cross-body-unreachable
        // signature the byte recognizer cannot reach).
        //
        // Two corrections handle a gate-collision event, where two
        // body-before-scaffold candidates decode the same flow-order call:
        //
        // - A MIS-DECODER (out-of-range, flow/disk decodes DISAGREE) read its
        //   own guarded call wrong: its flow-order read crossed a shared flow
        //   frame into a co-located macro's body. It is the shared macro
        //   instance (its flow-order and disk-order calls differ, gate out of
        //   range). It must NOT wrap on its flow call; instead it emits a
        //   RE-KEY directive that moves the byte-shape fold's provisionally
        //   gate-bound latch onto its real gate, vacating the foreign gate.
        //
        // - A PROMOTED TWIN (in-range, flow/disk AGREE) is the genuine macro
        //   whose CALL precedes its in-range scaffold, so the byte recognizer
        //   can't wrap it and the base out-of-range gate rejects it. Promoted
        //   ONLY when a same-event mis-decoder shares its flow target (the
        //   displaced twin on the vacated gate).
        //
        // Every other candidate keeps the base decision, so the change is
        // scoped to the one event with a mis-decoder pair. The apply-step
        // `locate_doonce` skip still excludes any candidate the byte recognizer
        // already wrapped on its gate.
        let base_survives = feature.out_of_range && feature.bbs;
        let is_misdecoder = feature.out_of_range && feature.bbs && !feature.flow_disk_agree;
        let is_promoted_twin = !feature.out_of_range
            && feature.bbs
            && feature.flow_disk_agree
            && misdecoded_targets.contains(&feature.target_name);

        if is_misdecoder {
            plans.push(SynthWrapPlan {
                gate_var: feature.gate_var.clone(),
                target_name: feature.target_name.clone(),
                sibling_reset_name: feature.sibling_reset_name.clone(),
                rekey_latch_named: feature.sibling_reset_name.clone(),
            });
            continue;
        }
        if !((base_survives && !is_misdecoder) || is_promoted_twin) {
            continue;
        }

        plans.push(SynthWrapPlan {
            gate_var: feature.gate_var.clone(),
            target_name: feature.target_name.clone(),
            sibling_reset_name: feature.sibling_reset_name.clone(),
            rekey_latch_named: None,
        });
    }
    plans
}

/// Apply the planned graph-identity DoOnce wraps to one event's fully
/// transform-stacked body, in place. Reads no `ctx`: every value the
/// rewrite needs already lives in `plans` (resolved by
/// `plan_doonce_wrap_synthesis` while the per-event `DecodeCtx` was alive).
///
/// Handles the residue the byte-shape recognizer (`recognize_latches`)
/// correctly cannot reach: a DoOnce whose gate scaffold lives in a sibling
/// event's byte range, so no execution edge from this event's arm flow
/// passes through it (the guarded-call-in-arm shape, and the flat-no-arm
/// cross-range cases the correlation diagnostic reports as `wrapped=false`).
///
/// Runs AFTER the full transform stack, so it sees the same statement tree
/// the emitter would. For each planned candidate it fires only when BOTH of:
///
/// - the gate is still flat in `body` (no `Latch{DoOnce}` for it),
/// - a flat guarded `Stmt::Call` for the candidate sits somewhere in the
///   body tree.
///
/// On a match it wraps the guarded call plus its trailing `ResetDoOnce(...)`
/// in a `Stmt::Latch{DoOnce}` named from the call (so the shape matches a
/// byte-recognized wrap), and drops a leading duplicate `ResetDoOnce(...)`.
/// Returns the count of wraps applied.
pub(crate) fn apply_doonce_wrap_synthesis(body: &mut Vec<Stmt>, plans: &[SynthWrapPlan]) -> usize {
    let mut wrap_count = 0usize;
    // Re-key directives run FIRST: a mis-decoder vacates the foreign gate the
    // byte-shape fold bound its sibling latch to (an else-arm cross-body reset
    // folded onto a co-located gate, re-keyed onto its real gate). The wrap
    // plans run after, so the displaced twin finds its gate freed.
    //
    // Each re-key records `(latch_name, old_gate_var)` so a final re-point pass
    // can fix the flat sibling `ResetDoOnce(latch_name)` the byte-shape fold
    // lifted: it was the fallback `DoOnce_<old_gate>` reset, prematurely
    // resolved to the latch's display name by the per-body naming pass that ran
    // before synthesis. After the gate swap, that reset must re-arm whatever
    // latch now occupies the vacated gate (the displaced twin).
    let mut rekeyed: Vec<(String, String)> = Vec::new();
    for plan in plans {
        if let Some(latch_name) = plan.rekey_latch_named.as_deref() {
            if let Some(old_gate) = rekey_doonce_latch(body, latch_name, &plan.gate_var) {
                rekeyed.push((latch_name.to_string(), old_gate));
            }
        }
    }
    for plan in plans {
        if plan.rekey_latch_named.is_some() {
            continue;
        }
        // Skip when the gate is already wrapped (the byte recognizer or an
        // earlier candidate handled it). This is what excludes every
        // `wrapped=true` site from the synthesis.
        if locate_doonce(body, &plan.gate_var, "top-level").is_some() {
            continue;
        }

        // The captured trailing `ResetDoOnce(...)` re-arms a SIBLING DoOnce
        // (the THEN arm re-arms the gate in the ELSE arm). The flow-stack body
        // carries the reset as the fallback for the wrap's OWN gate
        // (`DoOnce_<suffix>`) because the gate-LET locality pass attributes the
        // cross-body scaffold to this node; left as-is it would render the
        // wrap's own name. Prefer the plan-time sibling name keyed on the
        // candidate's DoOnce geometry (the only source that works when the
        // sibling arm is still flat). When plan-time resolution was absent,
        // fall back to a body `Latch{DoOnce}` scan keyed on the reset's actual
        // target class (a sole other recognized DoOnce); leave the captured
        // reset untouched on genuine ambiguity.
        let sibling_name = plan
            .sibling_reset_name
            .clone()
            .or_else(|| sole_other_doonce_latch_name(body, &plan.gate_var));
        if wrap_flat_doonce_anywhere(
            body,
            &plan.target_name,
            &plan.gate_var,
            sibling_name.as_deref(),
        )
        .is_some()
        {
            wrap_count += 1;
        }
    }
    // Re-point the lifted flat sibling resets onto the latch now occupying the
    // vacated gate. For each re-key `(latch_name, old_gate)`, the latch that
    // currently sits on `old_gate` is the displaced twin. A flat sibling
    // `ResetDoOnce(latch_name)` that shares a body slice with the re-keyed
    // latch is the lifted reset for `old_gate`; re-point it to the twin's
    // display name. No-op when the gate is now unoccupied or the twin's name
    // equals `latch_name` (no swap needed).
    for (latch_name, old_gate) in &rekeyed {
        if let Some(new_name) = doonce_name_on_gate(body, old_gate) {
            if new_name != *latch_name {
                repoint_sibling_resets_beside_latch(body, latch_name, &new_name);
            }
        }
    }
    wrap_count
}

/// Re-key the first top-level `Latch{DoOnce}` named `latch_name` whose gate
/// var differs from `new_gate_var` so its gate var becomes `new_gate_var`.
/// Recurses through container statements so the latch is found inside a
/// Branch arm. No-op when no such latch exists (the latch already carries
/// the right gate, or the fold left it flat). Returns `true` on a re-key.
///
/// The byte-shape fold provisionally binds a bare DoOnce call to a co-located
/// sibling's gate when the only local scaffold is that sibling's gate-CLEAR
/// reset-pair. The graph-identity synthesis corrects that binding to the
/// call's real gate (an else-arm cross-body reset bound to a co-located gate
/// rather than its own).
fn rekey_doonce_latch(body: &mut [Stmt], latch_name: &str, new_gate_var: &str) -> Option<String> {
    for stmt in body.iter_mut() {
        if let Stmt::Latch {
            kind: LatchKind::DoOnce { name, gate_var },
            ..
        } = stmt
        {
            if name == latch_name && gate_var != new_gate_var {
                let old_gate = gate_var.clone();
                *gate_var = new_gate_var.to_string();
                return Some(old_gate);
            }
        }
        for child in stmt.child_bodies_mut() {
            if let Some(old_gate) = rekey_doonce_latch(child, latch_name, new_gate_var) {
                return Some(old_gate);
            }
        }
    }
    None
}

/// The display name of the first `Latch{DoOnce}` on `gate_var` in `body`
/// (recursing through containers). `None` when no latch is on that gate.
fn doonce_name_on_gate(body: &[Stmt], gate_var: &str) -> Option<String> {
    for stmt in body {
        if let Stmt::Latch {
            kind:
                LatchKind::DoOnce {
                    name,
                    gate_var: var,
                },
            ..
        } = stmt
        {
            if var == gate_var {
                return Some(name.clone());
            }
        }
        for slice in stmt.child_bodies() {
            if let Some(found) = doonce_name_on_gate(slice, gate_var) {
                return Some(found);
            }
        }
    }
    None
}

/// Re-point flat sibling `ResetDoOnce(old_name)` calls that share a body slice
/// with a `Latch{DoOnce, name=old_name}` to `new_name`. The reset is the
/// lifted fallback reset whose target gate the synthesis just re-keyed; it
/// must re-arm the latch now on that vacated gate, not the re-keyed latch.
/// Recurses through container statements. Each direct sibling slice is fixed
/// independently so a Branch arm holding both is handled.
fn repoint_sibling_resets_beside_latch(body: &mut [Stmt], old_name: &str, new_name: &str) {
    let has_named_latch = body.iter().any(|stmt| {
        matches!(stmt, Stmt::Latch { kind: LatchKind::DoOnce { name, .. }, .. } if name == old_name)
    });
    if has_named_latch {
        for stmt in body.iter_mut() {
            if let Stmt::Call { func, args, .. } = stmt {
                if matches!(func, crate::bytecode::expr::Expr::Var(n) if n == RESET_DOONCE_CALL_NAME)
                {
                    if let Some(crate::bytecode::expr::Expr::Var(arg)) = args.first_mut() {
                        if arg == old_name {
                            *arg = new_name.to_string();
                        }
                    }
                }
            }
        }
    }
    for stmt in body.iter_mut() {
        for child in stmt.child_bodies_mut() {
            repoint_sibling_resets_beside_latch(child, old_name, new_name);
        }
    }
}

/// The display name of the sole recognized sibling `Latch{DoOnce}` in
/// `body` whose gate var differs from the wrap's own (`own_gate_var`).
/// Apply-time fallback used only when plan-time geometry resolution was
/// absent. Keys on DoOnce structure (the reset's actual target class), not
/// on arbitrary user-call counts: a `ResetDoOnce` re-arms a DoOnce, so the
/// sole other recognized DoOnce is the principled target. `None` when there
/// is no other recognized DoOnce, or two or more (genuine ambiguity), so the
/// captured fallback reset is left untouched rather than mis-targeted.
fn sole_other_doonce_latch_name(body: &[Stmt], own_gate_var: &str) -> Option<String> {
    let mut names: Vec<(String, String)> = Vec::new();
    collect_doonce_latch_names(body, &mut names);
    let others: BTreeSet<String> = names
        .into_iter()
        .filter(|(gate_var, name)| gate_var != own_gate_var && !name.starts_with('$'))
        .map(|(_, name)| name)
        .collect();
    if others.len() == 1 {
        others.into_iter().next()
    } else {
        None
    }
}

/// Gather every `Latch{DoOnce}`'s `(gate_var, display_name)` in `body`,
/// recursing through container statements.
fn collect_doonce_latch_names(body: &[Stmt], out: &mut Vec<(String, String)>) {
    for stmt in body {
        if let Stmt::Latch {
            kind: LatchKind::DoOnce { name, gate_var },
            ..
        } = stmt
        {
            out.push((gate_var.clone(), name.clone()));
        }
        for slice in stmt.child_bodies() {
            collect_doonce_latch_names(slice, out);
        }
    }
}

/// Find the body (at any nesting depth) that holds the flat guarded call
/// `target_name` as a direct child and wrap it there. Recurses into the
/// children of container statements (Branch arms, Sequence pins, Loop
/// body/completion, Switch cases/default, Latch init/body) so a THEN-arm
/// call wraps in place inside its arm rather than only at the event top
/// level. Returns the derived display name on the first body that wraps,
/// `None` when no body holds a matching flat call.
fn wrap_flat_doonce_anywhere(
    body: &mut Vec<Stmt>,
    target_name: &str,
    gate_var: &str,
    sibling_name: Option<&str>,
) -> Option<String> {
    if let Some(name) = wrap_flat_call_in_body(body, target_name, gate_var, sibling_name) {
        return Some(name);
    }
    for stmt in body.iter_mut() {
        for child in stmt.child_bodies_mut() {
            if let Some(name) =
                wrap_flat_doonce_anywhere(child, target_name, gate_var, sibling_name)
            {
                return Some(name);
            }
        }
    }
    None
}

/// Wrap the flat guarded call `target_name` sitting as a direct child of
/// `body` in a `Stmt::Latch{DoOnce}`, capturing one trailing sibling
/// `ResetDoOnce(...)` into the gated body and dropping one leading
/// duplicate `ResetDoOnce(...)`. Returns the derived display name on
/// success, `None` when no matching flat call sits directly in `body`.
fn wrap_flat_call_in_body(
    body: &mut Vec<Stmt>,
    target_name: &str,
    gate_var: &str,
    sibling_name: Option<&str>,
) -> Option<String> {
    let call_idx = body.iter().position(|stmt| {
        matches!(stmt, Stmt::Call { func, .. } if call_func_name(func).as_deref() == Some(target_name))
    })?;
    let call_offset = body[call_idx].offset();

    // The DoOnce body is the guarded call plus its trailing
    // `ResetDoOnce(...)`, matching a byte-recognized wrap
    // (`DoOnce(Call){ Call(...); ResetDoOnce(...) }`). The BP compiler
    // positions that trailing reset either as a direct sibling or inside a
    // single-pin scaffold-only `Sequence`; capture both shapes.
    let mut trailing_reset = take_trailing_reset_doonce(body, call_idx + 1);
    let trailing_arg = trailing_reset.as_ref().and_then(reset_doonce_arg);

    // Drop the leading duplicate `ResetDoOnce(...)` immediately preceding
    // the call when its target matches the trailing reset (the double
    // `ResetDoOnce` shape) so the wrap leaves a single reset, inside the
    // gated body, exactly like a byte-recognized wrap.
    let mut wrap_start = call_idx;
    if call_idx > 0
        && is_reset_doonce_call(&body[call_idx - 1])
        && trailing_arg.is_some()
        && reset_doonce_arg(&body[call_idx - 1]) == trailing_arg
    {
        body.remove(call_idx - 1);
        wrap_start -= 1;
    }

    // Re-arm the SIBLING gate. The captured reset arrives as an unresolved
    // fallback (`DoOnce` / `DoOnce_<N>`) because the gate-LET locality pass
    // attributes the cross-body scaffold to this node; point it at the
    // event's other DoOnce so the wrap reads `ResetDoOnce(<sibling>)`,
    // matching a byte-recognized wrap rather than a meaningless self-reset.
    if let (Some(reset), Some(sibling)) = (trailing_reset.as_mut(), sibling_name) {
        if reset_doonce_arg(reset)
            .as_deref()
            .is_some_and(is_fallback_doonce_name)
        {
            retarget_reset_doonce(reset, sibling);
        }
    }

    let mut gated: Vec<Stmt> = vec![body.remove(wrap_start)];
    if let Some(reset) = trailing_reset {
        gated.push(reset);
    }
    let derived_name = target_name.to_string();
    body.insert(
        wrap_start,
        Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: derived_name.clone(),
                gate_var: gate_var.to_string(),
            },
            init: Vec::new(),
            body: gated,
            offset: call_offset,
        },
    );
    Some(derived_name)
}

/// Extract the trailing `ResetDoOnce(...)` that closes a synthesized
/// DoOnce body, when one sits at `idx`. Handles two BP-emitted positions:
/// a direct sibling `Call(ResetDoOnce)`, or a single-pin scaffold-only
/// `Sequence` whose sole statement is the reset (the shape where the reset
/// lands in a one-pin Sequence after the guarded call). Removes the captured
/// statement / Sequence from `body` and returns the reset call; `None` when
/// no trailing reset is present.
fn take_trailing_reset_doonce(body: &mut Vec<Stmt>, idx: usize) -> Option<Stmt> {
    match body.get(idx) {
        Some(stmt) if is_reset_doonce_call(stmt) => Some(body.remove(idx)),
        Some(Stmt::Sequence { pins, .. })
            if pins.len() == 1 && pins[0].len() == 1 && is_reset_doonce_call(&pins[0][0]) =>
        {
            let Stmt::Sequence { mut pins, .. } = body.remove(idx) else {
                unreachable!("matched Sequence above");
            };
            Some(pins.remove(0).remove(0))
        }
        _ => None,
    }
}

/// The candidate's guarded user-call name (the display name a wrap derives
/// from): the first non-`ResetDoOnce`, non-library call in a flow-order
/// decode of the candidate's body geometry, the same physical-content read
/// the correlation diagnostic performs. The synthesis pass then locates a
/// matching flat call in the transformed tree by this name. `None` when the
/// body yields no such call.
fn candidate_guarded_call_name(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    ctx: &DecodeCtx,
) -> Option<String> {
    let decoded = decode_macro_region_body(cfg, candidate, ctx);
    first_guarded_call_name(&decoded)
}

/// The display name the synthesized wrap's captured `ResetDoOnce(...)` should
/// re-arm: the sibling DoOnce the reset targets.
///
/// The firing node's K2Node partition spans two bodies in the body-before-
/// scaffold layout: the flow-reachable guarded body (the THEN call, which the
/// flow-order region decode already resolved as `target_name`) and, at a
/// LOWER disk offset, the cross-body sibling content the reset re-arms. A
/// disk-order decode of the same partition therefore surfaces the sibling's
/// guarded call. Returning it only when it differs from `target_name` keys the
/// sibling name on the candidate's own DoOnce geometry rather than on counting
/// the event's user calls. `None` when no partition exists, the disk decode
/// finds no guarded call, or it matches `target_name` (no distinct sibling).
fn candidate_sibling_reset_name(
    map: &K2NodeByteMap,
    candidate: &MacroRegionCandidate,
    ctx: &DecodeCtx,
    target_name: &str,
) -> Option<String> {
    let partition = map.partitions.get(&candidate.node_id)?;
    let mut ranges: Vec<std::ops::Range<usize>> = partition.ranges.clone();
    ranges.sort_by_key(|range| range.start);
    let mut decoded = Vec::new();
    for range in &ranges {
        decoded.extend(crate::bytecode::decode::branch::decode_subrange(
            range.start,
            range.end,
            ctx,
        ));
    }
    let name = first_guarded_call_name(&decoded)?;
    (name != target_name).then_some(name)
}

/// First call-target name in flow order that is neither a `ResetDoOnce`
/// scaffold call nor a library helper, recursing through container
/// statements. The display name a DoOnce wrap derives from.
fn first_guarded_call_name(body: &[Stmt]) -> Option<String> {
    for stmt in body {
        if let Stmt::Call { func, .. } = stmt {
            if let Some(name) = call_func_name(func) {
                if name != RESET_DOONCE_CALL_NAME && !is_library_call_name(&name) {
                    return Some(name);
                }
            }
        }
        for slice in stmt.child_bodies() {
            if let Some(name) = first_guarded_call_name(slice) {
                return Some(name);
            }
        }
    }
    None
}

/// Library / math helper call-name prefixes that don't make good DoOnce
/// display names. Uses the shared `latch_recognition::LIBRARY_FUNC_PREFIXES`
/// so the synthesized name matches the byte-recognized one.
fn is_library_call_name(name: &str) -> bool {
    LIBRARY_FUNC_PREFIXES
        .iter()
        .any(|prefix| name.starts_with(prefix))
}

/// True when `stmt` is a synthetic `Call(ResetDoOnce(<arg>))`.
fn is_reset_doonce_call(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Call { func, .. } if call_func_name(func).as_deref() == Some(RESET_DOONCE_CALL_NAME))
}

/// True for an unresolved DoOnce fallback name (`DoOnce` or
/// `DoOnce_<N>`), the form the asset-wide reset-name pass would otherwise
/// resolve. A real display name returns false.
fn is_fallback_doonce_name(name: &str) -> bool {
    name == DOONCE_CALL_NAME
        || name
            .strip_prefix("DoOnce_")
            .is_some_and(|suffix| !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()))
}

/// Replace the single `Var` argument of a `Call(ResetDoOnce(<arg>))` with
/// `target`.
fn retarget_reset_doonce(stmt: &mut Stmt, target: &str) {
    if let Stmt::Call { args, .. } = stmt {
        if let Some(crate::bytecode::expr::Expr::Var(name)) = args.first_mut() {
            *name = target.to_string();
        }
    }
}

/// The single `Var` argument of a `Call(ResetDoOnce(<arg>))`, for the
/// leading-duplicate comparison. `None` for any other shape.
fn reset_doonce_arg(stmt: &Stmt) -> Option<String> {
    let Stmt::Call { func, args, .. } = stmt else {
        return None;
    };
    if call_func_name(func).as_deref() != Some(RESET_DOONCE_CALL_NAME) || args.len() != 1 {
        return None;
    }
    match &args[0] {
        crate::bytecode::expr::Expr::Var(name) => Some(name.clone()),
        crate::bytecode::expr::Expr::Literal(value) => Some(value.clone()),
        _ => None,
    }
}

/// The call-target name of a call-shaped `Expr` (`Call` / `MethodCall` /
/// bare `Var`), mirroring `region_decode::call_target_name`.
fn call_func_name(func: &crate::bytecode::expr::Expr) -> Option<String> {
    match func {
        crate::bytecode::expr::Expr::Call { name, .. }
        | crate::bytecode::expr::Expr::MethodCall { name, .. }
        | crate::bytecode::expr::Expr::Var(name) => Some(name.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn reset_call(target: &str) -> Stmt {
        Stmt::Call {
            func: crate::bytecode::expr::Expr::Var("ResetDoOnce".into()),
            args: vec![crate::bytecode::expr::Expr::Var(target.into())],
            offset: 10,
        }
    }

    const SYNTH_GATE_VAR: &str = "Temp_bool_IsClosed_Variable_0";

    fn user_call(name: &str) -> Stmt {
        Stmt::Call {
            func: crate::bytecode::expr::Expr::Var(name.into()),
            args: Vec::new(),
            offset: 20,
        }
    }

    fn synth_plan(target: &str, sibling: Option<&str>) -> SynthWrapPlan {
        SynthWrapPlan {
            gate_var: SYNTH_GATE_VAR.into(),
            target_name: target.into(),
            sibling_reset_name: sibling.map(str::to_string),
            rekey_latch_named: None,
        }
    }

    /// `apply_doonce_wrap_synthesis` wraps a flat guarded call plus its
    /// trailing `ResetDoOnce` into a `Latch{DoOnce}`, retargeting the reset
    /// to the plan's sibling and dropping a leading duplicate reset.
    #[test]
    fn synth_apply_wraps_flat_guarded_call() {
        let mut body = vec![
            reset_call("DoOnce_3"),
            user_call("AttemptGrip"),
            reset_call("DoOnce_3"),
        ];
        let wrapped = apply_doonce_wrap_synthesis(
            &mut body,
            &[synth_plan("AttemptGrip", Some("ReleaseGrip"))],
        );
        assert_eq!(wrapped, 1);
        // Leading duplicate reset dropped, single Latch remains.
        assert_eq!(body.len(), 1);
        let Stmt::Latch {
            kind: LatchKind::DoOnce { name, gate_var },
            body: gated,
            ..
        } = &body[0]
        else {
            panic!("expected synthesized Latch{{DoOnce}} at body[0]");
        };
        assert_eq!(name, "AttemptGrip");
        assert_eq!(gate_var, SYNTH_GATE_VAR);
        // Gated body: the guarded call plus the retargeted trailing reset.
        assert_eq!(gated.len(), 2);
        assert!(
            matches!(&gated[0], Stmt::Call { func, .. } if call_func_name(func).as_deref() == Some("AttemptGrip"))
        );
        assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("ReleaseGrip"));
    }

    /// When the gate is already wrapped (`locate_doonce` finds it), the
    /// apply step does NOT double-wrap and reports zero synthesized wraps.
    #[test]
    fn synth_apply_skips_already_wrapped_gate() {
        let mut body = vec![Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: "AttemptGrip".into(),
                gate_var: SYNTH_GATE_VAR.into(),
            },
            init: Vec::new(),
            body: vec![user_call("AttemptGrip")],
            offset: 0,
        }];
        let before = body.clone();
        let wrapped = apply_doonce_wrap_synthesis(
            &mut body,
            &[synth_plan("AttemptGrip", Some("ReleaseGrip"))],
        );
        assert_eq!(wrapped, 0);
        // Byte-identical: no second Latch, body unchanged.
        assert_eq!(body.len(), before.len());
        assert!(matches!(&body[0], Stmt::Latch { body, .. } if body.len() == 1));
    }

    /// Reset-target fallback: with no plan-time sibling name, the apply step
    /// uses the sole OTHER recognized `Latch{DoOnce}`'s name.
    #[test]
    fn synth_apply_reset_falls_back_to_sole_other_latch() {
        let mut body = vec![
            doonce_latch_named(
                "ReleaseGrip",
                "Temp_bool_Other_0",
                vec![user_call("ReleaseGrip")],
            ),
            user_call("AttemptGrip"),
            reset_call("DoOnce_3"),
        ];
        let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("AttemptGrip", None)]);
        assert_eq!(wrapped, 1);
        let gated = synthesized_gated_body(&body, "AttemptGrip");
        assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("ReleaseGrip"));
    }

    /// Reset-target fallback ambiguity: with no plan-time sibling and two or
    /// more other recognized DoOnce latches, the captured reset is left
    /// untouched (its unresolved fallback name).
    #[test]
    fn synth_apply_reset_untouched_when_ambiguous() {
        let mut body = vec![
            doonce_latch_named("ReleaseGrip", "Temp_bool_A_0", Vec::new()),
            doonce_latch_named("DropItem", "Temp_bool_B_0", Vec::new()),
            user_call("AttemptGrip"),
            reset_call("DoOnce_3"),
        ];
        let wrapped = apply_doonce_wrap_synthesis(&mut body, &[synth_plan("AttemptGrip", None)]);
        assert_eq!(wrapped, 1);
        let gated = synthesized_gated_body(&body, "AttemptGrip");
        assert_eq!(reset_doonce_arg(&gated[1]).as_deref(), Some("DoOnce_3"));
    }

    fn doonce_latch_named(name: &str, gate_var: &str, body: Vec<Stmt>) -> Stmt {
        Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: name.into(),
                gate_var: gate_var.into(),
            },
            init: Vec::new(),
            body,
            offset: 0,
        }
    }

    /// Extract the gated body of the synthesized `Latch{DoOnce}` named
    /// `name`, searching the top level of `body`.
    fn synthesized_gated_body<'a>(body: &'a [Stmt], name: &str) -> &'a [Stmt] {
        body.iter()
            .find_map(|stmt| match stmt {
                Stmt::Latch {
                    kind:
                        LatchKind::DoOnce {
                            name: latch_name, ..
                        },
                    body: gated,
                    ..
                } if latch_name == name => Some(gated.as_slice()),
                _ => None,
            })
            .expect("synthesized Latch present")
    }

    /// Positive body-before-scaffold discriminator: fires only when the
    /// POP/continuation precedes the PUSH on disk. Weakening this (so an
    /// in-range / normally-laid-out node fires) breaks the over-fire guard.
    #[test]
    fn synth_body_before_scaffold_predicate() {
        assert!(is_body_before_scaffold(0x10, 0x40));
        assert!(!is_body_before_scaffold(0x40, 0x40));
        assert!(!is_body_before_scaffold(0x80, 0x40));
    }

    /// Negative gate-set discriminator: every gate-SET must lie outside the
    /// event's owned ranges. A gate-SET inside an owned range means the
    /// scaffold is reachable, so synthesis must not fire.
    #[test]
    fn synth_gate_sets_out_of_range_predicate() {
        let owned = [0x00..0x50usize, 0x80..0xa0usize];
        assert!(all_gate_sets_out_of_range(&[0x100, 0x200], &owned));
        assert!(!all_gate_sets_out_of_range(&[0x100, 0x20], &owned));
        assert!(!all_gate_sets_out_of_range(&[0x90], &owned));
        // No owned ranges: every gate-set is trivially out of range.
        assert!(all_gate_sets_out_of_range(&[0x10], &[]));
    }
}
