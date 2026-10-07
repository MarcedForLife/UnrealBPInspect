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
    attribute_macro_gate, candidate_body_spans, decode_macro_region_body, form_event_macro_regions,
    MacroRegionCandidate,
};
use crate::bytecode::cfg::ControlFlowGraph;
use crate::bytecode::decode::ctx::DecodeCtx;
use crate::bytecode::k2node_byte_map::K2NodeByteMap;
use crate::bytecode::names::MacroKind;
use crate::bytecode::partition::OpcodeGraph;
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::latch_recognition::{
    LIBRARY_FUNC_PREFIXES, RESET_DOONCE_CALL_NAME,
};

/// The `Temp_bool_*` gate var named by the candidate's in-body `=false`
/// init-seed, when exactly one distinct such var sits in the body
/// geometry. Reads the locality-pass byte map and the CFG block extents
/// directly (the same maps `select_gate_set` reads); not inference.
/// `None` when no in-body seed exists or several distinct seed vars sit
/// in the body. Shares the body-span build and the map walk with
/// `select_gate_set`'s `in_body_seed_gate_var`; the logic is identical.
fn candidate_seed_gate_var(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> Option<String> {
    let body_spans = candidate_body_spans(cfg, candidate);
    map.in_body_seed_gate_var(&body_spans, candidate.node_id)
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
            crate::bytecode::expr::Expr::Literal(value) => value.to_string(),
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
        crate::bytecode::expr::Expr::Literal(value) => value.to_string(),
        other => format!("{:?}", other),
    }
}

/// A validated DoOnce candidate and its executable body anchors, retained
/// until the statement transforms finish so synthesis can match exact bytes.
pub(crate) struct SynthWrapPlan {
    gate_var: String,
    /// Display name when the candidate needs a synthesized wrap. None only
    /// corrects a misbound wrapper using the candidate's executable anchors.
    target_name: Option<String>,
    /// Opcode offsets on the straight-line path starting at the guarded call.
    /// Preserves execution order even when the reset precedes the call on disk.
    body_offsets: Vec<usize>,
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
    body_offsets: Vec<usize>,
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
    graph: &OpcodeGraph,
    owned_ranges: &[std::ops::Range<usize>],
) -> Option<CandidateFeatures> {
    let gate_var = attribute_macro_gate(cfg, candidate, map)
        .map(|attr| attr.gate_var)
        .or_else(|| candidate_seed_gate_var(cfg, candidate, map))?;
    let gate_sets = map.node_gate_set_offsets(candidate.node_id, Some(&gate_var));
    if gate_sets.is_empty() {
        return None;
    }
    let out_of_range = all_gate_sets_out_of_range(&gate_sets, owned_ranges);
    let bbs = is_body_before_scaffold(candidate.pop_addr, candidate.push_addr);
    let decoded = decode_macro_region_body(cfg, candidate, ctx);
    let call = first_guarded_call(&decoded)?;
    let Stmt::Call { func, offset, .. } = call else {
        return None;
    };
    let target_name = call_func_name(func)?;
    let body_offsets =
        straight_line_body_offsets(graph, *offset, &candidate_body_spans(cfg, candidate));
    let sibling_reset_name = candidate_sibling_reset_name(map, candidate, ctx, &target_name);
    let flow_disk_agree = sibling_reset_name.is_none();
    Some(CandidateFeatures {
        gate_var,
        out_of_range,
        bbs,
        target_name,
        body_offsets,
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
        .filter_map(|candidate| candidate_features(candidate, cfg, map, ctx, graph, owned_ranges))
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
        match classify_candidate(feature, &misdecoded_targets) {
            CandidateDecision::Skip => plans.push(SynthWrapPlan {
                gate_var: feature.gate_var.clone(),
                target_name: None,
                body_offsets: feature.body_offsets.clone(),
                rekey_latch_named: None,
            }),
            CandidateDecision::Rekey => plans.push(SynthWrapPlan {
                gate_var: feature.gate_var.clone(),
                target_name: Some(feature.target_name.clone()),
                body_offsets: feature.body_offsets.clone(),
                rekey_latch_named: feature.sibling_reset_name.clone(),
            }),
            CandidateDecision::Wrap => plans.push(SynthWrapPlan {
                gate_var: feature.gate_var.clone(),
                target_name: Some(feature.target_name.clone()),
                body_offsets: feature.body_offsets.clone(),
                rekey_latch_named: None,
            }),
        }
    }
    plans
}

/// The discriminator outcome for one candidate: skip it, re-key a foreign
/// gate, or synthesize a wrap. See `classify_candidate` for the rules.
enum CandidateDecision {
    Skip,
    Rekey,
    Wrap,
}

/// Decide a candidate's fate from its features and the event's mis-decoder set.
///
/// The base survivor is a body-before-scaffold candidate whose gate-SETs
/// all lie OUTSIDE the event's owned ranges (the cross-body-unreachable
/// signature the byte recognizer cannot reach).
///
/// Two corrections handle a gate-collision event, where two
/// body-before-scaffold candidates decode the same flow-order call:
///
/// - A MIS-DECODER (out-of-range, flow/disk decodes DISAGREE) read its
///   own guarded call wrong: its flow-order read crossed a shared flow
///   frame into a co-located macro's body. It is the shared macro
///   instance (its flow-order and disk-order calls differ, gate out of
///   range). It must NOT wrap on its flow call; instead it emits a
///   RE-KEY directive that moves the byte-shape fold's provisionally
///   gate-bound latch onto its real gate, vacating the foreign gate.
///
/// - A PROMOTED TWIN (in-range, flow/disk AGREE) is the genuine macro
///   whose CALL precedes its in-range scaffold, so the byte recognizer
///   can't wrap it and the base out-of-range gate rejects it. Promoted
///   ONLY when a same-event mis-decoder shares its flow target (the
///   displaced twin on the vacated gate).
///
/// Every other candidate keeps the base decision, so the change is
/// scoped to the one event with a mis-decoder pair. The apply-step
/// `locate_doonce` skip still excludes any candidate the byte recognizer
/// already wrapped on its gate.
fn classify_candidate(
    feature: &CandidateFeatures,
    misdecoded_targets: &BTreeSet<String>,
) -> CandidateDecision {
    let base_survives = feature.out_of_range && feature.bbs;
    let is_misdecoder = feature.out_of_range && feature.bbs && !feature.flow_disk_agree;
    let is_promoted_twin = !feature.out_of_range
        && feature.bbs
        && feature.flow_disk_agree
        && misdecoded_targets.contains(&feature.target_name);

    if is_misdecoder {
        return CandidateDecision::Rekey;
    }
    if (base_survives && !is_misdecoder) || is_promoted_twin {
        CandidateDecision::Wrap
    } else {
        CandidateDecision::Skip
    }
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
/// On a match it wraps the guarded call and resets on its proven execution
/// path. Reset targets keep their bytecode gate identity. Returns the wrap count.
pub(crate) fn apply_doonce_wrap_synthesis(body: &mut Vec<Stmt>, plans: &[SynthWrapPlan]) -> usize {
    for plan in plans {
        if let Some(latch_name) = plan.rekey_latch_named.as_deref() {
            rekey_doonce_latch(body, latch_name, &plan.gate_var);
        }
    }
    let mut wrap_count = 0;
    for plan in plans {
        if plan.rekey_latch_named.is_some() {
            continue;
        }
        if plan.target_name.is_none() || locate_doonce(body, &plan.gate_var, "top-level").is_some()
        {
            continue;
        }
        if wrap_flat_doonce_anywhere(body, plan) {
            wrap_count += 1;
        }
    }
    wrap_count
}

/// Remove duplicate representations only when both wrapper origins belong
/// to the same graph macro, or one is its exact guarded-call anchor.
pub(crate) fn unwrap_misbound_latch(body: &mut [Stmt], plan: &SynthWrapPlan, map: &K2NodeByteMap) {
    let Some(&call_offset) = plan.body_offsets.first() else {
        return;
    };
    let nodes: BTreeSet<_> = map
        .gate_let_var_by_offset
        .iter()
        .filter(|(offset, gate)| {
            *gate == &plan.gate_var && map.gate_let_is_set_by_offset.get(offset) == Some(&true)
        })
        .filter_map(|(offset, _)| map.gate_let_owner_by_offset.get(offset).copied())
        .collect();
    let Some(node) = (nodes.len() == 1).then(|| *nodes.iter().next().unwrap()) else {
        return;
    };
    for stmt in body {
        for children in stmt.child_bodies_structural_mut() {
            unwrap_misbound_latch(children, plan, map);
        }
        let Stmt::Latch {
            kind: LatchKind::DoOnce { gate_var, .. },
            init,
            body: nested,
            offset,
        } = stmt
        else {
            continue;
        };
        if gate_var != &plan.gate_var || !init.is_empty() || nested.len() != 1 {
            continue;
        }
        let Stmt::Latch {
            kind:
                LatchKind::DoOnce {
                    gate_var: inner_gate,
                    ..
                },
            offset: inner_offset,
            ..
        } = &nested[0]
        else {
            continue;
        };
        let attributed = |origin: usize| {
            origin == call_offset
                || map
                    .byte_to_node
                    .get(&origin)
                    .is_some_and(|owners| owners.as_slice() == [node])
        };
        if inner_gate == gate_var
            && attributed(*offset)
            && attributed(*inner_offset)
            && has_flat_call_at(nested, call_offset)
        {
            *stmt = nested.remove(0);
        }
    }
}

fn has_flat_call_at(body: &[Stmt], offset: usize) -> bool {
    body.iter().any(|stmt| {
        (stmt.offset() == offset && matches!(stmt, Stmt::Call { .. }))
            || stmt
                .child_bodies_structural()
                .iter()
                .any(|children| has_flat_call_at(children, offset))
    })
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
        for child in stmt.child_bodies_structural_mut() {
            if let Some(old_gate) = rekey_doonce_latch(child, latch_name, new_gate_var) {
                return Some(old_gate);
            }
        }
    }
    None
}

/// Follow only a single executable path. A branch or flow-stack boundary
/// ends the proof, so unrelated resets cannot be pulled into a guarded body.
fn straight_line_body_offsets(
    graph: &OpcodeGraph,
    start: usize,
    spans: &[std::ops::Range<usize>],
) -> Vec<usize> {
    use crate::bytecode::opcodes::{
        EX_END_OF_SCRIPT, EX_POP_EXECUTION_FLOW, EX_POP_FLOW_IF_NOT, EX_PUSH_EXECUTION_FLOW,
        EX_RETURN,
    };
    let mut offsets = Vec::new();
    let mut seen = BTreeSet::new();
    let mut current = start;
    while spans.iter().any(|span| span.contains(&current)) && seen.insert(current) {
        if matches!(
            graph.opcodes.get(&current),
            Some(&EX_POP_EXECUTION_FLOW)
                | Some(&EX_POP_FLOW_IF_NOT)
                | Some(&EX_PUSH_EXECUTION_FLOW)
                | Some(&EX_RETURN)
                | Some(&EX_END_OF_SCRIPT)
        ) {
            break;
        }
        offsets.push(current);
        let Some(successors) = graph.successors.get(&current) else {
            break;
        };
        let [next] = successors.as_slice() else {
            break;
        };
        current = *next;
    }
    offsets
}

fn wrap_flat_doonce_anywhere(body: &mut Vec<Stmt>, plan: &SynthWrapPlan) -> bool {
    if wrap_flat_call_in_body(body, plan) {
        return true;
    }
    for stmt in body {
        for children in stmt.child_bodies_structural_mut() {
            if wrap_flat_doonce_anywhere(children, plan) {
                return true;
            }
        }
    }
    false
}

/// Restore displaced resets using their proven bytecode successors, retaining
/// the gate identifiers read from the reset assignments themselves.
fn wrap_flat_call_in_body(body: &mut Vec<Stmt>, plan: &SynthWrapPlan) -> bool {
    let Some(target_name) = plan.target_name.as_deref() else {
        return false;
    };
    let Some(&call_offset) = plan.body_offsets.first() else {
        return false;
    };
    if !body.iter().any(|stmt| {
        stmt.offset() == call_offset
            && matches!(stmt,
        Stmt::Call { func, .. } if call_func_name(func).as_deref() == Some(target_name))
    }) {
        return false;
    }
    let mut remaining = Vec::new();
    let mut gated = Vec::new();
    let mut insertion = 0;
    for mut stmt in std::mem::take(body) {
        if stmt.offset() == call_offset {
            insertion = remaining.len();
            gated.push((0, stmt));
            continue;
        }
        let reset = match &stmt {
            Stmt::Sequence { pins, .. } if pins.len() == 1 && pins[0].len() == 1 => &pins[0][0],
            other => other,
        };
        if is_reset_doonce_call(reset) {
            if let Some(rank) = plan
                .body_offsets
                .iter()
                .position(|offset| *offset == reset.offset())
            {
                if let Stmt::Sequence { pins, .. } = &mut stmt {
                    stmt = pins[0].remove(0);
                }
                if !gated.iter().any(|(previous, _)| *previous == rank) {
                    gated.push((rank, stmt));
                }
                continue;
            }
        }
        remaining.push(stmt);
    }
    gated.sort_by_key(|(rank, _)| *rank);
    remaining.insert(
        insertion,
        Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: target_name.to_owned(),
                gate_var: plan.gate_var.clone(),
            },
            init: Vec::new(),
            body: gated.into_iter().map(|(_, stmt)| stmt).collect(),
            offset: call_offset,
        },
    );
    *body = remaining;
    true
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
    match first_guarded_call(body)? {
        Stmt::Call { func, .. } => call_func_name(func),
        _ => None,
    }
}

fn first_guarded_call(body: &[Stmt]) -> Option<&Stmt> {
    let mut first_library = None;
    for stmt in body {
        if let Stmt::Call { func, .. } = stmt {
            if let Some(name) = call_func_name(func) {
                if name != RESET_DOONCE_CALL_NAME {
                    if !is_library_call_name(&name) {
                        return Some(stmt);
                    }
                    first_library.get_or_insert(stmt);
                }
            }
        }
        for slice in stmt.child_bodies_structural() {
            if let Some(call) = first_guarded_call(slice) {
                if let Stmt::Call { func, .. } = call {
                    if call_func_name(func).is_some_and(|name| !is_library_call_name(&name)) {
                        return Some(call);
                    }
                    first_library.get_or_insert(call);
                }
            }
        }
    }
    first_library
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
#[path = "doonce_wrap_synthesis_tests.rs"]
mod tests;
