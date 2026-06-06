//! Flow-stack macro-region formation.
//!
//! Computes the control-flow region geometry of each flow-stack macro
//! (DoOnce / ExecutionSequence / MultiGate) directly from the VM
//! execution-flow-stack pairing, not from the macro's scattered bytecode
//! footprint.
//!
//! It replaces the earlier footprint-seeded + dominator-grown formation
//! (commit `052bd45`), which reported the scattered DoOnce family as
//! `multi_entry` because a macro's true entry is the
//! `EX_PUSH_EXECUTION_FLOW` block, which is NOT in the footprint.
//!
//! The output is live: `form_event_macro_regions` produces a
//! `MacroRegionCandidate` per validated macro, which
//! `doonce_wrap_synthesis::plan_doonce_wrap_synthesis` consumes to wrap
//! the cross-body-unreachable DoOnce candidates the byte recognizer
//! cannot reach. That synthesis does change production decode output, and
//! recovers a candidate's member-block body via [`decode_macro_region_body`].
//!
//! The verified rule, exactly:
//!
//! 1. **Association** (graph-based, NOT disk-span): for each MacroInstance
//!    footprint, pick the [`FlowFrame`] whose
//!    `graph_reachable(pushed_target, bounded at block_containing(pop_addr))`
//!    block set covers any footprint opcode; tie-break to the smallest
//!    reachable set. Disk-span association is wrong because the POP sits
//!    at a LOWER disk offset than the PUSH (body-before-scaffold), and
//!    footprint min/max envelope mis-resolves scattered footprints.
//! 2. **Growth**: seed from `block_containing(push_addr)`; BFS over CFG
//!    successors (this follows the back-jump down to the lower-disk body
//!    and the gate edges), bounded at `block_containing(pop_addr)` (the
//!    POP block is a member; its resume successor is the exit, not
//!    entered).
//! 3. **Validation**: single entry = only the seed/PUSH block has a
//!    predecessor outside the grown set; single exit = exactly one
//!    NON-SINK exit target (the synthetic CFG `sink` edge is an event
//!    boundary and is ignored: every flow-stack macro region has both a
//!    real `EX_PopExecutionFlow` exit and a synthetic sink edge).
//!
//! FlipFlop is OUT of scope: it is a toggle with no PUSH/POP frame and
//! stays on its byte-shape recognizer.

use std::collections::{BTreeSet, VecDeque};
use std::ops::Range;

use super::{reachable_bounded, BlockId, BoundedReach, ControlFlowGraph};
use crate::bytecode::decode::ctx::DecodeCtx;
use crate::bytecode::k2node_byte_map::{K2NodeByteMap, K2NodePartition};
use crate::bytecode::names::MacroKind;
use crate::bytecode::opcodes::EX_PUSH_EXECUTION_FLOW;
use crate::bytecode::partition::{FlowFrame, OpcodeGraph};
use crate::bytecode::stmt::Stmt;

/// Why a flow-stack macro failed (or passed) region formation. `Ok` is
/// the only success value; every other variant names the specific reason
/// the grown block set is not a usable single-entry / single-exit region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MacroRegionOutcome {
    /// Validated as a single-entry / single-exit region (the synthetic
    /// sink edge ignored).
    Ok,
    /// The partition has no disk ranges at all in this asset.
    EmptyFootprint,
    /// No `FlowFrame` associates with this footprint: no frame's
    /// `pushed_target`-reachable block set (bounded at the POP block)
    /// covers any footprint opcode. The macro lives in another event's
    /// CFG, or it carries no PUSH/POP frame (FlipFlop).
    NoFrame,
    /// A frame was associated but its PUSH or POP address does not land
    /// on a CFG block in this event's scope.
    NoSeedBlock,
    /// More than one block in the grown set has a predecessor outside the
    /// set (besides the seed/PUSH block).
    MultiEntry,
    /// The grown set has more than one distinct NON-SINK successor target
    /// leaving the set.
    MultiExit,
    /// The grown set never reached the matching POP block (the bound was
    /// not hit; the span did not close on the graph).
    Irreducible,
}

impl MacroRegionOutcome {
    /// Stable lower-case tag for log/JSON output and the failure
    /// histogram.
    pub fn tag(self) -> &'static str {
        match self {
            MacroRegionOutcome::Ok => "ok",
            MacroRegionOutcome::EmptyFootprint => "empty_footprint",
            MacroRegionOutcome::NoFrame => "no_frame",
            MacroRegionOutcome::NoSeedBlock => "no_seed_block",
            MacroRegionOutcome::MultiEntry => "multi_entry",
            MacroRegionOutcome::MultiExit => "multi_exit",
            MacroRegionOutcome::Irreducible => "irreducible",
        }
    }
}

/// The recovered region geometry for one validated flow-stack macro.
/// Consumed by the graph-identity DoOnce wrap synthesis path
/// (`plan_doonce_wrap_synthesis` / `apply_doonce_wrap_synthesis`) via the
/// candidate's body-before-scaffold discriminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroRegionCandidate {
    /// 1-based export id of the `K2Node_MacroInstance`.
    pub node_id: usize,
    /// Macro kind (`DoOnce`, `ExecutionSequence`, `MultiGate`).
    pub macro_kind: MacroKind,
    /// The seed (PUSH) block: the macro's true single entry.
    pub entry_block: BlockId,
    /// The single non-sink exit target the matching POP resumes.
    pub exit_target: BlockId,
    /// Every block grown into the region (PUSH block .. POP block).
    pub member_blocks: Vec<BlockId>,
    /// PUSH opcode disk offset of the associated frame.
    pub push_addr: usize,
    /// Matching POP opcode disk offset. When `pop_addr < push_addr` the
    /// macro is body-before-scaffold (the gated body sits at a lower disk
    /// offset than its gate scaffold), the cross-body shape the wrap
    /// synthesis discriminates on.
    pub pop_addr: usize,
}

/// Result of attempting region formation for one MacroInstance partition
/// in one event's CFG. Records the attempt regardless of outcome so the
/// audit captures a row per macro per event it could plausibly own.
#[derive(Clone, Debug)]
pub struct MacroRegionResult {
    pub node_id: usize,
    pub macro_kind: MacroKind,
    /// The event scope this attempt ran in.
    pub owner_event: String,
    /// Footprint span (min start, max end) across the partition's ranges.
    pub foot_min: Option<usize>,
    pub foot_max: Option<usize>,
    /// PUSH opcode disk offset of the associated frame, when one was found.
    pub push_addr: Option<usize>,
    /// Matching POP opcode disk offset of the associated frame.
    pub pop_addr: Option<usize>,
    /// Seed (PUSH) block id, when found.
    pub entry_block: Option<BlockId>,
    /// The single non-sink exit target, when validated.
    pub exit_target: Option<BlockId>,
    /// Every block grown into the region (sorted). Empty until growth runs.
    pub member_blocks: Vec<BlockId>,
    pub outcome: MacroRegionOutcome,
}

impl MacroRegionResult {
    pub fn validated(&self) -> bool {
        self.outcome == MacroRegionOutcome::Ok
    }

    /// Grown member set size.
    pub fn member_count(&self) -> usize {
        self.member_blocks.len()
    }

    /// The validated region geometry, when formation succeeded.
    pub fn candidate(&self) -> Option<MacroRegionCandidate> {
        if !self.validated() {
            return None;
        }
        Some(MacroRegionCandidate {
            node_id: self.node_id,
            macro_kind: self.macro_kind,
            entry_block: self.entry_block?,
            exit_target: self.exit_target?,
            member_blocks: self.member_blocks.clone(),
            push_addr: self.push_addr?,
            pop_addr: self.pop_addr?,
        })
    }
}

/// Label a partition the flow-stack formation pass targets.
///
/// Admission is by macro kind for recognised kinds; the structural
/// PUSH-in-footprint test applies only to the rest. Replacing the kind
/// admission with an unconditional footprint-PUSH test looks like the
/// obvious generalisation but is wrong: co-located macros share one flow
/// frame, and in the cross-body-unreachable DoOnce shape (gate scaffold
/// in another body region) the PUSH bytes are attributed to a sibling
/// partition, so the DoOnce's own footprint never pushes even though
/// `associate_frame` finds its shared frame during formation. Requiring
/// a footprint PUSH drops real candidates (verified: it loses the
/// VRPlayer GripLeft AttemptGrip synthesized wrap).
/// - DoOnce / MultiGate enter by kind alone (frame may live elsewhere).
/// - FlipFlop (toggle) and IsValid (lexical jump-if-not) never own a
///   frame; excluded.
/// - ExecutionSequence (a bare `K2Node_ExecutionSequence`, or a
///   MacroInstance whose name fell through the kind default) is admitted
///   only when its footprint actually pushes. Downstream only
///   distinguishes DoOnce, so the non-DoOnce label is informational.
fn flow_stack_label(partition: &K2NodePartition, graph: &OpcodeGraph) -> Option<MacroKind> {
    match partition.macro_kind {
        Some(kind @ (MacroKind::DoOnce | MacroKind::MultiGate)) => Some(kind),
        Some(MacroKind::FlipFlop | MacroKind::IsValid) => None,
        Some(MacroKind::ExecutionSequence) | None => {
            let has_push = partition.ranges.iter().any(|range| {
                graph
                    .opcodes
                    .range(range.clone())
                    .any(|(_, &opcode)| opcode == EX_PUSH_EXECUTION_FLOW)
            });
            has_push.then_some(MacroKind::ExecutionSequence)
        }
    }
}

/// Block whose `[start,end)` contains `addr`. The synthetic sink (empty
/// opcodes) never matches.
fn block_containing(cfg: &ControlFlowGraph, addr: usize) -> Option<BlockId> {
    cfg.blocks
        .iter()
        .find(|block| {
            block.id != cfg.sink
                && !block.opcodes.is_empty()
                && block.start <= addr
                && addr < block.end
        })
        .map(|block| block.id)
}

/// True if any block in `blocks` covers an opcode that lies inside one of
/// the footprint `ranges`.
fn blocks_cover_footprint(
    cfg: &ControlFlowGraph,
    blocks: &BTreeSet<BlockId>,
    ranges: &[Range<usize>],
) -> bool {
    for &block_id in blocks {
        let Some(block) = cfg.blocks.get(block_id) else {
            continue;
        };
        for &opcode_addr in &block.opcodes {
            if ranges
                .iter()
                .any(|range| range.start <= opcode_addr && opcode_addr < range.end)
            {
                return true;
            }
        }
    }
    false
}

/// Associate a footprint with a `FlowFrame` by graph reachability.
///
/// For each frame: locate `block_containing(pushed_target)` and
/// `block_containing(pop_addr)`, compute the `pushed_target`-reachable set
/// bounded at the POP block, and keep frames whose set covers a footprint
/// opcode. Tie-break to the frame with the smallest reachable set (the
/// tightest enclosing macro body). Returns the chosen frame and its
/// reachable-set size.
fn associate_frame<'a>(
    cfg: &ControlFlowGraph,
    frames: &'a [FlowFrame],
    ranges: &[Range<usize>],
) -> Option<&'a FlowFrame> {
    let mut best: Option<(&FlowFrame, usize)> = None;
    for frame in frames {
        let Some(pop_block) = block_containing(cfg, frame.pop_addr) else {
            continue;
        };
        let Some(target_block) = block_containing(cfg, frame.pushed_target) else {
            continue;
        };
        // `graph_reachable(pushed_target, bounded at the POP block)`,
        // skipping the synthetic sink. The POP block is a member but is
        // not expanded past.
        let reachable = reachable_bounded(
            cfg,
            target_block,
            pop_block,
            BoundedReach {
                skip_sink: true,
                include_boundary: false,
            },
        );
        if !blocks_cover_footprint(cfg, &reachable, ranges) {
            continue;
        }
        let size = reachable.len();
        match best {
            Some((_, best_size)) if best_size <= size => {}
            _ => best = Some((frame, size)),
        }
    }
    best.map(|(frame, _)| frame)
}

/// Grow the region forward from `seed` over CFG successors, bounded at
/// `pop_block`. The POP block is a member; its successors are recorded as
/// exits and not expanded. The synthetic sink is recorded as an exit but
/// never entered. Back-jump edges inside the span are followed naturally.
///
/// Returns the grown member set and the distinct exit targets (including
/// the synthetic sink, which the validator filters out).
fn grow_to_pop(
    cfg: &ControlFlowGraph,
    seed: BlockId,
    pop_block: BlockId,
) -> (BTreeSet<BlockId>, BTreeSet<BlockId>) {
    let mut region: BTreeSet<BlockId> = BTreeSet::new();
    let mut exits: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: Vec<BlockId> = vec![seed];
    region.insert(seed);
    while let Some(block) = queue.pop() {
        if block == pop_block {
            if let Some(succs) = cfg.successors.get(&block) {
                for &succ in succs {
                    exits.insert(succ);
                }
            }
            continue;
        }
        let succs = cfg
            .successors
            .get(&block)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        for &succ in succs {
            if succ == cfg.sink {
                exits.insert(succ);
                continue;
            }
            if region.insert(succ) {
                queue.push(succ);
            }
        }
    }
    (region, exits)
}

/// Validate the grown set as single-entry / single-exit.
///
/// 1. Irreducible: the POP block must be in the region (the grow bound
///    was actually reached); otherwise the span did not close.
/// 2. MultiEntry: only the seed block may have a predecessor outside the
///    region.
/// 3. MultiExit: exactly one NON-SINK distinct successor target leaves the
///    region. The synthetic sink edge is an event boundary and is ignored.
fn validate(
    cfg: &ControlFlowGraph,
    seed: BlockId,
    pop_block: BlockId,
    region: &BTreeSet<BlockId>,
    exits: &BTreeSet<BlockId>,
) -> (MacroRegionOutcome, Option<BlockId>) {
    if !region.contains(&pop_block) {
        return (MacroRegionOutcome::Irreducible, None);
    }
    let extra_entry = region.iter().copied().any(|member| {
        member != seed
            && cfg
                .predecessors
                .get(&member)
                .map(|preds| preds.iter().any(|pred| !region.contains(pred)))
                .unwrap_or(false)
    });
    if extra_entry {
        return (MacroRegionOutcome::MultiEntry, None);
    }
    let non_sink_exits: Vec<BlockId> = exits
        .iter()
        .copied()
        .filter(|&exit| exit != cfg.sink)
        .collect();
    if non_sink_exits.len() != 1 {
        return (MacroRegionOutcome::MultiExit, None);
    }
    (MacroRegionOutcome::Ok, non_sink_exits.into_iter().next())
}

/// Form the flow-stack region for one macro partition in one event's CFG.
/// Pure analysis; the caller consumes only the result record.
pub fn form_macro_region(
    cfg: &ControlFlowGraph,
    frames: &[FlowFrame],
    node_id: usize,
    macro_kind: MacroKind,
    owner_event: &str,
    ranges: &[Range<usize>],
) -> MacroRegionResult {
    let mut result = MacroRegionResult {
        node_id,
        macro_kind,
        owner_event: owner_event.to_string(),
        foot_min: ranges.iter().map(|range| range.start).min(),
        foot_max: ranges.iter().map(|range| range.end).max(),
        push_addr: None,
        pop_addr: None,
        entry_block: None,
        exit_target: None,
        member_blocks: Vec::new(),
        outcome: MacroRegionOutcome::EmptyFootprint,
    };
    if ranges.is_empty() {
        return result;
    }
    let Some(frame) = associate_frame(cfg, frames, ranges) else {
        result.outcome = MacroRegionOutcome::NoFrame;
        return result;
    };
    result.push_addr = Some(frame.push_addr);
    result.pop_addr = Some(frame.pop_addr);

    let Some(seed) = block_containing(cfg, frame.push_addr) else {
        result.outcome = MacroRegionOutcome::NoSeedBlock;
        return result;
    };
    let Some(pop_block) = block_containing(cfg, frame.pop_addr) else {
        result.outcome = MacroRegionOutcome::NoSeedBlock;
        return result;
    };
    result.entry_block = Some(seed);

    let (region, exits) = grow_to_pop(cfg, seed, pop_block);
    result.member_blocks = region.iter().copied().collect();
    let (outcome, exit) = validate(cfg, seed, pop_block, &region, &exits);
    result.outcome = outcome;
    result.exit_target = exit;
    result
}

/// Run flow-stack region formation for every flow-stack macro partition
/// reachable in this event's CFG. The CFG is already scoped to one event;
/// a partition is attempted in this event when its `owner_events` is empty
/// or contains the event.
pub(crate) fn form_event_macro_regions(
    cfg: &ControlFlowGraph,
    graph: &OpcodeGraph,
    map: &K2NodeByteMap,
    owner_event: &str,
) -> Vec<MacroRegionResult> {
    let frames = &graph.flow_frames;
    let mut results = Vec::new();
    for partition in map.partitions.values() {
        let Some(label) = flow_stack_label(partition, graph) else {
            continue;
        };
        let owns_event =
            partition.owner_events.is_empty() || partition.owner_events.contains(owner_event);
        if !owns_event {
            continue;
        }
        results.push(form_macro_region(
            cfg,
            frames,
            partition.node_id,
            label,
            owner_event,
            &partition.ranges,
        ));
    }
    results
}

/// Gate-LET-offset identity for one DoOnce flow-stack macro.
///
/// The flow frame gives the macro's *geometry* (where the body is) but
/// is shared across every macro co-located in one continuation, so it
/// cannot distinguish stacked macros. The disambiguator that works is
/// the gate-LET opcode offset: the `EX_LET*` that sets the macro's gate
/// boolean true is uniquely owned by ONE `K2Node_MacroInstance` via the
/// locality pass `attribute_macro_scaffold_bytes`. This struct binds the
/// candidate's `node_id` to that offset and the gate var it writes,
/// scoped to the candidate's body geometry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MacroGateAttribution {
    /// 1-based export id of the owning `K2Node_MacroInstance`.
    pub node_id: usize,
    /// Macro kind (`DoOnce` / `FlipFlop`).
    pub macro_kind: MacroKind,
    /// The gate boolean leaf name (`Temp_bool_IsClosed_Variable_*` /
    /// `Temp_bool_Has_Been_Initd_Variable_*`) the gate-LET writes.
    pub gate_var: String,
    /// Disk offset of the `EX_LET*` that sets the gate boolean true.
    /// The identity disambiguator: single-owned per offset by the
    /// locality pass.
    pub gate_let_offset: usize,
    /// The node id the locality pass resolved for `gate_let_offset`.
    /// Equals `node_id` for a clean attribution; recorded separately so
    /// the audit can flag any divergence.
    pub gate_let_owner: usize,
    /// The macro body's true single entry block (the PUSH/seed block of
    /// the flow frame).
    pub body_entry: BlockId,
    /// Every block in the macro's body geometry (the validated region
    /// member set), sorted.
    pub body_blocks: Vec<BlockId>,
}

/// True if a macro kind carries a DoOnce-style gate boolean the
/// attribution model keys on. ExecutionSequence / MultiGate are frame
/// constructs without a gate-LET; FlipFlop / IsValid are out of the
/// flow-stack model entirely.
fn is_gated_doonce(macro_kind: MacroKind) -> bool {
    macro_kind == MacroKind::DoOnce
}

/// Build the gate-LET-offset attribution for one validated DoOnce
/// candidate, reusing the locality pass result on [`K2NodeByteMap`].
///
/// The candidate's member blocks give the body geometry; the locality
/// pass's `gate_let_owner_by_offset` gives, per gate-LET disk offset,
/// the single MacroInstance node it belongs to, and
/// `gate_let_is_set_by_offset` says whether each write is the gate-SET
/// (`=true`, identity-bearing) or the INIT-SEED (`=false`, gate reset).
///
/// The macro's own gate-LET is the GATE-SET (`=true`) the locality pass
/// attributed to this candidate's `node_id`. The init-seed is NEVER
/// returned: for a body-before-scaffold macro the gate-set lives in the
/// scaffold OUTSIDE the body geometry while only the seed sits inside,
/// so a body-geometry filter would pick the wrong write. The search is
/// therefore over all node-owned gate-sets, not body-scoped.
///
/// Returns `None` (honest fallback, surfaced by the audit, not silently
/// dropped) when the candidate is not a gated DoOnce, when no `=true`
/// gate-set is owned by the node, or when more than one gate-set is
/// owned and the gate-open dispatch cannot disambiguate which reaches
/// the candidate's body.
pub(crate) fn attribute_macro_gate(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> Option<MacroGateAttribution> {
    if !is_gated_doonce(candidate.macro_kind) {
        return None;
    }
    let chosen = select_gate_set(cfg, candidate, map)?;
    let gate_var = map
        .gate_let_var_by_offset
        .get(&chosen)
        .cloned()
        .unwrap_or_default();
    Some(MacroGateAttribution {
        node_id: candidate.node_id,
        macro_kind: candidate.macro_kind,
        gate_var,
        gate_let_offset: chosen,
        gate_let_owner: candidate.node_id,
        body_entry: candidate.entry_block,
        body_blocks: candidate.member_blocks.clone(),
    })
}

/// Why a gated DoOnce candidate has no gate-set attribution, for the
/// audit's honest-`None` reporting. `NotGated` covers a non-DoOnce
/// candidate; `NoGateSet` means the node owns only init-seeds (or
/// nothing); `Ambiguous` means several gate-sets are owned and the
/// gate-open dispatch could not single one out.
///
/// Test-only: the production decode path never queries the miss reason,
/// only `attribute_macro_gate`'s `Option`. The classifier exists so the
/// gate-attribution tests can assert the specific failure mode.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateAttributionMiss {
    NotGated,
    NoGateSet,
    Ambiguous,
}

/// Classify why `attribute_macro_gate` would return `None` for this
/// candidate, so the audit can log an explicit reason. Mirrors the
/// selection logic exactly; only called when attribution is `None`.
#[cfg(test)]
pub(crate) fn gate_attribution_miss(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> GateAttributionMiss {
    if !is_gated_doonce(candidate.macro_kind) {
        return GateAttributionMiss::NotGated;
    }
    match select_gate_set(cfg, candidate, map) {
        Some(_) => GateAttributionMiss::NotGated,
        None if node_owned_gate_sets(candidate.node_id, map).is_empty() => {
            GateAttributionMiss::NoGateSet
        }
        None => GateAttributionMiss::Ambiguous,
    }
}

/// Disk offsets of every gate-SET (`EX_LET_BOOL gate = true`) the
/// locality pass attributed to `node_id`. Init-seeds (`=false`) are
/// excluded: only the gate-set bears macro identity.
fn node_owned_gate_sets(node_id: usize, map: &K2NodeByteMap) -> Vec<usize> {
    map.gate_let_owner_by_offset
        .iter()
        .filter(|(_, &owner)| owner == node_id)
        .map(|(&offset, _)| offset)
        .filter(|offset| map.gate_let_is_set_by_offset.get(offset).copied() == Some(true))
        .collect()
}

/// Pick the one `=true` GATE-SET that is the candidate macro's, or
/// `None` when the bytecode does not single one out.
///
/// The locality pass over-attributes: one `K2Node_MacroInstance` shared
/// across events accumulates gate-LETs from several gate variables and
/// several event CFGs. So a bare "lowest owned `=true`" is unreliable.
/// Two physical signals discipline the choice:
///
/// 1. **Gate var from the in-body init-seed.** A DoOnce resets its gate
///    to `false` at the top of its own body. So an in-body `=false`
///    seed names the macro's gate var. When exactly one such seed
///    exists, the gate-set must be a `=true` on that same var; this
///    rejects gate-sets the locality pass mixed in from a co-located
///    macro on a different var.
/// 2. **Gate-open dispatch reaches the body.** The chosen `=true` must
///    sit in a block with a CFG successor inside the body geometry (the
///    `EX_LET_BOOL gate=true; EX_JUMP body` gate-open shape). Gate-sets
///    that live in another event's CFG have no block here and cannot
///    reach the body.
///
/// Returns the unique gate-set passing both filters. `None` (honest)
/// when zero or several survive, e.g. a body-before-scaffold macro
/// whose in-body seed names a var but whose `=true` writes on that var
/// live in another event's CFG (none reach this body).
fn select_gate_set(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> Option<usize> {
    let body: BTreeSet<BlockId> = candidate.member_blocks.iter().copied().collect();
    let body_gate_var = in_body_seed_gate_var(cfg, candidate, map);
    let gate_sets = node_owned_gate_sets(candidate.node_id, map);
    let on_var: Vec<usize> = gate_sets
        .iter()
        .copied()
        .filter(|offset| match &body_gate_var {
            Some(var) => map.gate_let_var_by_offset.get(offset) == Some(var),
            None => true,
        })
        .collect();
    match on_var.as_slice() {
        [] => None,
        [only] => Some(*only),
        many => {
            let reaching: Vec<usize> = many
                .iter()
                .copied()
                .filter(|&offset| gate_open_reaches_body(cfg, offset, &body))
                .collect();
            match reaching.as_slice() {
                [single] => Some(*single),
                _ => None,
            }
        }
    }
}

/// The gate variable named by the candidate's in-body `=false`
/// init-seed, when exactly one distinct such variable exists. `None`
/// when no in-body seed exists (the gate-set is then disambiguated by
/// body-reach alone) or when several distinct seed variables sit in the
/// body (the locality pass mixed several macros' seeds in, so the var
/// is not determinable).
fn in_body_seed_gate_var(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    map: &K2NodeByteMap,
) -> Option<String> {
    let body_spans: Vec<Range<usize>> = candidate
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

/// True when the block containing the gate-set `EX_LET_BOOL` at
/// `let_offset` has a CFG successor inside `body` (the candidate's
/// member-block set). Models the gate-open dispatch jumping into the
/// gated body. The body block itself is excluded from `body` membership
/// of the LET's own block so a gate-set already inside the body does not
/// trivially "reach" itself.
fn gate_open_reaches_body(
    cfg: &ControlFlowGraph,
    let_offset: usize,
    body: &BTreeSet<BlockId>,
) -> bool {
    let Some(let_block) = block_containing(cfg, let_offset) else {
        return false;
    };
    cfg.successors
        .get(&let_block)
        .into_iter()
        .flatten()
        .any(|successor| *successor != let_block && body.contains(successor))
}

/// Decode a validated [`MacroRegionCandidate`]'s member blocks into a
/// flat statement list, reusing the production `decode_subrange` opcode
/// decoder over the candidate's disk-byte coverage.
///
/// This is the equivalence audit's parallel decode: it never feeds
/// production; the audit applies the standard transform stack to the result
/// and compares the recovered `Latch` against the recognizer's. The
/// returned statements are raw (pre-transform); the caller runs
/// `recognize_latches` + the rest of the stack to fold the macro.
pub(crate) fn decode_macro_region_body(
    cfg: &ControlFlowGraph,
    candidate: &MacroRegionCandidate,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    // Flow order, NOT disk order: the gated body sits at a lower disk
    // offset than its gate scaffold (body-before-scaffold), so a disk
    // sort scrambles the gate-then-body adjacency the recognizer needs.
    let blocks = flow_order_blocks(cfg, candidate);
    let mut stmts = Vec::new();
    for block_id in blocks {
        let Some(block) = cfg.blocks.get(block_id) else {
            continue;
        };
        if block.opcodes.is_empty() || block.end <= block.start {
            continue;
        }
        stmts.extend(crate::bytecode::decode::branch::decode_subrange(
            block.start,
            block.end,
            ctx,
        ));
    }
    stmts
}

/// Member blocks ordered by a forward BFS from the candidate's entry
/// block over CFG successors restricted to the member set. This honors
/// the macro's flow order (the back-jump down to a lower-disk body block)
/// instead of disk order, so the gated body decodes adjacent to its gate
/// scaffold even when the compiler placed it body-before-scaffold.
fn flow_order_blocks(cfg: &ControlFlowGraph, candidate: &MacroRegionCandidate) -> Vec<BlockId> {
    let members: BTreeSet<BlockId> = candidate.member_blocks.iter().copied().collect();
    let mut order: Vec<BlockId> = Vec::new();
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    queue.push_back(candidate.entry_block);
    seen.insert(candidate.entry_block);
    while let Some(block) = queue.pop_front() {
        order.push(block);
        if let Some(succs) = cfg.successors.get(&block) {
            for &succ in succs {
                if members.contains(&succ) && seen.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
    }
    // Any member not reached by the BFS (defensive) trails in disk order.
    for &block_id in &candidate.member_blocks {
        if seen.insert(block_id) {
            order.push(block_id);
        }
    }
    order
}

#[cfg(test)]
// Single-range footprints are intentional: tests anchor a macro on one
// block's byte span. The single-range-in-vec lint suggests a range
// collection, which is the wrong shape here.
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use super::*;
    use crate::bytecode::cfg::BasicBlock;
    use std::collections::BTreeMap;

    /// Build a synthetic CFG from `(source, target)` edges. Block ids are
    /// `0..node_count`; a synthetic sink at `node_count` collects every
    /// block with no outgoing edge. Each block gets a one-byte disk span
    /// (`[id, id+1)`) and a single opcode at `id`, so footprint and
    /// frame-address math lands on block ids directly.
    fn make_cfg(node_count: usize, edges: &[(BlockId, BlockId)]) -> ControlFlowGraph {
        let sink_id = node_count;
        let blocks: Vec<BasicBlock> = (0..=node_count)
            .map(|id| BasicBlock {
                id,
                start: id,
                end: id + 1,
                opcodes: if id == sink_id { Vec::new() } else { vec![id] },
            })
            .collect();
        let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for block in &blocks {
            successors.insert(block.id, Vec::new());
            predecessors.insert(block.id, Vec::new());
        }
        let mut has_outgoing: BTreeSet<BlockId> = BTreeSet::new();
        for &(source, target) in edges {
            successors.entry(source).or_default().push(target);
            predecessors.entry(target).or_default().push(source);
            has_outgoing.insert(source);
        }
        for block_id in 0..node_count {
            if !has_outgoing.contains(&block_id) {
                successors.entry(block_id).or_default().push(sink_id);
                predecessors.entry(sink_id).or_default().push(block_id);
            }
        }
        ControlFlowGraph {
            blocks,
            successors,
            predecessors,
            entry: 0,
            sink: sink_id,
        }
    }

    /// A frame whose addresses land on the given block ids (block id ==
    /// disk offset under `make_cfg`).
    fn frame(
        push: BlockId,
        pop: BlockId,
        pushed_target: BlockId,
        fallthrough: BlockId,
    ) -> FlowFrame {
        FlowFrame {
            push_addr: push,
            pop_addr: pop,
            pushed_target,
            fallthrough,
        }
    }

    /// Clean DoOnce-shaped flow-stack macro. The PUSH block (1) defers a
    /// continuation; the gate JIN routes to the body (2) which runs and
    /// reaches the POP block (3); the POP resumes the continuation (4).
    /// Footprint sits on the body block. Forms {1,2,3} with exit 4.
    #[test]
    fn clean_flowstack_macro_validates() {
        // 0 -> 1 (PUSH/entry); 1 -> 2 (body) and 1 -> 3 (gate skip to POP);
        // 2 -> 3 (POP block); 3 -> 4 (resume/exit).
        let cfg = make_cfg(5, &[(0, 1), (1, 2), (1, 3), (2, 3), (3, 4)]);
        // pushed_target is the body (2), pop on block 3.
        let frames = vec![frame(1, 3, 2, 4)];
        let footprint = vec![2usize..3];
        let result = form_macro_region(&cfg, &frames, 100, MacroKind::DoOnce, "Evt", &footprint);
        assert_eq!(result.outcome, MacroRegionOutcome::Ok, "{result:?}");
        assert_eq!(result.entry_block, Some(1));
        assert_eq!(result.exit_target, Some(4));
        let candidate = result.candidate().expect("validated => candidate");
        assert_eq!(candidate.entry_block, 1);
        assert_eq!(candidate.exit_target, 4);
    }

    /// Body-before-scaffold shape (POP at a LOWER disk offset than PUSH).
    /// The macro body (block 1) is reached by a back-jump from the PUSH
    /// block (block 3); the POP (block 2) sits before the PUSH on disk.
    /// Graph growth follows the back-jump down, so the region forms even
    /// though disk order is inverted. This is the case disk-span
    /// association gets wrong.
    #[test]
    fn body_before_scaffold_validates() {
        // Disk order: 0,1(body),2(POP),3(PUSH),4(exit).
        // Edges: 0 -> 3 (entry reaches PUSH); 3 -> 1 (push body, back-jump
        // down); 1 -> 2 (body to POP); 2 -> 4 (resume/exit).
        let cfg = make_cfg(5, &[(0, 3), (3, 1), (1, 2), (2, 4)]);
        // PUSH at block 3, POP at block 2, pushed_target is body block 1.
        let frames = vec![frame(3, 2, 1, 4)];
        let footprint = vec![1usize..2];
        let result = form_macro_region(&cfg, &frames, 101, MacroKind::DoOnce, "Evt", &footprint);
        assert_eq!(result.outcome, MacroRegionOutcome::Ok, "{result:?}");
        assert_eq!(result.entry_block, Some(3));
        assert_eq!(result.exit_target, Some(4));
        let members: BTreeSet<BlockId> = {
            let (region, _) = grow_to_pop(&cfg, 3, 2);
            region
        };
        assert!(members.contains(&1) && members.contains(&2) && members.contains(&3));
    }

    /// A second external edge into the macro body gives the region two
    /// entry blocks, which the validator rejects.
    #[test]
    fn multi_entry_rejected() {
        // 0 -> 1 (PUSH/entry), 0 -> 2 (also into the body directly);
        // 1 -> 2 (body/POP), 2 -> 3 (resume). Block 2 has an external
        // predecessor (0) besides the in-region edge from 1.
        let cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 2), (2, 3)]);
        let frames = vec![frame(1, 2, 2, 3)];
        let footprint = vec![2usize..3];
        let result = form_macro_region(&cfg, &frames, 102, MacroKind::DoOnce, "Evt", &footprint);
        assert_eq!(result.outcome, MacroRegionOutcome::MultiEntry, "{result:?}");
    }

    /// No frame's reachable set covers the footprint => `no_frame`.
    #[test]
    fn no_frame_reported() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        // The frame's pushed_target (1) reaches {1,2}, footprint is far
        // outside any block opcode.
        let frames = vec![frame(0, 2, 1, 3)];
        let footprint = vec![900usize..904];
        let result = form_macro_region(&cfg, &frames, 103, MacroKind::DoOnce, "Evt", &footprint);
        assert_eq!(result.outcome, MacroRegionOutcome::NoFrame, "{result:?}");
    }

    /// Association tie-breaks to the frame with the smallest reachable
    /// set. The footprint sits in both frames' bodies; the tighter one
    /// (smaller reachable set) wins.
    #[test]
    fn association_picks_tightest_reachable() {
        // 0 -> 1; 1 -> 2; 2 -> 3; 3 -> 4. Linear chain.
        let cfg = make_cfg(5, &[(0, 1), (1, 2), (2, 3), (3, 4)]);
        // Wide frame: pushed_target 1, pop 4 => reaches {1,2,3,4}.
        // Tight frame: pushed_target 2, pop 3 => reaches {2,3}.
        // Footprint on block 2 sits in both; tighter (pop=3) wins.
        let frames = vec![frame(0, 4, 1, 5), frame(1, 3, 2, 4)];
        let footprint = vec![2usize..3];
        let chosen = associate_frame(&cfg, &frames, &footprint).expect("a frame associates");
        assert_eq!(chosen.pop_addr, 3);
        assert_eq!(chosen.pushed_target, 2);
    }

    #[test]
    fn empty_footprint_reported() {
        let cfg = make_cfg(2, &[(0, 1)]);
        let result = form_macro_region(&cfg, &[], 105, MacroKind::DoOnce, "Evt", &[]);
        assert_eq!(result.outcome, MacroRegionOutcome::EmptyFootprint);
    }

    /// Flow order follows CFG successors from the entry block, so a
    /// body-before-scaffold layout (body at a lower disk offset, reached
    /// by a back-jump) is visited gate-then-body, not disk-sorted. Here
    /// the entry (3) jumps back to the body (1) then forward to the POP
    /// (2): flow order is 3,1,2, the reverse of disk order 1,2,3.
    #[test]
    fn flow_order_follows_back_jump() {
        let cfg = make_cfg(5, &[(0, 3), (3, 1), (1, 2), (2, 4)]);
        let candidate = MacroRegionCandidate {
            node_id: 1,
            macro_kind: MacroKind::DoOnce,
            entry_block: 3,
            exit_target: 4,
            member_blocks: vec![1, 2, 3],
            push_addr: 3,
            pop_addr: 2,
        };
        assert_eq!(flow_order_blocks(&cfg, &candidate), vec![3, 1, 2]);
    }

    /// Build a `K2NodeByteMap` with only the gate-LET locality fields
    /// populated (the slice the attribution model reads). Each entry is
    /// `(offset, owner_node, gate_var, is_set)`; `is_set` is `true` for
    /// the GATE-SET (`=true`) and `false` for the INIT-SEED (`=false`).
    fn gate_map(entries: &[(usize, usize, &str, bool)]) -> K2NodeByteMap {
        let mut map = K2NodeByteMap::empty();
        for (offset, owner, var, is_set) in entries {
            map.gate_let_owner_by_offset.insert(*offset, *owner);
            map.gate_let_var_by_offset.insert(*offset, var.to_string());
            map.gate_let_is_set_by_offset.insert(*offset, *is_set);
        }
        map
    }

    fn doonce_candidate(node_id: usize, member_blocks: Vec<BlockId>) -> MacroRegionCandidate {
        MacroRegionCandidate {
            node_id,
            macro_kind: MacroKind::DoOnce,
            entry_block: member_blocks[0],
            exit_target: 0,
            member_blocks,
            push_addr: 0,
            pop_addr: 0,
        }
    }

    /// A DoOnce whose body block (id == disk offset under `make_cfg`)
    /// covers a gate-LET offset owned by the candidate resolves to that
    /// offset and its gate var.
    #[test]
    fn gate_attribution_resolves_owned_offset() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        // Gate-SET at offset 2 (block 2's one-byte span) owned by node 100.
        let map = gate_map(&[(2, 100, "Temp_bool_IsClosed_Variable_3", true)]);
        let candidate = doonce_candidate(100, vec![1, 2]);
        let attribution = attribute_macro_gate(&cfg, &candidate, &map).expect("attributed");
        assert_eq!(attribution.node_id, 100);
        assert_eq!(attribution.gate_let_offset, 2);
        assert_eq!(attribution.gate_var, "Temp_bool_IsClosed_Variable_3");
        assert_eq!(attribution.gate_let_owner, 100);
    }

    /// Two stacked DoOnce sharing the same body geometry but owning
    /// distinct gate-LET offsets resolve to distinct offsets (two
    /// co-located DoOnce macros on one continuation in miniature).
    #[test]
    fn gate_attribution_distinguishes_stacked_macros() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        // Both macros' bodies span blocks {1,2}; offset 1 owned by node
        // 200, offset 2 owned by node 201. Same gate var, distinct
        // offsets.
        let map = gate_map(&[
            (1, 200, "Temp_bool_IsClosed_Variable_5", true),
            (2, 201, "Temp_bool_IsClosed_Variable_5", true),
        ]);
        let first = attribute_macro_gate(&cfg, &doonce_candidate(200, vec![1, 2]), &map)
            .expect("first attributed");
        let second = attribute_macro_gate(&cfg, &doonce_candidate(201, vec![1, 2]), &map)
            .expect("second attributed");
        assert_ne!(first.gate_let_offset, second.gate_let_offset);
        assert_eq!(first.gate_let_offset, 1);
        assert_eq!(second.gate_let_offset, 2);
    }

    /// A DoOnce with no gate-LET offset owned by its node inside its body
    /// geometry is unattributable (the audit flags it; we do not invent
    /// an offset).
    #[test]
    fn gate_attribution_unattributable_when_no_owned_offset() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        // Offset 2 owned by a DIFFERENT node (999), not the candidate.
        let map = gate_map(&[(2, 999, "Temp_bool_IsClosed_Variable_1", true)]);
        let candidate = doonce_candidate(100, vec![1, 2]);
        assert!(attribute_macro_gate(&cfg, &candidate, &map).is_none());
    }

    /// Non-DoOnce frame macros (ExecutionSequence) carry no gate-LET and
    /// are not attributed.
    #[test]
    fn gate_attribution_skips_non_doonce() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        let map = gate_map(&[(2, 100, "Temp_bool_IsClosed_Variable_0", true)]);
        let mut candidate = doonce_candidate(100, vec![1, 2]);
        candidate.macro_kind = MacroKind::ExecutionSequence;
        assert!(attribute_macro_gate(&cfg, &candidate, &map).is_none());
    }

    /// The init-seed (`=false`) is never returned. A node owning only an
    /// in-body `=false` write (the gate reset, no `=true` gate-set) is
    /// honestly unattributable, not bound to the seed offset (the old
    /// `.min()`-in-body bug returned the seed).
    #[test]
    fn gate_attribution_never_returns_init_seed() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        // Only an in-body `=false` seed at offset 2, owned by node 100.
        let map = gate_map(&[(2, 100, "Temp_bool_IsClosed_Variable_3", false)]);
        let candidate = doonce_candidate(100, vec![1, 2]);
        assert!(attribute_macro_gate(&cfg, &candidate, &map).is_none());
        assert_eq!(
            gate_attribution_miss(&cfg, &candidate, &map),
            GateAttributionMiss::NoGateSet
        );
    }

    /// Body-before-scaffold contamination: the node owns an in-body
    /// `=false` seed naming gate var X plus a `=true` gate-set on a
    /// DIFFERENT var Y (mixed in by the over-attributing locality pass).
    /// The seed names the macro's gate as X; no `=true` on X exists, so
    /// the result is honest `None` (ambiguous), never the foreign Y set.
    /// This is a body-before-scaffold DoOnce contamination shape in miniature.
    #[test]
    fn gate_attribution_rejects_foreign_var_gate_set() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        let map = gate_map(&[
            // In-body seed names IsClosed_Variable_3 (the macro's gate).
            (2, 100, "Temp_bool_IsClosed_Variable_3", false),
            // A =true gate-set on a foreign var, also in-body.
            (1, 100, "Temp_bool_Has_Been_Initd_Variable_3", true),
        ]);
        let candidate = doonce_candidate(100, vec![1, 2]);
        assert!(attribute_macro_gate(&cfg, &candidate, &map).is_none());
        assert_eq!(
            gate_attribution_miss(&cfg, &candidate, &map),
            GateAttributionMiss::Ambiguous
        );
    }

    /// With several `=true` gate-sets on the macro's gate var owned by
    /// the node, the gate-open dispatch (the `=true` block with a CFG
    /// successor into the body) singles out the right one. Here offset 0
    /// (block 0) jumps into the body {1,2}; offset 3 (block 3) does not.
    #[test]
    fn gate_attribution_disambiguates_by_body_reach() {
        // 0 -> 1 (gate-open into body); 1 -> 2 (body); 2 -> 3; 3 -> sink.
        let cfg = make_cfg(4, &[(0, 1), (1, 2), (2, 3)]);
        let map = gate_map(&[
            (0, 100, "Temp_bool_IsClosed_Variable_3", true),
            (3, 100, "Temp_bool_IsClosed_Variable_3", true),
        ]);
        let candidate = doonce_candidate(100, vec![1, 2]);
        let attribution = attribute_macro_gate(&cfg, &candidate, &map).expect("attributed");
        assert_eq!(attribution.gate_let_offset, 0);
    }

    /// Members unreachable from the entry through the member set still
    /// trail in disk order (defensive: never drop a member block).
    #[test]
    fn flow_order_appends_unreached_members() {
        let cfg = make_cfg(4, &[(0, 1), (1, 2)]);
        let candidate = MacroRegionCandidate {
            node_id: 1,
            macro_kind: MacroKind::DoOnce,
            entry_block: 1,
            exit_target: 3,
            // Block 3 is not reachable from 1 within the member set.
            member_blocks: vec![1, 2, 3],
            push_addr: 1,
            pop_addr: 2,
        };
        let order = flow_order_blocks(&cfg, &candidate);
        assert_eq!(order[0], 1);
        assert!(order.contains(&3));
        assert_eq!(order.len(), 3);
    }
}
