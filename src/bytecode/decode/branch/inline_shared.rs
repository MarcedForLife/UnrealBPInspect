//! Cross-event inline shared-body decoding.
//!
//! Decodes a body shared between events inline at the call site, wrapping
//! the result in the owning DoOnce/FlipFlop latch when the graph identity
//! calls for it.

use crate::bytecode::expr::Expr;
use crate::bytecode::names::MacroKind;
use crate::bytecode::stmt::{LatchKind, Stmt};

use super::super::cross_event_inline::{classify_for_decode_jump, CrossEventDisposition};
use super::super::ctx::{DecodeCtx, OwnerId};
use super::disjoint::{landing_is_entry_anchored, wrap_inlined_stmts};

/// Out-of-range jump path. Consults the cross-event inline classifier
/// when `cross_event_inline` is available; falls back to the previous
/// silent-drop behaviour otherwise.
///
/// Behaviour by `CrossEventDisposition`:
/// - `Inline { target_node, anchor_disk }`: recurse the decoder into
///   the target K2Node's bytecode range under an `OwnerId::SharedBody`
///   decoding owner. Returns the inlined body wrapped in a single-pin
///   `Stmt::Sequence` when more than one statement was produced, the
///   sole statement when exactly one was produced, or `None` when the
///   recursion produced nothing. Recognisers (DoOnce, etc.) run
///   normally inside the recursion so the body folds into the canonical
///   `Stmt::Latch` shape.
/// - `Schedule { event_name }`: emit `Stmt::EventCall`, extending the
///   exact-event-entry path to cover non-entry targets that the
///   classifier still treats as plain calls.
/// - `Drop`: preserve the previous silent-drop behaviour.
pub(super) fn try_cross_event_inline(target_mem: usize, ctx: &DecodeCtx) -> Option<Stmt> {
    let cei = ctx.cross_event_inline?;
    let event_entries = ctx.event_entries?;
    let mem_to_disk = ctx.mem_to_disk?;
    let target_disk = *mem_to_disk.get(&target_mem)?;
    // Generalized (shape-agnostic, knot-guard-free) classification. The
    // entry-anchor discriminator below rejects a resolved `Inline` whose
    // trampoline lands mid-body rather than at the shared region's entry
    // (a mid-body convergence case), keeping the direct-fan-in shared bodies the
    // generalized resolver newly admits (the four `Conv_*_B` cases) while
    // not over-firing on a spurious convergence.
    let disposition = match classify_for_decode_jump(target_mem, target_disk, event_entries, cei) {
        CrossEventDisposition::Inline { target_node, .. }
            if !landing_is_entry_anchored(target_node, target_disk, ctx) =>
        {
            CrossEventDisposition::Drop
        }
        other => other,
    };
    match disposition {
        // A FlipFlop convergence alternates between its A and B exec
        // outputs on successive triggers, so the non-owner event's inlined
        // byte range captures only the reached arm. A byte-range decode
        // there yields a bare one-arm call and silently drops the other
        // arm, misrepresenting the alternating latch as an unconditional
        // call. Synthesize the faithful FlipFlop (toggle + both arms) from
        // the owning event's full decode instead. On synthesis failure
        // return `None` (render empty) rather than the partial body.
        CrossEventDisposition::Inline { target_node, .. }
            if cei
                .macro_names
                .get(&target_node)
                .map(|name| MacroKind::from_name(name))
                == Some(MacroKind::FlipFlop) =>
        {
            synthesize_inline_flipflop(target_disk, ctx)
        }
        CrossEventDisposition::Inline {
            target_node,
            anchor_disk,
        } => decode_inlined_shared_body(target_disk, target_node, anchor_disk, ctx),
        CrossEventDisposition::Schedule { event_name } => Some(Stmt::EventCall {
            event_name,
            offset: target_mem,
        }),
        CrossEventDisposition::Drop => None,
    }
}

/// Recurse the decoder over the shared body region beginning at
/// `target_disk` under an `OwnerId::SharedBody` decoding owner.
///
/// The target K2Node's bytecode range is approximated as the owning
/// event's contiguous run starting at `target_disk` and ending at the
/// owning range's `range.end`. This matches the shared DoOnce shape: the
/// macro body is a contiguous sequence of opcodes within one event's
/// owned range. No `mark_claimed` is registered: the standalone event
/// that also owns these bytes still decodes them normally, the inline
/// recursion just duplicates the decode at the source pin (additive,
/// not exclusive).
///
/// The `decoding_owner` swap to `OwnerId::SharedBody` lets recursive
/// recognisers (DoOnce gate-set / gate-reset detection in particular)
/// distinguish "shared body decode under inline" from the standalone
/// event's own decode, in case future logic needs to gate on that. For
/// the shared DoOnce shape today the inline simply produces the same DoOnce
/// `Stmt::Latch` shape the standalone event would produce.
///
/// Returns `None` when the target disk doesn't fall in any event's
/// owned ranges (genuine orphan, the classifier should already have
/// returned `Drop` in that case but we double-check defensively) or
/// when the recursion produces no statements.
pub(super) fn decode_inlined_shared_body(
    target_disk: usize,
    target_node: usize,
    anchor_disk: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    use super::super::cross_event_inline::k2node_bytecode_range;
    use crate::bytecode::structure::build_skeleton;

    let cei = ctx.cross_event_inline?;

    // Cycle / re-entry guard: refuse to inline the same anchor twice
    // up the same call chain. Without this, an EX_JUMP inside the
    // shared body that targets back into a sibling-event range would
    // recurse without bound.
    if !cei.active_inline_anchors.borrow_mut().insert(anchor_disk) {
        return None;
    }

    let mem_to_disk = ctx.mem_to_disk?;

    // Resolve the K2Node's true logical entry by expanding the
    // trampoline target back to the chain head whose pin partitions
    // contain `target_disk`. Without this the inline range is a strict
    // suffix of the K2Node body and the latch recogniser splits the
    // gate scaffold across two passes, producing nested
    // `Stmt::Latch { Stmt::Latch { ... } }` wrappers.
    let owning_event = cei.event_owned_ranges.iter().find_map(|(name, ranges)| {
        ranges
            .iter()
            .any(|range| target_disk >= range.start && target_disk < range.end)
            .then_some(name.as_str())
    });
    let owning_range_for_skeleton = owning_event.and_then(|name| {
        let ranges = cei.event_owned_ranges.get(name)?;
        let lo = ranges.iter().map(|range| range.start).min()?;
        let hi = ranges.iter().map(|range| range.end).max()?;
        Some(lo..hi)
    });
    let resolved_range = owning_range_for_skeleton.and_then(|owning_full_range| {
        let owning_skeleton = build_skeleton(
            ctx.bytecode,
            ctx.ue5,
            ctx.name_table,
            mem_to_disk,
            owning_full_range,
            &[],
            ctx.graph,
        );
        k2node_bytecode_range(
            target_node,
            target_disk,
            &owning_skeleton,
            cei.event_owned_ranges,
        )
    });
    let mut inline_range = match resolved_range {
        Some(range) => range,
        None => {
            let body_end = inlined_body_end_for(target_disk, cei.event_owned_ranges)?;
            if body_end <= target_disk {
                cei.active_inline_anchors.borrow_mut().remove(&anchor_disk);
                return None;
            }
            target_disk..body_end
        }
    };

    // Embedded shared-body case: the shared DoOnce is a sub-range of a
    // larger owning event (BP_DecoderTest, the ownership-reversed shape),
    // so the owning-range-based resolution above overshoots
    // both ends and decodes unrelated content. Re-bound to the target
    // node's footprint cluster, which decodes to the bare guarded call.
    // Returns `None` (no override) for the tight-body shape,
    // whose owning range already bounds the body and whose decode
    // includes the gate scaffold so the latch recogniser fires normally.
    let footprint_range =
        super::super::cross_event_inline::embedded_inline_range(target_node, target_disk, cei);
    if let Some(range) = footprint_range.clone() {
        inline_range = range;
    }

    // A footprint cluster that begins before the trampoline landing has merged a
    // foreign statement (the owner's divergent tail) ahead of the shared body;
    // decoding from its start renders the owner's tail. Re-anchor at the landing,
    // which the region walk bounds to the shared body. (Divergent-tail boundary.)
    if let Some(range) = footprint_range.clone() {
        if range.start < target_disk && target_disk < range.end {
            inline_range = target_disk..range.end;
        }
    }

    if inline_range.start >= inline_range.end {
        cei.active_inline_anchors.borrow_mut().remove(&anchor_disk);
        return None;
    }

    // Per-event dedup keyed on the K2Node's resolved logical entry.
    // Multiple cross-event trampolines from one source event that all
    // target the same K2Node body collapse to the same `inline_range.start`
    // after the K2Node-entry expansion above; render once. Two
    // trampolines that actually land in distinct K2Node bodies (the
    // classifier maps both to the same `target_node` via the first-DoOnce
    // BFS heuristic) keep distinct entry offsets and both render.
    if cei.already_inlined_target(inline_range.start) {
        cei.active_inline_anchors.borrow_mut().remove(&anchor_disk);
        return None;
    }
    // Record before recursing so a recursive cross-event jump emitted
    // from inside the body decode (e.g. a backward JIN at the end of a
    // DoOnce gate) re-entering with a different anchor still hits the
    // dedup at the resolved entry rather than re-rendering the body.
    cei.record_inlined_target(inline_range.start);

    let owner = OwnerId::SharedBody {
        target_node_id: target_node,
        anchor_disk,
    };
    let graph = ctx.graph?;
    let stmts = decode_inline_region_body(&inline_range, owner, mem_to_disk, graph, ctx);

    cei.active_inline_anchors.borrow_mut().remove(&anchor_disk);

    wrap_inline_shared_body(
        stmts,
        target_node,
        target_disk,
        inline_range.start,
        footprint_range.is_some(),
        cei,
        ctx,
    )
}

/// Build the inlined shared-body statements by decoding the resolved
/// `inline_range` through the flow-scoped region-tree path.
///
/// Builds a target-region-scoped sub-context so the recursive region walk
/// runs prescans and skeleton-aware dispatch on the target's bytes
/// (Sequence chain heads, IsValid macros, tail-JIN arms). Reuses `ctx`'s
/// asset-derived state (name table, pin data, cross-event ctx) but pins
/// `owned_ranges` / `skeleton` / `cfg` / `region_tree` /
/// `region_byte_ranges` to the inlined region and uses a fresh `claimed`
/// map. The CFG is bounded to the flow-stack-reachable address set so the
/// body does not absorb non-flow-reachable scaffold from a sibling arm.
fn decode_inline_region_body(
    inline_range: &std::ops::Range<usize>,
    owner: OwnerId,
    mem_to_disk: &std::collections::BTreeMap<usize, usize>,
    graph: &crate::bytecode::partition::OpcodeGraph,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    use super::super::{build_inline_cfg_and_region_tree_flow_scoped, decode_region_body};
    use crate::bytecode::structure::build_skeleton;

    let inline_skeleton = build_skeleton(
        ctx.bytecode,
        ctx.ue5,
        ctx.name_table,
        mem_to_disk,
        inline_range.clone(),
        &[],
        Some(graph),
    );
    let inline_ranges_slice = std::slice::from_ref(inline_range);

    // The cei recursion (`active_inline_anchors` / `inlined_targets`) runs
    // for real on this production path: the anchor was inserted by the
    // caller and is removed after this returns; the resolved-entry dedup
    // recorded at `record_inlined_target` is the real per-event state.
    let (cfg, region_tree, region_byte_ranges) = build_inline_cfg_and_region_tree_flow_scoped(
        inline_range.start,
        inline_ranges_slice,
        graph,
        ctx.bytecode,
        ctx.ue5,
        ctx.name_table,
        mem_to_disk,
    );
    let inline_claimed: std::cell::RefCell<
        std::collections::BTreeMap<usize, super::super::ctx::Claim>,
    > = std::cell::RefCell::new(std::collections::BTreeMap::new());
    let inline_ctx = DecodeCtx {
        mem_to_disk: ctx.mem_to_disk,
        event_entries: ctx.event_entries,
        function_signatures: ctx.function_signatures,
        owned_ranges: Some(inline_ranges_slice),
        skeleton: Some(&inline_skeleton),
        claimed: Some(&inline_claimed),
        decoding_owner: std::cell::Cell::new(Some(owner)),
        graph: ctx.graph,
        cfg: Some(&cfg),
        region_tree: Some(&region_tree),
        region_byte_ranges: Some(&region_byte_ranges),
        cross_event_inline: ctx.cross_event_inline,
        k2node_byte_map: ctx.k2node_byte_map,
        ..DecodeCtx::new(
            ctx.bytecode,
            ctx.name_table,
            ctx._imports,
            ctx._export_names,
            ctx.ue5,
        )
    };
    decode_region_body(&region_tree, &cfg, &inline_ctx)
}

/// Wrap the decoded inline shared-body statements into the final `Stmt`.
///
/// When `target_node` is a DoOnce MacroInstance whose decoded body carries
/// no recognised DoOnce latch (the gate scaffold sat outside the inlined
/// range), synthesize the `DoOnce` wrapper from graph identity. Two
/// scaffold-placement shapes reach this synthesis:
/// - embedded footprint (`has_footprint == true`, BP_DecoderTest released
///   events): the body was re-bound to the target's footprint cluster,
///   excluding the prologue gate-set; and
/// - direct fan-in with no footprint cluster (`Conv_DirectDoOnce_B`): the
///   gate-set bytes sit entirely outside the resolved inline range.
///
/// The owner gate-name derivation applies only to the direct fan-in shape
/// (`prefer_owner_name = !has_footprint`); the embedded-footprint shape
/// keeps the body-derived name. Otherwise the statements wrap plainly.
fn wrap_inline_shared_body(
    stmts: Vec<Stmt>,
    target_node: usize,
    target_disk: usize,
    inline_start: usize,
    has_footprint: bool,
    cei: &super::super::cross_event_inline::CrossEventInlineCtx,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    if cei
        .macro_names
        .get(&target_node)
        .map(|name| MacroKind::from_name(name))
        == Some(MacroKind::DoOnce)
        && !stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Latch {
                    kind: LatchKind::DoOnce { .. },
                    ..
                }
            )
        })
    {
        let prefer_owner_name = !has_footprint;
        return wrap_inline_doonce(
            stmts,
            target_node,
            target_disk,
            inline_start,
            prefer_owner_name,
            ctx,
        );
    }
    wrap_inlined_stmts(stmts, inline_start)
}

/// Synthesize the faithful FlipFlop body for a non-owner event that
/// converges on a shared FlipFlop `target_node`.
///
/// The FlipFlop alternates between its A and B exec outputs on successive
/// triggers; only the reached arm's flat body sits in the non-owner
/// event's inlined byte range, so a byte-range decode there yields one
/// arm and silently drops the other. The owning event (the event whose
/// owned disk range contains `target_disk`) owns the complete macro
/// footprint contiguously, so re-decoding it through the normal
/// CFG-driven region decode plus the FlipFlop transforms recovers the
/// canonical `Stmt::Latch { FlipFlop }` with toggle + both arms. Returns a
/// clone of that latch so the non-owner renders the same body the owner
/// does (same gate var, same arm ordering).
///
/// Returns `None` when the owner can't be resolved or its decode produces
/// no recognised FlipFlop latch (the caller then keeps the previous
/// deferral, rendering empty rather than a partial body).
fn synthesize_inline_flipflop(target_disk: usize, ctx: &DecodeCtx) -> Option<Stmt> {
    let cei = ctx.cross_event_inline?;
    let owner_event = owning_event_name_for_disk(target_disk, cei.event_owned_ranges)?;
    let owner_ranges = cei.event_owned_ranges.get(owner_event)?;
    super::super::synthesize_owner_flipflop(owner_event, owner_ranges, ctx)
}

/// Owned name of the event whose disk ranges contain `target_disk`.
fn owning_event_name_for_disk(
    target_disk: usize,
    event_owned_ranges: &std::collections::BTreeMap<String, Vec<std::ops::Range<usize>>>,
) -> Option<&str> {
    event_owned_ranges.iter().find_map(|(name, ranges)| {
        ranges
            .iter()
            .any(|range| target_disk >= range.start && target_disk < range.end)
            .then_some(name.as_str())
    })
}

/// Wrap an embedded shared-DoOnce inline body in a `Stmt::Latch{DoOnce}`,
/// synthesizing the gate from graph identity (`target_node` is a DoOnce
/// MacroInstance). The gate var is a node-unique synthetic, the inlined
/// body carries no `ResetDoOnce` sibling so no real gate var is needed for
/// reset matching.
///
/// When `prefer_owner_name` is set (the direct fan-in shape), the display
/// name is taken from the OWNING event's own recognised DoOnce latch
/// (e.g. `DoOnce_3`), re-decoded from graph identity, so the non-owner
/// renders the same gate name the owner does. Otherwise (the
/// embedded-footprint shape, whose owner holds several DoOnce latches) the
/// name follows the first user call in the inlined body, matching the
/// standalone-event latch naming.
fn wrap_inline_doonce(
    stmts: Vec<Stmt>,
    target_node: usize,
    target_disk: usize,
    offset: usize,
    prefer_owner_name: bool,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    if stmts.is_empty() {
        return None;
    }
    let owner_name = prefer_owner_name
        .then(|| owner_doonce_name_for_disk(target_disk, ctx))
        .flatten();
    let name = owner_name
        .or_else(|| first_call_func_name(&stmts))
        .unwrap_or_else(|| "DoOnce".to_string());
    Some(Stmt::Latch {
        kind: LatchKind::DoOnce {
            name,
            gate_var: format!("Temp_bool_IsClosed_Inlined_{}", target_node),
        },
        init: Vec::new(),
        body: stmts,
        offset,
    })
}

/// The owning event's recognised DoOnce latch display name for the shared
/// DoOnce reached at `target_disk`, re-decoded from graph identity.
fn owner_doonce_name_for_disk(target_disk: usize, ctx: &DecodeCtx) -> Option<String> {
    let cei = ctx.cross_event_inline?;
    let owner_event = owning_event_name_for_disk(target_disk, cei.event_owned_ranges)?;
    let owner_ranges = cei.event_owned_ranges.get(owner_event)?;
    super::super::synthesize_owner_doonce_name(owner_event, owner_ranges, ctx)
}

/// The function name of the first `Stmt::Call` in `stmts` (recursing
/// through container bodies). Used to name a synthesized inline DoOnce.
fn first_call_func_name(stmts: &[Stmt]) -> Option<String> {
    for stmt in stmts {
        if let Stmt::Call {
            func: Expr::Var(name),
            ..
        } = stmt
        {
            return Some(name.clone());
        }
        for slice in stmt.child_bodies() {
            if let Some(name) = first_call_func_name(slice) {
                return Some(name);
            }
        }
    }
    None
}

/// Find the end of the contiguous owned range that contains
/// `target_disk`. Returns the matching `range.end` from
/// `event_owned_ranges`, or `None` when no event covers the offset.
fn inlined_body_end_for(
    target_disk: usize,
    event_owned_ranges: &std::collections::BTreeMap<String, Vec<std::ops::Range<usize>>>,
) -> Option<usize> {
    for ranges in event_owned_ranges.values() {
        for range in ranges {
            if target_disk >= range.start && target_disk < range.end {
                return Some(range.end);
            }
        }
    }
    None
}
