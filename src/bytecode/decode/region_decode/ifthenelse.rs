use super::*;

/// Region-driven emitter for `RegionKind::IfThenElse`. Returns a
/// `Vec<Stmt>` containing the entry block's pre-JIN preamble stmts
/// followed by a `Stmt::Branch` for the JIN itself. Returns `None`
/// when the region's entry block doesn't end with `EX_JUMP_IF_NOT`
/// so the per-opcode walk runs unchanged.
///
/// CFG successor convention (see `cfg/build.rs::wire_edges` and
/// `partition::scan_one_opcode`): for `EX_JUMP_IF_NOT`,
/// `successors[0]` is the operand target (jump taken when cond is
/// FALSE, i.e. the else-arm) and `successors[1]` is the fallthrough
/// (cond TRUE, i.e. the then-arm).
///
/// Preamble: the entry block's opcodes before the JIN terminator are
/// decoded via `decode_one_or_branch` and appended ahead of the
/// `Stmt::Branch`. A `consumed` tracker prevents re-emission when
/// multi-opcode recognisers (Call, Let, nested Branch) consume more
/// than one opcode address.
///
/// Cond inlining: the on-disk cond expression is decoded directly from
/// the JIN's operand bytes. Pre-JIN `EX_LET*` temp assignments now
/// appear in the preamble stmts; the existing post-decode
/// `inline_single_use_temps` pass (when wired in) is expected to fold
/// them into the cond. The current probe does not feed its output
/// through that pass, so the un-inlined shape is what the comparison
/// log shows.
pub(super) fn try_emit_ifthenelse_region(
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: Option<&RegionTree>,
) -> Option<(Vec<Stmt>, Option<RegionId>)> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    if region.kind != RegionKind::IfThenElse {
        return None;
    }
    // Dispatch-table probe: when the entry block heads a Blueprint
    // switch cascade, emit Stmt::Switch directly instead of letting the
    // per-link IfThenElse classification fire and let cascade_fold
    // produce a malformed Switch with empty case bodies. See
    // `try_emit_jumpifnot_cascade_region` for the recognised shapes.
    if let Some(stmt) = try_emit_jumpifnot_cascade_region(region, region_id, cfg, ctx) {
        return Some((vec![stmt], None));
    }
    let entry_block = cfg.blocks.get(region.entry)?;
    let terminator_addr = *entry_block.opcodes.last()?;
    if *ctx.bytecode.get(terminator_addr)? != EX_JUMP_IF_NOT {
        // Fallback for the naked-if-with-latent-call shape: the
        // entry block's terminator is the latent call (with both a
        // fallthrough and a SkipOffset resume edge), but the actual
        // gate is a `pop_flow_if_not` sitting mid-block.
        return try_emit_pop_flow_if_not_branch_region(region, region_id, cfg, ctx)
            .map(|stmts| (stmts, None));
    }

    // Nested-naked-if shape: an `EX_POP_FLOW_IF_NOT` sits earlier in
    // the entry block than the JIN terminator. The outer if is the
    // naked-if (Form B); the JIN is its body. The helper walks the
    // preamble up to the pop_flow_if_not, then decodes the naked-if
    // whose body absorbs the inner JIN. See
    // `try_emit_pop_flow_if_not_branch_region` for the byte-layout.
    if has_earlier_pop_flow_if_not(entry_block, terminator_addr, ctx) {
        return try_emit_pop_flow_if_not_branch_region(region, region_id, cfg, ctx)
            .map(|stmts| (stmts, None));
    }

    let cond = decode_jin_cond(terminator_addr, ctx)?;

    let succs = cfg.successors.get(&region.entry)?;
    if succs.len() != 2 {
        return None;
    }
    let else_block_id = succs[0];
    let then_block_id = succs[1];
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    // Shared interior-join hoist: detect a content-bearing block X that
    // immediately post-dominates the Branch (idom == region.entry,
    // reachable from both arms) but is buried in a descendant region's
    // coverage. When present, decode both arms bounded at X (so neither
    // arm emits X, and the descendant's own-exit tail pull for X is
    // suppressed via `hoist_join`) and emit X's content once after the
    // Branch, hoisting the join below the if/else.
    //
    // Gated to the then-arm-delegation shape: the then-arm is owned by a
    // single child IfThenElse region whose entry is the then-block (the
    // `find_coverage_full_then_arm_child` / `find_full_arm_ifthenelse_child`
    // precondition). That path decodes the then-arm by delegating to the
    // child region and the else-arm by byte slice, both of which exclude X
    // naturally once X sits in `arm_descent_stops`, so the hoist relocates
    // X cleanly without changing the arm-decode path selection. The
    // byte-slice-absorption shapes (`extend_then_with_merge_gap`,
    // displaced-else rebalance) instead key on disk-contiguous segment
    // gaps; excluding X there flips the path to the region walker and
    // restructures the arm nesting, so the hoist declines those (X stays
    // where the existing path placed it).
    let hoist_join = find_shared_interior_join(then_block_id, else_block_id, region, cfg, idom)
        .filter(|_| region_has_then_arm_delegate_child(region, region_tree, then_block_id));
    let _hoist_stops_guard = hoist_join.map(|join| {
        let mut stops = ctx.arm_descent_stops.borrow().clone();
        stops.insert(join);
        ctx.with_arm_descent_stops(stops)
    });

    // Walk entry-block opcodes before the JIN terminator. Each
    // pre-JIN opcode goes through the same per-opcode decoder used
    // for the linear sweep, so multi-opcode constructs (Call, Let,
    // Branch nested in preamble) consume their full span and the
    // consumed tracker keeps the next iteration from re-decoding
    // the same bytes.
    let preamble = decode_entry_preamble(entry_block, terminator_addr, entry_block.end, ctx);

    let (mut then_body, mut else_body, delegated_then_child) = decode_ifthenelse_arms(
        then_block_id,
        else_block_id,
        region,
        region_id,
        walk,
        region_tree,
        hoist_join,
    );

    // Emit the hoisted interior-join content once after the Branch. Both
    // arms were decoded bounded at X (X is in `arm_descent_stops`), so X
    // appears in neither arm body; the descendant region that owns X
    // suppressed its own-exit tail pull for X (see the `hoist_join` gate
    // in `decode_arm_via_region_dispatch`). The join block is decoded
    // under the region's owner guard, the same context the arm decoders
    // saw, so multi-opcode constructs in X resolve identically.
    if let Some(join) = hoist_join {
        if let Some(join_block) = cfg.blocks.get(join) {
            if !join_block.opcodes.is_empty() {
                let join_stmts = decode_subrange(join_block.start, join_block.end, ctx);
                if !join_stmts.is_empty() {
                    let mut out = preamble;
                    out.push(Stmt::Branch {
                        cond,
                        then_body,
                        else_body,
                        offset: terminator_addr,
                    });
                    out.extend(join_stmts);
                    return Some((out, None));
                }
            }
        }
    }

    // Merge-continuation pull-into-then-arm: when our else-arm is empty
    // and a merge-continuation sibling exists (a region whose entry
    // equals our exit and shares our parent), pull its decoded content
    // into our then-arm. The BP IsValid macro produces this shape: R1 =
    // IfThenElse{cond, then, empty} as the macro's valid-pin gate; R2 =
    // IfThenElse(...) is the macro's downstream content semantically
    // nested inside the valid arm but emitted as R1's sibling by the
    // SESE decomposition.
    //
    // EX_RETURN guard: skip pulling regions whose body decodes to just
    // `Return { None }`. Without the guard, the IfThenElse merge-block
    // trap re-emerges and synthetic else: [Return] shapes collapse.
    // The pull-into-then-arm fires when our else-arm is empty
    // (the IsValid-macro dual-role pattern) OR when our exit block
    // carries content owned by us. The own-exit-with-content case is
    // needed because `mark_region_consumed` would otherwise swallow the
    // continuation's entry block (R2.entry == R1.exit, owned by R1),
    // and the walker's `visited_blocks.contains(child_entry)` gate
    // would skip R2 entirely, dropping the continuation's content.
    // Pulling cont into then_arm keeps the content emitted; else-body
    // is preserved verbatim, the pull only appends after the existing
    // then-arm stmts.
    //
    // Full-arm IfThenElse delegation: when
    // `decode_ifthenelse_arms` already emitted the then-arm via
    // `emit_continuation_region(R2)`, propagate R2 as the pulled
    // continuation so the walker marks it consumed; skip the
    // merge-continuation pull (the then-arm already owns its content).
    let mut pulled_continuation: Option<RegionId> = delegated_then_child;
    let cluster_a_e_gate = pulled_continuation.is_none()
        && (else_body.is_empty()
            || region_tree
                .map(|tree| is_own_exit_with_content(region_id, tree, cfg))
                .unwrap_or(false));
    if cluster_a_e_gate {
        if let Some(tree) = region_tree {
            if let Some(continuation_id) = find_merge_continuation_region(region_id, tree) {
                if !region_body_is_only_return(continuation_id, cfg, ctx) {
                    let continuation_stmts = emit_continuation_region(continuation_id, tree, walk);
                    if !continuation_stmts.is_empty() {
                        // Both-arms post-dominator join: when the else-arm
                        // carries content and both arms reach the exit, the
                        // continuation is shared tail (post-dominates the
                        // Branch), not then-arm-local content. Emit it AFTER
                        // the Branch, mirroring the own_exit (true,true) arm,
                        // so it isn't pre-empted by being pulled into the
                        // then-arm. The continuation is already fully recursed
                        // by emit_continuation_region.
                        let arms_reach =
                            arms_reach_exit(then_block_id, else_block_id, region, cfg, idom);
                        if !else_body.is_empty() && arms_reach == (true, true) {
                            let mut out = preamble;
                            out.push(Stmt::Branch {
                                cond,
                                then_body,
                                else_body,
                                offset: terminator_addr,
                            });
                            out.extend(continuation_stmts);
                            return Some((out, Some(continuation_id)));
                        }
                        then_body.extend(continuation_stmts);
                        pulled_continuation = Some(continuation_id);
                    }
                }
            }
        }
    }

    // Own-exit-with-content dispatch: when no
    // sibling-continuation pull happened but the region's own exit block
    // carries user content, route by which arm(s) reach the exit. The
    // exit-block predecessor set in the CFG distinguishes the three
    // sub-cases: both arms reach (shared tail / empty-arm FlipFlop) ->
    // emit after the Branch; one arm reaches (then-only or else-only tail)
    // -> append to that arm; neither reaches (degenerate) -> leave alone.
    let own_exit = pulled_continuation.is_none()
        && region_tree
            .map(|tree| is_own_exit_with_content(region_id, tree, cfg))
            .unwrap_or(false);
    // `own_exit` is only true when `region_tree` is Some (it's computed from
    // `region_tree.map(...)`), so matching here can't drop the own-exit path;
    // it just avoids an expect on externally-derived structure.
    let after_branch_tail = if let (true, Some(tree)) = (own_exit, region_tree) {
        let tail = decode_post_merge_continuation(region_id, tree, cfg, ctx);
        distribute_own_exit_tail(
            tail,
            then_block_id,
            else_block_id,
            region,
            cfg,
            idom,
            &mut then_body,
            &mut else_body,
        )
    } else {
        None
    };

    let mut out = preamble;
    out.push(Stmt::Branch {
        cond,
        then_body,
        else_body,
        offset: terminator_addr,
    });
    if let Some(tail) = after_branch_tail {
        out.extend(tail);
    }
    Some((out, pulled_continuation))
}

/// Route an own-exit tail (the content of an IfThenElse region's own exit
/// block) into the correct emission slot by which arm(s) reach the exit.
///
/// - both arms reach (shared tail / empty-arm FlipFlop): returns
///   `Some(tail)` so the caller emits it AFTER the Branch;
/// - then-only / else-only reach: appends the tail to that arm body,
///   returns `None`;
/// - neither reaches (degenerate): leaves the exit alone, returns `None`.
///
/// A tail that is empty or just a bare `Return { None }` is dropped
/// (returns `None`).
#[allow(clippy::too_many_arguments)]
fn distribute_own_exit_tail(
    tail: Vec<Stmt>,
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    then_body: &mut Vec<Stmt>,
    else_body: &mut Vec<Stmt>,
) -> Option<Vec<Stmt>> {
    let tail_is_bare_return = matches!(tail.as_slice(), [Stmt::Return { value: None, .. }]);
    if tail.is_empty() || tail_is_bare_return {
        return None;
    }
    let (then_reaches, else_reaches) =
        arms_reach_exit(then_block_id, else_block_id, region, cfg, idom);
    match (then_reaches, else_reaches) {
        (true, true) => Some(tail),
        (true, false) => {
            then_body.extend(tail);
            None
        }
        (false, true) => {
            else_body.extend(tail);
            None
        }
        (false, false) => None,
    }
}

/// Detect a shared interior-join block X for the IfThenElse `region`:
/// a content-bearing block that immediately post-dominates the Branch
/// (its immediate dominator is the region entry, reached from BOTH arms)
/// yet is buried inside a descendant region's coverage rather than being
/// the region's own exit. Such a join belongs AFTER the if/else, but the
/// deepest-slice block assignment parents it into one arm's child region
/// and the other arm drops it (an interior join shared by both arms of a
/// nested branch).
///
/// Returns `Some(X)` only when EXACTLY ONE block qualifies, so the hoist
/// fires on the unambiguous single-join shape and bails (current
/// behavior) on anything with zero or multiple candidate joins. The gate
/// stack, all four conditions plus the uniqueness requirement, keeps the
/// structural "interior join reachable from both arms" predicate (which
/// matches dozens of correctly-emitted IfThenElse regions) from firing
/// where the existing emit is already right.
fn find_shared_interior_join(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
) -> Option<BlockId> {
    if region.exit == cfg.sink {
        return None;
    }
    let then_reachable = reachable_blocks_in_arm(
        then_block_id,
        Some(else_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );
    let else_reachable = reachable_blocks_in_arm(
        else_block_id,
        Some(then_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );

    let mut candidates: Vec<BlockId> = Vec::new();
    for block in &cfg.blocks {
        let join = block.id;
        if join == cfg.sink || block.opcodes.is_empty() {
            continue;
        }
        // X must immediately post-dominate the Branch: its idom is the
        // region entry itself, not a block inside either arm.
        if idom.get(&join) != Some(&region.entry) {
            continue;
        }
        // X is the interior join, not the region's own exit (which the
        // existing own-exit dispatch already handles).
        if join == region.exit {
            continue;
        }
        // X must be reachable from BOTH arms: a CFG predecessor in the
        // then-arm subtree AND one in the else-arm subtree.
        let preds = cfg
            .predecessors
            .get(&join)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        let from_then = preds.iter().any(|pred| then_reachable.contains(pred));
        let from_else = preds.iter().any(|pred| else_reachable.contains(pred));
        if from_then && from_else {
            candidates.push(join);
        }
    }
    match candidates.as_slice() {
        [single] => Some(*single),
        _ => None,
    }
}

/// Returns (then_reaches_exit, else_reaches_exit) by intersecting each
/// arm's reachable-block set with the predecessor set of `region.exit`.
/// Uses the same `reachable_blocks_in_arm` BFS the arm-slicer uses,
/// so the answer is consistent with how arm bodies were decoded.
fn arms_reach_exit(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
) -> (bool, bool) {
    let exit_preds: BTreeSet<BlockId> = cfg
        .predecessors
        .get(&region.exit)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .collect();
    if exit_preds.is_empty() {
        return (false, false);
    }
    let then_reachable = reachable_blocks_in_arm(
        then_block_id,
        Some(else_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );
    let else_reachable = reachable_blocks_in_arm(
        else_block_id,
        Some(then_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );
    // An empty arm (e.g. FlipFlop's A|B with content in the exit block)
    // still reaches exit via its direct successor edge.
    let then_reaches = exit_preds.contains(&then_block_id)
        || then_reachable
            .iter()
            .any(|block| exit_preds.contains(block));
    let else_reaches = exit_preds.contains(&else_block_id)
        || else_reachable
            .iter()
            .any(|block| exit_preds.contains(block));
    (then_reaches, else_reaches)
}

/// Decode a merge-continuation region for inclusion in the
/// previous IfThenElse's then-arm. Dispatches the continuation through
/// the same per-kind emitter priority as `walk_region` would, then
/// recurses into the continuation's own children when no per-kind
/// emitter accepts it.
///
/// Returns an empty `Vec` when the continuation classifies as Linear or
/// Trivial without any owned blocks; the caller treats an empty result
/// as "nothing to pull" and leaves the merge-continuation alone (it
/// will surface as a disk-order sibling instead).
fn emit_continuation_region(
    region_id: RegionId,
    region_tree: &RegionTree,
    walk: RegionWalkCtx,
) -> Vec<Stmt> {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    let region = &region_tree.regions[region_id];
    // Per-kind emitters return only the structured stmts derived from
    // the region's entry block + arm bodies. When the continuation
    // region itself owns a content-bearing exit block (R2.exit owned
    // by R2 with non-empty opcodes), those exit-block stmts must be
    // appended here; otherwise `mark_region_consumed(R2)` swallows
    // them. Done once at this layer so each per-kind emitter stays
    // focused on its own shape.
    let append_own_exit = |mut stmts: Vec<Stmt>| -> Vec<Stmt> {
        if is_own_exit_with_content(region_id, region_tree, cfg) {
            let mut tail = decode_post_merge_continuation(region_id, region_tree, cfg, ctx);
            stmts.append(&mut tail);
        }
        stmts
    };
    if let Some((emitted, _continuation, _is_sequence_chain)) =
        dispatch_region_emitters(region, region_id, region_tree, walk, true)
    {
        return append_own_exit(emitted);
    }
    // Linear / Trivial fallback: decode the region's transitive byte
    // coverage via decode_subrange under the region's owner guard.
    let Some(region_byte_ranges) = ctx.region_byte_ranges else {
        return Vec::new();
    };
    let Some(ranges) = region_byte_ranges.get(&region_id) else {
        return Vec::new();
    };
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });
    let mut stmts: Vec<Stmt> = Vec::new();
    for range in ranges {
        let mut decoded = decode_subrange(range.start, range.end, ctx);
        stmts.append(&mut decoded);
    }
    stmts
}

/// Decode both arms of an IfThenElse region, applying a "displaced
/// else" rebalance for the BP IsValid-macro-style shape.
///
/// IsValid macros (and similar K2Node compilations) emit one arm body
/// at a HIGHER disk address than the JIN's immediate jump target. The
/// CFG sees both arms as reachable from the same conditional, but in
/// disk order the layout looks like:
///   [JIN] [then-prefix bytes] [else (typically just EX_JUMP)] [displaced then-suffix]
/// or the mirror image with arms swapped. The byte-sliced
/// `decide_branch_layout` collapses the else range to span both the
/// EX_JUMP block and the displaced suffix, since they're disk-contiguous
/// and both rejoin at the same convergence point. The CFG-reachable BFS
/// here attributes the displaced suffix to its dominance-arm (the
/// then-arm), leaving the else-arm with just the EX_JUMP and producing
/// flattened output downstream.
///
/// We re-attribute trailing then-arm segments that sit AFTER the
/// else-arm in disk order back to the else-arm so the rendered Branch
/// matches the byte-slicing. The pattern is gated on:
/// - else-arm has exactly 1 segment
/// - then-arm has 2+ segments
/// - else-arm segment lies strictly between two then-arm segments
///
/// Without those gates we'd disturb regular CFG-driven IfThenElse
/// shapes where the BFS already produces correct arms.
fn decode_ifthenelse_arms(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: Option<&RegionTree>,
    hoist_join: Option<BlockId>,
) -> (Vec<Stmt>, Vec<Stmt>, Option<RegionId>) {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    let then_segments = arm_byte_slice(then_block_id, Some(else_block_id), region, region_id, walk);
    let else_segments = arm_byte_slice(else_block_id, Some(then_block_id), region, region_id, walk);

    if let Some(result) = try_full_arm_delegation(
        then_block_id,
        else_block_id,
        region,
        region_id,
        region_tree,
        else_segments.as_deref(),
        walk,
    ) {
        return result;
    }

    if let Some(result) = try_coverage_full_then_delegation(
        then_block_id,
        else_block_id,
        region,
        region_id,
        region_tree,
        then_segments.as_deref(),
        else_segments.as_deref(),
        walk,
    ) {
        return result;
    }

    if let (Some(then_segs), Some(else_segs)) = (then_segments.as_ref(), else_segments.as_ref()) {
        if let Some((rebalanced_then, rebalanced_else)) =
            rebalance_displaced_else(then_segs, else_segs, region, region_tree, then_block_id)
        {
            // Decode the then-arm first, then suppress its emitted offsets
            // when decoding the else-arm. A Sequence (or DoOnce/Latch) in
            // the then-arm can pull pin bodies from a physically-displaced
            // byte segment that `rebalance_displaced_else` moved into the
            // else-arm; without suppression the else re-decodes those same
            // bytes, duplicating the call (an IsValid-gated check, a
            // turn-style action). The exclude set is derived from
            // the then-arm's emitted statements, so genuine displaced-else
            // sites (whose then-arm emits nothing inside the moved segment)
            // see an empty intersection and are unaffected.
            let then_body = decode_arm_segments(&rebalanced_then, ctx);
            let exclude = stmt_offset_exclude_set(&then_body);
            let else_body = decode_arm_segments_excluding(&rebalanced_else, ctx, &exclude);
            return (then_body, else_body, None);
        }
    }

    // Byte-contiguous merge-block absorption:
    // the `decide_branch_layout` byte-slice covers the then-arm as
    // `[body_start, terminating_jump_pos]` where the terminator is the
    // first JUMP whose target lies at or past `else_disk`. Any block
    // sitting in `[then_block.start, else_block.start)` that's a merge
    // of both arms (dominated by the region entry, not by either arm
    // root) falls into the then-arm's byte range and the byte-slice
    // absorbs its stmts. The CFG-reachable BFS here excludes those merge
    // blocks because they aren't strictly dominated by the then-arm root.
    //
    // Pattern: a nested-branch function. R1's then-block B1 has
    // single successor B2 (a sibling-region-owned merge of B1 and
    // R2.then's tail). B2 sits at bytes [B1.end, R1.else_block.start),
    // so the byte-slice absorbs it. The fix gives the then-arm the
    // same byte coverage the byte-slice would: extend then-segs to
    // include any region-owned blocks in the gap
    // `[then_segs.end, else_segs.start)`.
    //
    // Suppressed when the merge-continuation pull
    // (`emit_continuation_region`) would pull a merge-continuation
    // sibling into the then-arm: that path handles the merge content at
    // the region-tree layer and running both paths double-emits the
    // merge block. The pull fires when else_body is empty OR
    // `is_own_exit_with_content`.
    let cluster_a_e_would_fire = if let Some(else_segs) = else_segments.as_ref() {
        else_segs.is_empty()
            || region_tree
                .map(|tree| is_own_exit_with_content(region_id, tree, cfg))
                .unwrap_or(false)
    } else {
        false
    };
    if !cluster_a_e_would_fire {
        if let (Some(then_segs), Some(else_segs)) = (then_segments.as_ref(), else_segments.as_ref())
        {
            let extended = extend_then_with_merge_gap(
                then_segs,
                else_segs,
                then_block_id,
                else_block_id,
                region,
                region_id,
                walk,
            );
            if let Some(extended_then) = extended {
                return (
                    decode_arm_segments(&extended_then, ctx),
                    decode_arm_segments(else_segs, ctx),
                    None,
                );
            }
        }
    }

    // Single-path arm decode: the region walker is the sole arm-decode
    // path. Dispatch each arm through `decode_arm_via_region_dispatch`,
    // which handles inner-region re-nesting. When the walker can't resolve
    // (no region tree, or a synthetic context missing `region_byte_ranges`)
    // fall back to the byte-slice `decode_arm_body` for both arms; this is
    // the byte-slice decode kept for non-region-aware paths.
    if let Some((walker_then, walker_else)) = try_region_dispatch_both_arms(
        then_block_id,
        else_block_id,
        region,
        region_id,
        walk,
        region_tree,
        hoist_join,
    ) {
        return (walker_then, walker_else, None);
    }

    let legacy_then = decode_arm_body(then_block_id, Some(else_block_id), region, region_id, walk);
    let legacy_else = decode_arm_body(else_block_id, Some(then_block_id), region, region_id, walk);
    (legacy_then, legacy_else, None)
}

/// Full-arm IfThenElse child delegation: when the current region has
/// a single IfThenElse child R2 whose entry equals the then-block and
/// whose exit equals the current region's exit, R2 owns the entire
/// then-arm structure (including its own then/else nesting). Emit
/// R1.then by delegating to R2 via `emit_continuation_region`; the
/// caller marks R2 consumed so the walker doesn't double-emit it.
/// R1.else_body comes from else_segs verbatim. Returns `None` when the
/// region has no such child.
fn try_full_arm_delegation(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    region_id: RegionId,
    region_tree: Option<&RegionTree>,
    else_segments: Option<&[Range<usize>]>,
    walk: RegionWalkCtx,
) -> Option<(Vec<Stmt>, Vec<Stmt>, Option<RegionId>)> {
    let ctx = walk.ctx;
    // `find_full_arm_ifthenelse_child` only returns Some when `region_tree` is
    // Some, so this pair-match can't drop the path; it avoids an expect.
    let (Some(child_id), Some(tree)) = (
        find_full_arm_ifthenelse_child(region, region_tree, then_block_id),
        region_tree,
    ) else {
        return None;
    };
    let then_body = emit_continuation_region(child_id, tree, walk);
    let else_body = match else_segments {
        Some(else_segs) => decode_arm_segments(else_segs, ctx),
        None => decode_arm_body(else_block_id, Some(then_block_id), region, region_id, walk),
    };
    Some((then_body, else_body, Some(child_id)))
}

/// Coverage-based full-then-arm IfThenElse delegation: when the
/// current region has a child IfThenElse R1 whose entry equals the
/// then-block AND whose transitive byte coverage equals the
/// then-arm's coverage, R1 owns the entire then-arm structure even
/// though R1.exit != R0.exit. R1's exit block is its own
/// merge-continuation, and `emit_continuation_region(R1)` appends
/// that exit content via `append_own_exit`. The else-arm decode
/// proceeds normally from else_segs.
///
/// Pattern: an event whose then-arm child region owns a local
/// merge. R0 has exit=B6 (the function-wide merge), R1 has exit=B3
/// (the then-arm-local merge). R1's coverage spans the whole
/// then-arm, including the trailing calls in B3. Returns `None` when
/// the then-segments are absent or no covering child exists.
#[allow(clippy::too_many_arguments)]
fn try_coverage_full_then_delegation(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    region_id: RegionId,
    region_tree: Option<&RegionTree>,
    then_segments: Option<&[Range<usize>]>,
    else_segments: Option<&[Range<usize>]>,
    walk: RegionWalkCtx,
) -> Option<(Vec<Stmt>, Vec<Stmt>, Option<RegionId>)> {
    let ctx = walk.ctx;
    let then_segs = then_segments?;
    // `find_coverage_full_then_arm_child` only returns Some when
    // `region_tree` is Some, so the pair-match can't drop the path.
    let (Some(child_id), Some(tree)) = (
        find_coverage_full_then_arm_child(region, region_tree, then_block_id, then_segs, ctx),
        region_tree,
    ) else {
        return None;
    };
    let child_region = &tree.regions[child_id];
    // Call `try_emit_ifthenelse_region` directly rather than
    // routing through `emit_continuation_region`. The continuation
    // wrapper's `append_own_exit` would double the inner region's
    // own-exit content (R1.exit is owned by R1 and the inner
    // IfThenElse emitter already absorbs it via the
    // `arms_reach_exit` dispatch).
    let then_body = match try_emit_ifthenelse_region(child_region, child_id, walk, Some(tree)) {
        Some((emitted, _)) => emitted,
        None => emit_continuation_region(child_id, tree, walk),
    };
    let else_body = match else_segments {
        Some(else_segs) => decode_arm_segments(else_segs, ctx),
        None => decode_arm_body(else_block_id, Some(then_block_id), region, region_id, walk),
    };
    Some((then_body, else_body, Some(child_id)))
}

/// Region-aware arm decode of both arms. Returns `Some((then, else))` when
/// the region tree is available and both arms resolve through
/// `decode_arm_via_region_dispatch`. Returns `None` otherwise (no region
/// tree, or synthetic context without `region_byte_ranges`) so the caller
/// can fall back to the byte-slice decode for both arms.
fn try_region_dispatch_both_arms(
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: Option<&RegionTree>,
    hoist_join: Option<BlockId>,
) -> Option<(Vec<Stmt>, Vec<Stmt>)> {
    let region_tree = region_tree?;
    let walker_then = decode_arm_via_region_dispatch(
        then_block_id,
        Some(else_block_id),
        region,
        region_id,
        walk,
        region_tree,
        hoist_join,
    )?;
    let walker_else = decode_arm_via_region_dispatch(
        else_block_id,
        Some(then_block_id),
        region,
        region_id,
        walk,
        region_tree,
        hoist_join,
    )?;
    Some((walker_then, walker_else))
}

/// Region-aware decode of one branch arm: a block BFS bounded to the arm
/// (the same SESE bounds `reachable_blocks_in_arm` uses: `region.entry`,
/// `region.exit`, `sibling_arm_entry`, and strict dominance from
/// `arm_entry`) that dispatches any block heading a descendant region
/// through `dispatch_child_region_at`, mirroring the SequenceChain pin
/// walk (`decode_pin_body`). Non-region blocks decode their opcodes via
/// `decode_block_opcodes`.
///
/// Returns `None` (treated as "couldn't resolve") when the
/// arm slice can't be computed (missing `region_byte_ranges` in synthetic
/// contexts).
pub(super) fn decode_arm_via_region_dispatch(
    arm_entry: BlockId,
    sibling_arm_entry: Option<BlockId>,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: &RegionTree,
    hoist_join: Option<BlockId>,
) -> Option<Vec<Stmt>> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    if arm_entry == region.exit {
        return Some(Vec::new());
    }
    // The arm slice doubles as the `enclosing_ranges` passed to
    // `decode_block_opcodes` (so multi-block constructs widen their jump
    // target window the same way the byte-slice path does) and as the
    // signal that the arm is computable. Absent in synthetic contexts.
    let arm_ranges = arm_byte_slice(arm_entry, sibling_arm_entry, region, region_id, walk)?;

    // Sibling-arm entry doubles as the dispatched child region's
    // arm-descent stop set so its arm slicer cannot over-walk into the
    // sibling arm, matching `dispatch_child_region_at`'s boundary guard.
    let mut sibling_stops: BTreeSet<BlockId> = BTreeSet::new();
    if let Some(sibling) = sibling_arm_entry {
        sibling_stops.insert(sibling);
    }

    // The hoisted interior-join block is a walk boundary the enclosing
    // IfThenElse will emit once after the Branch. It arrives either as the
    // explicit `hoist_join` param (this arm's own region) or via
    // `arm_descent_stops` (an ancestor IfThenElse installed it before
    // dispatching this nested region, so a descendant emitter, e.g. an
    // inner IfThen, must not pull it as a convergence tail either).
    let join_stops: BTreeSet<BlockId> = {
        let mut set = ctx.arm_descent_stops.borrow().clone();
        if let Some(join) = hoist_join {
            set.insert(join);
        }
        set
    };

    let mut stmts: Vec<Stmt> = Vec::new();
    let mut consumed: Vec<Range<usize>> = Vec::new();
    let mut visited_blocks: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    let is_boundary = |block_id: BlockId| -> bool {
        block_id == region.exit
            || block_id == region.entry
            || sibling_arm_entry == Some(block_id)
            || (block_id != arm_entry && join_stops.contains(&block_id))
    };
    queue.push_back(arm_entry);
    while let Some(block_id) = queue.pop_front() {
        if is_boundary(block_id) {
            continue;
        }
        if !visited_blocks.insert(block_id) {
            continue;
        }

        if let Some((emitted, consumed_ids)) =
            dispatch_child_region_at(block_id, region_id, region_tree, walk, &sibling_stops)
        {
            stmts.extend(emitted);
            for &consumed_id in &consumed_ids {
                mark_region_consumed(
                    region_tree,
                    consumed_id,
                    cfg,
                    &mut consumed,
                    &mut visited_blocks,
                );
            }
            let last_consumed = consumed_ids.last().copied().unwrap_or(consumed_ids[0]);
            let resume_exit = region_tree.regions[last_consumed].exit;

            // Post-branch convergence tail: when the dispatched child is an
            // IfThen whose own content-bearing exit was suppressed by its
            // own-exit dispatch (because an arm-decoding ancestor, i.e. THIS
            // arm walk, absorbs it), that exit is a convergence sibling that
            // runs unconditionally after the inner branch, not the inner
            // branch's else. `mark_region_consumed` above marked the exit
            // block visited, so the BFS resume below can't reach it and the
            // tail would be dropped (a dropped else, both-arms convergence
            // tail). Emit it here at top level so it surfaces as a sibling
            // after the inner branch, matching the byte-slice path's
            // `extend_then_with_merge_gap`.
            //
            // Gated to IfThen children: IfThenElse / SequenceChain children
            // self-absorb their own content-bearing exit during their own
            // emit (the merge-continuation pull / `append_own_exit`), so re-emitting here
            // would duplicate. IfThen is the only kind whose own-exit pull is
            // conditionally suppressed by `parent_owns_or_absorbs_exit`,
            // which is exactly the convergence-sibling case. A
            // SequenceChain-child shape with an empty exit never fires the
            // gate, so its genuine nested else stays intact.
            // Suppress the convergence-tail emit when the dispatched
            // child's content-bearing exit IS the enclosing IfThenElse's
            // hoisted interior join: that block belongs to neither arm
            // (the parent emits it once after the Branch), so emitting it
            // here would re-bury it inside this arm.
            let exit_is_hoisted_join =
                join_stops.contains(&region_tree.regions[last_consumed].exit);
            if !exit_is_hoisted_join
                && region_tree.regions[last_consumed].kind == RegionKind::IfThen
                && is_own_exit_with_content(last_consumed, region_tree, cfg)
                && parent_owns_or_absorbs_exit(last_consumed, region_tree, cfg)
            {
                let mut tail = decode_post_merge_continuation(last_consumed, region_tree, cfg, ctx);
                let tail_is_bare_return =
                    matches!(tail.as_slice(), [Stmt::Return { value: None, .. }]);
                if !tail.is_empty() && !tail_is_bare_return {
                    stmts.append(&mut tail);
                }
            }

            if !is_boundary(resume_exit)
                && !visited_blocks.contains(&resume_exit)
                && is_strictly_dominated_by(resume_exit, arm_entry, idom)
            {
                queue.push_back(resume_exit);
            }
            continue;
        }

        decode_block_opcodes(cfg, block_id, ctx, &mut stmts, &mut consumed, &arm_ranges);
        let Some(succs) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &succ in succs {
            if is_boundary(succ) || visited_blocks.contains(&succ) {
                continue;
            }
            if succ != arm_entry && !is_strictly_dominated_by(succ, arm_entry, idom) {
                continue;
            }
            queue.push_back(succ);
        }
    }
    Some(stmts)
}

/// Absorb byte-contiguous merge blocks into the then-arm to match the
/// byte-slicing layout. The byte-slice (`decide_branch_layout`) treats
/// every byte in `[body_start, else_disk)` as part of the then-body when a
/// terminating JUMP lives inside that range and jumps past else_disk. The
/// CFG-reachable
/// BFS in `reachable_blocks_in_arm` excludes merge blocks because they're
/// not strictly dominated by the then-arm root, so the bytes get dropped.
///
/// Conditions for the fix to fire:
/// 1. Both arms produced non-empty segments.
/// 2. Then-segments lie entirely BEFORE else-segments in disk order
///    (max-then-end <= min-else-start).
/// 3. There is a gap `[gap_start, gap_end)` between them.
/// 4. Region-owned blocks exist in the gap whose CFG predecessors include
///    a block in the then-arm's reachable set (the merge-from-then signal).
///
/// Returns `Some(extended_then_segs)` when the fix fires, `None` otherwise.
fn extend_then_with_merge_gap(
    then_segs: &[Range<usize>],
    else_segs: &[Range<usize>],
    then_block_id: BlockId,
    else_block_id: BlockId,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
) -> Option<Vec<Range<usize>>> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    if then_segs.is_empty() || else_segs.is_empty() {
        return None;
    }
    let then_max_end = then_segs.iter().map(|seg| seg.end).max()?;
    let else_min_start = else_segs.iter().map(|seg| seg.start).min()?;
    if then_max_end >= else_min_start {
        return None;
    }
    let region_ranges = ctx.region_byte_ranges?.get(&region_id)?;
    let then_reachable = reachable_blocks_in_arm(
        then_block_id,
        Some(else_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );
    let else_reachable = reachable_blocks_in_arm(
        else_block_id,
        Some(then_block_id),
        region.entry,
        region.exit,
        cfg,
        idom,
        &BTreeSet::new(),
    );

    let mut gap_blocks: Vec<&BasicBlock> = Vec::new();
    for block in &cfg.blocks {
        if block.opcodes.is_empty() {
            continue;
        }
        if block.start < then_max_end || block.end > else_min_start {
            continue;
        }
        if then_reachable.contains(&block.id) || else_reachable.contains(&block.id) {
            continue;
        }
        // Must live inside the region's transitive byte coverage.
        let in_region = region_ranges
            .iter()
            .any(|range| block.start < range.end && range.start < block.end);
        if !in_region {
            continue;
        }
        // Must be a forward-merge from the then-arm: at least one
        // predecessor reachable in then-arm. This filters out unrelated
        // blocks in the gap (e.g. sibling-region preamble).
        let preds = cfg
            .predecessors
            .get(&block.id)
            .map(|preds| preds.as_slice())
            .unwrap_or(&[]);
        let merges_from_then = preds.iter().any(|pred| then_reachable.contains(pred));
        if !merges_from_then {
            continue;
        }
        gap_blocks.push(block);
    }
    if gap_blocks.is_empty() {
        return None;
    }
    gap_blocks.sort_by_key(|block| block.start);

    let gap_ranges: Vec<Range<usize>> = gap_blocks.iter().map(|b| b.start..b.end).collect();
    let mut extended: Vec<Range<usize>> = then_segs.to_vec();
    extended.extend(gap_ranges);
    extended.sort_by_key(|range| range.start);
    Some(merge_adjacent(extended))
}

/// Detect the "displaced else" pattern and move trailing then-arm
/// segments into the else-arm. Returns `None` when the pattern doesn't
/// apply.
///
/// Pattern: `then_segs` has 2+ entries (sorted by start), `else_segs`
/// has exactly 1 entry, and the else segment sits strictly between two
/// consecutive then segments. The trailing then segments (those at or
/// after the else segment in disk order) move to the else-arm.
///
/// Declines when the current region has a single IfThenElse child R2
/// whose entry equals the then-arm root and whose exit equals the
/// current region's exit (R2 spans the full then-arm). In that case
/// the trailing then-segments are R2's own else-arm content, not
/// displaced else material, and rebalancing destroys R2's nesting.
/// The caller delegates the then-arm emit to R2 via
/// `emit_continuation_region`.
#[allow(clippy::type_complexity)]
fn rebalance_displaced_else(
    then_segs: &[Range<usize>],
    else_segs: &[Range<usize>],
    region: &Region,
    region_tree: Option<&RegionTree>,
    then_block_id: BlockId,
) -> Option<(Vec<Range<usize>>, Vec<Range<usize>>)> {
    if else_segs.len() != 1 || then_segs.len() < 2 {
        return None;
    }
    if find_full_arm_ifthenelse_child(region, region_tree, then_block_id).is_some() {
        return None;
    }
    let else_seg = &else_segs[0];
    let split_index = then_segs.iter().position(|seg| seg.start >= else_seg.end)?;
    if split_index == 0 {
        return None;
    }
    let last_prefix = &then_segs[split_index - 1];
    if last_prefix.end > else_seg.start {
        return None;
    }
    let mut new_then: Vec<Range<usize>> = then_segs[..split_index].to_vec();
    let mut new_else: Vec<Range<usize>> = Vec::new();
    new_else.push(else_seg.clone());
    new_else.extend(then_segs[split_index..].iter().cloned());
    new_else = merge_adjacent(new_else);
    new_then = merge_adjacent(new_then);
    Some((new_then, new_else))
}

/// True when `region`'s then-arm is delegated to a single child
/// IfThenElse region whose entry is the then-block (the precondition for
/// both `find_full_arm_ifthenelse_child` and
/// `find_coverage_full_then_arm_child`). Used to gate the shared
/// interior-join hoist to the arm-decode path whose path selection is
/// stable under excluding the join block: the then-arm delegates to the
/// child region and the else-arm decodes by byte slice, neither of which
/// keys on the disk-contiguous segment gaps the byte-slice-absorption
/// paths use, so relocating the join doesn't restructure the arms.
fn region_has_then_arm_delegate_child(
    region: &Region,
    region_tree: Option<&RegionTree>,
    then_block_id: BlockId,
) -> bool {
    let Some(tree) = region_tree else {
        return false;
    };
    ifthenelse_children_at_entry(region, tree, then_block_id)
        .next()
        .is_some()
}

/// Iterate the `IfThenElse` children of `region` whose entry block is
/// `entry`. Shared filter for the then-arm delegation predicates, each of
/// which layers its own exit/coverage condition on top.
fn ifthenelse_children_at_entry<'a>(
    region: &'a Region,
    tree: &'a RegionTree,
    entry: BlockId,
) -> impl Iterator<Item = (RegionId, &'a Region)> {
    region.children.iter().filter_map(move |&child_id| {
        let child = &tree.regions[child_id];
        (child.kind == RegionKind::IfThenElse && child.entry == entry).then_some((child_id, child))
    })
}

/// Locate an `IfThenElse` child region R2 of `region` where R2 spans
/// the entire then-arm, signalled by `R2.entry == then_block_id` and
/// `R2.exit == region.exit`. Used to discriminate the
/// "inner-IfThenElse-owns-the-then-arm" pattern from regular
/// displaced-else cases.
fn find_full_arm_ifthenelse_child(
    region: &Region,
    region_tree: Option<&RegionTree>,
    then_block_id: BlockId,
) -> Option<RegionId> {
    let tree = region_tree?;
    ifthenelse_children_at_entry(region, tree, then_block_id)
        .find(|(_, child)| child.exit == region.exit)
        .map(|(child_id, _)| child_id)
}

/// Coverage-based full-then-arm IfThenElse delegation predicate. Locate
/// a child IfThenElse R1 whose entry equals `then_block_id` AND whose
/// transitive byte coverage equals the then-arm's byte coverage. R1
/// owns the entire then-arm structure including any local merge block,
/// even when R1.exit differs from the parent region's exit.
///
/// Excludes the `find_full_arm_ifthenelse_child` case (R1.exit ==
/// region.exit), which the caller already handles. Excludes children
/// that do NOT own their exit block; in that shape R1's exit content
/// belongs to the parent and would be missed by R1's emit.
fn find_coverage_full_then_arm_child(
    region: &Region,
    region_tree: Option<&RegionTree>,
    then_block_id: BlockId,
    then_segs: &[Range<usize>],
    ctx: &DecodeCtx,
) -> Option<RegionId> {
    let tree = region_tree?;
    let region_byte_ranges = ctx.region_byte_ranges?;
    if then_segs.is_empty() {
        return None;
    }
    let then_max_end = then_segs.iter().map(|seg| seg.end).max()?;
    let then_min_start = then_segs.iter().map(|seg| seg.start).min()?;
    for (child_id, child) in ifthenelse_children_at_entry(region, tree, then_block_id) {
        if child.exit == region.exit {
            // `find_full_arm_ifthenelse_child` already covers this case.
            continue;
        }
        if tree.block_to_region.get(&child.exit) != Some(&child_id) {
            // R1 must own its exit block so `emit_continuation_region`'s
            // `append_own_exit` picks up the trailing merge content.
            // When the exit is owned by the parent the merge content
            // belongs to the parent and a different code path handles
            // it.
            continue;
        }
        let Some(child_ranges) = region_byte_ranges.get(&child_id) else {
            continue;
        };
        if child_ranges.is_empty() {
            continue;
        }
        let child_min_start = child_ranges.iter().map(|range| range.start).min()?;
        let child_max_end = child_ranges.iter().map(|range| range.end).max()?;
        if child_min_start != then_min_start || child_max_end != then_max_end {
            continue;
        }
        return Some(child_id);
    }
    None
}
