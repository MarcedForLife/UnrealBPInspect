use super::*;

/// Route a loop body/completion byte position to the structured
/// IfThenElse emitter when it is the entry of a nested `IfThenElse`
/// region carved under the loop region currently being decoded.
///
/// The loop emitter delegates body/completion extraction to the
/// byte-slice decoder (`try_decode_loop` -> `decode_subrange` ->
/// `decode_segment_into` -> `decode_branch`). When both arms of a nested
/// if/else converge BACKWARD at the loop merge, `decide_branch_layout`
/// finds no forward terminating `EX_JUMP` and produces an empty else,
/// dropping the else-arm (it floats unconditionally at the resume
/// position). The region tree, however, has already carved that if/else
/// as a distinct `IfThenElse` region whose arms slice correctly via CFG
/// reachability. This helper detects that situation and dispatches the
/// region to `try_emit_ifthenelse_region`, which arm-slices both arms.
///
/// Mirrors `dispatch_child_region_at` (the SequenceChain pin-entry
/// case) but is driven by a byte position reached during the loop's
/// linear body sweep rather than a pin-entry block. Returns the emitted
/// stmts plus the disk offset to advance past (the region's transitive
/// byte coverage end, clamped to `seg_end`). Returns `None` and leaves
/// the caller to use the legacy path when:
/// - no loop region is active (`loop_completion_region` unset),
/// - the position isn't a CFG block start,
/// - the block isn't the entry of an `IfThenElse` region,
/// - that `IfThenElse` region isn't a descendant of the active loop,
/// - the region has non-empty `region_byte_ranges` coverage (the normal
///   walk handles it; dispatching would duplicate content), or
/// - `try_emit_ifthenelse_region` declines the region.
pub(crate) fn try_dispatch_loop_body_region_at(
    pos: usize,
    seg_end: usize,
    ctx: &DecodeCtx,
) -> Option<(Vec<Stmt>, usize)> {
    let loop_region_id = ctx.loop_completion_region.get()?;
    let cfg = ctx.cfg?;
    let region_tree = ctx.region_tree?;

    let block_id = cfg.block_at_start(pos)?;

    // Find the IfThenElse region whose entry IS this block and which
    // descends from the active loop. The block may carry several regions
    // (it can be the shared entry of an inner loop AND a sibling if/else,
    // the dual-role pattern), so a parent-walk from `block_to_region`
    // would miss a SIBLING IfThenElse. Scan every region for an
    // entry == block_id match instead.
    let target_id = region_tree
        .regions
        .iter()
        .enumerate()
        .find(|(region_id, region)| {
            region.kind == RegionKind::IfThenElse
                && region.entry == block_id
                && region_is_descendant_of(*region_id, loop_region_id, region_tree)
        })
        .map(|(region_id, _)| region_id)?;

    // Only dispatch when this if/else region does NOT own its own entry
    // block: `block_to_region` assigns the entry (and arms) to an
    // overlapping sibling/ancestor loop region instead. That dual-role
    // ownership is the precise signature of the loop-shadowed dropped-else
    // case: with its blocks owned by the loop, the region gets no byte
    // coverage and the normal walk's arm slicer clips to an empty range
    // list, so only the loop's byte-slice path reaches these bytes, and
    // that path drops the backward-converging else.
    //
    // When the region DOES own its entry, it has real coverage and the
    // normal walk plus the byte-slice claim path emit it correctly, so
    // dispatching here would only re-emit (duplicate) content the
    // surrounding sweep already handles. This keeps the dispatch scoped to
    // the genuine drop (a nested if/else inside a loop body); loops with a
    // properly-carved nested if/else own their blocks and are left on the
    // existing path.
    let region_owns_entry = region_tree.block_to_region.get(&block_id).copied() == Some(target_id);
    if region_owns_entry {
        return None;
    }

    let idom = compute_dominators(cfg);
    let walk = RegionWalkCtx {
        cfg,
        ctx,
        idom: &idom,
    };
    let region = &region_tree.regions[target_id];
    let region_exit = region.exit;
    let (emitted, _continuation) =
        try_emit_ifthenelse_region(region, target_id, walk, Some(region_tree))?;

    // Advance past every byte the dispatched region's arms cover. The
    // region's transitive `block_to_region` byte ranges are unreliable
    // here: when the entry block is shared with a sibling inner-loop
    // region (the dual-role pattern), `block_to_region` assigns the
    // entry and arm blocks to the sibling, leaving this IfThenElse region
    // with empty coverage. Instead, walk the CFG arm successors from each
    // of the entry block's two successors, bounded by the region exit
    // (the loop merge), and take the furthest block end. Clamped to
    // `seg_end` so the loop sweep never swallows bytes outside the
    // completion window.
    let mut advance_end = cfg
        .blocks
        .get(block_id)
        .map(|block| block.end)
        .unwrap_or(pos);
    for arm_ranges in arm_extents_for_region(block_id, region_exit, cfg) {
        for range in arm_ranges {
            if range.start >= pos && range.end <= seg_end && range.end > advance_end {
                advance_end = range.end;
            }
        }
    }
    advance_end = advance_end.min(seg_end);
    if advance_end <= pos {
        // No covered bytes inside the segment to advance past; declining
        // keeps the caller's position monotonic and avoids an infinite
        // loop. The legacy byte-slice path handles this position instead.
        return None;
    }

    Some((emitted, advance_end))
}

/// Compute the disk-byte arm extents for the IfThenElse region headed by
/// `entry_block`. Returns one range list per arm (the two CFG successors
/// of the entry block), each being the union of disk segments reachable
/// from the arm entry without crossing `region_exit`. Returns an empty
/// vec when the entry block doesn't have exactly two successors. Reuses
/// `branch::region_arm_extents`, the same CFG-reachability walk the
/// IfThenElse emitter uses to slice arm bodies.
fn arm_extents_for_region(
    entry_block: BlockId,
    region_exit: BlockId,
    cfg: &ControlFlowGraph,
) -> Vec<Vec<Range<usize>>> {
    let Some(succs) = cfg.successors.get(&entry_block) else {
        return Vec::new();
    };
    if succs.len() != 2 {
        return Vec::new();
    }
    let arm_entries = [Some(succs[0]), Some(succs[1])];
    crate::bytecode::decode::branch::region_arm_extents(&arm_entries, region_exit, cfg)
}

/// Loop-body Loop-region dispatch. The sibling
/// (`try_dispatch_loop_body_region_at`) routes a nested IfThenElse carved
/// UNDER the active loop to the structured emitter. This one handles
/// the nested-ForEach-inside-ForEach shape: the inner loop is carved as a
/// SIBLING of the outer loop (both children
/// of the function root) rather than a descendant, because trampoline
/// displacement put the inner loop's bytes physically AFTER the outer
/// loop's bytes in disk order. During the outer loop's displaced-body
/// decode the sweep reaches the inner loop head; this helper intercepts it
/// and emits the inner as a real `Stmt::Loop` instead of letting the
/// byte-slice path render it as a one-shot `if`.
///
/// Returns `None` (legacy path) when no loop is active, the position isn't
/// a block start, no qualifying inner Loop region exists, or
/// `try_emit_loop_region` declines the inner.
pub(crate) fn try_dispatch_loop_body_loop_region_at(
    pos: usize,
    seg_end: usize,
    ctx: &DecodeCtx,
) -> Option<(Vec<Stmt>, usize)> {
    let active_loop = ctx.loop_completion_region.get()?;
    let cfg = ctx.cfg?;
    let region_tree = ctx.region_tree?;
    let block_id = cfg.block_at_start(pos)?;

    // Find a Loop region whose entry IS this block and which passes the
    // sibling-carving discriminator. The dual-role gate (the region must
    // NOT own its own entry block in `block_to_region`) is folded into the
    // discriminator as condition (5).
    let target = region_tree
        .regions
        .iter()
        .enumerate()
        .find(|(region_id, region)| {
            region.kind == RegionKind::Loop
                && region.entry == block_id
                && *region_id != active_loop
                && loop_body_dispatch_discriminator(*region_id, active_loop, region_tree, cfg, ctx)
        })
        .map(|(region_id, _)| region_id)?;

    let idom = compute_dominators(cfg);
    let walk = RegionWalkCtx {
        cfg,
        ctx,
        idom: &idom,
    };
    let region = &region_tree.regions[target];
    // `try_emit_loop_region` self-installs `with_loop_completion_region(target)`
    // around its own `try_decode_loop`, so the inner loop's body decode gets
    // the inner loop as its completion region.
    //
    // Part (i): the inner loop's JIN skip target (the post-loop landing
    // reached via the trampoline pop) differs from its back-edge resume, so
    // `try_decode_loop`'s strict skip-target gate would reject it. Set
    // `loop_dispatch_relaxed` ONLY around this emit so the gate's narrow
    // flow-pop bypass fires for the inner loop and nothing else.
    let emitted = {
        let _relaxed = ctx.with_loop_dispatch_relaxed();
        try_emit_loop_region(region, target, walk)?
    };

    // Part (ii): record the dispatched region so the later sibling
    // `walk_region(target)` skips it at its top. A `CfgRegion{target}` claim
    // cannot suppress that walk because the walk re-decodes under
    // `decoding_owner = CfgRegion{target}` and self-bypasses its own claim.
    ctx.dispatched_loop_regions.borrow_mut().insert(target);

    // Compute the inner loop's full disk footprint: from its entry block
    // start to the END of the block that its `EX_JUMP_IF_NOT` skip target
    // lands on (the trampoline flow-pop block, e.g. BB18). The inner loop's
    // `try_decode_loop` absorbed its displaced body (a SIBLING region R6 of
    // the inner loop, NOT a descendant, so `loop_transitive_coverage` does
    // not see it) up to that flow-pop. Bounding the claim by the skip
    // target's block end captures R4 + R5 (scaffold) + R6 (displaced body) +
    // the trampoline pop block, so the outer's disk-order re-walk and the
    // sibling walk find nothing left to re-emit.
    let footprint_end =
        inner_loop_footprint_end(target, region_tree, cfg, ctx).unwrap_or_else(|| {
            loop_transitive_coverage(target, region_tree, cfg)
                .iter()
                .map(|range| range.end)
                .max()
                .unwrap_or(pos)
        });

    // Claim the contiguous footprint under `CfgRegion { region_id: target }`
    // so the outer's disk-order re-walk and the outer's own nested-if dedup
    // skip the inner content. advance_end is the footprint end clamped to
    // the segment.
    let entry_start = cfg
        .blocks
        .get(block_id)
        .map(|block| block.start)
        .unwrap_or(pos);
    let claim_start = entry_start.max(pos);
    let claim_end = footprint_end.min(seg_end);
    if claim_end > claim_start {
        super::super::ctx::mark_claimed(
            ctx,
            claim_start,
            claim_end,
            OwnerId::CfgRegion { region_id: target },
        );
    }

    // Part (ii) extension: suppress the sibling walk for EVERY region whose
    // entry block falls inside the inner loop's footprint, not just the
    // dispatched Loop region. The inner loop's displaced body R6 is carved
    // as a sibling of R4 (both children of the function root), so without
    // suppressing R6 the walker re-emits the inner body a second time after
    // `// Completed:`. Record R6 (and any other region inside the
    // footprint) so `walk_region` skips them at its top.
    {
        let mut dispatched = ctx.dispatched_loop_regions.borrow_mut();
        for (sibling_id, sibling_region) in region_tree.regions.iter().enumerate() {
            if sibling_id == target {
                continue;
            }
            let Some(sibling_block) = cfg.blocks.get(sibling_region.entry) else {
                continue;
            };
            if sibling_block.start >= claim_start && sibling_block.start < claim_end {
                dispatched.insert(sibling_id);
            }
        }
    }

    let advance_end = claim_end;
    if advance_end <= pos {
        return None;
    }

    Some((emitted, advance_end))
}

/// Discriminator for `try_dispatch_loop_body_loop_region_at`. True iff the
/// candidate `target` is a genuine nested loop carved as a disk-order
/// sibling of `active_loop`. All five conditions must hold:
/// 1. `target.kind == Loop` and `target != active_loop`.
/// 2. target's entry block ends with `EX_JUMP_IF_NOT` (a real loop head, so
///    `try_emit_loop_region` will accept it; excludes trampoline-scaffold
///    Loop regions whose entry ends with `EX_PUSH_EXECUTION_FLOW`).
/// 3. target has its own back-edge (an `EX_JUMP` inside target's transitive
///    coverage whose disk target lies at or before target's entry start).
/// 4. `target.parent == active_loop.parent` (sibling carving) AND
///    `active_loop` precedes `target` in disk order. This is the
///    sibling-carving signature produced when trampoline displacement puts
///    the inner loop's bytes physically after the outer loop's.
/// 5. target does NOT own its own entry block in `block_to_region` (the
///    dual-role pattern: a trampoline-scaffold sibling owns the entry).
fn loop_body_dispatch_discriminator(
    target: RegionId,
    active_loop: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> bool {
    let target_region = &region_tree.regions[target];
    // (1)
    if target_region.kind != RegionKind::Loop || target == active_loop {
        return false;
    }
    // (2)
    if !region_entry_ends_with_jump_if_not(target_region, cfg, ctx) {
        return false;
    }
    // (3)
    if !loop_has_own_back_edge(target, region_tree, cfg, ctx) {
        return false;
    }
    // (4)
    let active_region = &region_tree.regions[active_loop];
    if target_region.parent != active_region.parent {
        return false;
    }
    let target_start = cfg.blocks.get(target_region.entry).map(|block| block.start);
    let active_start = cfg.blocks.get(active_region.entry).map(|block| block.start);
    match (active_start, target_start) {
        (Some(active), Some(candidate)) if active < candidate => {}
        _ => return false,
    }
    // (5)
    if region_tree
        .block_to_region
        .get(&target_region.entry)
        .copied()
        == Some(target)
    {
        return false;
    }
    true
}

/// True when the region's entry block's terminator opcode is
/// `EX_JUMP_IF_NOT`.
fn region_entry_ends_with_jump_if_not(
    region: &Region,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> bool {
    let Some(entry_block) = cfg.blocks.get(region.entry) else {
        return false;
    };
    let Some(&terminator_addr) = entry_block.opcodes.last() else {
        return false;
    };
    ctx.bytecode.get(terminator_addr).copied() == Some(EX_JUMP_IF_NOT)
}

/// True when `region_id`'s transitive coverage contains an `EX_JUMP` whose
/// disk target lies at or before the region's entry-block start (a
/// back-edge). The inner loop's back-edge can sit in a block owned by a
/// trampoline-scaffold descendant region, so the scan walks the region's
/// full transitive coverage rather than just its entry block.
fn loop_has_own_back_edge(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> bool {
    let Some(entry_start) = cfg
        .blocks
        .get(region_tree.regions[region_id].entry)
        .map(|block| block.start)
    else {
        return false;
    };
    for block_id in loop_transitive_blocks(region_id, region_tree) {
        let Some(block) = cfg.blocks.get(block_id) else {
            continue;
        };
        for &opcode_addr in &block.opcodes {
            if ctx.bytecode.get(opcode_addr).copied() != Some(EX_JUMP) {
                continue;
            }
            let mut cursor = opcode_addr + 1;
            if cursor + 4 > ctx.bytecode.len() {
                continue;
            }
            let target_mem = read_bc_u32(ctx.bytecode, &mut cursor) as usize;
            let target_disk = ctx
                .mem_to_disk
                .and_then(|map| map.get(&target_mem).copied())
                .unwrap_or(target_mem);
            if target_disk <= entry_start {
                return true;
            }
        }
    }
    false
}

/// Collect the set of blocks owned by `region_id` or any of its transitive
/// descendant regions, via `block_to_region`. Used to derive the inner
/// loop's full byte coverage when the region's own `block_to_region`
/// ownership is empty (dual-role: a trampoline scaffold owns the entry).
fn loop_transitive_blocks(region_id: RegionId, region_tree: &RegionTree) -> BTreeSet<BlockId> {
    let mut descendants: BTreeSet<RegionId> = BTreeSet::new();
    let mut stack = vec![region_id];
    while let Some(current) = stack.pop() {
        if !descendants.insert(current) {
            continue;
        }
        for &child in &region_tree.regions[current].children {
            stack.push(child);
        }
    }
    region_tree
        .block_to_region
        .iter()
        .filter(|(_, &owner)| descendants.contains(&owner))
        .map(|(&block_id, _)| block_id)
        .collect()
}

/// The disk-byte end of the inner loop's full footprint. The
/// inner loop's `EX_JUMP_IF_NOT` (its loop-head terminator) skips, when the
/// condition is false, to the trampoline flow-pop block that converges to
/// the loop exit (e.g. BB18 for a nested ForEach). The
/// inner loop's displaced body sits between the back-edge resume and that
/// flow-pop block, carved as a sibling region the loop's transitive
/// coverage does not include. Returning the flow-pop block's END bounds a
/// contiguous claim that covers the whole inner loop including its
/// displaced body, so the outer re-walk and sibling walk skip it.
///
/// Returns `None` when the entry block has no `EX_JUMP_IF_NOT` terminator,
/// the skip target can't be resolved, or no block starts at the skip
/// target; the caller falls back to the transitive-coverage max-end.
fn inner_loop_footprint_end(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Option<usize> {
    let region = &region_tree.regions[region_id];
    let entry_block = cfg.blocks.get(region.entry)?;
    let terminator_addr = *entry_block.opcodes.last()?;
    if ctx.bytecode.get(terminator_addr).copied() != Some(EX_JUMP_IF_NOT) {
        return None;
    }
    let mut cursor = terminator_addr + 1;
    if cursor + 4 > ctx.bytecode.len() {
        return None;
    }
    let skip_target_mem = read_bc_u32(ctx.bytecode, &mut cursor) as usize;
    let skip_target_disk = ctx
        .mem_to_disk
        .and_then(|map| map.get(&skip_target_mem).copied())
        .unwrap_or(skip_target_mem);
    let skip_block = cfg
        .blocks
        .iter()
        .find(|block| block.start == skip_target_disk)?;
    Some(skip_block.end)
}

/// Merged disk-byte ranges covering `region_id` and every transitive
/// descendant region's blocks (adjacent ranges coalesced). The inner loop
/// claims this so the outer's re-walk skips all inner bytes.
fn loop_transitive_coverage(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
) -> Vec<Range<usize>> {
    let mut ranges: Vec<Range<usize>> = loop_transitive_blocks(region_id, region_tree)
        .into_iter()
        .filter_map(|block_id| cfg.blocks.get(block_id))
        .filter(|block| !block.opcodes.is_empty())
        .map(|block| block.start..block.end)
        .collect();
    ranges.sort_by_key(|range| range.start);
    merge_adjacent(ranges)
}

/// Region-driven emitter for `RegionKind::Loop`. Returns a `Vec<Stmt>`
/// containing the entry block's pre-JIN preamble stmts followed by a
/// `Stmt::Loop` produced by `loop_decode::try_decode_loop` on the bytes
/// at the JIN terminator. Returns `None` when the region's entry block
/// doesn't end with `EX_JUMP_IF_NOT` or when `try_decode_loop` declines
/// the bytes (no back-edge, empty body, skip target doesn't match the
/// resume, etc.).
///
/// Delegating the body extraction to `try_decode_loop` reuses the same
/// path the disk pipeline takes: contiguous byte-slice decode between
/// the cond expression and the back-edge `EX_JUMP`, with the ForEach
/// displaced-body absorption (`absorb_displaced_body`) folding the
/// trampoline's PUSH/JUMP/POP layout back into a single body in
/// execution order. The earlier per-block dominance walk diverged on
/// both shapes because (a) CFG block extents (`start..end`) can overlap
/// in disk coordinates when a block leader sits inside another block's
/// fallthrough chain, so converting a dominance-reachable block set to
/// disk byte ranges over-walks past the back-edge, and (b) the
/// displaced body block has the POP-resume as a second predecessor and
/// fails the strict-dominance gate, so a dominance walk under-walks the
/// trampoline-displaced body bytes.
///
/// LoopKind: `try_decode_loop` emits `LoopKind::While` for every
/// recognised loop. ForC / ForEach refinement runs later in
/// `transforms::refine_loops` after temp inlining.
pub(super) fn try_emit_loop_region(
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
) -> Option<Vec<Stmt>> {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    let (entry_block, terminator_addr) =
        region_entry_terminator(region, RegionKind::Loop, EX_JUMP_IF_NOT, cfg, ctx)?;

    // Rotated-trampoline (do-while) ForEach. The trampoline PUSH lives
    // in the pre-header/increment block OUTSIDE the head's true-edge body
    // slice, so `absorb_displaced_body` cannot fold it and the canonical
    // path emits an empty `while` with the body (a DoOnce-wrapped Print)
    // hoisted out as a root-level sibling. Build the loop body explicitly:
    // the head's element-index fetch, the displaced user-body sibling
    // regions, and the increment, as a `While` that `refine_loops` lifts to
    // `ForEach { item in array }`. The discriminator is byte-precise and
    // fires on exactly one fixture function (proven target-only).
    {
        let rotated_range_end = loop_decode_range_end(terminator_addr, ctx);
        if let Some(layout) = super::super::loop_decode::detect_rotated_trampoline(
            ctx,
            cfg,
            terminator_addr,
            rotated_range_end,
        ) {
            if let Some(emitted) = emit_rotated_trampoline_loop(region_id, cfg, ctx, &layout) {
                return Some(emitted);
            }
        }
    }

    // Same break-sentinel + fixed-bound preamble walk the switch path
    // below uses; decode the entry block's pre-terminator opcodes under
    // this region's owner so claims attribute correctly.
    let preamble = {
        let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });
        decode_entry_preamble(entry_block, terminator_addr, entry_block.end, ctx)
    };

    let range_end = loop_decode_range_end(terminator_addr, ctx);
    let mut pos = terminator_addr;
    let loop_stmt = {
        let _completion_guard = ctx.with_loop_completion_region(region_id);
        try_decode_loop(&mut pos, range_end, ctx)?
    };

    let mut out = preamble;
    out.push(loop_stmt);
    Some(out)
}

/// Emit a rotated-trampoline (do-while) ForEach as a `While` loop the
/// `refine_loops` pass lifts to `ForEach { item in array }`.
///
/// The loop body is spliced in execution order from three parts:
/// 1. the head's element-index fetch `[body_start, back_edge)`
///    (`Array_Index = Loop_Counter`),
/// 2. the displaced user body: the loop region's SIBLING regions (the
///    root's children other than the loop), walked in disk order. These
///    carry the DoOnce-wrapped `PrintString` reached via the pre-header
///    trampoline; the canonical path leaves them as a hoisted root-level
///    sibling. Decoding them here and recording them in
///    `dispatched_loop_regions` moves the body INTO the loop and stops the
///    root walk re-emitting it,
/// 3. the increment `[increment_start, head_block_start)`
///    (`Loop_Counter += 1`).
///
/// The loop region's own scaffold child (the pre-header PUSH region) is
/// also marked dispatched so the root walk skips it. Downstream transforms
/// (DoOnce scaffold fold, `refine_loops` ForEach lift + item substitution,
/// CSE) then resolve the array element to `item`.
fn emit_rotated_trampoline_loop(
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
    layout: &super::super::loop_decode::RotatedTrampolineLayout,
) -> Option<Vec<Stmt>> {
    let region_tree = ctx.region_tree?;
    let mut loop_stmt = super::super::loop_decode::rotated_loop_cond(ctx, layout.head_offset)?;

    let head_block_start = cfg
        .blocks
        .iter()
        .find(|block| block.opcodes.last() == Some(&layout.head_offset))
        .map(|block| block.start)?;

    // The displaced user body lives in the loop's sibling regions (root
    // children other than the loop). Walk them in disk-start order so the
    // body content (the DoOnce-wrapped Print) is captured INSIDE the loop.
    let root = region_tree.root;
    let loop_region = &region_tree.regions[region_id];
    let mut sibling_ids: Vec<RegionId> = region_tree.regions[root]
        .children
        .iter()
        .copied()
        .filter(|&sib| sib != region_id)
        .collect();
    sibling_ids.sort_by_key(|&sib| {
        cfg.blocks
            .get(region_tree.regions[sib].entry)
            .map(|block| block.start)
            .unwrap_or(usize::MAX)
    });

    let idom = compute_dominators(cfg);
    let mut user_body: Vec<Stmt> = Vec::new();
    let mut user_consumed: Vec<Range<usize>> = Vec::new();
    let mut user_visited: BTreeSet<BlockId> = BTreeSet::new();
    {
        let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });
        for &sib in &sibling_ids {
            walk_region(
                region_tree,
                sib,
                RegionWalkCtx {
                    cfg,
                    ctx,
                    idom: &idom,
                },
                &mut user_body,
                &mut user_consumed,
                &mut user_visited,
            );
        }
    }

    // Splice the body: element-index fetch, displaced user body, increment.
    let mut body: Vec<Stmt> = decode_subrange(layout.body_start, layout.back_edge_disk, ctx);
    body.append(&mut user_body);
    body.extend(decode_subrange(
        layout.increment_start,
        head_block_start,
        ctx,
    ));

    if let Stmt::Loop { body: slot, .. } = &mut loop_stmt {
        *slot = body;
    }

    // The head block's preamble (`$Less_IntInt = Less_IntInt(counter,
    // Array_Length(array))` and the `Array_Length` fetch) sits before the
    // JIN. Decode it as a sibling preceding the loop so `refine_loops`
    // chain-resolution can recover the canonical `counter < Array_Length`
    // condition and lift the `While` to `ForEach`.
    let preamble = decode_subrange(head_block_start, layout.head_offset, ctx);

    // Suppress the root walk's re-emit of every region now folded into the
    // loop: the dispatched siblings, their descendants, and the loop's own
    // pre-header scaffold child.
    {
        let mut dispatched = ctx.dispatched_loop_regions.borrow_mut();
        for &sib in &sibling_ids {
            mark_subtree_dispatched(region_tree, sib, &mut dispatched);
        }
        for &child in &loop_region.children {
            mark_subtree_dispatched(region_tree, child, &mut dispatched);
        }
    }

    let mut out = preamble;
    out.push(loop_stmt);
    Some(out)
}

/// Upper bound for `try_decode_loop`'s range_end. Matches the bound the
/// region walk passes to `try_decode_loop` (the per-addr `range_end`
/// derivation): the end of the owned address range
/// containing `addr`. For standalone-function decode where `owned_ranges`
/// is `None`, falls back to the full bytecode length so the ForEach
/// trampoline's `scan_for_displaced_terminator` can still reach a final
/// `EX_RETURN` / `EX_END_OF_SCRIPT` at the function epilogue.
fn loop_decode_range_end(addr: usize, ctx: &DecodeCtx) -> usize {
    if let Some(ranges) = ctx.owned_ranges {
        if let Some(range) = ranges.iter().find(|range| range.contains(&addr)) {
            return range.end;
        }
    }
    ctx.bytecode.len()
}

/// True when the entry block contains an `EX_POP_FLOW_IF_NOT` at an
/// address strictly less than `jin_terminator_addr`. Indicates the
/// nested-naked-if shape where the outer gate is a Form B naked-if
/// (`pop_flow_if_not`) and the JIN-Branch is its body. Used by
/// `try_emit_ifthen_region` / `try_emit_ifthenelse_region` to delegate
/// to `try_emit_pop_flow_if_not_branch_region` so the naked-if's body
/// decode absorbs the inner JIN-Branch rather than the outer region
/// emitter emitting its own Branch on top of the naked-if's body.
pub(super) fn has_earlier_pop_flow_if_not(
    entry_block: &BasicBlock,
    jin_terminator_addr: usize,
    ctx: &DecodeCtx,
) -> bool {
    entry_block.opcodes.iter().any(|&addr| {
        addr < jin_terminator_addr && ctx.bytecode.get(addr).copied() == Some(EX_POP_FLOW_IF_NOT)
    })
}

/// Region-driven emitter for `RegionKind::Switch`. Returns a `Vec<Stmt>`
/// containing the entry block's pre-`EX_SWITCH_VALUE` preamble stmts
/// followed by a `Stmt::Switch { expr, cases, default, offset }` decoded
/// from the EX_SWITCH_VALUE instruction. Returns `None` when the entry
/// block's terminator isn't `EX_SWITCH_VALUE` or when the inline
/// `try_decode_switch` fails (malformed index_expr, truncated stream).
///
/// EX_SWITCH_VALUE bytecode layout (see `switch_decode.rs`):
/// ```text
/// EX_SWITCH_VALUE
///   u16 num_cases
///   u32 end_offset
///   <index_expr>
///   for each case: <case_value> u32 next_offset <case_body_expr>
///   <default_expr>
/// ```
/// Each case body is itself a sub-expression, NOT a separate CFG-routed
/// block. The Stmt::Switch shape produced by `try_decode_switch`
/// represents each case as a one-stmt body containing
/// `$switch_result = <case_result_expr>` synthesised from the case
/// sub-expression. The probe relies on this inline decode rather than
/// walking per-case CFG successors because EX_SWITCH_VALUE expression-
/// shape doesn't split the basic block.
///
/// Classifier status (per `cfg/region.rs::classify_region_kind`):
/// RegionKind::Switch fires only when the entry block's terminator is
/// EX_SWITCH_VALUE AND the CFG records >=2 successors at that block.
/// The current CFG builder does not split blocks at EX_SWITCH_VALUE
/// (the opcode is treated as inline), so this emitter is scaffold-only
/// in the present corpus. It is wired into `walk_region` so it activates
/// the moment the classifier starts assigning Switch.
pub(super) fn try_emit_switch_region(
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
) -> Option<Vec<Stmt>> {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    if region.kind != RegionKind::Switch {
        return None;
    }
    let entry_block = cfg.blocks.get(region.entry)?;
    let terminator_addr = *entry_block.opcodes.last()?;
    if *ctx.bytecode.get(terminator_addr)? != EX_SWITCH_VALUE {
        return None;
    }

    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    // Pre-switch preamble: any opcodes inside the entry block before the
    // EX_SWITCH_VALUE terminator. The current corpus places EX_SWITCH_VALUE
    // at block start typically, but the loop here keeps the emitter
    // symmetric with the other kinds for when the classifier evolves.
    let block_end = entry_block.end;
    let preamble = decode_entry_preamble(entry_block, terminator_addr, block_end, ctx);

    // Decode the EX_SWITCH_VALUE itself via the shared decoder. Bounds
    // pos to `block_end` so a malformed stream can't run past the entry
    // block. `try_decode_switch` returns None when the index_expr decodes
    // as Unknown or the stream is truncated; the emitter declines to
    // emit Stmt::Switch in that case so the existing per-opcode walk
    // can fall back to its Unknown statement.
    let mut switch_pos = terminator_addr;
    let switch_stmt = try_decode_switch(&mut switch_pos, block_end, ctx)?;

    let mut out = preamble;
    out.push(switch_stmt);
    Some(out)
}
