use super::*;

/// Which per-kind emitter produced a region's statements. Only the
/// disk-order walk (`walk_region`) acts on this: SequenceChain pin bodies
/// can land in an ancestor region, so it records every emitted offset into
/// the shared consumed set. The other callers ignore the kind.
pub(super) enum MatchedEmitter {
    IfThenElse,
    IfThen,
    DoOnce,
    SequenceChain,
    Loop,
    Switch,
}

/// Run the per-kind region emitters in priority order and return the
/// emitted statements, the optional pulled IfThenElse merge continuation,
/// and which emitter fired. The cascade ORDER is load-bearing and lives
/// here as the single source shared by `walk_region`,
/// `dispatch_child_region_at`, and `emit_continuation_region`.
///
/// `try_ifthenelse` is false only for the dual-role IsValid defer case
/// (`walk_region`), where the outer IfThenElse emit is skipped so the
/// disk-order walk reaches the inner sibling sharing its entry block.
#[allow(clippy::too_many_arguments)]
pub(super) fn dispatch_region_emitters(
    region: &Region,
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
    idom: &BTreeMap<BlockId, BlockId>,
    try_ifthenelse: bool,
) -> Option<(Vec<Stmt>, Option<RegionId>, MatchedEmitter)> {
    if try_ifthenelse {
        if let Some((emitted, continuation)) =
            try_emit_ifthenelse_region(region, region_id, cfg, ctx, idom, Some(region_tree))
        {
            return Some((emitted, continuation, MatchedEmitter::IfThenElse));
        }
    }
    if let Some(emitted) =
        try_emit_ifthen_region(region, region_id, cfg, ctx, idom, Some(region_tree))
    {
        return Some((emitted, None, MatchedEmitter::IfThen));
    }
    if let Some(emitted) = try_emit_doonce_region(region, region_id, cfg, ctx, idom) {
        return Some((emitted, None, MatchedEmitter::DoOnce));
    }
    if let Some(emitted) =
        try_emit_sequencechain_region(region, region_id, cfg, ctx, idom, region_tree)
    {
        return Some((emitted, None, MatchedEmitter::SequenceChain));
    }
    if let Some(emitted) = try_emit_loop_region(region, region_id, cfg, ctx, idom) {
        return Some((emitted, None, MatchedEmitter::Loop));
    }
    if let Some(emitted) = try_emit_switch_region(region, region_id, cfg, ctx, idom) {
        return Some((emitted, None, MatchedEmitter::Switch));
    }
    None
}

/// Decode a pin's body via linear sweep over its partition segments
/// (mirrors `try_decode_sequence`'s `decode_subrange` path). Used as
/// fallback when the pin entry address doesn't align with a CFG block
/// leader: `EX_JUMP` targets with a single predecessor aren't promoted
/// to leaders, so a pin body reached via JUMP from a sibling chains into
/// the previous block as a fallthrough and `block_at_start` returns None.
/// The skeleton's `pin_partitions` already carry the correct per-pin byte
/// ranges from `partition_seeds_with_stack`, so decoding them directly
/// recovers the pin's content.
pub(super) fn decode_pin_body_via_partition(
    segments: &[Range<usize>],
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    let mut stmts: Vec<Stmt> = Vec::new();
    for segment in segments {
        let mut decoded = super::super::branch::decode_subrange(segment.start, segment.end, ctx);
        stmts.append(&mut decoded);
    }
    stmts
}

/// Walk every block reachable from `pin_entry` under strict dominance,
/// stopping at `region_exit` or any block in `other_pin_entries`. Mirrors
/// `decode_arm_body`'s gating logic, with the exclusion set repurposed
/// from a single region-exit block to the union of sibling pins.
///
/// Nested-region descent: when a block reached by the BFS is the entry of
/// a child region of `parent_region_id` (per `region_tree`), the body
/// dispatches to the per-kind emitter (`try_emit_*`) for that child
/// instead of feeding raw opcodes through `decode_block_opcodes`. This
/// mirrors the SESE-bounded body decode used by IfThenElse / IfThen /
/// DoOnceGate / Loop. After the child region's stmts are appended, every
/// block transitively inside that region is marked visited and the BFS
/// continues from the region's exit so post-region content in this pin
/// still gets walked.
pub(super) fn decode_pin_body(
    pin_entry: BlockId,
    region_exit: BlockId,
    other_pin_entries: &BTreeSet<BlockId>,
    walk: RegionWalkCtx,
    region_tree: &RegionTree,
    parent_region_id: RegionId,
    pin_segments: &[Range<usize>],
) -> Vec<Stmt> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut consumed: Vec<Range<usize>> = Vec::new();
    let mut visited_blocks: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    if pin_entry == region_exit || other_pin_entries.contains(&pin_entry) {
        return stmts;
    }
    queue.push_back(pin_entry);
    while let Some(block_id) = queue.pop_front() {
        if block_id == region_exit || other_pin_entries.contains(&block_id) {
            continue;
        }
        if !visited_blocks.insert(block_id) {
            continue;
        }

        // If this block is the entry of a nested child region of the
        // parent SequenceChain, render that region via its per-kind
        // emitter instead of feeding raw opcodes through
        // decode_block_opcodes.
        if let Some((emitted, consumed_ids)) = dispatch_child_region_at(
            block_id,
            parent_region_id,
            region_tree,
            cfg,
            ctx,
            idom,
            other_pin_entries,
        ) {
            stmts.extend(emitted);
            for &cid in &consumed_ids {
                mark_region_consumed(region_tree, cid, cfg, &mut consumed, &mut visited_blocks);
            }
            // The walked child is the first id; subsequent ids in the
            // list are merge-continuation regions absorbed into the
            // child's then-arm. The post-region BFS
            // resumption should follow the LAST consumed region's exit,
            // not the child's, because the continuation extends further
            // along the parent's flow.
            if let Some(&last_consumed_id) = consumed_ids.last() {
                let resume_exit = region_tree.regions[last_consumed_id].exit;
                if resume_exit != region_exit
                    && !other_pin_entries.contains(&resume_exit)
                    && !visited_blocks.contains(&resume_exit)
                    && is_strictly_dominated_by(resume_exit, pin_entry, idom)
                {
                    queue.push_back(resume_exit);
                }
            }
            continue;
        }

        decode_block_opcodes(cfg, block_id, ctx, &mut stmts, &mut consumed, pin_segments);
        let Some(succs) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &succ in succs {
            if succ == region_exit || other_pin_entries.contains(&succ) {
                continue;
            }
            if visited_blocks.contains(&succ) {
                continue;
            }
            if !is_strictly_dominated_by(succ, pin_entry, idom) {
                continue;
            }
            queue.push_back(succ);
        }
    }

    // Recover any pin-partition segment the dominance-BFS never reached.
    // A gate-set scaffold block reached via a gate JIN is part of the pin's
    // partition but isn't strictly dominated by `pin_entry`, so the
    // successor filter above skips it. The legacy byte-slice path sweeps the
    // partition directly; mirror that by decoding any partition sub-range the
    // `consumed` set didn't touch (an else-pin second gate-set assign that the
    // dominance-BFS misses on some versions while others dominate both segments).
    //
    // Redundant nested-Sequence recovery: an uncovered
    // segment can itself be a nested Sequence chain-head scaffold whose pin
    // body lives back inside a segment the dominance-BFS already decoded. An
    // explicit Sequence node with a within-event fan-in through a Knot
    // produces exactly this: the recovered segment
    // decodes to a single `Stmt::Sequence` whose pin statements re-pull a
    // `ResetDoOnce` the BFS already emitted, duplicating it. Genuine
    // gate-set recoveries decode to a Branch / assign at offsets the BFS never
    // emitted (a recovered FlipFlop Branch, a gate-set assign),
    // so the redundancy predicate leaves them untouched.
    let bfs_offsets: BTreeSet<usize> = stmt_offset_exclude_set(&stmts)
        .iter()
        .map(|range| range.start)
        .collect();
    for uncovered in uncovered_partition_subranges(pin_segments, &consumed) {
        let current = decode_pin_body_via_partition(std::slice::from_ref(&uncovered), ctx);
        if recovered_is_redundant_nested_sequence(&current, &bfs_offsets) {
            continue;
        }
        stmts.extend(current);
    }
    stmts
}

/// True when `recovered` is a single top-level `Stmt::Sequence` whose every
/// non-structural (pin-body) statement offset was already emitted by the
/// dominance-BFS (`bfs_offsets`). This is the redundant re-decode shape: the
/// recovered segment is a nested Sequence chain-head scaffold whose pin body
/// lives back inside an already-decoded segment, so re-emitting it duplicates
/// those statements. A genuine recovery (a Branch, an assign, or a Sequence
/// carrying at least one not-yet-emitted statement) returns `false`.
fn recovered_is_redundant_nested_sequence(
    recovered: &[Stmt],
    bfs_offsets: &BTreeSet<usize>,
) -> bool {
    let [Stmt::Sequence { pins, .. }] = recovered else {
        return false;
    };
    let mut pin_offsets: Vec<usize> = Vec::new();
    for pin in pins {
        for stmt in pin {
            collect_stmt_offsets(stmt, &mut pin_offsets);
        }
    }
    // Empty pins would make this vacuously true; require at least one
    // re-pulled statement so we only drop genuinely-duplicating recoveries.
    !pin_offsets.is_empty() && pin_offsets.iter().all(|off| bfs_offsets.contains(off))
}

/// Sub-ranges of `segments` not covered by any range in `consumed`, in
/// ascending order. Used by `decode_pin_body` to recover partition segments
/// the dominance-BFS skipped. Splits a segment around interior consumed spans
/// so only the genuinely-undecoded gaps are returned.
fn uncovered_partition_subranges(
    segments: &[Range<usize>],
    consumed: &[Range<usize>],
) -> Vec<Range<usize>> {
    let mut uncovered: Vec<Range<usize>> = Vec::new();
    for segment in segments {
        let mut cursor = segment.start;
        // Consumed spans overlapping this segment, ordered by start.
        let mut overlaps: Vec<&Range<usize>> = consumed
            .iter()
            .filter(|span| span.start < segment.end && span.end > segment.start)
            .collect();
        overlaps.sort_by_key(|span| span.start);
        for span in overlaps {
            if span.start > cursor {
                uncovered.push(cursor..span.start.min(segment.end));
            }
            cursor = cursor.max(span.end);
            if cursor >= segment.end {
                break;
            }
        }
        if cursor < segment.end {
            uncovered.push(cursor..segment.end);
        }
    }
    uncovered
}

/// Try to render a nested descendant region whose entry block is
/// `block_id` (relative to `parent_region_id`). Resolves the OUTERMOST
/// descendant region whose entry equals `block_id` (via
/// `find_outermost_descendant_region_at`), then dispatches to the
/// per-kind emitter in the same priority order as `walk_region`. Returns
/// `None` when:
/// - the block isn't inside a descendant of `parent_region_id`,
/// - the resolved region's entry is some other block (we're not at its
///   entry yet, BFS will reach it later),
/// - no emitter recognised the region's shape.
///
/// `other_pin_entries` is the parent SequenceChain pin walk's
/// sibling-pin entry set. It is installed as the dispatched region's
/// arm-descent stop-set so its arm slicer cannot over-walk into a
/// sibling pin and cause duplicate emission.
pub(super) fn dispatch_child_region_at(
    block_id: BlockId,
    parent_region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
    idom: &BTreeMap<BlockId, BlockId>,
    other_pin_entries: &BTreeSet<BlockId>,
) -> Option<(Vec<Stmt>, Vec<RegionId>)> {
    let child_id = find_outermost_descendant_region_at(block_id, parent_region_id, region_tree)?;
    let child = &region_tree.regions[child_id];
    if child.entry != block_id {
        return None;
    }
    // Hold the sibling-pin boundary set live for the dispatched region's
    // arm decode, so its arm slicer cannot over-walk into a sibling pin.
    let _stops_guard = ctx.with_arm_descent_stops(other_pin_entries.clone());
    let (emitted, continuation, _matched) =
        dispatch_region_emitters(child, child_id, region_tree, cfg, ctx, idom, true)?;
    let mut consumed_ids = vec![child_id];
    if let Some(cont_id) = continuation {
        consumed_ids.push(cont_id);
    }
    Some((emitted, consumed_ids))
}

/// Resolve the wrapper region a SequenceChain pin should enter at when its
/// first partition segment lands INTERIOR to that wrapper, with the
/// wrapper's scaffold (its branch JIN) sitting in disk order ABOVE the
/// pin's body, the body-before-scaffold case.
///
/// The pin's lowest-disk segment block (`seg_block`) is owned by an
/// innermost region (`block_to_region[seg_block]`). When that innermost
/// region does NOT cover the whole pin (its byte coverage misses some of
/// the pin's segments), the pin body is a strict subset that precedes the
/// scaffold. The fix climbs to the nearest STRICT ANCESTOR `IfThenElse`
/// region whose transitive byte coverage contains every one of the pin's
/// segments and whose entry is upstream of `seg_block`; that ancestor is
/// the wrapper whose guard and else-arm would otherwise be dropped.
///
/// Returns `None` (no climb, byte-identical to the pre-fix path) when:
/// - `region_byte_ranges` is unavailable (synthetic test contexts),
/// - the innermost region already covers the whole pin (the pin enters at
///   the right place; not a body-before-scaffold shape),
/// - no strict-ancestor `IfThenElse` (up to but excluding
///   `parent_region_id`) covers all the pin's segments.
///
/// Restricting to `IfThenElse` ancestors with a non-covering innermost
/// region isolates the dropped IsValid guard, the only shape on the
/// current corpus where a SequenceChain pin body precedes its branch
/// scaffold. SequenceChain / DoOnceGate ancestors and the
/// already-covering interior shape are handled by the existing dispatch
/// and are deliberately left untouched.
pub(super) fn climb_to_wrapper_region_for_pin(
    seg_block: BlockId,
    parent_region_id: RegionId,
    pin_segments: &[Range<usize>],
    region_tree: &RegionTree,
    ctx: &DecodeCtx,
) -> Option<RegionId> {
    let region_byte_ranges = ctx.region_byte_ranges?;
    let &innermost = region_tree.block_to_region.get(&seg_block)?;

    let covers_all = |region_id: RegionId| -> bool {
        region_byte_ranges
            .get(&region_id)
            .map(|ranges| {
                pin_segments
                    .iter()
                    .all(|segment| byte_range_contains(ranges, segment))
            })
            .unwrap_or(false)
    };

    // Body-before-scaffold requires the innermost region to MISS part of
    // the pin. When it already covers the whole pin, the pin enters at the
    // correct block and the existing path is correct.
    if covers_all(innermost) {
        return None;
    }

    // Climb strict ancestors, stopping before the parent SequenceChain, and
    // return the nearest IfThenElse whose coverage contains the pin and
    // whose entry is upstream of the segment block.
    let mut cursor = region_tree.regions[innermost].parent;
    while let Some(region_id) = cursor {
        if region_id == parent_region_id {
            break;
        }
        let region = &region_tree.regions[region_id];
        if region.kind == RegionKind::IfThenElse
            && region.entry != seg_block
            && covers_all(region_id)
        {
            return Some(region_id);
        }
        cursor = region.parent;
    }
    None
}

/// True when `segment` is fully contained within one of the merged byte
/// `ranges` (each a half-open `start..end`). `ranges` come from
/// `build_region_byte_ranges`, which merges adjacent block extents.
fn byte_range_contains(ranges: &[Range<usize>], segment: &Range<usize>) -> bool {
    ranges
        .iter()
        .any(|range| range.start <= segment.start && segment.end <= range.end)
}

/// True when `block_id` is owned by `region_id` or one of its descendant
/// regions per `block_to_region`. Used by the SequenceChain pin walk to
/// decide whether the dominance-bounded BFS is safe, or whether the pin
/// entry lives in a sibling/ancestor region and partition-based decode
/// should be used instead.
pub(super) fn block_in_region_subtree(
    block_id: BlockId,
    region_id: RegionId,
    region_tree: &RegionTree,
) -> bool {
    let Some(&innermost) = region_tree.block_to_region.get(&block_id) else {
        return false;
    };
    let mut cursor = innermost;
    loop {
        if cursor == region_id {
            return true;
        }
        match region_tree.regions[cursor].parent {
            Some(parent) => cursor = parent,
            None => return false,
        }
    }
}

/// Boundary-aware descent resolver. Walks up the region tree from
/// `block_id`'s innermost region toward `parent_region_id`, returning the
/// OUTERMOST descendant region (closest to `parent_region_id`) whose
/// `entry == block_id`. Returns `None` when no such region exists in the
/// parent's subtree.
///
/// Resolving only the immediate child of the parent would decline a
/// grandchild whose entry block is the BFS cursor (e.g. a parent
/// region's pin walk reaches B9, which heads region 4 nested
/// under region 2; the immediate child is region 2, entry B3 != B9, so
/// dispatch would decline and B9 fall to the raw opcode sweep). Promoting
/// the outermost matching descendant lets the structured emitter handle
/// that grandchild instead.
fn find_outermost_descendant_region_at(
    block_id: BlockId,
    parent_region_id: RegionId,
    region_tree: &RegionTree,
) -> Option<RegionId> {
    let mut current = *region_tree.block_to_region.get(&block_id)?;
    if current == parent_region_id {
        return None;
    }
    let mut outermost: Option<RegionId> = None;
    loop {
        if region_tree.regions[current].entry == block_id {
            outermost = Some(current);
        }
        match region_tree.regions[current].parent {
            Some(parent) if parent == parent_region_id => return outermost,
            Some(parent) => current = parent,
            None => return None,
        }
    }
}
