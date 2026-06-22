use super::*;

use crate::bytecode::cfg::dom::DomChain;

/// Decode the body of one arm of a branch-like region by collecting
/// every CFG block reachable from `arm_entry` within the parent
/// region's SESE bounds, converting that block set to merged disk
/// byte ranges, and feeding each range through `decode_subrange`.
///
/// Reachability gates on three constraints: strict dominance from
/// `arm_entry` (mirrors the legacy BFS, prevents both arms of a
/// converging IfThenElse from absorbing the shared post-Branch
/// content), boundary blocks (`region.entry`, `region.exit`,
/// `sibling_arm_entry`) which terminate the walk, and the parent
/// region's transitive byte coverage which clips the resulting
/// byte ranges so an arm slice cannot extend into sibling regions
/// via pop_flow resume edges.
///
/// The resulting byte ranges feed `decode_subrange`, the byte-range
/// path used for branch bodies. This
/// gives cross-block recognisers (nested Branch, Loop, IsValid
/// macro) a contiguous stream and keeps them firing consistently.
///
/// Falls back to the dominance-bounded per-block BFS when
/// `region_byte_ranges` is unavailable (synthetic contexts that
/// don't install the per-region byte map).
pub(super) fn decode_arm_body(
    arm_entry: BlockId,
    sibling_arm_entry: Option<BlockId>,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
) -> Vec<Stmt> {
    if arm_entry == region.exit {
        return Vec::new();
    }
    match arm_byte_slice(arm_entry, sibling_arm_entry, region, region_id, walk) {
        Some(segments) => decode_arm_segments(&segments, walk.ctx),
        None => decode_arm_body_via_dominance(arm_entry, region.exit, walk),
    }
}

/// Compute the merged disk byte slice covered by the CFG blocks
/// reachable from `arm_entry` and strictly dominated by `arm_entry`,
/// without crossing `region.exit`, `region.entry`, or
/// `sibling_arm_entry`. Returns `None` when `region_byte_ranges` is
/// unavailable so the caller can fall back to the per-block walk.
pub(super) fn arm_byte_slice(
    arm_entry: BlockId,
    sibling_arm_entry: Option<BlockId>,
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
) -> Option<Vec<Range<usize>>> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    let region_ranges = ctx.region_byte_ranges?.get(&region_id)?;
    let arm_stops = ctx.arm_descent_stops.borrow();
    let reachable = reachable_blocks_in_arm(
        arm_entry,
        sibling_arm_entry,
        region.entry,
        region.exit,
        cfg,
        idom,
        &arm_stops,
    );
    let block_ranges = block_set_to_ranges(&reachable, cfg);
    // Successor-BFS ordering of the same reachable block set, anchored at
    // the arm entry. Used (under the displacement gate in
    // `pick_arm_segment_order`) to restore execution order when a
    // within-event Knot fan-in lays a segment at a lower disk address than
    // the segment that reaches it.
    let bfs_ranges = block_set_to_ranges_bfs_order(&reachable, arm_entry, cfg);
    // Dual-role coverage gap: when the region shares its entry block with
    // an overlapping sibling (e.g. a loop region whose body subsumes this
    // if/else), `block_to_region` assigns every block to the sibling and
    // `build_region_byte_ranges` leaves this region with empty transitive
    // coverage. Clipping against an empty range list would erase the whole
    // arm slice, dropping the arm body. The reachable-block ranges from the
    // CFG arm walk are already SESE-bounded (they stop at the region exit
    // and the sibling arm), so when the region has no recorded coverage we
    // use them directly instead of clipping to nothing.
    let disk_order = if region_ranges.is_empty() {
        block_ranges
    } else {
        clip_to_region_ranges(block_ranges, region_ranges)
    };
    let bfs_order = if region_ranges.is_empty() {
        bfs_ranges
    } else {
        clip_to_region_ranges_ordered(bfs_ranges, region_ranges)
    };
    Some(pick_arm_segment_order(
        arm_entry, disk_order, bfs_order, cfg,
    ))
}

/// Choose between the disk-order and successor-BFS arm-segment orderings.
///
/// The principled order is execution order (successor-BFS from the arm
/// entry), which fixes the displaced post-call re-arm shape: a DoOnce body
/// whose shared `ResetDoOnce` re-arm the Blueprint compiler placed at a
/// lower disk address than the user call it logically follows (a body
/// where the user call must precede the `ResetDoOnce` re-arm laid out
/// below it).
///
/// The reorder is gated to that displacement signal so it cannot disturb
/// the single-entry-single-exit-bounded body decode, content folding, and
/// common-subexpression elimination that depend on contiguous disk-ordered
/// subranges:
/// - **Pure permutation**: the BFS order must cover exactly the same
///   segment starts as the disk order (same segment set, no
///   merge-granularity change). Disk-order `merge_adjacent` collapses
///   disk-adjacent reachable blocks into wide ranges; the BFS order can
///   surface them as separate segments, which changes `decode_subrange`
///   boundaries. Requiring a pure permutation excludes every such case.
/// - **Backward displacement**: at least one segment must start below the
///   arm entry's disk address (the within-event Knot fan-in signal). A
///   forward-only arm already has disk order == execution order.
fn pick_arm_segment_order(
    arm_entry: BlockId,
    disk_order: Vec<Range<usize>>,
    bfs_order: Vec<Range<usize>>,
    cfg: &ControlFlowGraph,
) -> Vec<Range<usize>> {
    let disk_starts: BTreeSet<usize> = disk_order.iter().map(|range| range.start).collect();
    let bfs_starts: BTreeSet<usize> = bfs_order.iter().map(|range| range.start).collect();
    let pure_permutation = disk_order.len() == bfs_order.len() && disk_starts == bfs_starts;
    let arm_entry_start = cfg
        .blocks
        .get(arm_entry)
        .map(|block| block.start)
        .unwrap_or(0);
    let has_backward_displacement = bfs_order.iter().any(|range| range.start < arm_entry_start);
    if pure_permutation && has_backward_displacement && disk_order != bfs_order {
        bfs_order
    } else {
        disk_order
    }
}

/// Forward BFS from `arm_entry`. Successor expansion stops at any
/// boundary block (`region_entry`, `region_exit`, `sibling_arm_entry`,
/// or any block in `extra_stops`) and at any block not strictly
/// dominated by `arm_entry`. The dominance gate prevents IfThenElse arms
/// that share a post-Branch convergence from each absorbing the
/// convergence's content; the boundary checks prevent pop_flow resume
/// edges from pulling unrelated regions into the arm slice.
///
/// `extra_stops` carries the boundary-aware descent's sibling-pin entry
/// set (empty in every other caller and whenever the descent flag is
/// off). The arm entry itself is exempt from `extra_stops` so a
/// dispatched region whose arm root coincides with a sibling-pin entry
/// still decodes its own first block; only successors are clipped.
pub(super) fn reachable_blocks_in_arm(
    arm_entry: BlockId,
    sibling_arm_entry: Option<BlockId>,
    region_entry: BlockId,
    region_exit: BlockId,
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    extra_stops: &BTreeSet<BlockId>,
) -> BTreeSet<BlockId> {
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    let is_boundary = |block_id: BlockId| -> bool {
        block_id == region_exit
            || block_id == region_entry
            || sibling_arm_entry == Some(block_id)
            || (block_id != arm_entry && extra_stops.contains(&block_id))
    };
    if is_boundary(arm_entry) {
        return visited;
    }
    queue.push_back(arm_entry);
    while let Some(block_id) = queue.pop_front() {
        if !visited.insert(block_id) {
            continue;
        }
        let Some(succs) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &succ in succs {
            if is_boundary(succ) || visited.contains(&succ) {
                continue;
            }
            if succ != arm_entry && !is_strictly_dominated_by(succ, arm_entry, idom) {
                continue;
            }
            queue.push_back(succ);
        }
    }
    visited
}

/// Convert a set of block ids to a sorted, merged list of their disk
/// byte ranges. Empty blocks (synthetic sink, placeholders) are
/// skipped.
fn block_set_to_ranges(blocks: &BTreeSet<BlockId>, cfg: &ControlFlowGraph) -> Vec<Range<usize>> {
    let mut ranges: Vec<Range<usize>> = blocks
        .iter()
        .filter_map(|&block_id| cfg.blocks.get(block_id))
        .filter(|block| !block.opcodes.is_empty() && block.end > block.start)
        .map(|block| block.start..block.end)
        .collect();
    ranges.sort_by_key(|range| range.start);
    merge_adjacent(ranges)
}

/// Coalesce sorted ranges. With `ordered = false` any range starting at or
/// before the previous range's end merges (overlap/adjacency). With
/// `ordered = true` the range must ALSO start at or after the previous
/// range's start, so a backward-placed segment in an execution-order list
/// stays separate from its disk-neighbour.
pub(super) fn merge_ranges(ranges: Vec<Range<usize>>, ordered: bool) -> Vec<Range<usize>> {
    let mut merged: Vec<Range<usize>> = Vec::with_capacity(ranges.len());
    for range in ranges {
        match merged.last_mut() {
            Some(prev) if range.start <= prev.end && (!ordered || range.start >= prev.start) => {
                if range.end > prev.end {
                    prev.end = range.end;
                }
            }
            _ => merged.push(range),
        }
    }
    merged
}

/// Disk-order coalesce: merge overlapping or adjacent sorted ranges.
pub(super) fn merge_adjacent(ranges: Vec<Range<usize>>) -> Vec<Range<usize>> {
    merge_ranges(ranges, false)
}

/// Convert a set of block ids to their disk byte ranges ordered by a
/// successor-BFS from `arm_entry` (execution order) instead of disk
/// start. Each block is visited at most once; successors are expanded
/// only into blocks that are members of `blocks` (the arm's reachable
/// set), so the walk stays inside the arm. Blocks the BFS never reaches
/// (irreducible / back-edge residue) are appended in disk-start order at
/// the tail, mirroring `reorder_items_by_successor_bfs`. Disk-adjacent
/// ranges are merged only when they are also consecutive in the BFS
/// order, so a backward-fan-in segment placed at a lower disk address
/// keeps its execution-order position rather than merging into a
/// disk-neighbour. Empty blocks are skipped.
fn block_set_to_ranges_bfs_order(
    blocks: &BTreeSet<BlockId>,
    arm_entry: BlockId,
    cfg: &ControlFlowGraph,
) -> Vec<Range<usize>> {
    let range_of = |block_id: BlockId| -> Option<Range<usize>> {
        let block = cfg.blocks.get(block_id)?;
        if block.opcodes.is_empty() || block.end <= block.start {
            return None;
        }
        Some(block.start..block.end)
    };

    let mut ordered: Vec<Range<usize>> = Vec::with_capacity(blocks.len());
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    if blocks.contains(&arm_entry) {
        queue.push_back(arm_entry);
        visited.insert(arm_entry);
    }
    while let Some(block_id) = queue.pop_front() {
        if let Some(range) = range_of(block_id) {
            ordered.push(range);
        }
        if let Some(successors) = cfg.successors.get(&block_id) {
            for &succ in successors {
                if blocks.contains(&succ) && visited.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
    }
    // Append BFS-unreachable members in disk-start order.
    let mut residue: Vec<Range<usize>> = blocks
        .iter()
        .filter(|&&block_id| !visited.contains(&block_id))
        .filter_map(|&block_id| range_of(block_id))
        .collect();
    residue.sort_by_key(|range| range.start);
    ordered.extend(residue);

    // Merge only ranges that are consecutive in this order AND disk-adjacent,
    // so contiguous execution-order runs decode as one subrange while a
    // displaced segment stays separate.
    merge_ranges(ordered, true)
}

/// Clip an ordered list of arm byte ranges against the parent region's
/// transitive ranges, preserving the input order (execution order) rather
/// than re-sorting by disk start the way `clip_to_region_ranges` does.
/// Used by the successor-BFS arm-ordering path so the clip step cannot
/// shuffle a displaced backward-fan-in segment back into disk order.
fn clip_to_region_ranges_ordered(
    arm_ranges: Vec<Range<usize>>,
    region_ranges: &[Range<usize>],
) -> Vec<Range<usize>> {
    let mut clipped: Vec<Range<usize>> = Vec::new();
    for arm_range in arm_ranges {
        // Region ranges are disk-sorted; collect the overlapping fragments
        // for this arm range in disk order, then append them so the arm's
        // execution-order position is preserved across the clip.
        let mut fragments: Vec<Range<usize>> = Vec::new();
        for region_range in region_ranges {
            let lower = arm_range.start.max(region_range.start);
            let upper = arm_range.end.min(region_range.end);
            if lower < upper {
                fragments.push(lower..upper);
            }
        }
        fragments.sort_by_key(|range| range.start);
        clipped.extend(fragments);
    }
    // Merge only consecutive-in-order disk-adjacent fragments.
    merge_ranges(clipped, true)
}

/// Clip the arm's reachable byte ranges against the parent region's
/// transitive ranges so the arm slice cannot extend outside the
/// region's coverage. Each clipped segment is returned in disk order.
fn clip_to_region_ranges(
    arm_ranges: Vec<Range<usize>>,
    region_ranges: &[Range<usize>],
) -> Vec<Range<usize>> {
    let mut clipped: Vec<Range<usize>> = Vec::new();
    for arm_range in arm_ranges {
        for region_range in region_ranges {
            let lower = arm_range.start.max(region_range.start);
            let upper = arm_range.end.min(region_range.end);
            if lower < upper {
                clipped.push(lower..upper);
            }
        }
    }
    clipped.sort_by_key(|range| range.start);
    merge_adjacent(clipped)
}

/// Decode each segment of an arm's byte slice via `decode_subrange`,
/// concatenating the results. The owner-tagged `OwnerId::CfgRegion`
/// guard installed by the caller lets `decode_subrange` bypass claims
/// whose byte spans are fully contained in this region.
pub(super) fn decode_arm_segments(segments: &[Range<usize>], ctx: &DecodeCtx) -> Vec<Stmt> {
    let mut stmts: Vec<Stmt> = Vec::new();
    // Track the segments decoded so far in this arm. The disjoint-range
    // inline path consults `arm_covered_segments` so a later segment's
    // `EX_JUMP` doesn't re-pull a body an earlier segment already covered
    // directly. Seeded empty and grown segment-by-segment so a
    // segment's own jump can't see itself as prior coverage.
    let mut covered: Vec<Range<usize>> = Vec::new();
    for segment in segments {
        let _guard = ctx.with_arm_covered_segments(covered.clone());
        let mut decoded = decode_subrange(segment.start, segment.end, ctx);
        stmts.append(&mut decoded);
        covered.push(segment.clone());
    }
    stmts
}

/// Like `decode_arm_segments`, but suppresses any top-level statement
/// whose start offset lies in `exclude`. Used to stop a sibling arm from
/// re-emitting statements the first-decoded arm already pulled from a
/// physically-displaced segment (see the rebalance path in
/// `decode_ifthenelse_arms`). An empty `exclude` set is identical to
/// `decode_arm_segments`.
pub(super) fn decode_arm_segments_excluding(
    segments: &[Range<usize>],
    ctx: &DecodeCtx,
    exclude: &[Range<usize>],
) -> Vec<Stmt> {
    if exclude.is_empty() {
        return decode_arm_segments(segments, ctx);
    }
    let mut stmts: Vec<Stmt> = Vec::new();
    for segment in segments {
        let mut decoded = decode_subrange_excluding(segment.start, segment.end, ctx, exclude);
        stmts.append(&mut decoded);
    }
    stmts
}

/// Collect the disk offsets of every statement (recursively) emitted by
/// an arm into single-byte exclude ranges `[off..off+1]`. The opcode
/// re-decode gates check the opcode start address, so a single-byte mark
/// is sufficient to suppress re-emission.
pub(super) fn stmt_offset_exclude_set(stmts: &[Stmt]) -> Vec<Range<usize>> {
    let mut offsets: Vec<usize> = Vec::new();
    for stmt in stmts {
        collect_stmt_offsets(stmt, &mut offsets);
    }
    offsets.into_iter().map(|off| off..off + 1).collect()
}

/// Fallback arm decode for synthetic contexts that lack
/// `region_byte_ranges` (unit tests building a CFG by hand). Mirrors
/// the dominance-bounded BFS the previous implementation used.
fn decode_arm_body_via_dominance(
    arm_entry: BlockId,
    region_exit: BlockId,
    walk: RegionWalkCtx,
) -> Vec<Stmt> {
    let RegionWalkCtx { cfg, ctx, idom } = walk;
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut consumed: Vec<Range<usize>> = Vec::new();
    let mut visited_blocks: BTreeSet<BlockId> = BTreeSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    // Sibling-pin boundary set from the boundary-aware descent. Empty in
    // the synthetic contexts that reach this fallback and whenever the
    // descent flag is off, so successor expansion is unchanged there.
    let arm_stops = ctx.arm_descent_stops.borrow();
    if arm_entry == region_exit {
        return stmts;
    }
    queue.push_back(arm_entry);
    while let Some(block_id) = queue.pop_front() {
        if block_id == region_exit {
            continue;
        }
        if !visited_blocks.insert(block_id) {
            continue;
        }
        decode_block_opcodes(cfg, block_id, ctx, &mut stmts, &mut consumed, &[]);
        let Some(succs) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &succ in succs {
            if succ == region_exit {
                continue;
            }
            if succ != arm_entry && arm_stops.contains(&succ) {
                continue;
            }
            if visited_blocks.contains(&succ) {
                continue;
            }
            if !is_strictly_dominated_by(succ, arm_entry, idom) {
                continue;
            }
            queue.push_back(succ);
        }
    }
    stmts
}

/// True iff `block` is strictly dominated by `dominator`. Walks `block`'s
/// idom chain; if `dominator` appears before reaching the entry root,
/// `block` is dominated by it. `block == dominator` returns false
/// (strict). The arm-entry itself is always its own first BFS visit, so
/// the strictness exclusion does not skip it; it skips successors that
/// merely happen to equal the arm entry, which is the desired behaviour.
pub(super) fn is_strictly_dominated_by(
    block: BlockId,
    dominator: BlockId,
    idom: &BTreeMap<BlockId, BlockId>,
) -> bool {
    if block == dominator {
        return false;
    }
    DomChain(idom)
        .ancestors(block)
        .any(|parent| parent == dominator)
}

/// Decode the opcodes of one basic block, skipping addresses inside a
/// `consumed` span or claim-protected. Lighter sibling of
/// `decode_region_block_if_unclaimed` for use inside arm-body walks where the
/// `visited_blocks` set is owned by the arm's BFS and shouldn't leak
/// across arms.
pub(super) fn decode_block_opcodes(
    cfg: &ControlFlowGraph,
    block_id: BlockId,
    ctx: &DecodeCtx,
    stmts: &mut Vec<Stmt>,
    consumed: &mut Vec<Range<usize>>,
    enclosing_ranges: &[Range<usize>],
) {
    let block = match cfg.blocks.get(block_id) {
        Some(block) => block,
        None => return,
    };
    if block.opcodes.is_empty() {
        return;
    }
    for &opcode_addr in &block.opcodes {
        if address_in_consumed(consumed, opcode_addr) {
            continue;
        }
        if claimed_end_for_disk_sweep(ctx, opcode_addr).is_some() {
            continue;
        }
        if opcode_addr >= ctx.bytecode.len() {
            continue;
        }
        let range_end = enclosing_range_end(enclosing_ranges, opcode_addr).unwrap_or(block.end);
        let mut pos = opcode_addr;
        let before = pos;
        match decode_one_or_branch(&mut pos, range_end, ctx) {
            Ok(Some(stmt)) => {
                consumed.extend(extra_consumed_ranges(&stmt, before, pos));
                stmts.push(stmt);
                if pos > before {
                    consumed.push(before..pos);
                }
            }
            Ok(None) => {
                if pos > before {
                    consumed.push(before..pos);
                }
            }
            Err(unknown) => {
                stmts.push(*unknown);
                if pos > before {
                    consumed.push(before..pos);
                }
            }
        }
    }
}

/// Find the `end` of the enclosing byte range that contains `addr`.
/// Used by per-block opcode walks to widen `range_end` from the single
/// basic block to the full pin / arm coverage so multi-block constructs
/// (Branch then-bodies that span block boundaries) classify their jump
/// targets `InRange` rather than `OutOfRange`. Returns `None` when no
/// range contains the address.
fn enclosing_range_end(ranges: &[Range<usize>], addr: usize) -> Option<usize> {
    ranges
        .iter()
        .find(|range| range.contains(&addr))
        .map(|range| range.end)
}
