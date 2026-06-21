use super::*;

/// JIN (`EX_JUMP_IF_NOT`) operand layout is `[opcode][4-byte target][cond
/// expr]`. Decode the condition expression that follows the 4-byte jump
/// target of the terminator at `terminator_addr`. Returns `None` when the
/// cond start would run past the end of the bytecode.
pub(super) fn decode_jin_cond(terminator_addr: usize, ctx: &DecodeCtx) -> Option<Expr> {
    const JIN_TARGET_BYTES: usize = 4;
    let cond_pos_start = terminator_addr.checked_add(1 + JIN_TARGET_BYTES)?;
    if cond_pos_start > ctx.bytecode.len() {
        return None;
    }
    let mut cond_pos = cond_pos_start;
    Some(decode_expr(&mut cond_pos, ctx))
}

/// True when `region_id` is `ancestor_id` or one of its transitive
/// descendants, walking parent links upward from `region_id`. Tolerates a
/// missing id (returns false rather than panicking).
pub(super) fn region_is_descendant_of(
    region_id: RegionId,
    ancestor_id: RegionId,
    region_tree: &RegionTree,
) -> bool {
    let mut current = Some(region_id);
    while let Some(id) = current {
        if id == ancestor_id {
            return true;
        }
        current = region_tree.regions.get(id).and_then(|region| region.parent);
    }
    false
}

/// Probe whether an IfThen/IfThenElse region is actually the head of a
/// Blueprint switch dispatch table (the `[EX_LET_BOOL temp = X != C_n;
/// EX_JUMP_IF_NOT temp -> CASE_n]` chain emitted by `K2Node_SwitchEnum`).
///
/// The region classifier sees only the first JIN in the chain and labels
/// the surrounding region IfThenElse (or IfThen when the JIN's else arm
/// bypasses to the region exit). Without this probe, the per-arm
/// emitters wrap the first Eq pair as a `Stmt::Branch` and the remaining
/// pairs flow through `lower_sentinel_cascade` + `cascade_fold`, which
/// produces a malformed `Stmt::Switch` whose case bodies have already
/// been hoisted into siblings.
///
/// Reuses the same `try_decode_jumpifnot_cascade` (and `_shared` /
/// `_shared_via_trampoline`) recognizers the region walk calls,
/// so cascade semantics live in one place. Returns `Some(Stmt::Switch)`
/// when one of the three variants matches; the caller emits it in place
/// of the per-arm branch.
///
/// Range bound: the smallest enclosing owned-range end for the scan
/// address, falling back to `bytecode.len()` when the context has no
/// owned ranges (standalone function decode / synthetic test contexts).
pub(super) fn try_emit_jumpifnot_cascade_region(
    region: &Region,
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    if !matches!(region.kind, RegionKind::IfThen | RegionKind::IfThenElse) {
        return None;
    }
    let entry_block = cfg.blocks.get(region.entry)?;
    // Scan the entry block for the first semantic opcode that could
    // head a dispatch table. The block's first opcode is often
    // instrumentation (EX_TRACEPOINT / EX_WIRE_TRACEPOINT), so a raw
    // first-opcode check rejects real cascades. The cascade recognizer
    // itself walks past instrumentation, but a cheap gate avoids
    // installing the owner guard and constructing cursors when no
    // cascade-shaped opcode is present.
    let head_addr = entry_block.opcodes.iter().copied().find(|&addr| {
        ctx.bytecode
            .get(addr)
            .map(|byte| matches!(*byte, EX_LET_BOOL | EX_JUMP_IF_NOT))
            .unwrap_or(false)
    })?;

    let range_end = ctx
        .owned_ranges
        .and_then(|ranges| {
            ranges
                .iter()
                .find(|range| range.start <= head_addr && head_addr < range.end)
                .map(|range| range.end)
        })
        .unwrap_or(ctx.bytecode.len());

    // Install CfgRegion ownership so the recognizer's `decode_subrange`
    // calls on case bodies bypass any prescan claims that sit inside the
    // region's transitive byte coverage. Mirrors how the per-arm
    // emitters wrap their arm decodes below.
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    let mut pos = head_addr;
    if let Some(stmt) = try_decode_jumpifnot_cascade(&mut pos, range_end, ctx) {
        return Some(stmt);
    }
    let mut pos = head_addr;
    if let Some(stmt) = try_decode_jumpifnot_cascade_shared(&mut pos, range_end, ctx) {
        return Some(stmt);
    }
    let mut pos = head_addr;
    if let Some(stmt) = try_decode_jumpifnot_cascade_shared_via_trampoline(&mut pos, range_end, ctx)
    {
        return Some(stmt);
    }
    None
}

/// Decode the entry block's opcodes preceding a terminator into preamble
/// statements, via the same per-opcode decoder used for the linear sweep.
///
/// Stops at the first opcode address equal to `break_at` (the terminator
/// sentinel) and bounds each `decode_one_or_branch` at `decode_bound` so a
/// multi-opcode construct (Call, Let, nested Branch) consumes its full span
/// without overrunning the gate. An internal consumed tracker keeps the
/// next iteration from re-decoding bytes a multi-opcode construct already
/// claimed. Shared by the IfThenElse / IfThen / SequenceChain /
/// pop-flow-if-not preamble walks.
pub(super) fn decode_entry_preamble(
    entry_block: &BasicBlock,
    break_at: usize,
    decode_bound: usize,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    let mut preamble: Vec<Stmt> = Vec::new();
    let mut preamble_consumed: Vec<Range<usize>> = Vec::new();
    for &opcode_addr in &entry_block.opcodes {
        if opcode_addr == break_at {
            break;
        }
        if address_in_consumed(&preamble_consumed, opcode_addr) {
            continue;
        }
        if claimed_end_for_disk_sweep(ctx, opcode_addr).is_some() {
            continue;
        }
        if opcode_addr >= ctx.bytecode.len() {
            continue;
        }
        let mut pos = opcode_addr;
        let before = pos;
        match decode_one_or_branch(&mut pos, decode_bound, ctx) {
            Ok(Some(stmt)) => {
                preamble.push(stmt);
                if pos > before {
                    preamble_consumed.push(before..pos);
                }
            }
            Ok(None) => {
                if pos > before {
                    preamble_consumed.push(before..pos);
                }
            }
            Err(unknown) => {
                preamble.push(*unknown);
                if pos > before {
                    preamble_consumed.push(before..pos);
                }
            }
        }
    }
    preamble
}

/// Find a child region of `region_id`'s parent (a sibling) that shares
/// the same entry block as `region_id` itself AND is the immediate
/// inner region in the dual-role pattern produced by the BP IsValid
/// macro shape (see `walk_region` notes).
///
/// Pattern: outer IfThenElse R0 = entry=B0 exit=Bn, child IfThenElse
/// R1 = entry=B0 exit=Bk where Bk strictly precedes Bn in the
/// post-dominator chain. R0 and R1 share entry B0 because both have the
/// same JIN terminator block. `mark_region_consumed(R0)` would silently
/// drop every block transitively under R1 if R0's per-kind emitter
/// fires. This helper returns R1 so the caller can defer R0's emit and
/// route through the disk-order walk instead.
///
/// Returns `None` when no inner sibling shares R0's entry (the common
/// case for regular IfThenElse regions where R0 already correctly
/// represents the whole branch).
pub(super) fn find_same_entry_inner_sibling(
    region_id: RegionId,
    region_tree: &RegionTree,
) -> Option<RegionId> {
    let region = region_tree.regions.get(region_id)?;
    for &child_id in &region.children {
        let child = region_tree.regions.get(child_id)?;
        if child.entry == region.entry && child_id != region_id {
            return Some(child_id);
        }
    }
    None
}

/// Find a sibling region S of `region_id` such that `S.entry ==
/// region.exit` AND `S.parent == region.parent`. The merge-continuation
/// pattern produced by the BP IsValid macro: R1 = IfThenElse[B0..B2]
/// and S = IfThenElse[B2..B10] are emitted as siblings under R0 even
/// though S semantically nests inside R1's then-arm.
///
/// Returns `None` when no such continuation exists (the common case).
/// The caller is responsible for the EX_RETURN guard via
/// `region_body_is_only_return` before pulling the continuation into
/// R1's then-arm.
///
/// Linear-kind siblings are skipped: post-merge synthesis produces Linear
/// siblings to hold content that the byte-sliced descendant chain would
/// otherwise drop. Those Linears must surface as siblings-after-R, not
/// be pulled into R's then-arm. The BP IsValid macro's downstream
/// continuation is always IfThen/IfThenElse/SequenceChain, never
/// Linear, so the gate doesn't lose any real macro shape.
pub(super) fn find_merge_continuation_region(
    region_id: RegionId,
    region_tree: &RegionTree,
) -> Option<RegionId> {
    let region = region_tree.regions.get(region_id)?;
    let parent_id = region.parent?;
    let parent = region_tree.regions.get(parent_id)?;
    for &sibling_id in &parent.children {
        if sibling_id == region_id {
            continue;
        }
        let sibling = region_tree.regions.get(sibling_id)?;
        if sibling.kind == RegionKind::Linear {
            continue;
        }
        if sibling.entry == region.exit {
            return Some(sibling_id);
        }
    }
    None
}

/// True when the region's transitive byte coverage decodes to exactly
/// one `Stmt::Return { value: None }`. Used as the guard before pulling
/// a merge-continuation sibling into the previous region's then-arm:
/// the IfThenElse merge-block trap re-emerges without this check.
///
/// Conservative: decodes the region's byte coverage via the same
/// `decode_subrange` path the arm emitters use. Anything beyond a
/// single bare `Return` (with no value) returns false.
pub(super) fn region_body_is_only_return(
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> bool {
    let Some(region_byte_ranges) = ctx.region_byte_ranges else {
        return false;
    };
    let Some(ranges) = region_byte_ranges.get(&region_id) else {
        return false;
    };
    if ranges.is_empty() {
        return false;
    }
    let _ = cfg;
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });
    let mut stmts: Vec<Stmt> = Vec::new();
    for range in ranges {
        let mut decoded = decode_subrange(range.start, range.end, ctx);
        stmts.append(&mut decoded);
    }
    matches!(stmts.as_slice(), [Stmt::Return { value: None, .. }])
}

/// True when a region's own-exit continuation tail carries nothing worth
/// appending: it is empty, or it is just a bare `Return { None }`. The
/// per-kind emitters drop such a tail rather than re-emitting a redundant
/// trailing return after the region's structured statements.
pub(super) fn tail_is_droppable(tail: &[Stmt]) -> bool {
    tail.is_empty() || matches!(tail, [Stmt::Return { value: None, .. }])
}

/// Complement to the sibling merge-continuation case. True when
/// `region_id`'s exit block is NOT the synthetic sink, IS owned by the
/// region itself (`block_to_region[exit] == region_id`), AND carries
/// content (non-empty opcode list).
///
/// The sibling merge-continuation case covers a separate region S whose
/// `S.entry == R.exit` and `S.parent == R.parent`. This own-exit case
/// covers content that lives in `region.exit` itself (the FlipFlop A|B
/// shared destination, the IsValid valid-pin tail when no sibling region
/// was produced, etc.). The per-kind emitter never decoded that block, and
/// `mark_region_consumed(R)` then silently sweeps it away.
///
/// The two patterns can co-occur: the sibling case keys off a sibling
/// region whose entry matches our exit, while own-exit-with-content
/// indicates that R1 owns the merge block. When both fire, the
/// own-exit-with-content signal relaxes the sibling case's
/// `else_body.is_empty()` guard so the continuation content is pulled into
/// the then-arm rather than dropped by `mark_region_consumed`'s
/// downstream sweep over R2's entry block.
pub(super) fn is_own_exit_with_content(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
) -> bool {
    let Some(region) = region_tree.regions.get(region_id) else {
        return false;
    };
    if region.exit == cfg.sink {
        return false;
    }
    if region_tree.block_to_region.get(&region.exit) != Some(&region_id) {
        return false;
    }
    let Some(exit_block) = cfg.blocks.get(region.exit) else {
        return false;
    };
    !exit_block.opcodes.is_empty()
}

/// Decode the exit block of `region_id`, used to recover macro-pin
/// downstream content that `mark_region_consumed` would otherwise drop.
///
/// The exit block's content is decoded via `decode_subrange` over the
/// block's byte range, under the region's owner guard so multi-opcode
/// recognisers (Call, Let, nested Branch) see the same context as the
/// arm-body decoders. Nested IfThenElse / DoOnce / Sequence shapes
/// inside the exit block are picked up naturally by `decode_subrange`,
/// which dispatches through the standard `decode_one_or_branch` loop.
///
/// EX_RETURN guard: callers must avoid pushing a continuation that
/// decodes to a lone bare `Return { None }` (the IfThenElse-merge-block
/// trap). The guard sits at the callsite.
pub(super) fn decode_post_merge_continuation(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Vec<Stmt> {
    let Some(region) = region_tree.regions.get(region_id) else {
        return Vec::new();
    };
    let Some(exit_block) = cfg.blocks.get(region.exit) else {
        return Vec::new();
    };
    if exit_block.opcodes.is_empty() {
        return Vec::new();
    }
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });
    decode_subrange(exit_block.start, exit_block.end, ctx)
}
