//! Tail-JIN (jump-if-not) arm-range computation for chained branch arms.
//!
//! Walks balanced arm bodies of a tail-jump-if-not chain and reports the
//! disk ranges each arm spans, used by the layout decoder and by region
//! decoding.

use std::collections::BTreeSet;
use std::ops::Range;

use crate::bytecode::cfg::{BlockId, ControlFlowGraph};
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;

use super::super::ctx::DecodeCtx;
use super::target::{event_scan_end, peek_jump_at, skip_instrumentation, JUMP_TARGET_BYTES};

/// Compute the disk-byte span of each recogniser arm rooted at
/// `arm_entries`, bounded by `region_exit` (the post-dominator of the
/// construct's entry block).
///
/// Returns one `Vec<Range>` per arm in input order: the union of owned
/// disk segments reachable from the arm entry without crossing
/// `region_exit`. An empty Vec means the arm has no exclusive blocks
/// (fall-through to exit) or the entry was unresolved.
pub(crate) fn region_arm_extents(
    arm_entries: &[Option<BlockId>],
    region_exit: BlockId,
    cfg: &ControlFlowGraph,
) -> Vec<Vec<Range<usize>>> {
    arm_entries
        .iter()
        .map(|&entry| match entry {
            Some(block) if block != region_exit => arm_reachable_ranges(block, region_exit, cfg),
            _ => Vec::new(),
        })
        .collect()
}

/// Walk CFG successors from `arm_entry`, stopping at `region_exit`.
/// Returns block byte ranges merged where adjacent.
fn arm_reachable_ranges(
    arm_entry: BlockId,
    region_exit: BlockId,
    cfg: &ControlFlowGraph,
) -> Vec<Range<usize>> {
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let mut frontier: Vec<BlockId> = vec![arm_entry];
    while let Some(block_id) = frontier.pop() {
        if block_id == region_exit || !visited.insert(block_id) || block_id == cfg.sink {
            continue;
        }
        if let Some(succs) = cfg.successors.get(&block_id) {
            for &succ in succs {
                if !visited.contains(&succ) && succ != region_exit {
                    frontier.push(succ);
                }
            }
        }
    }
    let mut spans: Vec<Range<usize>> = visited
        .iter()
        .filter_map(|&id| cfg.blocks.get(id))
        .filter(|block| !block.opcodes.is_empty() && block.end > block.start)
        .map(|block| block.start..block.end)
        .collect();
    spans.sort_by_key(|range| range.start);
    let mut merged: Vec<Range<usize>> = Vec::with_capacity(spans.len());
    for span in spans {
        match merged.last_mut() {
            Some(last) if last.end >= span.start => last.end = last.end.max(span.end),
            _ => merged.push(span),
        }
    }
    merged
}

/// True when `disk` points at the canonical tail-JIN push-chain head:
/// optional instrumentation, then `EX_PUSH_EXECUTION_FLOW`, then
/// `EX_JUMP`. The structural marker that distinguishes the tail-JIN
/// displaced-arm shape from IsValid macros (target is a function call), DoOnce
/// gate-check (target is `Var = true`), sentinel cascades (target is
/// `<TRACEPOINT> jump <event-exit>` with no push_flow), and inline-THEN
/// backward-converge (target is a normal expression).
///
/// Used both directly (for the chain-head shape) and recursively from
/// [`is_tail_jin_arm_head`]'s bare-trampoline path (where the trampoline
/// target itself must be a chain head for the predicate to fire).
fn is_chain_head_at(disk: usize, scan_end: usize, ctx: &DecodeCtx) -> bool {
    if disk >= scan_end || disk >= ctx.bytecode.len() {
        return false;
    }
    let after_trace = skip_instrumentation(disk, scan_end, ctx);
    if after_trace >= scan_end || after_trace >= ctx.bytecode.len() {
        return false;
    }
    if ctx.bytecode[after_trace] != EX_PUSH_EXECUTION_FLOW {
        return false;
    }
    let push_length = opcode_length_at(after_trace, ctx.bytecode, ctx.ue5, ctx.name_table);
    if push_length == 0 {
        return false;
    }
    let after_push = skip_instrumentation(after_trace + push_length, scan_end, ctx);
    if after_push >= scan_end || after_push >= ctx.bytecode.len() {
        return false;
    }
    ctx.bytecode[after_push] == EX_JUMP
}

/// True when `disk` points at a tail-JIN displaced-arm head. Two shapes:
///
/// 1. **Chain head**: instrumentation + `EX_PUSH_EXECUTION_FLOW` +
///    `EX_JUMP` at the arm head itself. See [`is_chain_head_at`].
///
/// 2. **Bare trampoline**: instrumentation + `EX_JUMP <addr>` where the
///    target is itself a chain head (the bare-trampoline pattern). The
///    arm head logically moves through the trampoline to the chain at
///    the target; body decode walks the chain instead of the trampoline.
fn is_tail_jin_arm_head(disk: usize, scan_end: usize, ctx: &DecodeCtx) -> bool {
    if disk >= scan_end || disk >= ctx.bytecode.len() {
        return false;
    }
    let after_trace = skip_instrumentation(disk, scan_end, ctx);
    if after_trace >= scan_end || after_trace >= ctx.bytecode.len() {
        return false;
    }
    match ctx.bytecode[after_trace] {
        EX_PUSH_EXECUTION_FLOW => is_chain_head_at(disk, scan_end, ctx),
        EX_JUMP => {
            let opcode_byte_count = 1;
            if after_trace + opcode_byte_count + JUMP_TARGET_BYTES > ctx.bytecode.len() {
                return false;
            }
            let mut peek = after_trace + opcode_byte_count;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let Some(mem_to_disk) = ctx.mem_to_disk else {
                return false;
            };
            let Some(&target_disk) = mem_to_disk.get(&target_mem) else {
                return false;
            };
            is_chain_head_at(target_disk, scan_end, ctx)
        }
        _ => false,
    }
}

/// Resolve an arm target to its effective chain-head disk position.
///
/// For canonical chain-head arms (instrumentation + `EX_PUSH_EXECUTION_FLOW`)
/// the effective head is the arm target itself. For bare-trampoline arms
/// (instrumentation + `EX_JUMP <addr>` where the target is a chain head),
/// the effective head is the trampoline TARGET, so body-bound walks and
/// skeleton lookups dispatch on the chain at the target rather than the
/// trampoline jump.
///
/// Returns `None` when the arm doesn't satisfy [`is_tail_jin_arm_head`]'s
/// predicate (caller should have checked that already, but this helper
/// keeps the dispatch structurally tied to the predicate).
fn tail_jin_effective_arm_head(
    arm_target_disk: usize,
    scan_end: usize,
    ctx: &DecodeCtx,
) -> Option<usize> {
    if arm_target_disk >= scan_end || arm_target_disk >= ctx.bytecode.len() {
        return None;
    }
    let after_trace = skip_instrumentation(arm_target_disk, scan_end, ctx);
    if after_trace >= scan_end || after_trace >= ctx.bytecode.len() {
        return None;
    }
    match ctx.bytecode[after_trace] {
        EX_PUSH_EXECUTION_FLOW => Some(arm_target_disk),
        EX_JUMP => {
            let opcode_byte_count = 1;
            if after_trace + opcode_byte_count + JUMP_TARGET_BYTES > ctx.bytecode.len() {
                return None;
            }
            let mut peek = after_trace + opcode_byte_count;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let mem_to_disk = ctx.mem_to_disk?;
            mem_to_disk.get(&target_mem).copied()
        }
        _ => None,
    }
}

/// Walk forward from `arm_start` tracking balanced push/pop depth, and
/// return the disk position one past the `EX_POP_EXECUTION_FLOW` that
/// returns depth to the entry level. Used as a SIGNATURE-CHECK; the
/// authoritative arm extent comes from `tail_jin_arm_end` via the
/// chain skeleton.
fn walk_balanced_arm_end(arm_start: usize, scan_end: usize, ctx: &DecodeCtx) -> Option<usize> {
    const MAX_OPCODES: usize = 256;
    let limit = scan_end.min(ctx.bytecode.len());
    let mut cursor = arm_start;
    let mut depth: i32 = 0;
    let mut visited = 0usize;
    while cursor < limit && visited < MAX_OPCODES {
        let opcode = ctx.bytecode[cursor];
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        match opcode {
            EX_PUSH_EXECUTION_FLOW => depth += 1,
            EX_POP_EXECUTION_FLOW => {
                depth -= 1;
                if depth <= 0 {
                    return Some(cursor + length);
                }
            }
            _ => {}
        }
        cursor += length;
        visited += 1;
    }
    None
}

/// Locate the chain head whose extent includes `arm_target` and return
/// one past its max pin partition end. The skeleton's pin partitions
/// encode the chain's reachability-bounded extent computed once during
/// partitioning; preferred over the linear `walk_balanced_arm_end`
/// because the BP DoOnce expansion may close one push/pop pair and
/// then immediately open another within the same arm.
fn tail_jin_arm_end(arm_target: usize, scan_end: usize, ctx: &DecodeCtx) -> Option<usize> {
    let skeleton = ctx.skeleton?;
    let head_disk = skip_instrumentation(arm_target, scan_end, ctx);
    let chain = skeleton.push_chains.get(&head_disk)?;
    let max_end = chain
        .pin_partitions
        .iter()
        .flat_map(|segments| segments.iter().map(|range| range.end))
        .max()?;
    Some(max_end)
}

/// Result of validating a tail-JIN displaced-arm signature: the two arm
/// ranges.
#[derive(Debug, Clone)]
pub(crate) struct TailJinArms {
    pub then_range: (usize, usize),
    pub else_range: (usize, usize),
}

/// Validate the tail-JIN displaced-arm signature at `jin_offset` and
/// return the arm ranges. Returns `None` when the signature doesn't match
/// (so other recognisers can fire) or when one of the body-bound walks
/// fails (decline cleanly).
pub(crate) fn tail_jin_arm_ranges(
    jin_offset: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<TailJinArms> {
    let jin_length = opcode_length_at(jin_offset, ctx.bytecode, ctx.ue5, ctx.name_table);
    if jin_length == 0 {
        return None;
    }
    let opcode_byte_count = 1;
    if jin_offset + opcode_byte_count + JUMP_TARGET_BYTES > ctx.bytecode.len() {
        return None;
    }
    let mut peek = jin_offset + opcode_byte_count;
    let else_target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;

    let mem_to_disk = ctx.mem_to_disk?;
    let &else_target_disk = mem_to_disk.get(&else_target_mem)?;
    if else_target_disk >= jin_offset {
        return None;
    }

    let scan_end = event_scan_end(range_end, ctx);

    if !is_tail_jin_arm_head(else_target_disk, scan_end, ctx) {
        return None;
    }

    let after_jin = jin_offset + jin_length;
    if after_jin >= ctx.bytecode.len() {
        return None;
    }
    let post_jin_jump = skip_instrumentation(after_jin, scan_end, ctx);
    let (then_target_mem, _, _) = peek_jump_at(ctx.bytecode, post_jin_jump, scan_end)?;
    let &then_target_disk = mem_to_disk.get(&then_target_mem)?;
    if then_target_disk >= jin_offset {
        return None;
    }
    if !is_tail_jin_arm_head(then_target_disk, scan_end, ctx) {
        return None;
    }

    // Resolve each arm head to its effective chain-head position. For
    // canonical chain-head arms this is the arm target itself; for the
    // bare-trampoline shape this is the
    // trampoline TARGET, so the body decode walks the chain at the
    // target rather than the trampoline jump. The trampoline jump's
    // bytes get skipped silently by `decode_jump` (target classifies
    // InRange, returns no statement).
    let then_effective = tail_jin_effective_arm_head(then_target_disk, scan_end, ctx)?;
    let else_effective = tail_jin_effective_arm_head(else_target_disk, scan_end, ctx)?;

    // Region-aware path: when CFG + region tree are populated, take
    // each arm's end from the union of owned segments reachable from
    // the arm entry bounded by the SESE region exit. The skeleton /
    // walk fallback only fires when the accessor declines.
    let region_extents = ctx.region_arm_extents_for(jin_offset, &[then_effective, else_effective]);
    let region_arm_end = |index: usize, start: usize| -> Option<usize> {
        let arm = region_extents.as_ref()?.get(index)?;
        let end = arm.last()?.end;
        if end > start && end <= jin_offset {
            Some(end)
        } else {
            None
        }
    };

    let then_end = match region_arm_end(0, then_effective) {
        Some(end) => end,
        None => match tail_jin_arm_end(then_effective, scan_end, ctx) {
            Some(end) => end,
            None => walk_balanced_arm_end(then_effective, scan_end, ctx)?,
        },
    };
    let else_end = match region_arm_end(1, else_effective) {
        Some(end) => end,
        None => match tail_jin_arm_end(else_effective, scan_end, ctx) {
            Some(end) => end,
            None => walk_balanced_arm_end(else_effective, scan_end, ctx)?,
        },
    };

    if then_end > jin_offset || else_end > jin_offset {
        return None;
    }

    Some(TailJinArms {
        then_range: (then_effective, then_end),
        else_range: (else_effective, else_end),
    })
}
