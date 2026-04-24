use super::super::cfg::{BlockCfg, BlockExit, BlockId, ReturnKind};
use super::super::decode::{BcStatement, StmtKind};
use super::super::flow::{find_first_unmatched_pop, flow_depth};
use super::region::IfBlock;
use std::collections::{HashMap, HashSet};

/// Detect if/else blocks from `if !(cond) jump` patterns, then truncate false-blocks
/// where an early exit jump targets the convergence point.
pub(super) fn detect_if_blocks(
    stmts: &[BcStatement],
    find_target: &dyn Fn(usize) -> Option<usize>,
    cfg: &BlockCfg,
) -> Vec<IfBlock> {
    let mut if_blocks: Vec<IfBlock> = Vec::new();

    for (i, stmt) in stmts.iter().enumerate() {
        let Some((cond, target)) = stmt.if_jump() else {
            continue;
        };
        let Some(mut target_idx) = find_target(target) else {
            continue;
        };

        // Fuzzy offset resolution can land on a pop_flow or phantom
        // (inlined-away temp) when the real target is a filtered opcode or a
        // temp anchor; advance past both since neither can start a false branch.
        while target_idx < stmts.len()
            && (stmts[target_idx].kind == StmtKind::PopFlow || stmts[target_idx].inlined_away)
        {
            target_idx += 1;
        }

        let (mut jump_idx, mut end_idx) = detect_else_branch_via_cfg(cfg, stmts, i, target_idx);

        // Pin-aware tiebreaker: when pin-only-callee sets classify the
        // physical then/else split, trust the pin split and bound the else
        // block by the first unmatched pop_flow (same convention as the
        // LatchTerminal/POP_FLOW CFG paths).
        if target_idx > i + 1 && target_idx <= stmts.len() {
            if let Some(key) = crate::pin_hints_scope::current_function_key() {
                let pop_flow_end = find_else_end_by_pop_flow(stmts, target_idx);
                let bytecode_offset = stmts[i].mem_offset as u32;
                let then_side_text: Vec<&str> = stmts[i + 1..target_idx]
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect();
                let else_side_text: Vec<&str> = stmts[target_idx..pop_flow_end]
                    .iter()
                    .map(|s| s.text.as_str())
                    .collect();
                let pin_answer = crate::pin_hints::detect_else_branch_via_pins_scoped(
                    bytecode_offset,
                    &key,
                    &then_side_text,
                    &else_side_text,
                );
                if pin_answer == (Some(0), Some(0)) {
                    jump_idx = None;
                    end_idx = Some(pop_flow_end);
                }
            }
        }

        if_blocks.push(IfBlock {
            if_idx: i,
            cond: cond.to_string(),
            target_idx,
            jump_idx,
            end_idx,
            else_close_idx: None,
        });
    }

    truncate_false_blocks(&mut if_blocks, stmts, find_target);

    if_blocks
}

/// True when the `pop_flow` at `pop_idx` is unmatched within `[start, pop_idx)`
/// (balanced push/pop pairs mean it's a genuine scope exit).
fn is_unmatched_pop_flow(stmts: &[BcStatement], start: usize, pop_idx: usize) -> bool {
    flow_depth(stmts, start, pop_idx) == 0
}

/// End of the false branch when the true branch terminates in pop_flow: the
/// first depth-0 pop_flow from `start`. Returns exclusive end so the pop_flow
/// is included in the else region and emitted as `return`/`break`.
fn find_else_end_by_pop_flow(stmts: &[BcStatement], start: usize) -> usize {
    find_first_unmatched_pop(stmts, start, stmts.len())
        .map(|idx| idx + 1)
        .unwrap_or(stmts.len())
}

/// Map a CondJump true-branch tail exit to `(jump_idx, end_idx)`. Returns
/// `(None, None)` when no recognised else-branch terminator matches.
fn detect_else_branch_via_cfg(
    cfg: &BlockCfg,
    stmts: &[BcStatement],
    if_idx: usize,
    target_idx: usize,
) -> (Option<usize>, Option<usize>) {
    if target_idx == 0 || target_idx > stmts.len() || if_idx >= target_idx {
        return (None, None);
    }

    let Some(if_bid) = cfg.block_of(if_idx) else {
        return (None, None);
    };
    let BlockExit::CondJump { fall_through, .. } = cfg.blocks[if_bid].exit else {
        return (None, None);
    };

    let Some(last_bid) = last_block_before_target(cfg, fall_through, target_idx) else {
        return (None, None);
    };

    let last_block = &cfg.blocks[last_bid];
    let last_stmt_idx = last_block.stmt_range.end.saturating_sub(1);

    match &last_block.exit {
        BlockExit::Jump(conv_bid) => {
            let conv_start = cfg.blocks[*conv_bid].stmt_range.start;
            if conv_start >= target_idx {
                (Some(last_stmt_idx), Some(conv_start))
            } else {
                (None, None)
            }
        }
        BlockExit::ReturnTerminal => {
            let last_kind = stmts[last_stmt_idx].kind;
            if matches!(last_kind, StmtKind::ReturnNop | StmtKind::BareReturn) {
                if target_idx < stmts.len() {
                    (Some(last_stmt_idx), Some(stmts.len()))
                } else {
                    (None, None)
                }
            } else if last_kind == StmtKind::PopFlow
                && target_idx < stmts.len()
                && is_unmatched_pop_flow(stmts, if_idx + 1, last_stmt_idx)
            {
                let end_idx = find_else_end_by_pop_flow(stmts, target_idx);
                (None, Some(end_idx))
            } else {
                (None, None)
            }
        }
        BlockExit::LatchTerminal => {
            if target_idx < stmts.len()
                && has_latch_opener_in_range(stmts, if_idx + 1, last_stmt_idx)
            {
                let end_idx = find_else_end_by_pop_flow(stmts, target_idx);
                (None, Some(end_idx))
            } else {
                (None, None)
            }
        }
        BlockExit::FallThrough | BlockExit::CondJump { .. } => (None, None),
    }
}

/// Last block at or before `target_idx`, reachable by physical layout from
/// `entry`. Physical-order build means rightmost block ending <= target_idx
/// matches a backward scan's landing point.
fn last_block_before_target(cfg: &BlockCfg, entry: BlockId, target_idx: usize) -> Option<BlockId> {
    if entry >= cfg.blocks.len() {
        return None;
    }
    if cfg.blocks[entry].stmt_range.start >= target_idx {
        return None;
    }
    let mut last = None;
    for bid in entry..cfg.blocks.len() {
        let range = &cfg.blocks[bid].stmt_range;
        if range.start >= target_idx {
            break;
        }
        if range.end <= target_idx {
            last = Some(bid);
        } else {
            // Defensive: basic-block split on jump targets, shouldn't straddle.
            break;
        }
    }
    last
}

/// True if any statement in `[start, end)` is a DoOnce/FlipFlop opener.
fn has_latch_opener_in_range(stmts: &[BcStatement], start: usize, end: usize) -> bool {
    (start..end).any(|j| {
        let opener = stmts[j].text.trim();
        (opener.starts_with("DoOnce(") || opener.starts_with("FlipFlop(")) && opener.ends_with(" {")
    })
}

/// Scan each else block for an early-exit jump targeting end_idx and set
/// `else_close_idx` so the else doesn't engulf subsequent code in nested patterns.
fn truncate_false_blocks(
    if_blocks: &mut [IfBlock],
    stmts: &[BcStatement],
    find_target: &dyn Fn(usize) -> Option<usize>,
) {
    for blk in if_blocks.iter_mut() {
        let Some(end_idx) = blk.end_idx else {
            continue;
        };
        if blk.target_idx >= end_idx {
            continue;
        }
        // Only at if-depth 0: jumps inside nested if-blocks are their own exits.
        // Relies on UE's shape: each if_jump is followed by exactly one
        // unconditional jump (its else-exit) before the next if_jump or body.
        let mut if_depth = 0usize;
        for (j, stmt) in stmts.iter().enumerate().take(end_idx).skip(blk.target_idx) {
            if stmt.if_jump().is_some() {
                if_depth += 1;
                continue;
            }
            if let Some(jt) = stmt.jump_target() {
                if if_depth > 0 {
                    if_depth -= 1;
                    continue;
                }
                if find_target(jt) == Some(end_idx) {
                    blk.else_close_idx = Some(j + 1);
                    break;
                }
                // Backward jump to before the else start: control returns to
                // earlier convergence, so the else body ends here.
                if let Some(target_idx) = find_target(jt) {
                    if target_idx < blk.target_idx {
                        blk.else_close_idx = Some(j + 1);
                        break;
                    }
                }
            }
            // Return at depth 0 terminates the else (branch diverges).
            if if_depth == 0 && matches!(stmt.kind, StmtKind::ReturnNop | StmtKind::BareReturn) {
                blk.else_close_idx = Some(j + 1);
                break;
            }
        }
    }
}

/// Pre-collect jump targets so `emit_stmts_range` can emit `goto LABEL` and
/// inject label definitions. Returns:
/// - `label_targets[stmt_idx]` = the `goto ...` text for that jump
/// - `pending_labels[target_idx]` = synthetic label to inject before it
pub(super) fn collect_label_targets(
    stmts: &[BcStatement],
    skip: &HashSet<usize>,
    label_at: &HashMap<usize, &String>,
    find_target_idx_or_end: &dyn Fn(usize) -> Option<usize>,
) -> (HashMap<usize, String>, HashMap<usize, String>) {
    let mut label_targets: HashMap<usize, String> = HashMap::new();
    let mut pending_labels: HashMap<usize, String> = HashMap::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if skip.contains(&i) {
            continue;
        }
        if let Some(target) = stmt.jump_target() {
            if let Some(mut target_idx) = find_target_idx_or_end(target) {
                // Pin labels to a live statement: phantoms carry no text and
                // emit_stmts_range would bury the label at an index that falls
                // inside a skipped region.
                while target_idx < stmts.len() && stmts[target_idx].inlined_away {
                    target_idx += 1;
                }
                let is_jump_to_end_label = target_idx >= stmts.len()
                    || (target_idx == stmts.len() - 1
                        && stmts[target_idx].kind == StmtKind::ReturnNop);
                if is_jump_to_end_label {
                    // Will become `break` or be omitted.
                } else if let Some(lbl) = label_at.get(&target_idx) {
                    label_targets.insert(i, format!("goto {}", lbl));
                } else {
                    let label_name = format!("L_{:04x}", target);
                    pending_labels
                        .entry(target_idx)
                        .or_insert_with(|| label_name.clone());
                    label_targets.insert(i, format!("goto {}", label_name));
                }
            }
        }
    }
    (label_targets, pending_labels)
}

/// Exclusive end of the flow scope starting at block-boundary `start`. Walks
/// the block CFG from `start`, matching nested push/pop via
/// `push_flow_count` and `return_kind`; returns the end of the first block
/// whose terminal closes the scope (depth-0 `PopFlow` or `Return`), falling
/// back to the last block's end.
fn find_block_end_via_cfg(cfg: &BlockCfg, start: usize) -> usize {
    let first = cfg.blocks.partition_point(|b| b.stmt_range.start < start);
    let mut depth: u32 = 0;
    for block in &cfg.blocks[first..] {
        depth += block.push_flow_count;
        match block.return_kind {
            Some(ReturnKind::PopFlow) => {
                if depth == 0 {
                    return block.stmt_range.end;
                }
                depth -= 1;
            }
            Some(ReturnKind::Return) if depth == 0 => {
                return block.stmt_range.end;
            }
            _ => {}
        }
    }
    cfg.blocks.last().map(|b| b.stmt_range.end).unwrap_or(0)
}

/// Restore nested if/else containment when UE displaces a nested else past
/// the outer one:
/// ```text
///   if !A jump X
///     if !B jump Y
///       B-true body
///       pop_flow
///   X: A-false body
///     pop_flow
///   Y: B-false body   <- displaced inner else
/// ```
/// Moves B-false before A-false. Returns `None` if no reordering needed.
pub(super) fn reorder_displaced_else(stmts: &[BcStatement]) -> Option<Vec<BcStatement>> {
    if stmts.len() < 4 {
        return None;
    }

    let mut result: Option<Vec<BcStatement>> = None;

    // One displacement per iteration until stable.
    loop {
        let working = result.as_deref().unwrap_or(stmts);
        let Some((outer_target, inner_target, inner_else_end)) =
            find_displaced_else_splice(working)
        else {
            break;
        };
        // outer_target < inner_target, so drain-first keeps insertion stable.
        let mut reordered = working.to_vec();
        let block: Vec<BcStatement> = reordered.drain(inner_target..inner_else_end).collect();
        reordered.splice(outer_target..outer_target, block);
        result = Some(reordered);
    }

    result
}

/// Find a displaced-else splice. Returns
/// `(outer_target, inner_target, inner_else_end)`: drain
/// `[inner_target..inner_else_end)` and insert at `outer_target`.
fn find_displaced_else_splice(stmts: &[BcStatement]) -> Option<(usize, usize, usize)> {
    let omap = super::super::OffsetMap::build(stmts);
    let cfg = BlockCfg::build_for_structurer(stmts, &omap);

    let cond_blocks: Vec<(BlockId, usize, usize)> = (0..cfg.blocks.len())
        .filter_map(|bid| cond_jump_info(&cfg, stmts, bid).map(|(i, t)| (bid, i, t)))
        .collect();

    for (oi, &(_, outer_if, outer_target)) in cond_blocks.iter().enumerate() {
        for (ii, &(_, inner_if, inner_target)) in cond_blocks.iter().enumerate() {
            if oi == ii {
                continue;
            }
            if inner_if <= outer_if || inner_if >= outer_target || inner_target <= outer_target {
                continue;
            }
            if !range_has_exit_via_cfg(&cfg, inner_if + 1, outer_target) {
                continue;
            }
            let inner_else_end = find_block_end_via_cfg(&cfg, inner_target);
            if inner_else_end <= inner_target {
                continue;
            }
            return Some((outer_target, inner_target, inner_else_end));
        }
    }
    None
}

/// `(if_stmt_idx, target_stmt_idx)` for a CondJump block. Target is advanced
/// past a leading pop_flow from fuzzy-offset resolution (real target is the
/// next statement after a filtered wire_trace).
fn cond_jump_info(cfg: &BlockCfg, stmts: &[BcStatement], bid: BlockId) -> Option<(usize, usize)> {
    let block = &cfg.blocks[bid];
    let BlockExit::CondJump { target, .. } = block.exit else {
        return None;
    };
    if block.stmt_range.is_empty() {
        return None;
    }
    let if_idx = block.stmt_range.end - 1;
    let mut target_idx = cfg.blocks[target].stmt_range.start;
    if target_idx < stmts.len() && stmts[target_idx].kind == StmtKind::PopFlow {
        target_idx += 1;
    }
    Some((if_idx, target_idx))
}

/// True when any block fully contained in `[start, end)` exits via
/// [`BlockExit::ReturnTerminal`].
fn range_has_exit_via_cfg(cfg: &BlockCfg, start: usize, end: usize) -> bool {
    if start >= end {
        return false;
    }
    let first = cfg.blocks.partition_point(|b| b.stmt_range.start < start);
    cfg.blocks[first..]
        .iter()
        .take_while(|b| b.stmt_range.start < end)
        .any(|b| b.stmt_range.end <= end && matches!(b.exit, BlockExit::ReturnTerminal))
}
