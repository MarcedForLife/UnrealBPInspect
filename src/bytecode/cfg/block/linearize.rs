//! DFS linearization, emits blocks so conditional jumps point forward.

use crate::bytecode::decode::BcStatement;

use super::analysis::{all_predecessors_emitted, find_convergence_target};
use super::types::{Block, BlockExit, BlockId};

/// Recursive DFS linearization. Shared by `flow::reorder_convergence` and
/// `output_summary::ubergraph::linearize_from_entry`. Callers typically seed
/// with the event entry block first, then sweep remaining blocks so
/// unreachable code is preserved.
///
/// - CondJump: emit fall-through (true body) first, then target (false body)
/// - Jump to single-entry block: follow inline
/// - Jump to multi-entry block: leave the jump in place (becomes goto label)
/// - FallThrough: follow next block, insert synthetic jump if already emitted
pub(crate) fn linearize_blocks(
    blocks: &mut [Block],
    stmts: &[BcStatement],
    in_degree: &[usize],
    predecessors: &[Vec<BlockId>],
    bid: BlockId,
    output: &mut Vec<BcStatement>,
) {
    if bid >= blocks.len() || blocks[bid].emitted {
        return;
    }
    blocks[bid].emitted = true;

    let range = blocks[bid].stmt_range.clone();
    for idx in range {
        output.push(stmts[idx].clone());
    }

    let exit = blocks[bid].exit.clone();
    match exit {
        BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}

        BlockExit::FallThrough => {
            let next = bid + 1;
            if next < blocks.len() {
                if !blocks[next].emitted && in_degree[next] <= 1 {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, next, output);
                } else {
                    // Synthetic forward jump so the structurer's else-branch
                    // detector sees an explicit exit even when the successor
                    // is deferred.
                    let target_offset = stmts[blocks[next].stmt_range.start].mem_offset;
                    output.push(BcStatement::new(0, format!("jump 0x{target_offset:x}")));
                }
            }
        }

        BlockExit::Jump(target) => {
            // Single-entry target inline; multi-entry convergence block's
            // jump becomes a goto in structure_bytecode.
            if target < blocks.len() && in_degree[target] <= 1 && !blocks[target].emitted {
                linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
            }
        }

        BlockExit::CondJump {
            fall_through,
            target,
        } => {
            if fall_through < blocks.len()
                && in_degree[fall_through] > 1
                && target < blocks.len()
                && in_degree[target] <= 1
            {
                // Guard pattern: fall-through is multi-entry convergence,
                // target is single-entry false body. Emit false body first
                // then the convergence to get `if (cond) { false } conv`.
                // Negate the if-jump to compensate for the swap.
                negate_last_if_jump(stmts, &blocks[bid].stmt_range, output);
                linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                linearize_blocks(blocks, stmts, in_degree, predecessors, fall_through, output);
            } else {
                linearize_blocks(blocks, stmts, in_degree, predecessors, fall_through, output);
                if target < blocks.len() && in_degree[target] <= 1 {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                }
                // Inner if/else convergence: now that fall-through is out,
                // emit the deferred target if nothing else still needs it.
                if target < blocks.len()
                    && !blocks[target].emitted
                    && all_predecessors_emitted(blocks, predecessors, target)
                {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                }
            }

            if let Some(conv) = find_convergence_target(blocks, fall_through, target) {
                if !blocks[conv].emitted && all_predecessors_emitted(blocks, predecessors, conv) {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, conv, output);
                }
            }
        }
    }
}

/// Wraps the condition in an extra `!()` so the structurer (which strips
/// the outer `!`) gets the negated condition. Double-negation is cleaned up
/// later.
fn negate_last_if_jump(
    stmts: &[BcStatement],
    block_range: &std::ops::Range<usize>,
    output: &mut [BcStatement],
) {
    if block_range.is_empty() {
        return;
    }
    let last_idx = block_range.end - 1;
    let last_stmt = &stmts[last_idx];
    if let Some((cond, target)) = last_stmt.if_jump() {
        if let Some(out_stmt) = output.last_mut() {
            if out_stmt.text == last_stmt.text {
                out_stmt.set_text(format!("if !(!{cond}) jump 0x{target:x}"));
            }
        }
    }
}
