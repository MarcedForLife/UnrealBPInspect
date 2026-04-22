//! In-degree, predecessors, convergence detection, reachability walks.

use std::collections::HashSet;

use super::types::{Block, BlockExit, BlockId};

pub(super) fn compute_in_degree(blocks: &[Block]) -> Vec<usize> {
    let mut deg = vec![0usize; blocks.len()];
    for (bid, block) in blocks.iter().enumerate() {
        match &block.exit {
            BlockExit::FallThrough => {
                if bid + 1 < blocks.len() {
                    deg[bid + 1] += 1;
                }
            }
            BlockExit::Jump(target) => {
                deg[*target] += 1;
            }
            BlockExit::CondJump {
                fall_through,
                target,
            } => {
                deg[*fall_through] += 1;
                deg[*target] += 1;
            }
            BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        }
    }
    deg
}

pub(super) fn compute_predecessors(blocks: &[Block]) -> Vec<Vec<BlockId>> {
    let mut preds = vec![Vec::new(); blocks.len()];
    for (bid, block) in blocks.iter().enumerate() {
        match &block.exit {
            BlockExit::FallThrough => {
                if bid + 1 < blocks.len() {
                    preds[bid + 1].push(bid);
                }
            }
            BlockExit::Jump(target) => {
                preds[*target].push(bid);
            }
            BlockExit::CondJump {
                fall_through,
                target,
            } => {
                preds[*fall_through].push(bid);
                preds[*target].push(bid);
            }
            BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        }
    }
    preds
}

/// True if every predecessor of `target` is already emitted. Linearization
/// uses this to decide inline emission vs deferring to the sweep pass.
pub(crate) fn all_predecessors_emitted(
    blocks: &[Block],
    predecessors: &[Vec<BlockId>],
    target: BlockId,
) -> bool {
    if target >= predecessors.len() {
        return true;
    }
    predecessors[target]
        .iter()
        .all(|&pred| blocks[pred].emitted)
}

/// Block that both branches eventually reach via explicit Jump/CondJump
/// edges, lowest block id among qualifying candidates.
///
/// Return-branch guard: if either branch's entry is immediately
/// `ReturnTerminal`, returns `None` (prevents pulling post-return code into
/// an already-exited region). `LatchTerminal` is NOT guarded: shared
/// post-latch code can still be the sibling branch's convergence.
///
/// A broader "outside-predecessor" filter was tried and regressed
/// `AttemptGrip` (legitimate convergence candidate has a backward predecessor
/// from later-emitted code). The terminal-branch guard alone is sufficient
/// to prevent `EvaluateClimbing`.
pub(crate) fn find_convergence_target(
    blocks: &[Block],
    branch_a: BlockId,
    branch_b: BlockId,
) -> Option<BlockId> {
    if branch_a >= blocks.len() || branch_b >= blocks.len() {
        return None;
    }
    if blocks[branch_a].exit.is_return() || blocks[branch_b].exit.is_return() {
        return None;
    }

    let mut targets_a: HashSet<BlockId> = HashSet::new();
    let mut visited_a: HashSet<BlockId> = HashSet::new();
    collect_branch_exits(blocks, branch_a, &mut targets_a, &mut visited_a);

    let mut targets_b: HashSet<BlockId> = HashSet::new();
    let mut visited_b: HashSet<BlockId> = HashSet::new();
    collect_branch_exits(blocks, branch_b, &mut targets_b, &mut visited_b);

    targets_a.intersection(&targets_b).copied().min()
}

/// Blocks reachable from `entry` without entering `avoid`. Convergence-aware
/// nesting computes this for each branch of a CondJump, avoiding the sibling,
/// then uses set differences to classify successors as ft-only, target-only,
/// or convergent.
#[allow(dead_code)]
pub(crate) fn blocks_reachable_avoiding(
    blocks: &[Block],
    entry: BlockId,
    avoid: BlockId,
) -> HashSet<BlockId> {
    let mut reached: HashSet<BlockId> = HashSet::new();
    if entry >= blocks.len() || entry == avoid {
        return reached;
    }
    walk_reachable(blocks, entry, avoid, &mut reached);
    reached
}

fn walk_reachable(blocks: &[Block], bid: BlockId, avoid: BlockId, reached: &mut HashSet<BlockId>) {
    if bid >= blocks.len() || bid == avoid || !reached.insert(bid) {
        return;
    }
    match &blocks[bid].exit {
        BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        BlockExit::Jump(target) => {
            walk_reachable(blocks, *target, avoid, reached);
        }
        BlockExit::FallThrough => {
            walk_reachable(blocks, bid + 1, avoid, reached);
        }
        BlockExit::CondJump {
            fall_through,
            target,
        } => {
            walk_reachable(blocks, *fall_through, avoid, reached);
            walk_reachable(blocks, *target, avoid, reached);
        }
    }
}

/// Jump targets reachable from `bid`, following all edge types transitively.
/// `visited` guards against backward-edge loops.
fn collect_branch_exits(
    blocks: &[Block],
    bid: BlockId,
    targets: &mut HashSet<BlockId>,
    visited: &mut HashSet<BlockId>,
) {
    if bid >= blocks.len() || !visited.insert(bid) {
        return;
    }
    match &blocks[bid].exit {
        BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        BlockExit::Jump(target) => {
            targets.insert(*target);
            collect_branch_exits(blocks, *target, targets, visited);
        }
        BlockExit::FallThrough => {
            collect_branch_exits(blocks, bid + 1, targets, visited);
        }
        BlockExit::CondJump {
            fall_through,
            target,
        } => {
            collect_branch_exits(blocks, *fall_through, targets, visited);
            collect_branch_exits(blocks, *target, targets, visited);
        }
    }
}
