//! Top-level reordering: Sequence/ForLoop body splicing and CFG linearization,
//! with a pre-pass that rewrites UE cast-failure back-edges to forward jumps.

use super::super::cfg::{linearize_blocks, BlockCfg};
use super::super::decode::BcStatement;
use super::super::{OffsetMap, JUMP_OFFSET_TOLERANCE, SEQUENCE_MARKER_PREFIX};
use super::emit::emit_reordered;
use super::loops::{detect_for_loops, detect_grouped_sequences, detect_interleaved_sequences};
use super::parsers::{parse_if_jump, parse_jump};

/// Reorder bytecode statements to place sequence/loop bodies in logical execution order.
pub fn reorder_flow_patterns(stmts: &[BcStatement]) -> Vec<BcStatement> {
    if stmts.is_empty() {
        return Vec::new();
    }

    let offset_map = OffsetMap::build(stmts);
    let mut used = vec![false; stmts.len()];

    let mut sequences = detect_grouped_sequences(stmts, &offset_map);
    detect_interleaved_sequences(stmts, &used, &offset_map, &mut sequences);
    let loops = detect_for_loops(stmts, &sequences, &offset_map);

    if sequences.is_empty() && loops.is_empty() {
        return stmts.to_vec();
    }

    emit_reordered(stmts, &sequences, &loops, &mut used, &offset_map)
}

/// Reorder bytecode so if/else branches use forward jumps: build a basic-block
/// CFG, linearize via recursive DFS placing true-bodies before false-bodies.
/// Convergence blocks (shared code targeted by multiple paths) stay in place
/// as `goto` labels handled by `structure_bytecode::extract_convergence`.
pub fn reorder_convergence(stmts: &mut Vec<BcStatement>) {
    if stmts.len() < 4 {
        return;
    }

    // Pre-pass: resolve degenerate back-edges. Each call rewrites at most one
    // back-edge; bounded by stmts.len() to guard against infinite loops from
    // buggy rewrites (each real pass removes a statement).
    let max_iterations = stmts.len();
    let mut iter_count = 0;
    loop {
        let offset_map = OffsetMap::build(stmts);
        if !resolve_degenerate_backedge(stmts, &offset_map) {
            break;
        }
        iter_count += 1;
        if iter_count >= max_iterations {
            break;
        }
    }

    let offset_map = OffsetMap::build(stmts);
    let has_backward = stmts.iter().enumerate().any(|(i, stmt)| {
        parse_jump(&stmt.text)
            .and_then(|t| offset_map.find_fuzzy(t, JUMP_OFFSET_TOLERANCE))
            .is_some_and(|ti| ti < i)
    });
    if !has_backward {
        return;
    }

    // Skip linearization for functions with sequence markers: Sequences are
    // split and structured per-body by `structure_statements`, so backward
    // jumps inside Sequences are already handled. Linearizing the whole
    // function would break the sequence/cascade prefix layout that
    // `fold_cascade_across_sequences` depends on, and regresses VRPlayer
    // ReceiveTick on the ubergraph pipeline (see `docs/pipeline-coupling-audit.md`
    // point #2: tried and reverted).
    let has_sequences = stmts
        .iter()
        .any(|s| s.text.starts_with(SEQUENCE_MARKER_PREFIX));
    if has_sequences {
        return;
    }

    let mut cfg = BlockCfg::build(stmts, &offset_map);
    if cfg.blocks.is_empty() {
        return;
    }

    let in_degree = cfg.compute_in_degree();
    let predecessors = cfg.compute_predecessors();
    let blocks = &mut cfg.blocks;

    let mut output: Vec<BcStatement> = Vec::with_capacity(stmts.len() + 8);
    linearize_blocks(blocks, stmts, &in_degree, &predecessors, 0, &mut output);
    // Sweep unemitted blocks (convergence points, unreachable code).
    for bid in 0..blocks.len() {
        linearize_blocks(blocks, stmts, &in_degree, &predecessors, bid, &mut output);
    }

    *stmts = output;
}

/// Resolve UE cast-failure back-edge loops: `$var = false; jump backward to
/// if !($var)`. At runtime the condition-set-to-false falls through to the
/// else target; rewrite to a direct forward jump to that target.
fn resolve_degenerate_backedge(stmts: &mut Vec<BcStatement>, offset_map: &OffsetMap) -> bool {
    let find_idx =
        |target: usize| -> Option<usize> { offset_map.find_fuzzy(target, JUMP_OFFSET_TOLERANCE) };

    for (bj_idx, stmt) in stmts.iter().enumerate() {
        let Some(target) = parse_jump(&stmt.text) else {
            continue;
        };
        let Some(target_idx) = find_idx(target) else {
            continue;
        };
        if target_idx >= bj_idx {
            continue; // not backward
        }

        // Target must be `if !(VAR) jump ELSE_TARGET`.
        let Some((cond, else_target)) = parse_if_jump(&stmts[target_idx].text) else {
            continue;
        };

        // Prior statement must set the same VAR to false (so `!false = true`
        // is taken on the next iteration).
        if bj_idx == 0 {
            continue;
        }
        let prev = stmts[bj_idx - 1].text.trim();
        let matches = prev.strip_suffix(" = false").is_some_and(|var| var == cond);
        if !matches {
            continue;
        }

        // Replace assignment + backward jump with a single forward jump.
        stmts[bj_idx - 1].text = format!("jump 0x{:x}", else_target);
        stmts.remove(bj_idx);
        return true;
    }
    false
}
