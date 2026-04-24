use super::super::decode::{BcStatement, StmtKind};
use super::super::BLOCK_CLOSE;
use super::region::{adopt_children, insert_child_sorted, IfBlock, Region, RegionKind};
use std::collections::HashSet;

/// Build a region tree from detected if-blocks. Each becomes IfThen +
/// optional Else. Overlapping blocks are skipped and emitted as guards.
pub(super) fn build_region_tree(
    num_stmts: usize,
    if_blocks: &[IfBlock],
    skip: &mut HashSet<usize>,
) -> Region {
    let mut root = Region::new(RegionKind::Root, 0, num_stmts);

    // (if_idx asc, effective_end desc) so outer blocks insert first.
    let mut order: Vec<usize> = (0..if_blocks.len()).collect();
    order.sort_by(|&a, &b| {
        let a_blk = &if_blocks[a];
        let b_blk = &if_blocks[b];
        let a_end = a_blk
            .else_close_idx
            .or(a_blk.end_idx)
            .unwrap_or(a_blk.target_idx);
        let b_end = b_blk
            .else_close_idx
            .or(b_blk.end_idx)
            .unwrap_or(b_blk.target_idx);
        a_blk.if_idx.cmp(&b_blk.if_idx).then(b_end.cmp(&a_end))
    });

    for &blk_idx in &order {
        let blk = &if_blocks[blk_idx];
        let effective_end = blk.else_close_idx.or(blk.end_idx).unwrap_or(blk.target_idx);

        if blk.target_idx <= blk.if_idx + 1 {
            continue; // empty true-branch
        }

        if insert_if_block(&mut root, blk, effective_end, skip) {
            skip.insert(blk.if_idx);
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }
        }
    }

    root
}

/// Convert an existing Else region starting at `blk.if_idx` into ElseIf,
/// returning true if the conversion happened.
fn try_convert_to_else_if(
    region: &mut Region,
    blk: &IfBlock,
    cond_text: &str,
    skip: &mut HashSet<usize>,
) -> bool {
    let then_start = blk.if_idx + 1;
    let then_end = blk.target_idx;

    for (ci, child) in region.children.iter().enumerate() {
        if matches!(child.kind, RegionKind::Else) && child.start == blk.if_idx {
            skip.insert(blk.if_idx);
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }

            let child = &mut region.children[ci];
            if blk.end_idx.is_some() {
                // With else: shrink to ElseIf body and add a new Else sibling.
                child.kind = RegionKind::ElseIf(cond_text.to_string());
                child.end = then_end.max(then_start);

                let else_start = blk.target_idx;
                let else_end = blk.else_close_idx.or(blk.end_idx).unwrap_or(blk.target_idx);
                if else_end > else_start {
                    let else_region = Region::new(RegionKind::Else, else_start, else_end);
                    insert_child_sorted(region, else_region);
                }
            } else {
                child.kind = RegionKind::ElseIf(cond_text.to_string());
                child.end = blk.target_idx;
            }
            return true;
        }
    }
    false
}

/// Insert an if-block into the deepest containing region. Returns `false`
/// on partial overlap so the block is demoted to a guard.
fn insert_if_block(
    region: &mut Region,
    blk: &IfBlock,
    effective_end: usize,
    skip: &mut HashSet<usize>,
) -> bool {
    let if_start = blk.if_idx;

    if if_start < region.start || effective_end > region.end {
        return false;
    }

    // `blk.cond` is the raw `if !(cond) jump` condition. Bytecode jumps when
    // NOT cond, so the true-branch runs when cond IS true: no negation.
    let cond_text = blk.cond.clone();

    let then_start = blk.if_idx + 1;
    // Include the exit jump in IfThen (it's skipped anyway) so nested
    // if-blocks whose else extends up to the exit jump still fit.
    let then_end = blk.target_idx;

    // Else-if check runs before recursion: if our `if_idx` starts an existing
    // Else in this region, convert it in place rather than recursing into it.
    if try_convert_to_else_if(region, blk, &cond_text, skip) {
        return true;
    }

    for child in &mut region.children {
        if if_start >= child.start && effective_end <= child.end {
            return insert_if_block(child, blk, effective_end, skip);
        }
    }

    for child in &region.children {
        let overlaps = if_start < child.end && effective_end > child.start;
        let contains = if_start <= child.start && effective_end >= child.end;
        if overlaps && !contains {
            return false;
        }
    }

    let then_region = Region::new(
        RegionKind::IfThen(cond_text),
        then_start,
        then_end.max(then_start),
    );
    let then_region = adopt_children(region, then_region);
    insert_child_sorted(region, then_region);

    if blk.end_idx.is_some() {
        let else_start = blk.target_idx;
        let else_end = blk.else_close_idx.or(blk.end_idx).unwrap_or(blk.target_idx);
        if else_end > else_start {
            let else_region = Region::new(RegionKind::Else, else_start, else_end);
            let else_region = adopt_children(region, else_region);
            insert_child_sorted(region, else_region);
        }
    }

    true
}

/// Detect brace-delimited blocks (while/for loops emitted by `flow.rs`) by
/// stack-matching `ends_with(" {")` to `== BLOCK_CLOSE`.
fn detect_brace_blocks(stmts: &[BcStatement]) -> Vec<(usize, usize)> {
    let mut stack: Vec<usize> = Vec::new();
    let mut blocks: Vec<(usize, usize)> = Vec::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        if stmt.text.ends_with(" {") {
            stack.push(idx);
        } else if stmt.text == BLOCK_CLOSE {
            if let Some(open_idx) = stack.pop() {
                blocks.push((open_idx, idx));
            }
        }
    }
    blocks
}

/// Insert detected brace blocks as Loop regions. Recursive descent so loops
/// nested inside if-blocks or other loops land at the correct depth.
pub(super) fn insert_brace_blocks(
    root: &mut Region,
    stmts: &[BcStatement],
    skip: &mut HashSet<usize>,
) {
    let brace_blocks = detect_brace_blocks(stmts);
    for (open_idx, close_idx) in brace_blocks {
        insert_loop_region(root, stmts, open_idx, close_idx, skip);
    }
}

/// Insert a single loop region into the deepest containing region.
fn insert_loop_region(
    region: &mut Region,
    stmts: &[BcStatement],
    open_idx: usize,
    close_idx: usize,
    skip: &mut HashSet<usize>,
) -> bool {
    let body_start = open_idx + 1;
    let body_end = close_idx;

    if body_start >= body_end {
        return false;
    }

    if open_idx < region.start || close_idx >= region.end {
        return false;
    }

    for child in &mut region.children {
        if open_idx >= child.start && close_idx < child.end {
            return insert_loop_region(child, stmts, open_idx, close_idx, skip);
        }
    }

    let overlaps = region.children.iter().any(|child| {
        let ov = body_start < child.end && body_end > child.start;
        let contains = body_start <= child.start && body_end >= child.end;
        ov && !contains
    });
    if overlaps {
        return false;
    }

    let header = stmts[open_idx].text.clone();
    let loop_region = Region::new(RegionKind::Loop(header), body_start, body_end);
    let loop_region = adopt_children(region, loop_region);
    insert_child_sorted(region, loop_region);
    skip.insert(open_idx);
    skip.insert(close_idx);
    true
}

/// Convert guard statements (`pop_flow_if_not`, unresolvable `if_jump`) into
/// IfThen regions wrapping the rest of the scope. Matches the Blueprint
/// Branch-node true-pin shape instead of `if (!cond) return` guards;
/// consecutive guards nest naturally.
pub(super) fn insert_guard_regions(
    region: &mut Region,
    stmts: &[BcStatement],
    skip: &mut HashSet<usize>,
) {
    // Bottom-up: resolve inner guards before outer adopts them.
    for child in &mut region.children {
        insert_guard_regions(child, stmts, skip);
    }

    let mut guards: Vec<(usize, String)> = Vec::new();
    for idx in region.start..region.end {
        if idx >= stmts.len() || skip.contains(&idx) {
            continue;
        }
        let in_child = region
            .children
            .iter()
            .any(|c| idx >= c.start && idx < c.end);
        if in_child {
            continue;
        }

        // pop_flow_if_not / continue_if_not: exit or skip-iteration when
        // COND is false; body runs when true (matches Branch true-pin).
        if let Some(cond) = stmts[idx].pop_flow_if_not_cond() {
            guards.push((idx, cond.to_string()));
        } else if let Some(cond) = stmts[idx].continue_if_not_cond() {
            guards.push((idx, cond.to_string()));
        } else if let Some((cond, _)) = stmts[idx].if_jump() {
            // Unresolvable if_jump: same semantics.
            guards.push((idx, cond.to_string()));
        }
    }

    // Right-to-left so inner guards nest inside outer ones.
    for (guard_idx, cond) in guards.into_iter().rev() {
        let body_start = guard_idx + 1;
        if body_start >= region.end {
            continue;
        }

        skip.insert(guard_idx);

        let guard_region = Region::new(RegionKind::IfThen(cond), body_start, region.end);
        let guard_region = adopt_children(region, guard_region);
        insert_child_sorted(region, guard_region);
    }
}

/// Mark push_flow and jump_computed statements for skipping during emission.
pub(super) fn suppress_flow_opcodes(stmts: &[BcStatement], skip: &mut HashSet<usize>) {
    for (i, stmt) in stmts.iter().enumerate() {
        if stmt.push_flow_target().is_some() || matches!(stmt.kind, StmtKind::JumpComputed) {
            skip.insert(i);
        }
    }
}
