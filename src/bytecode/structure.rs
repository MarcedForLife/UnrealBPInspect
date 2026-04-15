//! If/else block structuring: reconstructs control flow from flat jump patterns.
//!
//! Takes the reordered statement list from [`super::flow`] and builds structured
//! if/else/while blocks by matching `jump_if_not` + `push_flow` pairs, detecting
//! else branches via unconditional jumps, and handling nested blocks through a region
//! tree. Post-processing converts remaining `goto` to `break` where applicable and
//! extracts convergence code shared by multiple branches.

use super::decode::BcStatement;
use super::flow::{
    find_first_unmatched_pop, flow_depth, parse_continue_if_not, parse_if_jump, parse_jump,
    parse_jump_computed, parse_pop_flow_if_not, parse_push_flow,
};
use super::{POP_FLOW, RETURN_NOP};
use crate::helpers::{closes_block, is_loop_header, opens_block, SECTION_SEPARATOR};
use std::collections::{HashMap, HashSet};

/// Indentation string per nesting level (4 spaces).
const INDENT: &str = "    ";

/// Fuzzy offset tolerance for jump target resolution. Wider than the base
/// JUMP_OFFSET_TOLERANCE (4) because structure runs after flow reordering,
/// where two adjacent FName adjustments can compound.
const STRUCTURE_OFFSET_TOLERANCE: usize = 8;

/// Negate a condition string for if/else inversion.
///
/// Three cases:
/// - `!X` -> `X` (strip simple negation, but only if X has no spaces/operators)
/// - `!(expr)` -> `expr` (strip negated parens, but only if parens are balanced)
/// - Otherwise -> `!(cond)` (wraps compound conditions to preserve precedence)
///
/// The wrapping is critical: `!A && B` means `(!A) && B`, not `!(A && B)`,
/// so compound conditions must get `!()` not just `!` prefix.
#[cfg(test)]
fn negate_cond(cond: &str) -> String {
    // Already negated simple expr: !X -> X
    if cond.starts_with('!') && !cond.starts_with("!(") {
        let rest = &cond[1..];
        // Only strip if rest has no top-level operators (it's a simple !ident)
        if !rest.contains(' ') {
            return rest.to_string();
        }
    }
    // Already negated parenthesized expr: !(X) -> X
    if cond.starts_with("!(") {
        if let Some(inner) = cond.strip_prefix("!(").and_then(|s| s.strip_suffix(')')) {
            // Verify parens are balanced (the stripped ')' is the matching one)
            let mut depth = 0i32;
            let balanced = inner.chars().all(|ch| {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                depth >= 0
            }) && depth == 0;
            if balanced {
                return inner.to_string();
            }
        }
    }
    // Check if condition has infix operators at paren depth 0 (needs wrapping)
    let mut depth = 0i32;
    let bytes = cond.as_bytes();
    let mut has_infix = false;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' if depth == 0 && i > 0 && i + 1 < bytes.len() => {
                has_infix = true;
                break;
            }
            _ => {}
        }
    }
    if has_infix {
        format!("!({})", cond)
    } else {
        format!("!{}", cond)
    }
}

#[derive(Debug, Clone)]
enum RegionKind {
    Root,
    IfThen(String),
    Else,
    ElseIf(String),
    Loop(String),
}

#[derive(Debug, Clone)]
struct Region {
    kind: RegionKind,
    /// Statement index range [start, end), inclusive start, exclusive end
    start: usize,
    end: usize,
    /// Ordered child regions (non-overlapping, contained within [start, end))
    children: Vec<Region>,
}

impl Region {
    fn new(kind: RegionKind, start: usize, end: usize) -> Self {
        Region {
            kind,
            start,
            end,
            children: Vec::new(),
        }
    }
}

struct IfBlock {
    /// Statement index of the `if !(cond) jump` instruction.
    if_idx: usize,
    cond: String,
    /// Where the false branch starts (the jump target).
    target_idx: usize,
    /// Unconditional jump at the end of the true branch (to skip the else). None if no else.
    jump_idx: Option<usize>,
    /// Statement index where both branches converge.
    end_idx: Option<usize>,
    /// If the else block has an early exit jump, the statement after that jump.
    /// Used to avoid the else engulfing subsequent code in nested patterns.
    else_close_idx: Option<usize>,
}

/// Track block types for pop_flow -> break/return disambiguation
#[derive(Clone, Copy, PartialEq)]
enum BlockType {
    If,
    Loop,
}

fn in_loop(stack: &[BlockType]) -> bool {
    stack.iter().rev().any(|b| *b == BlockType::Loop)
}

/// Shared context for `emit_stmts_range` and `emit_region_tree` to reduce parameter passing.
struct EmitCtx<'a> {
    stmts: &'a [BcStatement],
    skip: &'a HashSet<usize>,
    label_targets: &'a HashMap<usize, String>,
    pending_labels: &'a HashMap<usize, String>,
    label_at: &'a HashMap<usize, &'a String>,
    is_ubergraph: bool,
    find_target_idx_or_end: &'a dyn Fn(usize) -> Option<usize>,
}

/// Build a region tree from detected if-blocks.
///
/// Each if-block becomes IfThen + optional Else regions. Overlapping blocks
/// are skipped (emitted as guards during output).
fn build_region_tree(num_stmts: usize, if_blocks: &[IfBlock], skip: &mut HashSet<usize>) -> Region {
    let mut root = Region::new(RegionKind::Root, 0, num_stmts);

    // Sort if-blocks by (if_idx, effective_end descending) so outer blocks
    // are inserted before inner ones
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
        a_blk.if_idx.cmp(&b_blk.if_idx).then(b_end.cmp(&a_end)) // larger span first
    });

    for &blk_idx in &order {
        let blk = &if_blocks[blk_idx];
        let effective_end = blk.else_close_idx.or(blk.end_idx).unwrap_or(blk.target_idx);

        // Skip degenerate blocks (empty true-branch)
        if blk.target_idx <= blk.if_idx + 1 {
            continue;
        }

        // Try to insert this if-block into the tree
        if insert_if_block(&mut root, blk, effective_end, skip) {
            // Mark the if-jump statement for skip
            skip.insert(blk.if_idx);
            // Mark the unconditional jump at end of true-branch for skip
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }
        }
    }

    root
}

/// Check if this if-block should become an else-if by converting an existing Else
/// region that starts at the same index. Returns true if conversion was done.
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
            // Found an Else that starts at our if_idx; convert to ElseIf
            skip.insert(blk.if_idx);
            if let Some(ji) = blk.jump_idx {
                skip.insert(ji);
            }

            let child = &mut region.children[ci];
            if blk.end_idx.is_some() {
                // Has else: shrink this region to ElseIf body, add new Else sibling
                child.kind = RegionKind::ElseIf(cond_text.to_string());
                child.end = then_end.max(then_start);

                let else_start = blk.target_idx;
                let else_end = blk.else_close_idx.or(blk.end_idx).unwrap_or(blk.target_idx);
                if else_end > else_start {
                    let else_region = Region::new(RegionKind::Else, else_start, else_end);
                    insert_child_sorted(region, else_region);
                }
            } else {
                // No else: just convert Else to ElseIf, adjust end
                child.kind = RegionKind::ElseIf(cond_text.to_string());
                child.end = blk.target_idx;
            }
            return true;
        }
    }
    false
}

/// Try to insert an if-block as children of the deepest containing region.
/// Returns true if inserted, false if overlapping (demoted to guard).
fn insert_if_block(
    region: &mut Region,
    blk: &IfBlock,
    effective_end: usize,
    skip: &mut HashSet<usize>,
) -> bool {
    let if_start = blk.if_idx;

    // Range that this if-block needs to fit within
    if if_start < region.start || effective_end > region.end {
        return false;
    }

    // blk.cond is the raw condition from parse_if_jump("if !(cond) jump").
    // The bytecode means "if NOT cond, jump past true-block", so the true-block
    // executes when cond IS true. Use blk.cond directly (no negation).
    let cond_text = blk.cond.clone();

    let then_start = blk.if_idx + 1;
    // Include the exit jump in the IfThen region (it's in the skip set
    // and won't be emitted). This allows nested if-blocks whose else
    // extends up to the exit jump to fit within the region.
    let then_end = blk.target_idx;

    // Check if this is an else-if chain BEFORE recursing into children.
    // If our if_idx is the start of an existing Else region in this region's
    // children, convert that Else to ElseIf (don't recurse into it).
    if try_convert_to_else_if(region, blk, &cond_text, skip) {
        return true;
    }

    // Try to insert into the deepest child that fully contains our range
    for child in &mut region.children {
        if if_start >= child.start && effective_end <= child.end {
            return insert_if_block(child, blk, effective_end, skip);
        }
    }

    // Check if our range [if_start, effective_end) partially overlaps any child
    for child in &region.children {
        let overlaps = if_start < child.end && effective_end > child.start;
        let contains = if_start <= child.start && effective_end >= child.end;
        if overlaps && !contains {
            return false;
        }
    }

    // Normal insertion: create IfThen + optional Else
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

/// Move children of `parent` that fall within `new_region` into `new_region.children`.
fn adopt_children(parent: &mut Region, mut new_region: Region) -> Region {
    let mut adopted = Vec::new();
    let mut kept = Vec::new();
    for child in parent.children.drain(..) {
        if child.start >= new_region.start && child.end <= new_region.end {
            adopted.push(child);
        } else {
            kept.push(child);
        }
    }
    parent.children = kept;
    new_region.children.extend(adopted);
    new_region
        .children
        .sort_by_key(|c| (c.start, std::cmp::Reverse(c.end)));
    new_region
}

/// Insert a child region maintaining sorted order by start index.
fn insert_child_sorted(parent: &mut Region, child: Region) {
    let pos = parent.children.partition_point(|c| c.start < child.start);
    parent.children.insert(pos, child);
}

/// Resolve an unconditional jump to a display string, or None to suppress.
fn resolve_jump_line(
    ctx: &EmitCtx,
    stmt_idx: usize,
    target: usize,
    in_loop: bool,
) -> Option<String> {
    if let Some(target_idx) = (ctx.find_target_idx_or_end)(target) {
        let is_jump_to_end = target_idx >= ctx.stmts.len()
            || (target_idx == ctx.stmts.len() - 1 && ctx.stmts[target_idx].text == RETURN_NOP);
        if is_jump_to_end {
            if in_loop {
                Some("break".to_string())
            } else {
                None
            }
        } else if let Some(goto_text) = ctx.label_targets.get(&stmt_idx) {
            Some(goto_text.clone())
        } else {
            Some(ctx.stmts[stmt_idx].text.clone())
        }
    } else if in_loop {
        Some("break".to_string())
    } else {
        None
    }
}

/// Emit flat (unindented) statements in range [from, to).
/// Indentation is applied later by `apply_indentation`.
fn emit_stmts_range(
    ctx: &EmitCtx,
    from: usize,
    to: usize,
    block_stack: &[BlockType],
    output: &mut Vec<String>,
) {
    for i in from..to {
        if i >= ctx.stmts.len() {
            break;
        }

        // Inject pending labels
        if let Some(lbl) = ctx.pending_labels.get(&i) {
            output.push(format!("{}:", lbl));
        }

        if let Some(label) = ctx.label_at.get(&i) {
            if ctx.is_ubergraph
                && !output.is_empty()
                && !output.iter().any(|l| l.starts_with(SECTION_SEPARATOR))
            {
                let has_content = output.iter().any(|l| {
                    let trimmed = l.trim();
                    !trimmed.is_empty() && trimmed != "return"
                });
                if has_content {
                    output.insert(0, "--- (latent resume) ---".to_string());
                }
            }
            output.push(format!("--- {} ---", label));
        }

        if ctx.skip.contains(&i) {
            continue;
        }

        let stmt = &ctx.stmts[i];

        if stmt.text == POP_FLOW {
            let keyword = if in_loop(block_stack) {
                "break"
            } else {
                "return"
            };
            // UE ForEach-with-break emits multiple pop_flow to unwind the
            // flow stack. Only the first one is semantically meaningful.
            let already_breaking = output.last().is_some_and(|l| l.trim() == keyword);
            if !already_breaking {
                output.push(keyword.to_string());
            }
        } else if parse_continue_if_not(&stmt.text).is_some()
            || parse_pop_flow_if_not(&stmt.text).is_some()
            || parse_if_jump(&stmt.text).is_some()
        {
            // Residual guard: insert_guard_regions already consumed mid-scope
            // guards, so anything still here is at the end of its scope with
            // nothing left to wrap. Suppress it.
        } else if let Some(target) = parse_jump(&stmt.text) {
            if let Some(text) = resolve_jump_line(ctx, i, target, in_loop(block_stack)) {
                output.push(text);
            }
        } else {
            let text = if stmt.text == RETURN_NOP {
                "return"
            } else {
                &stmt.text
            };
            output.push(text.to_string());
        }
    }
}

/// Pre-collect jump targets so `emit_stmts_range` can emit `goto LABEL` and inject
/// label definitions. Returns `(label_targets, pending_labels)`:
/// - `label_targets[stmt_idx]` = the `goto ...` text for that jump statement
/// - `pending_labels[target_idx]` = the synthetic label to inject before that statement
fn collect_label_targets(
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
        if let Some(target) = parse_jump(&stmt.text) {
            if let Some(target_idx) = find_target_idx_or_end(target) {
                let is_jump_to_end_label = target_idx >= stmts.len()
                    || (target_idx == stmts.len() - 1 && stmts[target_idx].text == RETURN_NOP);
                if is_jump_to_end_label {
                    // Will be break or omitted
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

/// Whether a statement unconditionally exits the current scope.
fn is_block_exit(text: &str) -> bool {
    text == POP_FLOW || text == RETURN_NOP || text == "return"
}

/// Find the exclusive end index of a block starting at `start`.
///
/// Scans for the first unmatched `pop_flow` or depth-0 `return nop` /
/// `return`, and returns the index after it.
fn find_block_end(stmts: &[BcStatement], start: usize) -> usize {
    let mut depth: i32 = 0;
    for (idx, stmt) in stmts.iter().enumerate().skip(start) {
        if parse_push_flow(&stmt.text).is_some() {
            depth += 1;
        } else if stmt.text == POP_FLOW {
            if depth > 0 {
                depth -= 1;
            } else {
                return idx + 1;
            }
        }
        if depth == 0 && (stmt.text == RETURN_NOP || stmt.text == "return") {
            return idx + 1;
        }
    }
    stmts.len()
}

/// Collect `(if_idx, target_idx)` pairs from if-jump statements, resolving
/// targets through the offset map and skipping pop_flow landing targets.
fn collect_if_jumps(
    stmts: &[BcStatement],
    find: &dyn Fn(usize) -> Option<usize>,
) -> Vec<(usize, usize)> {
    stmts
        .iter()
        .enumerate()
        .filter_map(|(idx, stmt)| {
            let (_, target) = parse_if_jump(&stmt.text)?;
            let mut target_idx = find(target)?;
            if target_idx < stmts.len() && stmts[target_idx].text == POP_FLOW {
                target_idx += 1;
            }
            Some((idx, target_idx))
        })
        .collect()
}

/// Reorder displaced else blocks so nested if/else containment is clean.
///
/// UE bytecode interleaves else blocks when a nested if's false branch gets
/// displaced past the outer if's false branch:
///
/// ```text
///   if !A jump X           (outer if)
///     if !B jump Y         (inner if, nested in A's true body)
///       B-true body
///       pop_flow
///   X: A-false body        (outer else)
///     pop_flow
///   Y: B-false body        (displaced inner else)
/// ```
///
/// Moves the B-false block before the A-false block, restoring proper
/// containment for the region tree. Returns `None` when no reordering
/// is needed.
fn reorder_displaced_else(stmts: &[BcStatement]) -> Option<Vec<BcStatement>> {
    if stmts.len() < 4 {
        return None;
    }

    let tolerance = STRUCTURE_OFFSET_TOLERANCE;
    let mut result: Option<Vec<BcStatement>> = None;

    // One displacement per iteration; repeat until stable.
    loop {
        let working = result.as_deref().unwrap_or(stmts);
        let omap = super::OffsetMap::build(working);
        let wlen = working.len();
        let find =
            |target: usize| -> Option<usize> { omap.find_fuzzy_or_end(target, tolerance, wlen) };
        let jumps = collect_if_jumps(working, &find);

        let mut moved = false;
        'search: for (oi, &(outer_if, outer_target)) in jumps.iter().enumerate() {
            for (ii, &(inner_if, inner_target)) in jumps.iter().enumerate() {
                if oi == ii {
                    continue;
                }
                // Inner if must be inside outer's true body, with its else
                // displaced past the outer's else.
                if inner_if <= outer_if || inner_if >= outer_target || inner_target <= outer_target
                {
                    continue;
                }
                // The inner true body must exit before the outer else
                // (pop_flow or return nop after flow reordering).
                let has_exit = (inner_if + 1..outer_target)
                    .rev()
                    .any(|si| is_block_exit(&working[si].text));
                if !has_exit {
                    continue;
                }
                let inner_else_end = find_block_end(working, inner_target);
                if inner_else_end <= inner_target {
                    continue;
                }

                // Extract the inner else and splice it before the outer else.
                // outer_target < inner_target, so the drain doesn't shift it.
                let mut reordered = working.to_vec();
                let block: Vec<BcStatement> =
                    reordered.drain(inner_target..inner_else_end).collect();
                reordered.splice(outer_target..outer_target, block);
                result = Some(reordered);
                moved = true;
                break 'search;
            }
        }
        if !moved {
            break;
        }
    }

    result
}

/// Convert flat bytecode statements into structured pseudo-code lines (unindented).
///
/// `labels` maps memory offsets to display names (e.g. `--- EventName ---` markers).
///
/// **Condition fidelity:** `&&`/`||` in decoded bytecode are faithful to the original
/// Blueprint (from `BooleanAND`/`BooleanOR` calls inlined by `try_inline_operator`).
/// This pass never merges separate Branch nodes into compound conditions; it only
/// detects if/else blocks from `JumpIfNot` opcodes and chains them into else-if
/// when they share the same end target.
pub fn structure_bytecode(stmts: &[BcStatement], labels: &HashMap<usize, String>) -> Vec<String> {
    if stmts.is_empty() {
        return Vec::new();
    }

    // Fix interleaved else blocks before if-detection (see reorder_displaced_else).
    let owned;
    let stmts = if let Some(reordered) = reorder_displaced_else(stmts) {
        owned = reordered;
        &owned[..]
    } else {
        stmts
    };

    let offset_map = super::OffsetMap::build(stmts);
    let find_target = |target: usize| -> Option<usize> {
        offset_map.find_fuzzy_or_end(target, STRUCTURE_OFFSET_TOLERANCE, stmts.len())
    };

    let label_at: HashMap<usize, &String> = labels
        .iter()
        .filter_map(|(offset, name)| {
            stmts
                .iter()
                .position(|s| s.mem_offset >= *offset)
                .map(|idx| (idx, name))
        })
        .collect();

    let mut skip: HashSet<usize> = HashSet::new();
    let if_blocks = detect_if_blocks(stmts, &find_target);
    suppress_flow_opcodes(stmts, &mut skip);
    let mut region_tree = build_region_tree(stmts.len(), &if_blocks, &mut skip);
    insert_brace_blocks(&mut region_tree, stmts, &mut skip);
    insert_guard_regions(&mut region_tree, stmts, &mut skip);
    let (label_targets, pending_labels) =
        collect_label_targets(stmts, &skip, &label_at, &find_target);

    let is_ubergraph = !labels.is_empty();
    let ctx = EmitCtx {
        stmts,
        skip: &skip,
        label_targets: &label_targets,
        pending_labels: &pending_labels,
        label_at: &label_at,
        is_ubergraph,
        find_target_idx_or_end: &find_target,
    };

    let mut output = Vec::new();
    let mut block_stack: Vec<BlockType> = Vec::new();
    emit_region_tree(&region_tree, &ctx, &mut block_stack, &mut output);

    convert_gotos_to_breaks(&mut output);
    extract_convergence(&mut output);
    collapse_double_else(&mut output);

    output
}

/// Apply indentation based on brace nesting depth.
/// Lines starting with `}` decrement before indenting; lines ending with ` {` increment after.
/// Called once at the end of the pipeline so all intermediate passes work with flat text.
pub fn apply_indentation(lines: &mut [String]) {
    let mut depth = 0usize;
    for line in lines.iter_mut() {
        let trimmed = line.trim().to_string();
        if trimmed.is_empty() {
            continue;
        }

        let closes = trimmed.starts_with('}');
        let opens = opens_block(&trimmed);

        if closes {
            depth = depth.saturating_sub(1);
        }

        *line = if depth > 0 {
            format!("{}{}", INDENT.repeat(depth), trimmed)
        } else {
            trimmed
        };

        if opens {
            depth += 1;
        }
    }
}

/// Detect if/else blocks from `if !(cond) jump` patterns, then truncate false-blocks
/// where an early exit jump targets the convergence point.
fn detect_if_blocks(
    stmts: &[BcStatement],
    find_target: &dyn Fn(usize) -> Option<usize>,
) -> Vec<IfBlock> {
    let mut if_blocks: Vec<IfBlock> = Vec::new();

    for (i, stmt) in stmts.iter().enumerate() {
        let Some((cond, target)) = parse_if_jump(&stmt.text) else {
            continue;
        };
        let Some(mut target_idx) = find_target(target) else {
            continue;
        };

        // A pop_flow can't be the start of a false branch; it's a flow exit.
        // Fuzzy offset resolution sometimes lands on a pop_flow when the actual
        // target is a filtered opcode (wire_trace) between the pop_flow and the
        // next statement. Advance past it.
        if target_idx < stmts.len() && stmts[target_idx].text == POP_FLOW {
            target_idx += 1;
        }

        // Check for an else branch: search backward from the false-branch start
        // for the true-branch's terminating jump or return
        let (jump_idx, end_idx) = detect_else_branch(stmts, i, target_idx, find_target);

        if_blocks.push(IfBlock {
            if_idx: i,
            cond: cond.to_string(),
            target_idx,
            jump_idx,
            end_idx,
            else_close_idx: None,
        });
    }

    // False-block truncation: find early exit jumps within else blocks
    truncate_false_blocks(&mut if_blocks, stmts, find_target);

    if_blocks
}

/// Check whether a `pop_flow` at `pop_idx` is unmatched within `[start, pop_idx)`.
///
/// When the push/pop pairs in the range are balanced (net depth 0), the pop_flow
/// at `pop_idx` is a genuine scope exit, not part of a nested push/pop pair.
fn is_unmatched_pop_flow(stmts: &[BcStatement], start: usize, pop_idx: usize) -> bool {
    flow_depth(stmts, start, pop_idx) == 0
}

/// Find where the false branch ends when the true branch terminates with pop_flow.
///
/// The first `pop_flow` at depth 0 from `start` is the false branch's own exit.
/// Returns exclusive end (pop_flow index + 1) so the pop_flow is included in the
/// else region and emitted as `return`/`break`.
fn find_else_end_by_pop_flow(stmts: &[BcStatement], start: usize) -> usize {
    find_first_unmatched_pop(stmts, start, stmts.len())
        .map(|idx| idx + 1)
        .unwrap_or(stmts.len())
}

/// Check if the true-branch ends with an unconditional jump (else) or return (diverging).
///
/// Searches backward from `target_idx`, skipping only comment/marker lines, to find
/// the true-branch terminator (a jump past the false-branch, or a return).
/// The search is bounded by `if_idx` to avoid crossing into unrelated code.
fn detect_else_branch(
    stmts: &[BcStatement],
    if_idx: usize,
    target_idx: usize,
    find_target: &dyn Fn(usize) -> Option<usize>,
) -> (Option<usize>, Option<usize>) {
    if target_idx == 0 || target_idx > stmts.len() || if_idx >= target_idx {
        return (None, None);
    }

    // Search backward from the false-branch start, skipping only
    // non-executable lines (comments, markers). Stop at the first
    // executable statement.
    let search_start = if_idx + 1;
    for check_idx in (search_start..target_idx).rev() {
        let stmt = &stmts[check_idx];
        let trimmed = stmt.text.trim();

        // Skip comments and markers
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }

        // Unconditional jump past the false-branch: classic if/else skip
        if let Some(end_target) = parse_jump(&stmt.text) {
            if let Some(end_idx) = find_target(end_target) {
                if end_idx >= target_idx {
                    return (Some(check_idx), Some(end_idx));
                }
            }
        }
        // Diverging return: both branches exit independently.
        else if (stmt.text == RETURN_NOP || stmt.text == "return") && target_idx < stmts.len() {
            return (Some(check_idx), Some(stmts.len()));
        }
        // Diverging pop_flow: the true branch exits via pop_flow back to the
        // enclosing push_flow. Safe only when the pop_flow is unmatched (not
        // from a nested push/pop pair within the true body). The else end is
        // found by scanning forward for the false branch's own balanced pop_flow.
        // Unlike the return case, jump_idx stays None so the pop_flow remains
        // visible and emits as return/break in the true branch.
        else if stmt.text == POP_FLOW
            && target_idx < stmts.len()
            && is_unmatched_pop_flow(stmts, if_idx + 1, check_idx)
        {
            let end_idx = find_else_end_by_pop_flow(stmts, target_idx);
            return (None, Some(end_idx));
        }

        // Any other executable statement means no else detected
        break;
    }

    (None, None)
}

/// Scan each else block for an unconditional jump targeting end_idx.
/// When found, set else_close_idx to truncate the else and prevent it
/// from engulfing subsequent code in nested patterns.
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
        // Scan the else block for an early exit jump targeting end_idx, but
        // only at if-nesting depth 0. Jumps inside nested if-blocks are their
        // own branch exits and should not truncate the outer else.
        // Assumes UE bytecode pattern: each if_jump is followed by exactly one
        // unconditional jump (its else-exit) before the next if_jump or body code.
        let mut if_depth = 0usize;
        for (j, stmt) in stmts.iter().enumerate().take(end_idx).skip(blk.target_idx) {
            if parse_if_jump(&stmt.text).is_some() {
                if_depth += 1;
                continue;
            }
            if let Some(jt) = parse_jump(&stmt.text) {
                if if_depth > 0 {
                    if_depth -= 1;
                    continue;
                }
                if find_target(jt) == Some(end_idx) {
                    blk.else_close_idx = Some(j + 1);
                    break;
                }
                // Backward jump to before the else start: control is returning
                // to earlier convergence code, so the else body ends here.
                if let Some(target_idx) = find_target(jt) {
                    if target_idx < blk.target_idx {
                        blk.else_close_idx = Some(j + 1);
                        break;
                    }
                }
            }
            // Return at depth 0 terminates the else block (the branch
            // diverges, so nothing after it belongs to this else).
            if if_depth == 0 && (stmt.text == RETURN_NOP || stmt.text == "return") {
                blk.else_close_idx = Some(j + 1);
                break;
            }
        }
    }
}

/// Mark push_flow and jump_computed statements for skipping during emission.
fn suppress_flow_opcodes(stmts: &[BcStatement], skip: &mut HashSet<usize>) {
    for (i, stmt) in stmts.iter().enumerate() {
        if parse_push_flow(&stmt.text).is_some() || parse_jump_computed(&stmt.text) {
            skip.insert(i);
        }
    }
}

/// Detect brace-delimited blocks (while/for loops from flow.rs) by matching
/// `ends_with(" {")` / `== "}"` pairs with a simple stack.
fn detect_brace_blocks(stmts: &[BcStatement]) -> Vec<(usize, usize)> {
    let mut stack: Vec<usize> = Vec::new();
    let mut blocks: Vec<(usize, usize)> = Vec::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        if stmt.text.ends_with(" {") {
            stack.push(idx);
        } else if stmt.text == "}" {
            if let Some(open_idx) = stack.pop() {
                blocks.push((open_idx, idx));
            }
        }
    }
    blocks
}

/// Insert detected brace blocks as Loop regions into the region tree.
/// Uses recursive descent (like `insert_if_block`) so loops nested inside
/// if-blocks or other loops are placed at the correct depth.
fn insert_brace_blocks(root: &mut Region, stmts: &[BcStatement], skip: &mut HashSet<usize>) {
    let brace_blocks = detect_brace_blocks(stmts);
    for (open_idx, close_idx) in brace_blocks {
        insert_loop_region(root, stmts, open_idx, close_idx, skip);
    }
}

/// Try to insert a single loop region into the deepest containing region.
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

    // Must fit within this region
    if open_idx < region.start || close_idx >= region.end {
        return false;
    }

    // Try to insert into a child that fully contains the range
    for child in &mut region.children {
        if open_idx >= child.start && close_idx < child.end {
            return insert_loop_region(child, stmts, open_idx, close_idx, skip);
        }
    }

    // Check for partial overlap with existing children
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
/// IfThen regions that wrap the remaining scope.
///
/// This produces output closer to the Blueprint graph where a Branch node's
/// true pin leads into the body, rather than the inverted `if (!cond) return`
/// guard style. Consecutive guards nest naturally: each wraps everything
/// after it in the current scope.
fn insert_guard_regions(region: &mut Region, stmts: &[BcStatement], skip: &mut HashSet<usize>) {
    // Process children first (bottom-up) so inner guards are resolved
    // before outer ones adopt them
    for child in &mut region.children {
        insert_guard_regions(child, stmts, skip);
    }

    // Collect guard positions in this region's gaps (not inside children, not skipped)
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

        // pop_flow_if_not(COND) / continue_if_not(COND): exit scope or skip
        // iteration when COND is false. The body runs when true, matching the
        // Blueprint Branch node's true-pin path.
        if let Some(cond) = parse_pop_flow_if_not(&stmts[idx].text) {
            guards.push((idx, cond.to_string()));
        } else if let Some(cond) = parse_continue_if_not(&stmts[idx].text) {
            guards.push((idx, cond.to_string()));
        }
        // Unresolvable if_jump: same semantics (not consumed by if-block detection)
        else if let Some((cond, _)) = parse_if_jump(&stmts[idx].text) {
            guards.push((idx, cond.to_string()));
        }
    }

    // Process right to left: inner guards get nested inside outer ones
    for (guard_idx, cond) in guards.into_iter().rev() {
        let body_start = guard_idx + 1;
        if body_start >= region.end {
            continue; // guard at end of scope, nothing to wrap
        }

        skip.insert(guard_idx);

        let guard_region = Region::new(RegionKind::IfThen(cond), body_start, region.end);
        let guard_region = adopt_children(region, guard_region);
        insert_child_sorted(region, guard_region);
    }
}

/// Emit the region tree as flat (unindented) text. Braces are emitted for
/// if/else/loop blocks; `apply_indentation` assigns depth afterward.
#[allow(clippy::ptr_arg)] // push/pop needed on block_stack
fn emit_region_tree(
    region: &Region,
    ctx: &EmitCtx,
    block_stack: &mut Vec<BlockType>,
    output: &mut Vec<String>,
) {
    // Emit opening
    match &region.kind {
        RegionKind::Root => {}
        RegionKind::IfThen(cond) => {
            output.push(format!("if ({}) {{", cond));
            block_stack.push(BlockType::If);
        }
        RegionKind::Else => {
            output.push("} else {".to_string());
        }
        RegionKind::ElseIf(cond) => {
            output.push(format!("}} else if ({}) {{", cond));
        }
        RegionKind::Loop(header) => {
            output.push(header.clone());
            block_stack.push(BlockType::Loop);
        }
    }

    // Emit body: walk [start, end), recursing into children
    let mut pos = region.start;

    let children = &region.children;
    let mut child_idx = 0;
    while child_idx < children.len() {
        let child = &children[child_idx];

        // Emit statements [pos, child.start)
        emit_stmts_range(ctx, pos, child.start, block_stack, output);

        emit_region_tree(child, ctx, block_stack, output);
        pos = child.end;
        child_idx += 1;

        if matches!(child.kind, RegionKind::IfThen(_)) {
            // Collect Else/ElseIf siblings that form an if/else chain
            while child_idx < children.len() {
                let next = &children[child_idx];
                if !matches!(next.kind, RegionKind::Else | RegionKind::ElseIf(_)) {
                    break;
                }
                emit_stmts_range(ctx, pos, next.start, block_stack, output);
                emit_region_tree(next, ctx, block_stack, output);
                pos = next.end;
                child_idx += 1;
            }
        }

        // IfThen and Loop both open a block that needs closing
        if matches!(child.kind, RegionKind::IfThen(_) | RegionKind::Loop(_)) {
            output.push("}".to_string());
            block_stack.pop();
        }
    }

    // Emit remaining statements [pos, end)
    emit_stmts_range(ctx, pos, region.end, block_stack, output);
}

/// Convert `goto LABEL` to `break` (in loop context) or remove (outside loop) when
/// the label sits near a closing brace or end-of-output. Cleans up orphaned labels
/// that no longer have matching gotos.
fn convert_gotos_to_breaks(output: &mut Vec<String>) {
    let break_labels = find_break_labels(output);
    if break_labels.is_empty() {
        return;
    }
    rewrite_gotos(output, &break_labels);
    remove_orphaned_labels(output, &break_labels);
}

/// A label is "break-able" if it sits right after a closing `}` or near the end of output
/// (only empty lines, returns, or braces follow it).
fn find_break_labels(output: &[String]) -> HashSet<String> {
    let mut labels = HashSet::new();
    for (i, line) in output.iter().enumerate() {
        let trimmed = line.trim();
        if !trimmed.ends_with(':')
            || trimmed.starts_with(SECTION_SEPARATOR)
            || trimmed.starts_with("//")
        {
            continue;
        }
        let label = &trimmed[..trimmed.len() - 1];
        let after_brace = output[..i]
            .iter()
            .rev()
            .find(|l| !l.trim().is_empty())
            .is_some_and(|l| l.trim() == "}");
        let near_end = output[i + 1..].iter().all(|l| {
            let trimmed = l.trim();
            trimmed.is_empty() || trimmed == "return" || trimmed == "}"
        });
        if after_brace || near_end {
            labels.insert(label.to_string());
        }
    }
    labels
}

/// Replace `goto LABEL` with `break` (in loop context) or remove (outside loop).
/// Uses backward brace scanning to detect enclosing loops.
fn rewrite_gotos(output: &mut [String], break_labels: &HashSet<String>) {
    for i in 0..output.len() {
        let trimmed = output[i].trim().to_string();
        let Some(label) = trimmed.strip_prefix("goto ") else {
            continue;
        };
        if !break_labels.contains(label) {
            continue;
        }
        // Scan backward through braces to find the enclosing block opener
        let in_loop = {
            let mut depth = 0i32;
            output[..i].iter().rev().any(|line| {
                let ltrim = line.trim();
                if closes_block(ltrim) {
                    depth += 1; // going backward, closing brace increases depth
                }
                if opens_block(ltrim) {
                    if depth == 0 {
                        // Found the enclosing block opener
                        return is_loop_header(ltrim);
                    }
                    depth -= 1;
                }
                false
            })
        };
        if in_loop {
            output[i] = "break".to_string();
        } else {
            output[i] = String::new();
        }
    }
}

/// Remove empty lines from goto removal, then remove labels that no longer have matching gotos.
fn remove_orphaned_labels(output: &mut Vec<String>, break_labels: &HashSet<String>) {
    output.retain(|line| !line.is_empty());
    let remaining_gotos: HashSet<String> = output
        .iter()
        .filter_map(|l| l.trim().strip_prefix("goto ").map(|s| s.to_string()))
        .collect();
    output.retain(|line| {
        let trimmed = line.trim();
        if trimmed.ends_with(':')
            && !trimmed.starts_with(SECTION_SEPARATOR)
            && !trimmed.starts_with("//")
        {
            let label = &trimmed[..trimmed.len() - 1];
            if break_labels.contains(label) {
                return remaining_gotos.contains(label);
            }
        }
        true
    });
}

/// Find the extent of convergence code starting at `code_start`.
/// Uses brace depth tracking -- stops when a closing brace exits the current scope.
fn find_convergence_extent(output: &[String], code_start: usize) -> usize {
    let mut depth = 0i32;
    let mut code_end = code_start;
    for (j, line) in output[code_start..].iter().enumerate() {
        let j = j + code_start;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            code_end = j + 1;
            continue;
        }
        // Check for scope exit before processing this line
        if trimmed.starts_with('}') {
            depth -= 1;
            if depth < 0 {
                break;
            }
        }
        if j > code_start
            && trimmed.ends_with(':')
            && !trimmed.starts_with("//")
            && !trimmed.starts_with(SECTION_SEPARATOR)
        {
            break;
        }
        if opens_block(trimmed) {
            depth += 1;
        }
        code_end = j + 1;
    }
    code_end
}

/// Find the closing `}` that exits the scope containing all gotos.
/// Scans forward from after the last goto, tracking brace depth.
fn find_insertion_point(output: &[String], max_goto: usize) -> usize {
    let mut depth = 0i32;
    for (j, line) in output[(max_goto + 1)..].iter().enumerate() {
        let j = j + max_goto + 1;
        let trimmed = line.trim();
        if opens_block(trimmed) {
            depth += 1;
        }
        if closes_block(trimmed) {
            if depth == 0 {
                return j;
            }
            depth -= 1;
        }
    }
    output.len()
}

/// Remove old convergence lines and insert at the new position.
/// All text is flat (unindented); `apply_indentation` handles formatting later.
fn splice_convergence(
    output: &mut Vec<String>,
    label_idx: usize,
    code_range: std::ops::Range<usize>,
    goto_indices: &[usize],
    insert_pos: usize,
    conv_content: Vec<String>,
) {
    let mut to_remove: Vec<usize> = Vec::new();
    to_remove.push(label_idx);
    to_remove.extend(code_range);
    to_remove.extend(goto_indices);
    to_remove.sort();
    to_remove.dedup();

    for &idx in to_remove.iter().rev() {
        if idx < output.len() {
            output.remove(idx);
        }
    }

    let removed_before = to_remove.iter().filter(|&&idx| idx < insert_pos).count();
    let adjusted_pos = insert_pos.saturating_sub(removed_before);

    for (i, content) in conv_content.iter().enumerate() {
        let pos = (adjusted_pos + 1 + i).min(output.len());
        output.insert(pos, content.clone());
    }
}

/// Extract convergence code (shared by multiple branches) and relocate it
/// after the outermost closing brace. Repeats until no candidates remain,
/// since each splice shifts indices.
fn extract_convergence(output: &mut Vec<String>) {
    loop {
        let goto_map = build_goto_map(output);
        let Some((label_name, goto_indices)) = pick_convergence_candidate(&goto_map, output) else {
            break;
        };

        // Find the label and its code block
        let label_text = format!("{}:", label_name);
        let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
            break;
        };
        let code_start = label_idx + 1;
        if code_start >= output.len() {
            break;
        }
        let code_end = find_convergence_extent(output, code_start);
        if code_end <= code_start {
            break;
        }

        // Collect convergence code lines (already flat)
        let conv_content: Vec<String> = output[code_start..code_end].to_vec();

        // Find where to insert: after the `}` that encloses all the gotos
        let max_goto = goto_indices.iter().copied().max().unwrap_or(0);
        let insert_pos = find_insertion_point(output, max_goto);

        splice_convergence(
            output,
            label_idx,
            code_start..code_end,
            &goto_indices,
            insert_pos,
            conv_content,
        );
    }
}

/// Map each goto label to its line indices.
fn build_goto_map(output: &[String]) -> HashMap<String, Vec<usize>> {
    let mut map: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, line) in output.iter().enumerate() {
        if let Some(label) = line.trim().strip_prefix("goto ") {
            map.entry(label.to_string()).or_default().push(i);
        }
    }
    map
}

/// Pick the best convergence candidate: a label targeted by 2+ gotos, or by a single
/// goto that crosses a structural boundary (closing brace between goto and label).
/// Returns the earliest candidate by first goto position.
fn pick_convergence_candidate(
    goto_map: &HashMap<String, Vec<usize>>,
    output: &[String],
) -> Option<(String, Vec<usize>)> {
    let mut candidates: Vec<(String, Vec<usize>)> = goto_map
        .iter()
        .filter(|(label_name, gotos)| {
            if gotos.len() >= 2 {
                return true;
            }
            // Single goto: only a candidate if a structural boundary separates it from the label
            gotos.len() == 1 && has_boundary_between(output, label_name, gotos[0])
        })
        .map(|(name, gotos)| (name.clone(), gotos.clone()))
        .collect();
    if candidates.is_empty() {
        return None;
    }
    candidates.sort_by_key(|(_, gotos)| gotos.iter().copied().min().unwrap_or(usize::MAX));
    Some(candidates.remove(0))
}

/// Check if a closing brace or `} else` appears between a goto and its label.
fn has_boundary_between(output: &[String], label_name: &str, goto_idx: usize) -> bool {
    let label_text = format!("{}:", label_name);
    let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
        return false;
    };
    // A label at the start of an else block isn't a convergence target,
    // it's the else body's entry. Skip single-goto convergence here so
    // extraction doesn't empty the else and destroy its braces.
    if label_idx > 0 && output[label_idx - 1].trim().starts_with("} else") {
        return false;
    }
    let (lo, hi) = if label_idx < goto_idx {
        (label_idx, goto_idx)
    } else {
        (goto_idx, label_idx)
    };
    output[lo + 1..hi].iter().any(|l| {
        let trimmed = l.trim();
        trimmed == "}" || trimmed.starts_with("} else")
    })
}

fn collapse_double_else(output: &mut Vec<String>) {
    loop {
        let mut changed = false;
        let mut i = 0;
        while i + 1 < output.len() {
            let trimmed = output[i].trim();
            let next_trimmed = output[i + 1].trim();

            if trimmed == "} else {" && next_trimmed == "} else {" {
                output.remove(i);
                changed = true;
                continue;
            }

            if trimmed == "} else {" && next_trimmed == "}" {
                output.remove(i);
                output.remove(i);
                changed = true;
                continue;
            }

            i += 1;
        }
        if !changed {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negate_simple_not() {
        assert_eq!(negate_cond("!X"), "X");
    }

    #[test]
    fn negate_parenthesized_not() {
        assert_eq!(negate_cond("!(A && B)"), "A && B");
    }

    #[test]
    fn negate_simple_var() {
        assert_eq!(negate_cond("X"), "!X");
    }

    #[test]
    fn negate_compound() {
        assert_eq!(negate_cond("A && B"), "!(A && B)");
    }

    #[test]
    fn negate_self_member() {
        assert_eq!(negate_cond("!self.GrippingActor"), "self.GrippingActor");
    }

    fn make_stmt(offset: usize, text: &str) -> BcStatement {
        BcStatement::new(offset, text.to_string())
    }

    #[test]
    fn simple_if_block() {
        // if !(cond) jump 0x30 -> negated to "if (cond) {"
        // body
        // return nop
        let stmts = vec![
            make_stmt(0x10, "if !(Cond) jump 0x30"),
            make_stmt(0x20, "DoSomething()"),
            make_stmt(0x30, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        assert!(result.iter().any(|l| l.contains("if (Cond) {")));
        assert!(result.iter().any(|l| l.contains("DoSomething()")));
    }

    #[test]
    fn simple_if_else() {
        // if !(cond) jump 0x30
        // TrueBranch()
        // jump 0x40          (unconditional jump to end)
        // FalseBranch()
        // return nop
        let stmts = vec![
            make_stmt(0x10, "if !(Cond) jump 0x30"),
            make_stmt(0x20, "TrueBranch()"),
            make_stmt(0x28, "jump 0x40"),
            make_stmt(0x30, "FalseBranch()"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("if (Cond) {"));
        assert!(text.contains("TrueBranch()"));
        assert!(text.contains("} else {"));
        assert!(text.contains("FalseBranch()"));
    }

    #[test]
    fn if_else_with_return_terminated_true_body() {
        // if !(cond) jump 0x30
        // TrueBranch()
        // return nop          (true body returns instead of jumping)
        // FalseBranch()       (at jump target)
        // return nop
        let stmts = vec![
            make_stmt(0x10, "if !(Cond) jump 0x30"),
            make_stmt(0x20, "TrueBranch()"),
            make_stmt(0x28, "return nop"),
            make_stmt(0x30, "FalseBranch()"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("if (Cond) {"), "missing if: {}", text);
        assert!(text.contains("TrueBranch()"), "missing true: {}", text);
        assert!(text.contains("} else {"), "missing else: {}", text);
        assert!(text.contains("FalseBranch()"), "missing false: {}", text);
    }

    #[test]
    fn nested_if_blocks() {
        // if !(A) jump 0x50
        //   if !(B) jump 0x40
        //     InnerBody()
        //   OuterAfterInner()
        // return nop
        let stmts = vec![
            make_stmt(0x10, "if !(A) jump 0x50"),
            make_stmt(0x18, "if !(B) jump 0x40"),
            make_stmt(0x20, "InnerBody()"),
            make_stmt(0x40, "OuterAfterInner()"),
            make_stmt(0x50, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("if (A) {"));
        assert!(text.contains("if (B) {"));
        assert!(text.contains("InnerBody()"));
        assert!(text.contains("OuterAfterInner()"));
    }

    #[test]
    fn overlapping_blocks_demoted_to_guard() {
        // Two if-blocks that partially overlap should not crash.
        // The overlapping one becomes a guard.
        let stmts = vec![
            make_stmt(0x10, "if !(A) jump 0x40"),
            make_stmt(0x18, "if !(B) jump 0x50"),
            make_stmt(0x20, "Body()"),
            make_stmt(0x40, "AfterA()"),
            make_stmt(0x50, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        // Should not panic and should produce output
        assert!(!result.is_empty());
    }

    #[test]
    fn if_else_if_chain() {
        // if !(A) jump 0x30
        // TrueA()
        // jump 0x50
        // if !(B) jump 0x50
        // TrueB()
        // return nop
        let stmts = vec![
            make_stmt(0x10, "if !(A) jump 0x30"),
            make_stmt(0x20, "TrueA()"),
            make_stmt(0x28, "jump 0x50"),
            make_stmt(0x30, "if !(B) jump 0x50"),
            make_stmt(0x40, "TrueB()"),
            make_stmt(0x50, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("if (A) {"));
        assert!(text.contains("} else if (B) {"));
        assert!(text.contains("TrueB()"));
    }

    #[test]
    fn region_tree_simple_if() {
        let mut skip = HashSet::new();
        let blocks = vec![IfBlock {
            if_idx: 0,
            cond: "X".to_string(),
            target_idx: 3,
            jump_idx: None,
            end_idx: None,
            else_close_idx: None,
        }];
        let tree = build_region_tree(5, &blocks, &mut skip);
        assert_eq!(tree.children.len(), 1);
        assert!(matches!(tree.children[0].kind, RegionKind::IfThen(_)));
        assert_eq!(tree.children[0].start, 1);
        assert_eq!(tree.children[0].end, 3);
        assert!(skip.contains(&0));
    }

    #[test]
    fn region_tree_if_else() {
        let mut skip = HashSet::new();
        let blocks = vec![IfBlock {
            if_idx: 0,
            cond: "X".to_string(),
            target_idx: 3,
            jump_idx: Some(2),
            end_idx: Some(5),
            else_close_idx: None,
        }];
        let tree = build_region_tree(6, &blocks, &mut skip);
        assert_eq!(tree.children.len(), 2);
        assert!(matches!(tree.children[0].kind, RegionKind::IfThen(_)));
        assert!(matches!(tree.children[1].kind, RegionKind::Else));
        assert_eq!(tree.children[0].start, 1);
        assert_eq!(tree.children[0].end, 3); // includes jump_idx (skipped during emit)
        assert_eq!(tree.children[1].start, 3);
        assert_eq!(tree.children[1].end, 5);
        assert!(skip.contains(&0));
        assert!(skip.contains(&2));
    }

    #[test]
    fn region_tree_nested() {
        let mut skip = HashSet::new();
        // Outer: if at 0, target 5
        // Inner: if at 1, target 3
        let blocks = vec![
            IfBlock {
                if_idx: 0,
                cond: "A".to_string(),
                target_idx: 5,
                jump_idx: None,
                end_idx: None,
                else_close_idx: None,
            },
            IfBlock {
                if_idx: 1,
                cond: "B".to_string(),
                target_idx: 3,
                jump_idx: None,
                end_idx: None,
                else_close_idx: None,
            },
        ];
        let tree = build_region_tree(6, &blocks, &mut skip);
        assert_eq!(tree.children.len(), 1); // outer IfThen
        assert_eq!(tree.children[0].children.len(), 1); // inner IfThen
    }

    #[test]
    fn if_then_else_followed_by_if_then() {
        // Pattern from OnActorGripped: if/else followed by a second if (no else).
        // structure_bytecode produces flat output; verify brace structure.
        let stmts = vec![
            make_stmt(0x10, "if !(LeftHand) jump 0x30"),
            make_stmt(0x20, "self.Left = GrippedActor"),
            make_stmt(0x28, "jump 0x40"),
            make_stmt(0x30, "self.Right = GrippedActor"),
            make_stmt(0x40, "if !(GrippedActor.IsClimbable) jump 0x60"),
            make_stmt(0x50, "UpdateClimbing(LeftHand)"),
            make_stmt(0x60, "OnGripped(GrippedActor)"),
            make_stmt(0x70, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(
            text.contains("if (LeftHand) {"),
            "missing first if:\n{}",
            text
        );
        assert!(
            text.contains("if (GrippedActor.IsClimbable) {"),
            "missing second if:\n{}",
            text
        );
        // apply_indentation produces correct indent when called at the pipeline end
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        let itext = indented.join("\n");
        assert!(
            itext.contains("    UpdateClimbing(LeftHand)"),
            "IsClimbable body not indented after apply_indentation:\n{}",
            itext
        );
    }

    #[test]
    fn while_loop_body_indented() {
        let stmts = vec![
            make_stmt(0x10, "while (Cond) {"),
            make_stmt(0x20, "Body()"),
            make_stmt(0x30, "}"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        assert!(
            result.iter().any(|l| l == "while (Cond) {"),
            "missing while"
        );
        assert!(result.iter().any(|l| l == "Body()"), "missing body");
        // Verify indentation works
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        assert!(
            indented.iter().any(|l| l == "    Body()"),
            "body not indented:\n{}",
            indented.join("\n")
        );
    }

    #[test]
    fn if_inside_while_indented() {
        let stmts = vec![
            make_stmt(0x10, "while (LoopCond) {"),
            make_stmt(0x18, "if !(X) jump 0x30"),
            make_stmt(0x20, "IfBody()"),
            make_stmt(0x30, "AfterIf()"),
            make_stmt(0x38, "}"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        // Flat output has correct braces
        assert!(result.iter().any(|l| l == "while (LoopCond) {"));
        assert!(result.iter().any(|l| l == "if (X) {"));
        // After indentation: double-nested
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        let itext = indented.join("\n");
        assert!(
            itext.contains("        IfBody()"),
            "if body not double-indented:\n{}",
            itext
        );
        assert!(
            itext.contains("    AfterIf()"),
            "after-if not single-indented:\n{}",
            itext
        );
    }

    #[test]
    fn nested_while_loops() {
        let stmts = vec![
            make_stmt(0x10, "while (Outer) {"),
            make_stmt(0x18, "while (Inner) {"),
            make_stmt(0x20, "Body()"),
            make_stmt(0x28, "}"),
            make_stmt(0x30, "}"),
            make_stmt(0x38, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        let text = indented.join("\n");
        assert!(
            text.contains("        Body()"),
            "body not double-indented:\n{}",
            text
        );
        assert!(
            text.contains("    while (Inner) {"),
            "inner while not indented:\n{}",
            text
        );
    }

    #[test]
    fn apply_indentation_else_if_chain() {
        let mut lines = vec![
            "if (A) {".to_string(),
            "BodyA()".to_string(),
            "} else if (B) {".to_string(),
            "BodyB()".to_string(),
            "} else {".to_string(),
            "BodyC()".to_string(),
            "}".to_string(),
        ];
        apply_indentation(&mut lines);
        assert_eq!(lines[0], "if (A) {");
        assert_eq!(lines[1], "    BodyA()");
        assert_eq!(lines[2], "} else if (B) {");
        assert_eq!(lines[3], "    BodyB()");
        assert_eq!(lines[4], "} else {");
        assert_eq!(lines[5], "    BodyC()");
        assert_eq!(lines[6], "}");
    }

    #[test]
    fn apply_indentation_depth_zero_no_prefix() {
        let mut lines = vec!["TopLevel()".to_string(), "return".to_string()];
        apply_indentation(&mut lines);
        assert_eq!(lines[0], "TopLevel()");
        assert_eq!(lines[1], "return");
    }

    #[test]
    fn rewrite_gotos_detects_loop_via_braces() {
        // goto inside a while loop should become break
        let mut output = vec![
            "while (Cond) {".to_string(),
            "if (X) {".to_string(),
            "goto L_0050".to_string(),
            "}".to_string(),
            "}".to_string(),
            "L_0050:".to_string(),
        ];
        convert_gotos_to_breaks(&mut output);
        assert!(
            output.iter().any(|l| l == "break"),
            "goto not converted to break:\n{}",
            output.join("\n")
        );
    }

    #[test]
    fn rewrite_gotos_outside_loop_removes() {
        // goto outside any loop should be removed
        let mut output = vec![
            "if (X) {".to_string(),
            "goto L_0050".to_string(),
            "}".to_string(),
            "L_0050:".to_string(),
        ];
        convert_gotos_to_breaks(&mut output);
        assert!(
            !output.iter().any(|l| l.contains("goto")),
            "goto not removed:\n{}",
            output.join("\n")
        );
    }

    #[test]
    fn guard_wraps_remaining_scope() {
        // pop_flow_if_not(X) should wrap all subsequent code in if (X) { ... }
        let stmts = vec![
            make_stmt(0x10, "pop_flow_if_not(IsValid)"),
            make_stmt(0x20, "DoA()"),
            make_stmt(0x30, "DoB()"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(
            text.contains("if (IsValid) {"),
            "missing wrapping if:\n{}",
            text
        );
        assert!(text.contains("DoA()"), "missing body A:\n{}", text);
        assert!(text.contains("DoB()"), "missing body B:\n{}", text);
    }

    #[test]
    fn consecutive_guards_nest() {
        // Two consecutive guards should produce nested if blocks
        let stmts = vec![
            make_stmt(0x10, "pop_flow_if_not(A)"),
            make_stmt(0x20, "pop_flow_if_not(B)"),
            make_stmt(0x30, "Body()"),
            make_stmt(0x40, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        let text = indented.join("\n");
        assert!(text.contains("if (A) {"), "missing outer if:\n{}", text);
        assert!(
            text.contains("    if (B) {"),
            "missing nested if:\n{}",
            text
        );
        assert!(
            text.contains("        Body()"),
            "body not double-indented:\n{}",
            text
        );
    }

    #[test]
    fn guard_wraps_child_if_block() {
        // Guard followed by an if/else block: the guard should wrap both
        let stmts = vec![
            make_stmt(0x10, "pop_flow_if_not(Valid)"),
            make_stmt(0x20, "if !(X) jump 0x40"),
            make_stmt(0x30, "TrueBranch()"),
            make_stmt(0x40, "FalseBranch()"),
            make_stmt(0x50, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let mut indented = result.clone();
        apply_indentation(&mut indented);
        let text = indented.join("\n");
        assert!(text.contains("if (Valid) {"), "missing guard if:\n{}", text);
        assert!(
            text.contains("    if (X) {"),
            "child if not inside guard:\n{}",
            text
        );
    }

    #[test]
    fn guard_at_end_of_scope_suppressed() {
        // Guard as the very last statement (nothing after it to wrap)
        // should be suppressed rather than appearing as raw bytecode
        let stmts = vec![
            make_stmt(0x10, "if !(Outer) jump 0x30"),
            make_stmt(0x18, "DoWork()"),
            make_stmt(0x20, "pop_flow_if_not(Cond)"),
            make_stmt(0x30, "return nop"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("DoWork()"), "missing body:\n{}", text);
        assert!(
            !text.contains("pop_flow_if_not"),
            "raw guard leaked:\n{}",
            text
        );
    }

    #[test]
    fn pop_flow_terminates_true_branch_with_else() {
        // Pattern: if !(cond) jump TARGET; true_body; pop_flow; TARGET: false_body; pop_flow
        let stmts = vec![
            make_stmt(0x10, "if !($IsValid) jump 0x40"),
            make_stmt(0x20, "SpawnSound()"),
            make_stmt(0x30, "pop_flow"),
            make_stmt(0x40, "PrintString(\"no sound\")"),
            make_stmt(0x50, "pop_flow"),
            make_stmt(0x60, "AfterBlock()"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(text.contains("} else {"), "missing else:\n{}", text);
        assert!(
            text.contains("SpawnSound()"),
            "missing true body:\n{}",
            text
        );
        assert!(
            text.contains("PrintString(\"no sound\")"),
            "missing false body:\n{}",
            text
        );
    }

    #[test]
    fn nested_push_pop_not_treated_as_else_terminator() {
        // push_flow/pop_flow pair inside true body is balanced, not an exit
        let stmts = vec![
            make_stmt(0x10, "if !(Cond) jump 0x60"),
            make_stmt(0x20, "push_flow 0x40"),
            make_stmt(0x28, "DoWork()"),
            make_stmt(0x30, "pop_flow"),
            make_stmt(0x40, "AfterPush()"),
            make_stmt(0x50, "pop_flow"),
            make_stmt(0x60, "FalseBody()"),
        ];
        let result = structure_bytecode(&stmts, &HashMap::new());
        let text = result.join("\n");
        assert!(
            text.contains("AfterPush()"),
            "push/pop body lost:\n{}",
            text
        );
    }
}
