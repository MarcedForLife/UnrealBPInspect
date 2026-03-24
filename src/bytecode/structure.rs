//! If/else block structuring: reconstructs control flow from flat jump patterns.
//!
//! Takes the reordered statement list from [`super::flow`] and builds structured
//! if/else/while blocks by matching `jump_if_not` + `push_flow` pairs, detecting
//! else branches via unconditional jumps, and handling nested blocks through a region
//! tree. Post-processing converts remaining `goto` to `break` where applicable and
//! extracts convergence code shared by multiple branches.

use super::decode::BcStatement;
use super::flow::{
    parse_if_jump, parse_jump, parse_jump_computed, parse_pop_flow_if_not, parse_push_flow,
};
use crate::helpers::indent_of;
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
    let then_end = if blk.jump_idx.is_some() {
        blk.target_idx - 1
    } else {
        blk.target_idx
    };

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
    let then_end = if blk.jump_idx.is_some() {
        blk.target_idx - 1 // exclude the unconditional jump
    } else {
        blk.target_idx
    };

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
            || (target_idx == ctx.stmts.len() - 1 && ctx.stmts[target_idx].text == "return nop");
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

/// Emit statements in range [from, to) with given indent.
fn emit_stmts_range(
    ctx: &EmitCtx,
    from: usize,
    to: usize,
    indent: usize,
    block_stack: &mut Vec<BlockType>,
    output: &mut Vec<String>,
) {
    let emit = |text: &str| -> String { format!("{}{}", INDENT.repeat(indent), text) };

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
                && !output.iter().any(|l| l.starts_with("---"))
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

        if stmt.text == "}" {
            // Closing brace from flow.rs (loop end)
            block_stack.pop();
            let close_indent = indent.saturating_sub(1);
            output.push(format!("{}}}", INDENT.repeat(close_indent)));
        } else if stmt.text.ends_with(" {") {
            let is_loop = stmt.text.starts_with("while ") || stmt.text.starts_with("for ");
            output.push(emit(&stmt.text));
            block_stack.push(if is_loop {
                BlockType::Loop
            } else {
                BlockType::If
            });
        } else if stmt.text == "pop_flow" {
            let keyword = if in_loop(block_stack) {
                "break"
            } else {
                "return"
            };
            output.push(emit(keyword));
        } else if let Some(cond) = parse_pop_flow_if_not(&stmt.text) {
            let keyword = if in_loop(block_stack) {
                "break"
            } else {
                "return"
            };
            let negated = negate_cond(cond);
            output.push(emit(&format!("if ({}) {}", negated, keyword)));
        } else if let Some((cond, _target)) = parse_if_jump(&stmt.text) {
            // Unresolvable conditional jump, treat as guard
            let negated = negate_cond(cond);
            let keyword = if in_loop(block_stack) {
                "break"
            } else {
                "return"
            };
            output.push(emit(&format!("if ({}) {}", negated, keyword)));
        } else if let Some(target) = parse_jump(&stmt.text) {
            if let Some(text) = resolve_jump_line(ctx, i, target, in_loop(block_stack)) {
                output.push(emit(&text));
            }
        } else {
            let text = if stmt.text == "return nop" {
                "return"
            } else {
                &stmt.text
            };
            output.push(emit(text));
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
                    || (target_idx == stmts.len() - 1 && stmts[target_idx].text == "return nop");
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

/// Convert flat bytecode statements into indented pseudo-code lines.
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
    let region_tree = build_region_tree(stmts.len(), &if_blocks, &mut skip);
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
    emit_region_tree(&region_tree, &ctx, 0, &mut block_stack, &mut output);

    convert_gotos_to_breaks(&mut output);
    extract_convergence(&mut output);
    collapse_double_else(&mut output);

    output
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
        let Some(target_idx) = find_target(target) else {
            continue;
        };

        // Check for an else branch: the statement before the false-branch start
        // should be an unconditional jump (skip-else) or a return (diverging branches)
        let (jump_idx, end_idx) = detect_else_branch(stmts, target_idx, find_target);

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

/// Check if the true-branch ends with an unconditional jump (else) or return (diverging).
fn detect_else_branch(
    stmts: &[BcStatement],
    target_idx: usize,
    find_target: &dyn Fn(usize) -> Option<usize>,
) -> (Option<usize>, Option<usize>) {
    if target_idx == 0 || target_idx > stmts.len() {
        return (None, None);
    }
    let check_idx = target_idx - 1;
    let prev = &stmts[check_idx];
    if let Some(end_target) = parse_jump(&prev.text) {
        if let Some(end_idx) = find_target(end_target) {
            if end_idx >= target_idx {
                return (Some(check_idx), Some(end_idx));
            }
        }
    } else if (prev.text == "return nop" || prev.text == "return") && target_idx < stmts.len() {
        return (Some(check_idx), Some(stmts.len()));
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
        for (j, stmt) in stmts.iter().enumerate().take(end_idx).skip(blk.target_idx) {
            if let Some(jt) = parse_jump(&stmt.text) {
                if find_target(jt) == Some(end_idx) {
                    blk.else_close_idx = Some(j + 1);
                    break;
                }
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

/// Emit the region tree, managing `}` placement for if/else/else-if groups.
fn emit_region_tree(
    region: &Region,
    ctx: &EmitCtx,
    indent: usize,
    block_stack: &mut Vec<BlockType>,
    output: &mut Vec<String>,
) {
    let body_indent = match region.kind {
        RegionKind::Root => indent,
        _ => indent + 1,
    };

    // Emit opening
    match &region.kind {
        RegionKind::Root => {}
        RegionKind::IfThen(cond) => {
            output.push(format!("{}if ({}) {{", INDENT.repeat(indent), cond));
            block_stack.push(BlockType::If);
        }
        RegionKind::Else => {
            output.push(format!("{}}} else {{", INDENT.repeat(indent)));
        }
        RegionKind::ElseIf(cond) => {
            output.push(format!("{}}} else if ({}) {{", INDENT.repeat(indent), cond));
        }
    }

    // Emit body: walk [start, end), recursing into children
    let mut pos = region.start;

    let children = &region.children;
    let mut child_idx = 0;
    while child_idx < children.len() {
        let child = &children[child_idx];

        // Emit statements [pos, child.start) at body_indent
        emit_stmts_range(ctx, pos, child.start, body_indent, block_stack, output);

        // Detect if/else groups: IfThen possibly followed by Else/ElseIf
        if matches!(child.kind, RegionKind::IfThen(_)) {
            // Emit the IfThen
            emit_region_tree(child, ctx, body_indent, block_stack, output);
            pos = child.end;
            child_idx += 1;

            // Continue emitting Else/ElseIf siblings that form a chain
            while child_idx < children.len() {
                let next = &children[child_idx];
                if !matches!(next.kind, RegionKind::Else | RegionKind::ElseIf(_)) {
                    break;
                }
                // Emit any gap statements between previous and this else
                emit_stmts_range(ctx, pos, next.start, body_indent, block_stack, output);
                emit_region_tree(next, ctx, body_indent, block_stack, output);
                pos = next.end;
                child_idx += 1;
            }

            // Close the if/else group
            output.push(format!("{}}}", INDENT.repeat(body_indent)));
            block_stack.pop();
        } else {
            // Non-if child (shouldn't happen with current data, but handle gracefully)
            emit_region_tree(child, ctx, body_indent, block_stack, output);
            pos = child.end;
            child_idx += 1;
        }
    }

    // Emit remaining statements [pos, end)
    emit_stmts_range(ctx, pos, region.end, body_indent, block_stack, output);
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
        if !trimmed.ends_with(':') || trimmed.starts_with("---") || trimmed.starts_with("//") {
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
fn rewrite_gotos(output: &mut [String], break_labels: &HashSet<String>) {
    for i in 0..output.len() {
        let trimmed = output[i].trim().to_string();
        let Some(label) = trimmed.strip_prefix("goto ") else {
            continue;
        };
        if !break_labels.contains(label) {
            continue;
        }
        let indent_len = output[i].len() - trimmed.len();
        let indent_str = &output[i][..indent_len];
        let line_depth = indent_len / INDENT.len();
        let in_loop = output[..i].iter().rev().any(|l| {
            let depth = indent_of(l) / INDENT.len();
            let trimmed = l.trim();
            depth < line_depth && (trimmed.starts_with("while ") || trimmed.starts_with("for "))
        });
        if in_loop {
            output[i] = format!("{}break", indent_str);
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
        if trimmed.ends_with(':') && !trimmed.starts_with("---") && !trimmed.starts_with("//") {
            let label = &trimmed[..trimmed.len() - 1];
            if break_labels.contains(label) {
                return remaining_gotos.contains(label);
            }
        }
        true
    });
}

/// Find the extent of convergence code starting at `code_start`.
/// Returns the end index (exclusive) of the convergence block.
fn find_convergence_extent(output: &[String], code_start: usize) -> usize {
    let first_indent = indent_of(&output[code_start]);
    let mut code_end = code_start;
    for (j, line) in output[code_start..].iter().enumerate() {
        let j = j + code_start;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            code_end = j + 1;
            continue;
        }
        let line_indent = indent_of(line);
        if line_indent < first_indent && (trimmed.starts_with('}') || trimmed.starts_with("} else"))
        {
            break;
        }
        if j > code_start
            && trimmed.ends_with(':')
            && !trimmed.starts_with("//")
            && !trimmed.starts_with("---")
        {
            break;
        }
        code_end = j + 1;
    }
    code_end
}

/// Find the `}` line after all gotos where convergence code should be inserted.
fn find_insertion_point(output: &[String], max_goto: usize, min_goto_indent: usize) -> usize {
    for (j, line) in output[(max_goto + 1)..].iter().enumerate() {
        let j = j + max_goto + 1;
        let trimmed = line.trim();
        let line_indent = indent_of(line);
        if trimmed == "}" && line_indent < min_goto_indent {
            return j;
        }
    }
    output.len()
}

/// Remove old convergence lines and insert at the new position with adjusted indentation.
fn splice_convergence(
    output: &mut Vec<String>,
    label_idx: usize,
    code_range: std::ops::Range<usize>,
    goto_indices: &[usize],
    insert_pos: usize,
    target_indent: usize,
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

    let indent_str = INDENT.repeat(target_indent / INDENT.len());
    for (i, content) in conv_content.iter().enumerate() {
        let line = if content.is_empty() {
            String::new()
        } else {
            format!("{}{}", indent_str, content)
        };
        let pos = (adjusted_pos + 1 + i).min(output.len());
        output.insert(pos, line);
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

        // Strip indentation from the convergence code (will be re-indented at the insertion point)
        let conv_content: Vec<String> = output[code_start..code_end]
            .iter()
            .map(|l| l.trim().to_string())
            .collect();

        // Find where to insert: after the outermost `}` that encloses all the gotos
        let min_goto_indent = goto_indices
            .iter()
            .map(|&i| indent_of(&output[i]))
            .min()
            .unwrap_or(0);
        let max_goto = goto_indices.iter().copied().max().unwrap_or(0);
        let insert_pos = find_insertion_point(output, max_goto, min_goto_indent);
        let target_indent = output.get(insert_pos).map_or(0, |l| indent_of(l));

        splice_convergence(
            output,
            label_idx,
            code_start..code_end,
            &goto_indices,
            insert_pos,
            target_indent,
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
        BcStatement {
            mem_offset: offset,
            text: text.to_string(),
        }
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
        assert_eq!(tree.children[0].end, 2); // excludes jump_idx
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
}
