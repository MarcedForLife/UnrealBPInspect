use super::super::decode::StmtKind;
use super::region::{in_loop, BlockType, Region, RegionKind};
use crate::helpers::SECTION_SEPARATOR;

pub(super) use super::region::EmitCtx;

/// Resolve an unconditional jump to a display string, `None` to suppress.
fn resolve_jump_line(
    ctx: &EmitCtx,
    stmt_idx: usize,
    target: usize,
    in_loop: bool,
) -> Option<String> {
    if let Some(target_idx) = (ctx.find_target_idx_or_end)(target) {
        let is_jump_to_end = target_idx >= ctx.stmts.len()
            || (target_idx == ctx.stmts.len() - 1
                && ctx.stmts[target_idx].kind == StmtKind::ReturnNop);
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

/// Emit flat statements in `[from, to)`. Indentation is applied later.
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

        // Phantoms (inlined-away temps) only carry mem_offset for jump
        // resolution; their text is blank and emits nothing.
        if stmt.inlined_away {
            continue;
        }

        if stmt.kind == StmtKind::PopFlow {
            let keyword = if in_loop(block_stack) {
                "break"
            } else {
                "return"
            };
            // ForEach-with-break emits multiple pop_flow to unwind the flow
            // stack; only the first is semantically meaningful.
            let already_breaking = output.last().is_some_and(|l| l.trim() == keyword);
            if !already_breaking {
                output.push(keyword.to_string());
            }
        } else if stmt.continue_if_not_cond().is_some()
            || stmt.pop_flow_if_not_cond().is_some()
            || stmt.if_jump().is_some()
        {
            // Residual guard at end of scope: insert_guard_regions already
            // consumed mid-scope guards; nothing left to wrap here.
        } else if let Some(target) = stmt.jump_target() {
            if let Some(text) = resolve_jump_line(ctx, i, target, in_loop(block_stack)) {
                output.push(text);
            }
        } else {
            let text = if stmt.kind == StmtKind::ReturnNop {
                "return"
            } else {
                &stmt.text
            };
            output.push(text.to_string());
        }
    }
}

/// Emit the region tree as flat text. Braces emitted for if/else/loop;
/// `apply_indentation` assigns depth afterward.
#[allow(clippy::ptr_arg)] // push/pop needed on block_stack
pub(super) fn emit_region_tree(
    region: &Region,
    ctx: &EmitCtx,
    block_stack: &mut Vec<BlockType>,
    output: &mut Vec<String>,
) {
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

    let mut pos = region.start;

    let children = &region.children;
    let mut child_idx = 0;
    while child_idx < children.len() {
        let child = &children[child_idx];

        emit_stmts_range(ctx, pos, child.start, block_stack, output);

        emit_region_tree(child, ctx, block_stack, output);
        pos = child.end;
        child_idx += 1;

        if matches!(child.kind, RegionKind::IfThen(_)) {
            // Chain Else/ElseIf siblings into a single if/else.
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

        if matches!(child.kind, RegionKind::IfThen(_) | RegionKind::Loop(_)) {
            output.push("}".to_string());
            block_stack.pop();
        }
    }

    emit_stmts_range(ctx, pos, region.end, block_stack, output);
}
