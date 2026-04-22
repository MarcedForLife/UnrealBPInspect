//! If/else block structuring. Builds structured if/else/while blocks from the
//! reordered statements in [`super::flow`] by matching `jump_if_not`/`push_flow`
//! pairs and tracking nesting via a region tree. Post-processing converts
//! remaining `goto` to `break` and extracts multi-branch convergence code.

use super::decode::BcStatement;
use super::STRUCTURE_OFFSET_TOLERANCE;
use crate::helpers::opens_block;
use std::collections::{HashMap, HashSet};

mod build;
mod detect;
mod emit;
mod postprocess;
mod region;

#[cfg(test)]
mod tests;

use build::{build_region_tree, insert_brace_blocks, insert_guard_regions, suppress_flow_opcodes};
use detect::{collect_label_targets, detect_if_blocks, reorder_displaced_else};
use emit::{emit_region_tree, EmitCtx};
use postprocess::{
    collapse_double_else, convert_gotos_to_breaks, extract_convergence, strip_dead_backward_gotos,
};
use region::BlockType;

/// Indentation string per nesting level (4 spaces).
const INDENT: &str = "    ";

/// Negate a condition string for if/else inversion.
///
/// - `!X` -> `X` (simple strip, only when X has no spaces/operators)
/// - `!(expr)` -> `expr` (only when parens are balanced)
/// - Otherwise wraps as `!(cond)` so compound precedence is preserved
///   (`!A && B` means `(!A) && B`, not `!(A && B)`).
pub(crate) fn negate_cond(cond: &str) -> String {
    if cond.starts_with('!') && !cond.starts_with("!(") {
        let rest = &cond[1..];
        if !rest.contains(' ') {
            return rest.to_string();
        }
    }
    if cond.starts_with("!(") {
        if let Some(inner) = cond.strip_prefix("!(").and_then(|s| s.strip_suffix(')')) {
            // Verify the stripped ')' is the matching one.
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
    // Wrap if condition has infix operators at paren depth 0.
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

/// Convert flat bytecode statements into structured pseudo-code lines (unindented).
/// `labels` maps memory offsets to display names (e.g. `--- EventName ---`).
///
/// Condition fidelity: `&&`/`||` in decoded bytecode come from `BooleanAND`/
/// `BooleanOR` calls inlined by `try_inline_operator`. This pass never merges
/// separate Branch nodes into compound conditions; it only chains if-blocks
/// into else-if when they share the same end target.
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

    // Structurer-specific CFG: jump tolerance matches `find_target` and
    // Sequence dispatch chains stay as individual blocks so the else-branch
    // detector sees each `if !(cond) jump` block independently.
    let cfg = super::cfg::BlockCfg::build_for_structurer(stmts, &offset_map);

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
    let if_blocks = detect_if_blocks(stmts, &find_target, &cfg);
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
    strip_dead_backward_gotos(&mut output);
    extract_convergence(&mut output);
    strip_dead_backward_gotos(&mut output);
    collapse_double_else(&mut output);

    output
}

/// Apply indentation based on brace nesting depth. Lines starting with `}`
/// decrement before indenting; lines ending ` {` increment after. Called
/// once at the end so all intermediate passes work with flat text.
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
