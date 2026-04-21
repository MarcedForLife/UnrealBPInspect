//! Parse the flat line list into `IfBlock` descriptors and locate the
//! first actionable one. "Actionable" means the block's body shares at
//! least one callee with some `BranchInfo`'s pin-only sets.

use crate::pin_hints::BranchInfo;

use super::matching::match_branch_info;

/// Shape of an if-block discovered in the flat line list, with the indices
/// needed to splice orphans into either side.
#[derive(Debug, Clone)]
pub(super) struct IfBlock {
    /// Index of the `if (...) {` opening line.
    pub(super) if_idx: usize,
    /// Index of the then-side closing `}` line.
    pub(super) then_close_idx: usize,
    /// Index of the `} else {` line, if present.
    pub(super) else_open_idx: Option<usize>,
    /// Index of the else-side closing `}` line, if else is present.
    pub(super) else_close_idx: Option<usize>,
    /// Condition is inverted (`if (!...)`), meaning current-then corresponds
    /// to the original pin's Else side.
    pub(super) inverted: bool,
}

impl IfBlock {
    /// Last line index covered by this block (else-close if present,
    /// otherwise then-close).
    pub(super) fn end_idx(&self) -> usize {
        self.else_close_idx.unwrap_or(self.then_close_idx)
    }
}

/// Find the first if-block in `lines` whose body matches a single
/// `BranchInfo`. Returns `None` when no if-block is actionable.
pub(super) fn find_first_actionable_if(
    lines: &[String],
    branches: &[BranchInfo],
) -> Option<IfBlock> {
    let mut idx = 0;
    while idx < lines.len() {
        if is_if_open(lines[idx].trim()) {
            if let Some(block) = parse_if_block(lines, idx) {
                if match_branch_info(lines, &block, branches).is_some() {
                    return Some(block);
                }
                // Skip past this if-block; don't recurse into its body for
                // outer-level orphan placement (we only rewrite at the
                // block's own depth).
                idx = block.end_idx() + 1;
                continue;
            }
        }
        idx += 1;
    }
    None
}

/// True when `trimmed` opens an `if (COND) {` statement (not an `else if`,
/// which is lexed by the emitter as `} else if`).
fn is_if_open(trimmed: &str) -> bool {
    trimmed.starts_with("if (") && trimmed.ends_with('{')
}

/// Parse a single if-block starting at `if_idx`. Returns `None` if the
/// block is malformed (no matching close, etc.).
fn parse_if_block(lines: &[String], if_idx: usize) -> Option<IfBlock> {
    let if_line = lines[if_idx].trim();
    let inverted = condition_is_inverted(if_line);
    let then_close_idx = find_matching_close(lines, if_idx)?;

    // Canonical else shapes: `} else {` on its own line, or `} else if (...) {`.
    // Relocation handles only the plain `} else {` form; `else if` chains
    // are conservative no-ops.
    let (else_open_idx, else_close_idx) = lines
        .get(then_close_idx + 1)
        .and_then(|line| {
            let t = line.trim();
            let is_plain_else =
                t == "} else {" || (t.starts_with("} else {") && !t.starts_with("} else if "));
            if !is_plain_else {
                return None;
            }
            let else_open = then_close_idx + 1;
            let else_close = find_matching_close(lines, else_open)?;
            Some((Some(else_open), Some(else_close)))
        })
        .unwrap_or((None, None));

    Some(IfBlock {
        if_idx,
        then_close_idx,
        else_open_idx,
        else_close_idx,
        inverted,
    })
}

/// Detect whether `if_line` (already `if (COND) {`) has a leading `!` on
/// its condition.
pub(super) fn condition_is_inverted(if_line: &str) -> bool {
    if_line
        .strip_prefix("if (")
        .is_some_and(|rest| rest.trim_start().starts_with('!'))
}

/// Find the index of the `}` that matches the `{` on `open_line_idx`,
/// where that line is any block-opener (`if (...) {`, `} else {`,
/// `DoOnce(X) {`, etc.). A `} else ...` continuation at nested depth
/// closes then reopens on the same line and does not terminate the outer
/// block.
pub(super) fn find_matching_close(lines: &[String], open_line_idx: usize) -> Option<usize> {
    let open_line = lines.get(open_line_idx)?.trim();
    if !open_line.ends_with('{') {
        return None;
    }
    let mut depth: i32 = 1;
    for (offset, line) in lines.iter().enumerate().skip(open_line_idx + 1) {
        let trimmed = line.trim();
        let opens = trimmed.ends_with('{');

        if trimmed == "}" {
            depth -= 1;
        } else if trimmed.starts_with("} else ") && opens {
            // Chained continuation at nested depth is a no-op on depth.
            continue;
        } else if opens {
            depth += 1;
        } else if trimmed.starts_with('}') {
            depth -= 1;
        } else {
            continue;
        }

        if depth == 0 {
            return Some(offset);
        }
    }
    None
}
