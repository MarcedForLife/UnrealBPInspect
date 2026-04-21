//! Splice captured orphan DoOnce blocks into the matched if-block.

use crate::pin_hints::BranchInfo;

use super::if_block::{find_matching_close, IfBlock};
use super::matching::match_branch_info;

/// Attempt one relocation on the matched if-block. Returns true when at
/// least one orphan was moved, false otherwise.
pub(super) fn try_relocate_one(
    lines: &mut Vec<String>,
    block: &IfBlock,
    branches: &[BranchInfo],
) -> bool {
    let Some(info) = match_branch_info(lines, block, branches) else {
        return false;
    };

    let then_only = info.then_only_callees();
    let else_only = info.else_only_callees();
    if then_only.is_empty() && else_only.is_empty() {
        return false;
    }

    // Walk forward from the if-block's last line, picking up CONTIGUOUS
    // `DoOnce(X) { ... }` orphans at the outer depth whose X is in the
    // then-only or else-only set.
    let mut cursor = block.end_idx() + 1;
    let mut orphans: Vec<(String, Vec<String>)> = Vec::new();
    while cursor < lines.len() {
        let trimmed = lines[cursor].trim();
        if trimmed.is_empty() {
            // Blank line between orphans is tolerated; the emitter does
            // not produce blanks mid-block, but be defensive.
            cursor += 1;
            continue;
        }
        let Some(name) = parse_doonce_open(trimmed) else {
            break; // non-DoOnce content terminates the contiguous run
        };
        if !then_only.contains(&name) && !else_only.contains(&name) {
            // Orphan, but not in our hints: leave it alone and stop.
            break;
        }
        let Some(close) = find_matching_close(lines, cursor) else {
            break;
        };
        let body: Vec<String> = lines[cursor..=close].to_vec();
        orphans.push((name, body));
        cursor = close + 1;
    }

    if orphans.is_empty() {
        return false;
    }

    // Snapshot existing bodies and the if-opener before we mutate.
    let if_idx = block.if_idx;
    let existing_if_line = lines[if_idx].clone();
    let existing_then_body: Vec<String> = lines[if_idx + 1..block.then_close_idx].to_vec();
    let (existing_else_body, block_end) = match (block.else_open_idx, block.else_close_idx) {
        (Some(open), Some(close)) => (lines[open + 1..close].to_vec(), close),
        _ => (Vec::new(), block.then_close_idx),
    };

    // Remove orphans first (they sit after the block), then the whole
    // if-block, so index math is straightforward.
    lines.drain(block_end + 1..cursor);
    lines.drain(if_idx..=block_end);

    // Partition orphans by original pin side, then map current-sides to
    // original-sides via inversion. The rebuilt block is always
    // un-inverted so readers see `if (cond)` rather than `if (!cond)`.
    let mut then_orphans: Vec<Vec<String>> = Vec::new();
    let mut else_orphans: Vec<Vec<String>> = Vec::new();
    for (name, body) in orphans {
        if then_only.contains(&name) {
            then_orphans.push(body);
        } else {
            else_orphans.push(body);
        }
    }

    let (original_then_body, original_else_body) = if block.inverted {
        (existing_else_body, existing_then_body)
    } else {
        (existing_then_body, existing_else_body)
    };

    let mut new_then = original_then_body;
    for body in then_orphans {
        new_then.extend(body);
    }
    let mut new_else = original_else_body;
    for body in else_orphans {
        new_else.extend(body);
    }

    let new_if_line = if block.inverted {
        un_invert_if_line(&existing_if_line)
    } else {
        existing_if_line
    };

    let mut new_lines: Vec<String> = Vec::with_capacity(3 + new_then.len() + new_else.len());
    new_lines.push(new_if_line);
    new_lines.extend(new_then);
    if !new_else.is_empty() {
        new_lines.push("} else {".to_string());
        new_lines.extend(new_else);
    }
    new_lines.push("}".to_string());

    // Splice in one shot; `if_idx..if_idx` is an empty range, so this is
    // a pure insert.
    lines.splice(if_idx..if_idx, new_lines);

    true
}

/// Remove a leading negation from `if (!COND) {`, producing `if (COND) {`.
/// Handles both `if (!x) {` and `if (!(x)) {` shapes. Returns the input
/// unchanged if no negation is found.
fn un_invert_if_line(if_line: &str) -> String {
    un_invert_inner(if_line).unwrap_or_else(|| if_line.to_string())
}

fn un_invert_inner(if_line: &str) -> Option<String> {
    let trimmed = if_line.trim_end();
    let rest = trimmed.strip_prefix("if (")?;
    let core = rest.strip_suffix(") {")?.trim_start();
    let after_bang = core.strip_prefix('!')?.trim_start();
    // If the remaining expression is wrapped in a single balanced pair of
    // parens, unwrap them for cleanliness.
    let inner = after_bang
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .filter(|s| is_balanced_parens(s))
        .unwrap_or(after_bang);
    Some(format!("if ({}) {{", inner))
}

/// True when `s` has balanced parentheses. Used to decide whether the
/// outer pair from `if (!(expr)) {` can be unwrapped safely.
fn is_balanced_parens(s: &str) -> bool {
    let mut depth: i32 = 0;
    for ch in s.chars() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

/// Parse a `DoOnce(X) {` opener and return `X`, or `None` if the line is
/// not a well-formed DoOnce opener with a non-empty argument.
pub(super) fn parse_doonce_open(trimmed: &str) -> Option<String> {
    let rest = trimmed.strip_prefix("DoOnce(")?;
    let close = rest.find(')')?;
    let name = rest[..close].trim();
    if name.is_empty() {
        return None;
    }
    if !rest[close + 1..].trim_start().starts_with('{') {
        return None;
    }
    Some(name.to_string())
}
