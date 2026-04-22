//! Line folding for long pseudocode lines.
//!
//! Splits lines exceeding `MAX_LINE_WIDTH` at argument boundaries, logical
//! operators, or ternary/arithmetic operators. Continuation lines are indented
//! one level (4 spaces) beyond the original line's indentation. Runs as the
//! final pass in `format_summary` on the fully assembled output.

use crate::bytecode::MAX_LINE_WIDTH;
use crate::helpers::SECTION_SEPARATOR;

/// Fold all lines in `lines` that exceed `MAX_LINE_WIDTH`.
pub fn fold_long_lines(lines: &mut Vec<String>) {
    let mut idx = 0;
    while idx < lines.len() {
        if lines[idx].len() <= MAX_LINE_WIDTH {
            idx += 1;
            continue;
        }

        let trimmed = lines[idx].trim();
        if trimmed.starts_with(SECTION_SEPARATOR)
            || trimmed.starts_with("//")
            || trimmed == "}"
            || trimmed == "{"
        {
            idx += 1;
            continue;
        }

        let base_indent = lines[idx].len() - lines[idx].trim_start().len();
        let cont_indent = base_indent + 4;

        if let Some(folded) = fold_line(&lines[idx], base_indent, cont_indent) {
            let count = folded.len();
            lines.splice(idx..=idx, folded);
            idx += count;
        } else {
            idx += 1;
        }
    }
}

/// Split a long line into multiple lines. The first line keeps `base_indent`,
/// all continuations use `cont_indent`. Keeps splitting until every part fits
/// or no more break points exist.
fn fold_line(line: &str, base_indent: usize, cont_indent: usize) -> Option<Vec<String>> {
    let content = line.trim_start();
    let break_pos = find_best_break(content, MAX_LINE_WIDTH.saturating_sub(base_indent))?;

    let mut result = vec![format!(
        "{}{}",
        &" ".repeat(base_indent),
        content[..break_pos].trim_end()
    )];

    let mut remaining = content[break_pos..].trim_start().to_string();
    let budget = MAX_LINE_WIDTH.saturating_sub(cont_indent);
    loop {
        if remaining.len() <= budget {
            result.push(format!("{}{}", " ".repeat(cont_indent), remaining));
            break;
        }
        match find_best_break(&remaining, budget) {
            Some(pos) => {
                result.push(format!(
                    "{}{}",
                    " ".repeat(cont_indent),
                    remaining[..pos].trim_end()
                ));
                remaining = remaining[pos..].trim_start().to_string();
            }
            None => {
                result.push(format!("{}{}", " ".repeat(cont_indent), remaining));
                break;
            }
        }
    }
    Some(result)
}

/// Scan `content` for the best position to break. Prefers: shallowest paren
/// depth, then break type (comma > logic > ternary > arithmetic), then
/// rightmost position that still fits within `budget`.
///
/// When nothing fits within `budget`, picks the candidate closest to it.
fn find_best_break(content: &str, budget: usize) -> Option<usize> {
    let candidates = find_break_candidates(content);
    select_break(candidates, budget)
}

/// Scan for all valid break positions, returning `(pos, depth, priority)` tuples.
///
/// Priority: 0 = comma, 1 = logical (`&&`/`||`), 2 = ternary (`?`), 3 = arithmetic
fn find_break_candidates(content: &str) -> Vec<(usize, i32, u8)> {
    let bytes = content.as_bytes();
    let mut candidates = Vec::new();
    let mut depth = 0i32;
    let mut in_string = false;

    // Check whether `bytes[idx]` is a space-surrounded operator: " X "
    let is_spaced = |idx: usize| -> bool {
        idx > 0 && bytes[idx - 1] == b' ' && matches!(bytes.get(idx + 1), Some(b' '))
    };

    let mut idx = 0;
    while idx < bytes.len() {
        let byte = bytes[idx];

        if byte == b'\'' {
            in_string = !in_string;
            idx += 1;
            continue;
        }
        if in_string {
            idx += 1;
            continue;
        }

        match byte {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            // Break after ", "
            b',' if matches!(bytes.get(idx + 1), Some(b' ')) => {
                candidates.push((idx + 2, depth, 0));
            }
            // Break before " && " or " || "
            b'&' | b'|'
                if idx > 0
                    && bytes[idx - 1] == b' '
                    && bytes.get(idx + 1) == Some(&byte)
                    && matches!(bytes.get(idx + 2), Some(b' ')) =>
            {
                candidates.push((idx, depth, 1));
                idx += 3;
                continue;
            }
            // Break before " ? ", " + ", " - ", " * ", " / "
            b'?' if is_spaced(idx) => candidates.push((idx, depth, 2)),
            b'+' | b'-' | b'*' | b'/' if is_spaced(idx) => candidates.push((idx, depth, 3)),
            _ => {}
        }
        idx += 1;
    }
    candidates
}

/// Pick the best break from candidates. Among those fitting within `budget`,
/// prefer shallowest depth, lowest priority, rightmost position. If nothing
/// fits, pick the candidate closest to `budget`.
fn select_break(candidates: Vec<(usize, i32, u8)>, budget: usize) -> Option<usize> {
    use std::cmp::Reverse;

    // Prefer rightmost candidate that fits, at shallowest depth / lowest priority
    let fitting = candidates
        .iter()
        .filter(|(pos, _, _)| *pos <= budget)
        .min_by_key(|(pos, depth, prio)| (*depth, *prio, Reverse(*pos)));

    if let Some(&(pos, _, _)) = fitting {
        return Some(pos);
    }

    // Nothing fits: pick closest to budget, breaking ties by depth/priority
    candidates
        .iter()
        .min_by_key(|(pos, depth, prio)| (pos.abs_diff(budget), *depth, *prio))
        .map(|&(pos, _, _)| pos)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_lines_unchanged() {
        let mut lines = vec!["    foo(a, b, c)".to_string()];
        fold_long_lines(&mut lines);
        assert_eq!(lines, vec!["    foo(a, b, c)"]);
    }

    #[test]
    fn fold_at_comma() {
        let args: Vec<String> = (0..10).map(|i| format!("argument_{}", i)).collect();
        let mut lines = vec![format!("    FunctionName({})", args.join(", "))];
        assert!(lines[0].len() > MAX_LINE_WIDTH);
        fold_long_lines(&mut lines);
        assert!(lines.len() > 1, "should have folded: {:?}", lines);
        assert!(lines[0].len() <= MAX_LINE_WIDTH);
        assert!(lines[1].starts_with("        "));
    }

    #[test]
    fn fold_at_logical_operator() {
        let long_cond = format!(
            "    if ({} && {} && {}) {{",
            "a".repeat(40),
            "b".repeat(40),
            "c".repeat(40)
        );
        let mut lines = vec![long_cond];
        fold_long_lines(&mut lines);
        assert!(lines.len() > 1, "should have folded: {:?}", lines);
    }

    #[test]
    fn comment_lines_not_folded() {
        let long_comment = format!("    // {}", "x".repeat(200));
        let mut lines = vec![long_comment.clone()];
        fold_long_lines(&mut lines);
        assert_eq!(lines, vec![long_comment]);
    }

    #[test]
    fn prefers_shallow_depth() {
        let line = format!("    Func(Inner({}), {})", "x".repeat(60), "y".repeat(60));
        let mut lines = vec![line];
        fold_long_lines(&mut lines);
        assert!(lines.len() > 1);
        assert!(lines[0].contains("Inner("));
    }

    #[test]
    fn barely_over_limit() {
        let line = "        $InverseTransformLocation = InverseTransformLocation($GetComponentToWorld_ReturnValue_1, GetTransform().Location)".to_string();
        let original_len = line.len();
        assert!(original_len > MAX_LINE_WIDTH);
        let mut lines = vec![line];
        fold_long_lines(&mut lines);
        assert!(lines.len() > 1, "should have folded");
        assert!(lines[0].len() <= MAX_LINE_WIDTH);
    }

    #[test]
    fn string_literals_not_split() {
        let line = format!(
            "    PrintString('{}', true, true, {})",
            "a, b, c, d, e, f, g, h, i, j",
            "x".repeat(80)
        );
        let mut lines = vec![line];
        fold_long_lines(&mut lines);
        let joined = lines.join("\n");
        assert!(joined.contains("'a, b, c, d, e, f, g, h, i, j'"));
    }
}
