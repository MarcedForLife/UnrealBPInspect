//! Scope-tree builder for post-structure pseudocode lines.
//!
//! Consumes a `Vec<String>` of pseudocode lines and emits a `LineRegion`
//! tree describing the nesting structure (if/else chains, for-each loops,
//! for-range loops, while loops, bare blocks). Pure shape analysis, no
//! text rewriting. Used by `inline_scoped` to reason about block-scope
//! boundaries when deciding whether a temp inline is safe.
//!
//! Range convention: `stmt_range` is half-open and covers the full span
//! including the opener line and the closer line. Else/ElseIf siblings
//! are disjoint from the preceding If. For `if (a) { ... } else { ... }`,
//! the If region ends at the `} else {` line (exclusive) and the Else
//! region starts at the same line (inclusive), so ranges are disjoint
//! and together cover the whole chain.

use crate::bytecode::decode::{parse_stmt, Stmt};

/// Kind of lexical region opened by a pseudocode line.
///
/// `Root` is the synthetic outermost region covering the full input.
/// `Block` is the fallback for bare `{` openers or unrecognised
/// keyword-opener shapes that `parse_stmt` classifies as `Unknown`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LineRegionKind {
    Root,
    If,
    Else,
    ElseIf,
    ForEach,
    ForRange,
    Loop,
    Block,
}

/// One region in the scope tree. `stmt_range` is half-open and includes
/// opener and closer lines. Depth, if needed, can be recovered by
/// walking the tree from the root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LineRegion {
    pub kind: LineRegionKind,
    pub stmt_range: std::ops::Range<usize>,
    pub children: Vec<LineRegion>,
}

/// In-progress region held on the builder stack. Promoted to a
/// `LineRegion` when the matching closer (or sibling opener, for
/// else-chains) is encountered.
struct Open {
    kind: LineRegionKind,
    start: usize,
    children: Vec<LineRegion>,
}

/// Build a scope tree from `lines`. The returned region is always
/// `LineRegionKind::Root`, covering `0..lines.len()`.
///
/// Tolerant of malformed input: an extra `}` with no matching opener
/// becomes a leaf under the current parent, and an `} else {` with no
/// preceding If/ElseIf is treated as a leaf too. Neither case panics.
pub(crate) fn build_region_tree(lines: &[String]) -> LineRegion {
    let mut stack: Vec<Open> = vec![Open {
        kind: LineRegionKind::Root,
        start: 0,
        children: Vec::new(),
    }];

    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let stmt = parse_stmt(trimmed);
        handle_line(&mut stack, idx, trimmed, &stmt);
    }

    // Close any regions that were opened but never explicitly closed.
    // Their end is clamped to the end of the input. This keeps the tree
    // well-formed on truncated / malformed fixtures.
    while stack.len() > 1 {
        let finished = pop_and_finish(&mut stack, lines.len());
        if let Some(parent) = stack.last_mut() {
            parent.children.push(finished);
        }
    }

    let root = stack.pop().expect("root sentinel always present");
    LineRegion {
        kind: LineRegionKind::Root,
        stmt_range: 0..lines.len(),
        children: root.children,
    }
}

fn handle_line(stack: &mut Vec<Open>, idx: usize, trimmed: &str, stmt: &Stmt) {
    match stmt {
        Stmt::IfOpen { .. } => push_open(stack, LineRegionKind::If, idx),
        Stmt::Else => close_and_open_sibling(stack, LineRegionKind::Else, idx),
        Stmt::BlockClose => close_top(stack, idx),
        Stmt::Unknown(_) => handle_unknown(stack, idx, trimmed),
        _ => { /* leaf line, no stack op */ }
    }
}

/// Fallback classifier for lines `parse_stmt` returns as `Unknown`.
/// Catches opener shapes (`} else if (cond) {`, `for (...) {`, `while
/// (...) {`, bare `{` or keyword-opener `{`) that don't have a typed
/// `Stmt` variant yet.
fn handle_unknown(stack: &mut Vec<Open>, idx: usize, trimmed: &str) {
    if !trimmed.ends_with('{') {
        return; // leaf line
    }

    // `} else if (cond) {` is a sibling of the preceding If/ElseIf.
    if trimmed.starts_with("} else if ") || trimmed.starts_with("}else if ") {
        close_and_open_sibling(stack, LineRegionKind::ElseIf, idx);
        return;
    }

    let kind = classify_opener(trimmed);
    push_open(stack, kind, idx);
}

/// Classify a trimmed opener line (ends with `{`) by keyword prefix.
/// Falls back to `Block` for bare `{` or unrecognised keyword openers.
fn classify_opener(trimmed: &str) -> LineRegionKind {
    // Strip leading `} ` for chained closers followed by an opener on
    // the same line, though we already handle `} else if` above. Other
    // keyword-opener shapes with a leading `}` aren't expected.
    let head = trimmed.trim_end_matches('{').trim();

    if head.starts_with("foreach ") || head.starts_with("foreach(") {
        return LineRegionKind::ForEach;
    }
    if let Some(rest) = head
        .strip_prefix("for ")
        .or_else(|| head.strip_prefix("for("))
    {
        // `for (x in arr)` -> ForEach, `for (i = 0 to N)` -> ForRange.
        // Both variants may appear with or without a leading space after
        // `for`, hence the two strip prefixes above.
        if rest.contains(" in ") {
            return LineRegionKind::ForEach;
        }
        if rest.contains(" to ") || rest.contains(" = ") {
            return LineRegionKind::ForRange;
        }
        return LineRegionKind::Loop;
    }
    if head.starts_with("while ") || head.starts_with("while(") || head == "loop" {
        return LineRegionKind::Loop;
    }
    LineRegionKind::Block
}

fn push_open(stack: &mut Vec<Open>, kind: LineRegionKind, idx: usize) {
    stack.push(Open {
        kind,
        start: idx,
        children: Vec::new(),
    });
}

/// Close the current top-of-stack region at `idx + 1` and attach it to
/// its parent. Extra `}` lines (underflow into the root sentinel) are
/// ignored, the line stays a silent leaf.
fn close_top(stack: &mut Vec<Open>, idx: usize) {
    if stack.len() <= 1 {
        return; // unmatched `}`; leave as leaf
    }
    let finished = pop_and_finish(stack, idx + 1);
    if let Some(parent) = stack.last_mut() {
        parent.children.push(finished);
    }
}

/// Close the top If/ElseIf region at `idx` (exclusive) and push a fresh
/// sibling of kind `new_kind` starting at `idx`. Used for `} else {`
/// and `} else if (cond) {` shapes so the chain becomes siblings under
/// the shared parent rather than nested children.
///
/// If the top of stack isn't an If/ElseIf (malformed input, e.g. a
/// stray `} else {` with no preceding If), the line is dropped as a
/// leaf and no region is opened.
fn close_and_open_sibling(stack: &mut Vec<Open>, new_kind: LineRegionKind, idx: usize) {
    let top_kind = stack.last().map(|o| &o.kind);
    let chainable = matches!(
        top_kind,
        Some(LineRegionKind::If) | Some(LineRegionKind::ElseIf)
    );
    if !chainable {
        return; // unmatched else / else-if, treat as leaf
    }

    let finished = pop_and_finish(stack, idx);
    if let Some(parent) = stack.last_mut() {
        parent.children.push(finished);
    }
    stack.push(Open {
        kind: new_kind,
        start: idx,
        children: Vec::new(),
    });
}

fn pop_and_finish(stack: &mut Vec<Open>, end: usize) -> LineRegion {
    let open = stack.pop().expect("caller ensured non-empty");
    LineRegion {
        kind: open.kind,
        stmt_range: open.start..end,
        children: open.children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compact tuple shape for tree assertions: (kind, start, end, children).
    #[derive(Debug, PartialEq, Eq)]
    struct Shape(LineRegionKind, usize, usize, Vec<Shape>);

    fn shape_of(region: &LineRegion) -> Shape {
        Shape(
            region.kind.clone(),
            region.stmt_range.start,
            region.stmt_range.end,
            region.children.iter().map(shape_of).collect(),
        )
    }

    fn lines(src: &[&str]) -> Vec<String> {
        src.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn empty_input_has_no_children() {
        let tree = build_region_tree(&[]);
        assert_eq!(shape_of(&tree), Shape(LineRegionKind::Root, 0, 0, vec![]));
    }

    #[test]
    fn flat_input_has_no_nested_regions() {
        let src = lines(&["x = 1", "y = 2"]);
        let tree = build_region_tree(&src);
        assert_eq!(shape_of(&tree), Shape(LineRegionKind::Root, 0, 2, vec![]));
    }

    #[test]
    fn simple_if_nests_one_region() {
        let src = lines(&["if (cond) {", "    x = 1", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                3,
                vec![Shape(LineRegionKind::If, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn if_else_produces_sibling_regions() {
        let src = lines(&["if (a) {", "    x = 1", "} else {", "    y = 2", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                5,
                vec![
                    Shape(LineRegionKind::If, 0, 2, vec![]),
                    Shape(LineRegionKind::Else, 2, 5, vec![]),
                ],
            )
        );
    }

    #[test]
    fn if_elseif_else_chain_is_three_siblings() {
        let src = lines(&[
            "if (a) {",
            "    x = 1",
            "} else if (b) {",
            "    x = 2",
            "} else {",
            "    x = 3",
            "}",
        ]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                7,
                vec![
                    Shape(LineRegionKind::If, 0, 2, vec![]),
                    Shape(LineRegionKind::ElseIf, 2, 4, vec![]),
                    Shape(LineRegionKind::Else, 4, 7, vec![]),
                ],
            )
        );
    }

    #[test]
    fn foreach_with_nested_if_nests_as_child() {
        let src = lines(&[
            "for (item in arr) {",
            "    if (item > 0) {",
            "        x = 1",
            "    }",
            "}",
        ]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                5,
                vec![Shape(
                    LineRegionKind::ForEach,
                    0,
                    5,
                    vec![Shape(LineRegionKind::If, 1, 4, vec![])],
                )],
            )
        );
    }

    #[test]
    fn for_range_opener_classifies_as_for_range() {
        let src = lines(&["for (i = 0 to 10) {", "    x = i", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                3,
                vec![Shape(LineRegionKind::ForRange, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn while_opener_classifies_as_loop() {
        let src = lines(&["while (running) {", "    tick()", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                3,
                vec![Shape(LineRegionKind::Loop, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn unknown_opener_falls_back_to_block() {
        let src = lines(&["weird_keyword (foo) {", "    x = 1", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                3,
                vec![Shape(LineRegionKind::Block, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn bare_brace_opener_is_block() {
        let src = lines(&["{", "    x = 1", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                3,
                vec![Shape(LineRegionKind::Block, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn extra_close_brace_is_silent_leaf() {
        // One `}` too many: stays as a leaf under Root, no panic.
        let src = lines(&["if (a) {", "    x = 1", "}", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                4,
                vec![Shape(LineRegionKind::If, 0, 3, vec![])],
            )
        );
    }

    #[test]
    fn stray_else_without_if_is_silent_leaf() {
        // `} else {` with no preceding If: dropped as a leaf, the
        // trailing `}` underflows and is dropped too. No panic.
        let src = lines(&["} else {", "    y = 2", "}"]);
        let tree = build_region_tree(&src);
        assert_eq!(shape_of(&tree), Shape(LineRegionKind::Root, 0, 3, vec![]));
    }

    #[test]
    fn unclosed_opener_is_clamped_to_input_end() {
        // Opener with no matching close: region extends to end of input.
        let src = lines(&["if (a) {", "    x = 1"]);
        let tree = build_region_tree(&src);
        assert_eq!(
            shape_of(&tree),
            Shape(
                LineRegionKind::Root,
                0,
                2,
                vec![Shape(LineRegionKind::If, 0, 2, vec![])],
            )
        );
    }
}
