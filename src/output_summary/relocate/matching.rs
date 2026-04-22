//! Match the body of an `IfBlock` against `BranchInfo` pin-only sets.

use std::collections::BTreeSet;

use crate::pin_hints::BranchInfo;

use super::if_block::IfBlock;

/// Scan `branches` for exactly one `BranchInfo` whose
/// `then_only ∪ else_only` intersects the callee names found inside
/// `block`. Returns `Some` only when exactly one branch matches.
pub(super) fn match_branch_info<'a>(
    lines: &[String],
    block: &IfBlock,
    branches: &'a [BranchInfo],
) -> Option<&'a BranchInfo> {
    let inside = collect_body_names(lines, block);
    if inside.is_empty() {
        return None;
    }
    let mut matched: Option<&BranchInfo> = None;
    for info in branches {
        let sides: BTreeSet<String> = info
            .then_only_callees()
            .union(&info.else_only_callees())
            .cloned()
            .collect();
        if sides.is_empty() || sides.is_disjoint(&inside) {
            continue;
        }
        if matched.is_some() {
            return None; // ambiguous
        }
        matched = Some(info);
    }
    matched
}

/// Collect callee-like names appearing on either side of an if-block.
/// Looks at the last capitalized identifier on each body line, which
/// catches `DoOnce(Name)`, `ResetDoOnce(Name)`, and `Name(args)` shapes.
fn collect_body_names(lines: &[String], block: &IfBlock) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut absorb = |range: std::ops::Range<usize>| {
        for line in lines.get(range).into_iter().flatten() {
            if let Some(name) = last_capitalized_ident(line) {
                names.insert(name);
            }
        }
    };
    absorb((block.if_idx + 1)..block.then_close_idx);
    if let (Some(open), Some(close)) = (block.else_open_idx, block.else_close_idx) {
        absorb((open + 1)..close);
    }
    names
}

/// Return the last capitalized ASCII identifier in `line`, or `None`.
/// Used to extract callee names: the matcher downstream is a subset
/// test, so any one capitalized identifier on the line suffices.
fn last_capitalized_ident(line: &str) -> Option<String> {
    line.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .rfind(|tok| tok.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
        .map(str::to_string)
}
