//! Pin-aware else-branch classifier.
//!
//! Given a branch offset and the decoded text of each side, consult pin
//! hints + bytecode map to decide whether the physical order matches pin
//! evidence. Returns `(Some(0), Some(0))` to signal "classified", or
//! `(None, None)` when the evidence is silent or contradictory.

use std::collections::BTreeSet;

use super::bytecode_map::BytecodeBranchMap;
use super::types::{BranchHints, BranchSide};

/// Answer shape returned by both the CFG and pin-aware else-branch detectors.
///
/// Mirrors the tuple returned by `detect_else_branch_via_cfg`, where
/// `jump_idx` marks the true-branch terminating jump and `end_idx` marks
/// the else-block's exclusive end. `(None, None)` means the detector could
/// not classify an else-branch.
///
/// The pin-aware detector returns `(Some(0), Some(0))` as a sentinel
/// meaning "classified with confidence"; the caller resolves concrete
/// indices from the surrounding CFG when the sentinel fires.
pub type ElseBranchAnswer = (Option<usize>, Option<usize>);

const CLASSIFIED: ElseBranchAnswer = (Some(0), Some(0));
const UNKNOWN: ElseBranchAnswer = (None, None);

/// Pin-aware parallel to `detect_else_branch_via_cfg`.
///
/// Returns `CLASSIFIED` when pins classify the two sides consistently
/// with their physical order (then-side matches then-only callees and/or
/// else-side matches else-only callees, with no contradiction). Returns
/// `UNKNOWN` when the branch is unmapped, the hint sets are empty, the
/// evidence is contradictory, or no callees appear in the text windows.
pub fn detect_else_branch_via_pins(
    bytecode_offset: u32,
    function_key: &str,
    hints: &BranchHints,
    map: &BytecodeBranchMap,
    then_side_text: &[&str],
    else_side_text: &[&str],
) -> ElseBranchAnswer {
    let Some(branch_export) = map
        .offset_to_branch
        .get(&(function_key.to_string(), bytecode_offset))
        .copied()
    else {
        return UNKNOWN;
    };

    let Some(branches) = hints.by_function.get(function_key) else {
        return UNKNOWN;
    };
    let Some(info) = branches
        .iter()
        .find(|b| b.branch_export_idx == branch_export)
    else {
        return UNKNOWN;
    };

    let then_only = info.then_only_callees();
    let else_only = info.else_only_callees();
    if then_only.is_empty() && else_only.is_empty() {
        return UNKNOWN;
    }

    let classify = |side: &BTreeSet<String>| -> Option<BranchSide> {
        match (!side.is_disjoint(&then_only), !side.is_disjoint(&else_only)) {
            (true, false) => Some(BranchSide::Then),
            (false, true) => Some(BranchSide::Else),
            _ => None,
        }
    };

    let then_class = classify(&callees_in_text(then_side_text));
    let else_class = classify(&callees_in_text(else_side_text));

    match (then_class, else_class) {
        // Consistent with physical order, or one side unambiguous + other quiet.
        (Some(BranchSide::Then), Some(BranchSide::Else))
        | (Some(BranchSide::Then), None)
        | (None, Some(BranchSide::Else)) => CLASSIFIED,
        _ => UNKNOWN,
    }
}

/// Thin wrapper around `detect_else_branch_via_pins` that sources hints
/// and map from the thread-local `pin_hints_scope`. Returns `UNKNOWN`
/// when no scope is installed (e.g. raw bytecode tests bypassing the
/// summary pipeline).
pub fn detect_else_branch_via_pins_scoped(
    bytecode_offset: u32,
    function_key: &str,
    then_side_text: &[&str],
    else_side_text: &[&str],
) -> ElseBranchAnswer {
    crate::pin_hints_scope::with(|scope| match scope {
        Some((hints, map)) => detect_else_branch_via_pins(
            bytecode_offset,
            function_key,
            hints,
            map,
            then_side_text,
            else_side_text,
        ),
        None => UNKNOWN,
    })
}

/// Best-effort extraction of callee short names referenced anywhere in a
/// slice of statement texts. Matches shapes produced by the bytecode
/// decoder: bare `Name(...)`, `self.Name(...)`, `$Name_ReturnValue`, and
/// `self.Member.Name(...)`.
fn callees_in_text(lines: &[&str]) -> BTreeSet<String> {
    let is_token_char = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.';
    let mut found = BTreeSet::new();
    for line in lines {
        for tok in line.split(|c: char| !is_token_char(c)) {
            if let Some(name) = extract_callee_token(tok) {
                found.insert(name);
            }
        }
    }
    found
}

fn extract_callee_token(tok: &str) -> Option<String> {
    if tok.is_empty() {
        return None;
    }
    // `$Foo_ReturnValue` or `$Foo_ReturnValue_2` carries the callee name.
    if let Some(rest) = tok.strip_prefix('$') {
        let idx = rest.find("_ReturnValue")?;
        return (idx > 0).then(|| rest[..idx].to_string());
    }
    // Bare `Name` or dotted `a.b.Name` gives the last segment. Filter
    // out lowercase-only tokens to skip keywords like `if`, `jump`, `self`.
    let last = tok.rsplit('.').next()?;
    last.chars()
        .next()
        .filter(char::is_ascii_uppercase)
        .map(|_| last.to_string())
}
