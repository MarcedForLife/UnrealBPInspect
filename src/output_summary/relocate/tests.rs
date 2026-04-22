use std::collections::BTreeMap;

use crate::pin_hints::{BranchHints, BranchInfo};

use super::if_block::condition_is_inverted;
use super::relocate_with_hints;
use super::rewrite::parse_doonce_open;

fn make_info(branch_export_idx: usize, then: &[&str], else_: &[&str]) -> BranchInfo {
    BranchInfo {
        branch_export_idx,
        then_callees: then.iter().map(|s| s.to_string()).collect(),
        else_callees: else_.iter().map(|s| s.to_string()).collect(),
    }
}

fn make_hints(key: &str, infos: Vec<BranchInfo>) -> BranchHints {
    let mut by_function: BTreeMap<String, Vec<BranchInfo>> = BTreeMap::new();
    by_function.insert(key.into(), infos);
    BranchHints { by_function }
}

fn to_lines(text: &str) -> Vec<String> {
    text.lines().map(|s| s.to_string()).collect()
}

#[test]
fn parses_doonce_open() {
    assert_eq!(
        parse_doonce_open("DoOnce(Attempt) {"),
        Some("Attempt".into())
    );
    assert_eq!(parse_doonce_open("DoOnce(A){"), Some("A".into()));
    assert_eq!(parse_doonce_open("DoOnce()"), None);
    assert_eq!(parse_doonce_open("not a doonce"), None);
}

#[test]
fn detects_inverted_condition() {
    assert!(condition_is_inverted("if (!(x >= y)) {"));
    assert!(condition_is_inverted("if (!x) {"));
    assert!(!condition_is_inverted("if (x >= y) {"));
}

#[test]
fn basic_relocation_inverted_un_inverts_condition() {
    // Mirrors the GripRight shape: inverted if with Reset inside, plus
    // two orphan DoOnces following. The pass should un-invert the
    // condition and place each orphan on its pin-derived side.
    let mut lines = to_lines(
        "self.X = Axis\n\
         if (!(self.X >= self.T)) {\n\
         ResetDoOnce(Attempt)\n\
         }\n\
         DoOnce(Attempt) {\n\
         Attempt(false)\n\
         ResetDoOnce(Release)\n\
         }\n\
         DoOnce(Release) {\n\
         Release(false)\n\
         }",
    );
    let hints = make_hints("ev", vec![make_info(10, &["Attempt"], &["Release"])]);
    relocate_with_hints(&mut lines, "ev", &hints);

    let joined = lines.join("\n");
    assert!(
        joined.contains("if (self.X >= self.T) {"),
        "condition un-inverted: {}",
        joined
    );
    assert!(
        !joined.contains("if (!(self.X >= self.T))"),
        "negation removed: {}",
        joined
    );

    let if_idx = lines
        .iter()
        .position(|l| l.trim() == "if (self.X >= self.T) {")
        .unwrap();
    let else_pivot = lines
        .iter()
        .position(|l| l.trim() == "} else {")
        .expect("else branch created");
    let final_close = lines
        .iter()
        .enumerate()
        .skip(else_pivot + 1)
        .find(|(_, l)| l.trim() == "}")
        .map(|(i, _)| i)
        .unwrap();
    let then_body: String = lines[if_idx + 1..else_pivot].join("\n");
    let else_body: String = lines[else_pivot + 1..final_close].join("\n");
    assert!(
        then_body.contains("DoOnce(Attempt)"),
        "then body should have DoOnce(Attempt): {}",
        then_body
    );
    assert!(
        else_body.contains("ResetDoOnce(Attempt)"),
        "else body keeps ResetDoOnce(Attempt): {}",
        else_body
    );
    assert!(
        else_body.contains("DoOnce(Release)"),
        "else body should have DoOnce(Release): {}",
        else_body
    );
}

#[test]
fn basic_relocation_non_inverted_preserves_existing_else() {
    let mut lines = to_lines(
        "if (x >= y) {\n\
         DoOnce(A) {\n\
         A(true)\n\
         }\n\
         } else {\n\
         ResetDoOnce(A)\n\
         }\n\
         DoOnce(B) {\n\
         B(false)\n\
         }",
    );
    let hints = make_hints("ev", vec![make_info(10, &["A"], &["B"])]);
    relocate_with_hints(&mut lines, "ev", &hints);
    let joined = lines.join("\n");
    assert!(joined.contains("DoOnce(B)"), "B kept somewhere: {}", joined);
    let else_open = lines
        .iter()
        .position(|l| l.trim() == "} else {")
        .expect("preserved else");
    let after_else: String = lines[else_open..].join("\n");
    assert!(
        after_else.contains("DoOnce(B)"),
        "DoOnce(B) should be in/after the else: {}",
        after_else
    );
}

#[test]
fn unknown_orphan_is_skipped() {
    let mut lines = to_lines(
        "if (cond) {\n\
         Known()\n\
         }\n\
         DoOnce(Unrelated) {\n\
         Do()\n\
         }",
    );
    let hints = make_hints("ev", vec![make_info(10, &["Known"], &["OtherSide"])]);
    let before = lines.clone();
    relocate_with_hints(&mut lines, "ev", &hints);
    assert_eq!(lines, before, "Unrelated DoOnce must stay put");
}

#[test]
fn no_hints_is_noop() {
    let mut lines = to_lines(
        "if (cond) { Foo() }\n\
         DoOnce(Bar) { Bar() }",
    );
    let before = lines.clone();
    let hints = BranchHints::default();
    relocate_with_hints(&mut lines, "other_key", &hints);
    assert_eq!(lines, before);
}

#[test]
fn ambiguous_multiple_matches_skipped() {
    // Two BranchInfos with non-empty sides both overlap the if-body,
    // so the match is ambiguous and nothing moves.
    let mut lines = to_lines(
        "if (cond) {\n\
         Shared()\n\
         }\n\
         DoOnce(Shared) {\n\
         Shared()\n\
         }",
    );
    let hints = make_hints(
        "ev",
        vec![
            make_info(1, &["Shared"], &["X"]),
            make_info(2, &["Shared"], &["Y"]),
        ],
    );
    let before = lines.clone();
    relocate_with_hints(&mut lines, "ev", &hints);
    assert_eq!(lines, before);
}

#[test]
fn non_adjacent_orphan_not_pulled() {
    let mut lines = to_lines(
        "if (cond) {\n\
         Known()\n\
         }\n\
         Unrelated()\n\
         DoOnce(Known) {\n\
         Known()\n\
         }",
    );
    let hints = make_hints("ev", vec![make_info(10, &["Known"], &["Other"])]);
    let before = lines.clone();
    relocate_with_hints(&mut lines, "ev", &hints);
    assert_eq!(lines, before);
}
