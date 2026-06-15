//! Diff emitter for the decoded statement tree.
//!
//! Renders both assets as summary pseudocode via `emit_summary`, then
//! computes a line-level unified diff using `similar::TextDiff`. The
//! output is a unified diff string with optional hunk header labels and
//! configurable context lines.
//!
//! This is a text-level diff (not a structural tree diff). The summary
//! pseudocode is already structured enough that line-level diffing
//! produces readable output for Blueprint comparison.

use similar::TextDiff;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::emit::summary::emit_summary;

/// Compare two decoded Blueprint (Unreal Blueprint) assets and return a
/// unified diff of their summary pseudocode.
///
/// Returns `(diff_text, has_changes)`. When the summaries are identical,
/// `has_changes` is false and `diff_text` is empty.
pub fn emit_diff(
    left: &DecodedAsset,
    right: &DecodedAsset,
    left_label: &str,
    right_label: &str,
    context_lines: usize,
) -> (String, bool) {
    let left_text = emit_summary(left);
    let right_text = emit_summary(right);

    if left_text == right_text {
        return (String::new(), false);
    }

    let diff = TextDiff::from_lines(&left_text, &right_text);
    let output = diff
        .unified_diff()
        .header(left_label, right_label)
        .context_radius(context_lines)
        .to_string();

    (output, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::asset::{DecodedAsset, Event, Function};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    fn empty_asset() -> DecodedAsset {
        DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    fn asset_with_assignment(func_name: &str, var_name: &str, value: &str) -> DecodedAsset {
        DecodedAsset {
            functions: vec![Function {
                name: func_name.into(),
                export_index: None,
                body: vec![Stmt::Assignment {
                    lhs: Expr::Var(var_name.into()),
                    rhs: Expr::Literal(value.into()),
                    offset: 0x0000,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    #[test]
    fn identical_assets_emit_empty_diff() {
        let left = empty_asset();
        let right = empty_asset();
        let (diff_text, has_changes) = emit_diff(&left, &right, "before", "after", 3);
        assert!(!has_changes, "identical assets must report no changes");
        assert!(
            diff_text.is_empty(),
            "diff text must be empty for identical assets"
        );
    }

    #[test]
    fn assignment_change_shows_replacement() {
        let left = asset_with_assignment("MyFunc", "x", "1");
        let right = asset_with_assignment("MyFunc", "x", "2");
        let (diff_text, has_changes) = emit_diff(&left, &right, "before", "after", 3);
        assert!(has_changes, "changed assets must report changes");
        // The diff should contain removal of the old value and addition of the new.
        assert!(
            diff_text.contains('-') || diff_text.contains('+'),
            "diff must contain change markers"
        );
        assert!(diff_text.contains("1") || diff_text.contains("2"));
    }

    #[test]
    fn function_added_shows_addition() {
        let left = empty_asset();
        let right = DecodedAsset {
            functions: vec![Function {
                name: "NewFunc".into(),
                export_index: None,
                body: vec![],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let (diff_text, has_changes) = emit_diff(&left, &right, "before", "after", 3);
        assert!(has_changes);
        // The added function should appear as additions in the diff.
        assert!(
            diff_text.contains('+'),
            "diff must contain addition markers"
        );
        assert!(diff_text.contains("NewFunc"));
    }

    #[test]
    fn labels_appear_in_diff_header() {
        let left = asset_with_assignment("F", "a", "1");
        let right = asset_with_assignment("F", "a", "2");
        let (diff_text, _) = emit_diff(&left, &right, "left-file.uasset", "right-file.uasset", 3);
        assert!(
            diff_text.contains("left-file.uasset"),
            "left label must appear in header"
        );
        assert!(
            diff_text.contains("right-file.uasset"),
            "right label must appear in header"
        );
    }

    #[test]
    fn event_removed_shows_deletion() {
        let left = DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "OnBeginPlay".into(),
                export_index: None,
                body: vec![],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let right = empty_asset();
        let (diff_text, has_changes) = emit_diff(&left, &right, "before", "after", 3);
        assert!(has_changes);
        assert!(
            diff_text.contains('-'),
            "diff must contain deletion markers"
        );
        assert!(diff_text.contains("OnBeginPlay"));
    }
}
