use similar::TextDiff;

use crate::output_summary::{filter_summary, format_summary};
use crate::parser::parse_asset;

/// Compare two `.uasset` files and return a unified diff of their summaries.
///
/// Returns `(diff_text, has_changes)`. When the summaries are identical,
/// `has_changes` is false and `diff_text` is empty.
pub fn format_diff(
    before_data: &[u8],
    after_data: &[u8],
    before_label: &str,
    after_label: &str,
    filters: &[String],
    context_lines: usize,
) -> anyhow::Result<(String, bool)> {
    let before_asset = parse_asset(before_data, false)?;
    let after_asset = parse_asset(after_data, false)?;
    let before_text = filter_summary(&format_summary(&before_asset), filters);
    let after_text = filter_summary(&format_summary(&after_asset), filters);

    if before_text == after_text {
        return Ok((String::new(), false));
    }

    let diff = TextDiff::from_lines(&before_text, &after_text);
    let output = diff
        .unified_diff()
        .header(before_label, after_label)
        .context_radius(context_lines)
        .to_string();

    Ok((output, true))
}
