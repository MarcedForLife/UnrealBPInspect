use similar::TextDiff;

/// Render a unified diff between two already-formatted summary texts.
///
/// Returns `(diff_text, has_changes)`; when the texts are identical,
/// `has_changes` is false and `diff_text` is empty. Used by the CLI's
/// summary diff path.
pub fn diff_summary_texts(
    before_text: &str,
    after_text: &str,
    before_label: &str,
    after_label: &str,
    context_lines: usize,
) -> (String, bool) {
    if before_text == after_text {
        return (String::new(), false);
    }

    let diff = TextDiff::from_lines(before_text, after_text);
    let output = diff
        .unified_diff()
        .header(before_label, after_label)
        .context_radius(context_lines)
        .to_string();

    (output, true)
}
