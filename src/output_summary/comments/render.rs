//! Render a comment box's text into the summary marker lines.
//!
//! The marker syntax is `<indent>// "<text>"`, a line comment whose payload
//! is the quoted comment text. This is distinct from the structural markers
//! (`// called by:`, `// sequence [N]:`) which are never quoted, so a reader
//! can tell an authored annotation from a generated legibility aid.
//!
//! Each source paragraph wraps independently at [`COMMENT_WRAP_WIDTH`]
//! columns. A single wrapped line reads `// "text"`; a multi-line paragraph
//! opens the quote on the first line, closes it on the last, and indents
//! continuation lines by two extra spaces after the `//` so the wrapped body
//! lines up under the opening quote.
//!
//! Editor comment text uses CRLF line endings and may carry stray whitespace
//! (a trailing carriage return, doubled spaces). Paragraphs split via
//! `str::lines`, each paragraph is trimmed (empty ones are skipped), and words
//! are re-joined through `split_whitespace`, so no raw `\r` or doubled space
//! survives into the rendered marker.

/// Column width a rendered comment paragraph wraps at. The wrap is measured
/// against the full line including the `indent` prefix and the `// ` marker.
pub(crate) const COMMENT_WRAP_WIDTH: usize = 100;

/// Render `text` as the summary comment lines at `indent`.
///
/// `indent` is the leading whitespace each line starts with (the indent of
/// the construct the comment annotates, or the block-header indent for
/// event/function-level placements). Returns one `String` per output line,
/// without trailing newlines. Returns an empty vector for empty or
/// whitespace-only text.
pub(crate) fn render_comment_lines(text: &str, indent: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for paragraph in text.lines() {
        render_paragraph(paragraph, indent, &mut lines);
    }
    lines
}

/// Wrap one paragraph and push its rendered lines onto `out`.
///
/// The opening `// "` and closing `"` bracket the whole paragraph; the quote
/// marks sit on the first and last wrapped line respectively. Continuation
/// lines use `//  ` (two spaces after the slashes) so the wrapped words align
/// under the opening quote. Empty (or whitespace-only) paragraphs render
/// nothing.
fn render_paragraph(paragraph: &str, indent: &str, out: &mut Vec<String>) {
    let first_prefix = format!("{indent}// \"");
    let cont_prefix = format!("{indent}//  ");

    let mut wrapped: Vec<String> = Vec::new();
    let mut current = String::new();
    for word in paragraph.split_whitespace() {
        let prefix_len = if wrapped.is_empty() {
            first_prefix.len()
        } else {
            cont_prefix.len()
        };
        // The closing quote only lands on the final line, so it does not
        // factor into the per-line wrap budget here.
        if !current.is_empty() && prefix_len + current.len() + 1 + word.len() > COMMENT_WRAP_WIDTH {
            wrapped.push(std::mem::take(&mut current));
        }
        if current.is_empty() {
            current.push_str(word);
        } else {
            current.push(' ');
            current.push_str(word);
        }
    }
    if !current.is_empty() {
        wrapped.push(current);
    }

    let Some(last_index) = wrapped.len().checked_sub(1) else {
        return;
    };
    for (index, segment) in wrapped.into_iter().enumerate() {
        let prefix = if index == 0 {
            &first_prefix
        } else {
            &cont_prefix
        };
        let suffix = if index == last_index { "\"" } else { "" };
        out.push(format!("{prefix}{segment}{suffix}"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_short_line() {
        let lines = render_comment_lines("A linear event, two calls one after the other", "  ");
        assert_eq!(
            lines,
            vec!["  // \"A linear event, two calls one after the other\""]
        );
    }

    #[test]
    fn body_indent_single_line() {
        let lines =
            render_comment_lines("A cast with both the Success and Failed pins wired", "    ");
        assert_eq!(
            lines,
            vec!["    // \"A cast with both the Success and Failed pins wired\""]
        );
    }

    #[test]
    fn long_line_wraps_with_aligned_continuation() {
        let text = "Left side of a paired axis input. Above the threshold runs Attempt, \
                    dropping below resets Attempt and runs Release.";
        let lines = render_comment_lines(text, "    ");
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("    // \""));
        assert!(!lines[0].ends_with('"'), "first line keeps the quote open");
        // Continuation line uses two spaces after the slashes.
        assert!(lines[1].starts_with("    //  "));
        assert!(lines[1].ends_with('"'), "last line closes the quote");
        // Every line stays within the wrap budget.
        for line in &lines {
            assert!(
                line.len() <= COMMENT_WRAP_WIDTH,
                "line over budget: {line:?}"
            );
        }
    }

    #[test]
    fn explicit_newline_splits_paragraphs() {
        let lines = render_comment_lines("first para\nsecond para", "  ");
        assert_eq!(lines, vec!["  // \"first para\"", "  // \"second para\""]);
    }

    #[test]
    fn crlf_newline_splits_paragraphs_without_carriage_return() {
        // Editor comment text uses CRLF; no raw `\r` may survive into the
        // rendered marker (it would display as a bare `"` line under
        // universal-newline tooling).
        let lines = render_comment_lines(
            "Since we attach to movable components when climbing,\r\nreset roll and pitch rotation to zero",
            "  ",
        );
        assert_eq!(
            lines,
            vec![
                "  // \"Since we attach to movable components when climbing,\"",
                "  // \"reset roll and pitch rotation to zero\"",
            ]
        );
    }

    #[test]
    fn stray_trailing_carriage_return_is_trimmed() {
        // `str::lines` only strips `\r` from `\r\n`; a lone trailing `\r`
        // must still be normalised away by the whitespace re-join.
        let lines = render_comment_lines("Attempt and runs Release.\r", "  ");
        assert_eq!(lines, vec!["  // \"Attempt and runs Release.\""]);
    }

    #[test]
    fn interior_whitespace_runs_collapse() {
        // Doubled spaces and trailing whitespace collapse under the
        // `split_whitespace` re-join.
        let lines = render_comment_lines("Make  sure we are gripping something  ", "  ");
        assert_eq!(lines, vec!["  // \"Make sure we are gripping something\""]);
    }

    #[test]
    fn empty_text_renders_nothing() {
        // Empty paragraphs are skipped entirely; callers also drop empty-text
        // boxes during extraction, so this is defensive only.
        assert!(render_comment_lines("", "  ").is_empty());
        assert!(render_comment_lines("   \r\n  ", "  ").is_empty());
    }

    #[test]
    fn continuation_format_brackets_the_paragraph() {
        // Opening quote only on the first line, continuation `//` plus two
        // spaces, closing quote on the last text line.
        let text = "Left side of a paired axis input. Above the threshold runs Attempt, \
                    dropping below resets Attempt and runs Release.\r";
        let lines = render_comment_lines(text, "    ");
        assert_eq!(
            lines,
            vec![
                "    // \"Left side of a paired axis input. Above the threshold runs Attempt, dropping below resets",
                "    //  Attempt and runs Release.\"",
            ]
        );
    }

    #[test]
    fn single_word_longer_than_budget_is_not_split() {
        let word = "x".repeat(200);
        let lines = render_comment_lines(&word, "");
        // One oversized word cannot be broken; it stays on its own line.
        assert_eq!(lines.len(), 1);
        assert!(lines[0].starts_with("// \""));
        assert!(lines[0].ends_with('"'));
    }
}
