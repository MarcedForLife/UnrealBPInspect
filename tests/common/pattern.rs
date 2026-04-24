// Structural-assertion helpers for the bp-inspect summary output.
//
// These utilities parse the human-readable summary into a tree of events,
// functions, and nested blocks so tests can make structural claims (such as
// "this event has an if-block with a DoOnce in its then-branch") without
// matching exact whitespace, line numbers, or comment text.
//
// The helpers intentionally cover the shapes the current regression tests
// need; extend them when a new assertion is required rather than trying to
// model every possible output shape upfront.

#![allow(dead_code)]

/// A parsed view of the full summary output.
pub struct OutputAssertion {
    blocks: Vec<TopBlock>,
}

/// A top-level event or function definition.
#[derive(Debug, Clone)]
struct TopBlock {
    name: String,
    /// Raw header line (indent stripped) -- preserved for diagnostics.
    header: String,
    /// Lines of the body, each stripped of a common indent prefix relative to
    /// the header. `Line::raw` retains the remaining leading whitespace so
    /// indentation-based block structure can still be recovered.
    body: Vec<Line>,
}

#[derive(Debug, Clone)]
struct Line {
    /// Body content with the header's indent+2 stripped off the left.
    /// Lines that are blank keep their emptiness but are stored as "".
    text: String,
    /// Indent measured relative to the header body start (0 = top level of
    /// event/function body, 4 = inside a single nested block, and so on).
    indent: usize,
}

impl OutputAssertion {
    pub fn from(summary: &str) -> Self {
        Self {
            blocks: parse_top_blocks(summary),
        }
    }

    /// Start an assertion chain against an event by name. Panics if no event
    /// with that name exists.
    pub fn event(&self, name: &str) -> EventAssertion<'_> {
        match self.find_block(name) {
            Some(block) => EventAssertion {
                owner: block.name.clone(),
                kind: "event",
                scope: Scope::from_block(block),
            },
            None => panic!(
                "event `{name}` not found. Available top-level blocks:\n{}",
                self.list_blocks()
            ),
        }
    }

    /// Start an assertion chain against a function by name. Panics if no
    /// function with that name exists.
    pub fn function(&self, name: &str) -> EventAssertion<'_> {
        match self.find_block(name) {
            Some(block) => EventAssertion {
                owner: block.name.clone(),
                kind: "function",
                scope: Scope::from_block(block),
            },
            None => panic!(
                "function `{name}` not found. Available top-level blocks:\n{}",
                self.list_blocks()
            ),
        }
    }

    fn find_block(&self, name: &str) -> Option<&TopBlock> {
        self.blocks.iter().find(|b| b.name == name)
    }

    fn list_blocks(&self) -> String {
        self.blocks
            .iter()
            .map(|b| format!("  - {}", b.header))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// Top-level fluent assertion chain (works for both events and functions).
/// "event" is in the type name because the original API request named it so,
/// but functions share the same shape.
pub struct EventAssertion<'a> {
    owner: String,
    kind: &'static str,
    scope: Scope<'a>,
}

impl<'a> EventAssertion<'a> {
    /// Narrow the scope to the top-level statements of the event, ignoring
    /// anything nested in an if-block, DoOnce, etc. Useful for asserting that
    /// a call happens "directly" in the event, not inside a guard.
    pub fn top_level(self) -> Self {
        Self {
            scope: self.scope.at_indent(0),
            ..self
        }
    }

    /// Assert that at least one line in scope contains `needle`.
    pub fn contains_line_matching(self, needle: &str) -> Self {
        if !self.scope.any_line_contains(needle) {
            panic!(
                "{} `{}` did not contain any line matching `{}`.\nScope contents:\n{}",
                self.kind,
                self.owner,
                needle,
                self.scope.render(),
            );
        }
        self
    }

    /// Assert that NO line in scope contains `needle`.
    pub fn does_not_contain_line_matching(self, needle: &str) -> Self {
        if self.scope.any_line_contains(needle) {
            panic!(
                "{} `{}` unexpectedly contained a line matching `{}`.\nScope contents:\n{}",
                self.kind,
                self.owner,
                needle,
                self.scope.render(),
            );
        }
        self
    }

    /// Assert that a DoOnce with the given key name appears somewhere in
    /// scope (including nested). Returns a block assertion scoped to the
    /// DoOnce body.
    pub fn contains_do_once(self, do_once_name: &str) -> BlockBodyAssertion<'a> {
        let header = format!("DoOnce({do_once_name})");
        match self.scope.find_opening_block(&header) {
            Some(body) => BlockBodyAssertion {
                owner: self.owner,
                label: format!("DoOnce({do_once_name}) in {}", self.kind),
                scope: body,
            },
            None => panic!(
                "{} `{}` did not contain `DoOnce({do_once_name}) {{`.\nScope contents:\n{}",
                self.kind,
                self.owner,
                self.scope.render(),
            ),
        }
    }

    /// Assert that a FlipFlop with the given key name appears somewhere in
    /// scope. Returns a block assertion scoped to the FlipFlop's A|B body.
    pub fn contains_flip_flop(self, flip_flop_name: &str) -> BlockBodyAssertion<'a> {
        let header = format!("FlipFlop({flip_flop_name})");
        match self.scope.find_opening_block(&header) {
            Some(flip_body) => {
                // FlipFlop bodies always wrap an inner "A|B: {" sub-block.
                match flip_body.find_opening_block("A|B:") {
                    Some(ab_body) => BlockBodyAssertion {
                        owner: self.owner,
                        label: format!("FlipFlop({flip_flop_name}) A|B in {}", self.kind),
                        scope: ab_body,
                    },
                    None => panic!(
                        "FlipFlop({flip_flop_name}) in {} `{}` did not contain an `A|B:` body.\nFlipFlop contents:\n{}",
                        self.kind,
                        self.owner,
                        flip_body.render(),
                    ),
                }
            }
            None => panic!(
                "{} `{}` did not contain `FlipFlop({flip_flop_name}) {{`.\nScope contents:\n{}",
                self.kind,
                self.owner,
                self.scope.render(),
            ),
        }
    }

    /// Assert that a top-level `ResetDoOnce(name)` call appears in scope.
    pub fn contains_reset_do_once(self, do_once_name: &str) -> Self {
        let needle = format!("ResetDoOnce({do_once_name})");
        self.contains_line_matching(&needle)
    }

    /// Find the first `if (...)` whose condition contains `cond_substr`.
    /// Returns a handle that can be narrowed to the then/else branch.
    pub fn has_if_block_with_condition_containing(self, cond_substr: &str) -> IfBlockAssertion<'a> {
        match self.scope.find_if_with_condition(cond_substr) {
            Some(if_block) => IfBlockAssertion {
                owner: self.owner,
                scope: if_block,
                cond_substr: cond_substr.to_string(),
            },
            None => panic!(
                "{} `{}` did not contain an if-block with condition containing `{}`.\nScope contents:\n{}",
                self.kind,
                self.owner,
                cond_substr,
                self.scope.render(),
            ),
        }
    }

    /// True when the first-level scope (or a nested `if` inside it) contains
    /// at least one line matching needle. Returns a bool rather than
    /// asserting, useful for conditional test-state verification.
    pub fn has_line(&self, needle: &str) -> bool {
        self.scope.any_line_contains(needle)
    }
}

/// A block that opens with `KEYWORD {` (DoOnce, FlipFlop, A|B:, etc.).
/// Scoped to the statements inside its braces.
pub struct BlockBodyAssertion<'a> {
    owner: String,
    label: String,
    scope: Scope<'a>,
}

impl<'a> BlockBodyAssertion<'a> {
    pub fn contains_line_matching(self, needle: &str) -> Self {
        if !self.scope.any_line_contains(needle) {
            panic!(
                "{} (in `{}`) did not contain a line matching `{}`.\nBody contents:\n{}",
                self.label,
                self.owner,
                needle,
                self.scope.render(),
            );
        }
        self
    }

    pub fn contains_reset_do_once(self, do_once_name: &str) -> Self {
        let needle = format!("ResetDoOnce({do_once_name})");
        self.contains_line_matching(&needle)
    }

    pub fn contains_do_once(self, do_once_name: &str) -> BlockBodyAssertion<'a> {
        let header = format!("DoOnce({do_once_name})");
        match self.scope.find_opening_block(&header) {
            Some(body) => BlockBodyAssertion {
                owner: self.owner,
                label: format!("DoOnce({do_once_name}) inside {}", self.label),
                scope: body,
            },
            None => panic!(
                "{} (in `{}`) did not contain `DoOnce({do_once_name}) {{`.\nBody contents:\n{}",
                self.label,
                self.owner,
                self.scope.render(),
            ),
        }
    }
}

/// An if/else block with a known condition. Call `.then_branch()` or
/// `.else_branch()` to scope inside a specific arm.
pub struct IfBlockAssertion<'a> {
    owner: String,
    scope: IfScope<'a>,
    cond_substr: String,
}

impl<'a> IfBlockAssertion<'a> {
    pub fn then_branch(self) -> BlockBodyAssertion<'a> {
        BlockBodyAssertion {
            owner: self.owner,
            label: format!("then-branch of if (… {} …)", self.cond_substr),
            scope: self.scope.then_scope,
        }
    }

    pub fn else_branch(self) -> BlockBodyAssertion<'a> {
        match self.scope.else_scope {
            Some(scope) => BlockBodyAssertion {
                owner: self.owner,
                label: format!("else-branch of if (… {} …)", self.cond_substr),
                scope,
            },
            None => panic!(
                "if-block with condition containing `{}` in `{}` has no else branch.\nThen-branch contents:\n{}",
                self.cond_substr,
                self.owner,
                self.scope.then_scope.render(),
            ),
        }
    }

    pub fn has_else(&self) -> bool {
        self.scope.else_scope.is_some()
    }
}

// --- internals ---------------------------------------------------------

/// Slice view of a block's body lines plus an indent-floor indicating the
/// lexical "top level" of the current scope.
#[derive(Clone)]
struct Scope<'a> {
    lines: &'a [Line],
    /// The indentation value that counts as "top level" for this scope.
    /// Lines with `indent == floor` are the direct children.
    floor: usize,
    /// When true, assertions only consider lines at exactly `floor`; nested
    /// content is ignored. Set via `at_indent()` (top_level() entry point).
    direct_only: bool,
}

struct IfScope<'a> {
    then_scope: Scope<'a>,
    else_scope: Option<Scope<'a>>,
}

impl<'a> Scope<'a> {
    fn from_block(block: &'a TopBlock) -> Self {
        Self {
            lines: &block.body,
            floor: 0,
            direct_only: false,
        }
    }

    fn at_indent(self, floor: usize) -> Self {
        Self {
            lines: self.lines,
            floor,
            direct_only: true,
        }
    }

    fn render(&self) -> String {
        let mut out = String::new();
        for line in self.lines {
            out.push_str(&" ".repeat(line.indent));
            out.push_str(&line.text);
            out.push('\n');
        }
        if out.is_empty() {
            out.push_str("  (empty)\n");
        }
        out
    }

    /// True if any line in this scope contains `needle`.
    ///
    /// By default we scan every body line in this scope (useful for "does
    /// this event mention X anywhere in its body"). When `direct_only` is
    /// set -- via `at_indent()` / `top_level()` -- we only scan lines at
    /// exactly `floor` so "top_level()" means "not inside any nested
    /// block".
    fn any_line_contains(&self, needle: &str) -> bool {
        if self.direct_only {
            self.lines
                .iter()
                .filter(|l| l.indent == self.floor)
                .any(|l| l.text.contains(needle))
        } else {
            self.lines.iter().any(|l| l.text.contains(needle))
        }
    }

    /// Look for a block-opener line (non-if, non-else) whose text starts with
    /// `prefix` and ends with `{`. Returns a Scope of the lines inside the
    /// matching `}`.
    fn find_opening_block(&self, prefix: &str) -> Option<Scope<'a>> {
        for (idx, line) in self.lines.iter().enumerate() {
            if line.text.starts_with(prefix) && line.text.trim_end().ends_with('{') {
                let body = body_slice(self.lines, idx)?;
                return Some(Scope {
                    lines: body,
                    floor: line.indent + 4,
                    direct_only: false,
                });
            }
        }
        None
    }

    /// Find the first top-level (or deeper, scanning inorder) `if (...)`
    /// whose condition contains `cond_substr`. Returns a scope split into
    /// then / optional else branches.
    fn find_if_with_condition(&self, cond_substr: &str) -> Option<IfScope<'a>> {
        for (idx, line) in self.lines.iter().enumerate() {
            let text = &line.text;
            if !text.starts_with("if (") {
                continue;
            }
            if !text.contains(cond_substr) {
                continue;
            }
            // `if (...) {` opens a body that ends in the matching `}` or `} else {`.
            let (then_body, else_body) = split_if_body(self.lines, idx)?;
            let then_scope = Scope {
                lines: then_body,
                floor: line.indent + 4,
                direct_only: false,
            };
            let else_scope = else_body.map(|body| Scope {
                lines: body,
                floor: line.indent + 4,
                direct_only: false,
            });
            return Some(IfScope {
                then_scope,
                else_scope,
            });
        }
        None
    }
}

/// Given a slice of lines and an index pointing at a line ending with `{`,
/// return the lines enclosed by its matching `}` (exclusive).
fn body_slice(lines: &[Line], opener_idx: usize) -> Option<&[Line]> {
    let body_start = opener_idx + 1;
    let closer_idx = find_matching_closer(lines, opener_idx)?;
    Some(&lines[body_start..closer_idx])
}

/// Given a line index that opens a block (ends with `{`), return the index
/// of its matching closing `}` line.
fn find_matching_closer(lines: &[Line], opener_idx: usize) -> Option<usize> {
    let opener_indent = lines[opener_idx].indent;
    // Brace depth tracking. The opener already counts as +1; walk forward,
    // balancing nested `{` / `}` at indents >= opener_indent.
    let mut depth = 1usize;
    for (i, line) in lines.iter().enumerate().skip(opener_idx + 1) {
        if line.indent < opener_indent {
            // Left the enclosing scope without finding the closer.
            return None;
        }
        let trimmed = line.text.trim_end();
        // A pure close line at the opener's indent is the match.
        if line.indent == opener_indent && (trimmed == "}" || trimmed.starts_with("} else")) {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
            // else-branch continues the same if-block at the same depth
            if trimmed.starts_with("} else") {
                depth += 1;
            }
            continue;
        }
        // Nested `} else {` closes then reopens on one line, net zero.
        if line.indent > opener_indent && trimmed.starts_with("} else") && trimmed.ends_with('{') {
            continue;
        }
        // Nested openers at deeper indent increase depth.
        if line.indent > opener_indent && trimmed.ends_with('{') {
            depth += 1;
        } else if line.indent > opener_indent && (trimmed == "}" || trimmed.starts_with("} else")) {
            depth = depth.saturating_sub(1);
        }
    }
    None
}

/// Split an if-block into then / optional else slices.
///
/// Lines look like:
/// ```text
/// if (cond) {
///     then-body...
/// } else {
///     else-body...
/// }
/// ```
/// or just:
/// ```text
/// if (cond) {
///     then-body...
/// }
/// ```
fn split_if_body(lines: &[Line], opener_idx: usize) -> Option<(&[Line], Option<&[Line]>)> {
    let opener_indent = lines[opener_idx].indent;
    let body_start = opener_idx + 1;
    let mut depth = 1usize;
    let mut then_end: Option<usize> = None;
    let mut else_start: Option<usize> = None;

    for (i, line) in lines.iter().enumerate().skip(body_start) {
        if line.indent < opener_indent {
            break;
        }
        if line.indent > opener_indent {
            // Track nested braces so we don't confuse a nested `} else {` with ours.
            let trimmed = line.text.trim_end();
            // Nested `} else {` closes then reopens on one line, net zero.
            if trimmed.starts_with("} else") && trimmed.ends_with('{') {
                continue;
            }
            if trimmed.ends_with('{') {
                depth += 1;
            } else if trimmed == "}" || trimmed.starts_with("} else") {
                depth = depth.saturating_sub(1);
            }
            continue;
        }
        // line.indent == opener_indent
        let trimmed = line.text.trim_end();
        if trimmed.starts_with("} else") && depth == 1 {
            then_end = Some(i);
            else_start = Some(i + 1);
            continue;
        }
        if trimmed == "}" && depth == 1 {
            if then_end.is_none() {
                // Simple if without else.
                return Some((&lines[body_start..i], None));
            }
            // Close of else-branch.
            let then_slice = &lines[body_start..then_end.unwrap()];
            let else_slice = &lines[else_start.unwrap()..i];
            return Some((then_slice, Some(else_slice)));
        }
    }
    None
}

/// Parse the full summary into a flat list of top-level events and functions.
fn parse_top_blocks(summary: &str) -> Vec<TopBlock> {
    let raw_lines: Vec<&str> = summary.lines().collect();
    let mut blocks = Vec::new();
    let mut i = 0;
    while i < raw_lines.len() {
        if let Some(header_end) = detect_block_header(&raw_lines, i) {
            // A header may span multiple lines (e.g. long function signatures).
            let header_line = raw_lines[i];
            let header_indent = leading_spaces(header_line);
            let name = extract_block_name(header_line).unwrap_or_default();
            let header_text = raw_lines[i..=header_end].join(" ").trim().to_string();

            // Collect body lines until we hit another header (at any indent)
            // or an outer-indent line that isn't a comment. Event/function
            // headers can appear at several indent levels (2 or 4 spaces)
            // and we need to treat each as starting a new top block.
            let body_start = header_end + 1;
            let mut body_end = body_start;
            while body_end < raw_lines.len() {
                let bl = raw_lines[body_end];
                if bl.is_empty() {
                    body_end += 1;
                    continue;
                }
                let indent = leading_spaces(bl);
                if indent <= header_indent && !bl.trim_start().starts_with("//") {
                    // Hit an outer or peer indent that isn't a comment.
                    break;
                }
                if detect_block_header(&raw_lines, body_end).is_some() {
                    // Next event/function header: end the current body here.
                    break;
                }
                body_end += 1;
            }

            // The body indent isn't always header_indent + 2 -- grouped
            // events inside a comment group can have body at header_indent
            // + 4 instead (the group adds a 2-space visual shift but keeps
            // the standard 4-space body-nesting). Discover it from the
            // first non-blank, non-comment body line; default to +2.
            let body_indent =
                detect_body_indent(&raw_lines[body_start..body_end]).unwrap_or(header_indent + 2);

            let body = build_body_lines(&raw_lines[body_start..body_end], body_indent);
            blocks.push(TopBlock {
                name,
                header: header_text,
                body,
            });
            i = body_end;
        } else {
            i += 1;
        }
    }
    blocks
}

/// Return Some(header_end_index) if the line at `i` opens an event or
/// function definition, handling multi-line signatures. None otherwise.
fn detect_block_header(lines: &[&str], i: usize) -> Option<usize> {
    let line = lines[i];
    let trimmed = line.trim_start();
    // Skip comments, section headers, component/variable blocks.
    if trimmed.is_empty() || trimmed.starts_with("//") {
        return None;
    }
    // Reject section headers like "Functions:", "Variables:", "Components:",
    // "Call graph:". These are at column 0.
    let indent = leading_spaces(line);
    if indent == 0 {
        return None;
    }
    // A header always contains `(` and is followed (possibly on later lines)
    // by a closing `)` with either `:` (events/bare functions) or a `[FLAGS]`
    // block (regular functions).
    if !trimmed.contains('(') {
        return None;
    }
    if !is_likely_block_name_start(trimmed) {
        return None;
    }
    // Walk forward until we see the end of the signature.
    let mut j = i;
    while j < lines.len() {
        let l = lines[j];
        let rtrim = l.trim_end();
        if rtrim.ends_with("):") {
            return Some(j);
        }
        if rtrim.ends_with(']') && rtrim.contains('[') {
            // Make sure the `[...]` is a flag tag, not e.g. an array literal.
            if rtrim.contains(") [") || rtrim.contains(")[") {
                return Some(j);
            }
        }
        // Multi-line sig continuation heuristic: if line does NOT end with
        // `{` or `}` and the next line has more indentation, keep going.
        if j + 1 < lines.len() {
            let next_indent = leading_spaces(lines[j + 1]);
            if next_indent > indent && !rtrim.ends_with('{') && !rtrim.ends_with('}') {
                j += 1;
                continue;
            }
        }
        break;
    }
    None
}

fn is_likely_block_name_start(trimmed: &str) -> bool {
    // Header names always begin with an uppercase ASCII letter (K2Node_*,
    // InputAction_*, ReceiveTick, etc.) or are of the form `Some Name With
    // Spaces(...)` (blueprint display names with spaces -- all start
    // uppercase). Local variables, `$`-temps, keywords like `if (`, `for (`,
    // `while (`, `switch (`, and `return`/`break` are excluded.
    let first = trimmed.chars().next().unwrap_or(' ');
    if !first.is_ascii_uppercase() {
        return false;
    }
    for kw in ["if ", "for ", "while ", "switch ", "case ", "return "] {
        if trimmed.starts_with(kw) {
            return false;
        }
    }
    true
}

fn extract_block_name(header: &str) -> Option<String> {
    let trimmed = header.trim_start();
    let paren = trimmed.find('(')?;
    // Block names may contain spaces (blueprint display names).
    Some(trimmed[..paren].trim().to_string())
}

fn leading_spaces(line: &str) -> usize {
    line.chars().take_while(|c| *c == ' ').count()
}

/// Find the indent of the first body-content line (skipping blanks and
/// comments) so we can strip the correct prefix off descendant lines.
fn detect_body_indent(body: &[&str]) -> Option<usize> {
    for line in body {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        return Some(leading_spaces(line));
    }
    None
}

/// Convert raw body lines into structured `Line`s, stripping the common
/// `body_indent` prefix so indent values are measured relative to the body
/// top level. Blank lines are dropped (they are never load-bearing for
/// structure matching).
fn build_body_lines(raw: &[&str], body_indent: usize) -> Vec<Line> {
    let mut out = Vec::with_capacity(raw.len());
    for line in raw {
        if line.trim().is_empty() {
            continue;
        }
        let indent = leading_spaces(line);
        let rel_indent = indent.saturating_sub(body_indent);
        let text = line[indent.min(line.len())..].to_string();
        out.push(Line {
            text,
            indent: rel_indent,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINI: &str = r#"Blueprint: Foo

Functions:
  Bar(X: int) [Public]
    if (X > 0) {
        DoOnce(Thing) {
            Call()
        }
    } else {
        ResetDoOnce(Thing)
    }
    AfterIf()

  Baz():
    Simple()
"#;

    #[test]
    fn parses_header_names() {
        let out = OutputAssertion::from(MINI);
        assert_eq!(out.blocks.len(), 2);
        assert_eq!(out.blocks[0].name, "Bar");
        assert_eq!(out.blocks[1].name, "Baz");
    }

    #[test]
    fn detects_if_with_condition() {
        let out = OutputAssertion::from(MINI);
        let _ = out
            .function("Bar")
            .has_if_block_with_condition_containing("X > 0")
            .then_branch()
            .contains_do_once("Thing")
            .contains_line_matching("Call()");
    }

    #[test]
    fn else_branch_reachable() {
        let out = OutputAssertion::from(MINI);
        let _ = out
            .function("Bar")
            .has_if_block_with_condition_containing("X > 0")
            .else_branch()
            .contains_reset_do_once("Thing");
    }

    #[test]
    fn top_level_scope_ignores_nested() {
        let out = OutputAssertion::from(MINI);
        // AfterIf is at top level; Call() is nested inside if/DoOnce so
        // top_level().contains_line_matching should accept AfterIf but not
        // Call.
        let _ = out
            .function("Bar")
            .top_level()
            .contains_line_matching("AfterIf()");
    }

    #[test]
    #[should_panic(expected = "did not contain")]
    fn top_level_panics_on_nested_only_line() {
        let out = OutputAssertion::from(MINI);
        // Call() is inside a nested block; asking for it at top level should fail.
        let _ = out
            .function("Bar")
            .top_level()
            .contains_line_matching("Call()");
    }

    #[test]
    fn simple_event_has_call() {
        let out = OutputAssertion::from(MINI);
        let _ = out.event("Baz").contains_line_matching("Simple()");
    }

    fn mk(text: &str, indent: usize) -> Line {
        Line {
            text: text.to_string(),
            indent,
        }
    }

    #[test]
    fn matching_closer_handles_nested_else_chain() {
        // Outer `if` at indent 0, inner `if/else` at indent 4. The nested
        // `} else {` must not bump depth net-positive, or the outer closer
        // is never found.
        let lines = vec![
            mk("if (a) {", 0),
            mk("if (b) {", 4),
            mk("Inner1()", 8),
            mk("} else {", 4),
            mk("Inner2()", 8),
            mk("}", 4),
            mk("}", 0),
        ];
        assert_eq!(find_matching_closer(&lines, 0), Some(6));
    }

    #[test]
    fn split_if_body_with_nested_else_chain() {
        let lines = vec![
            mk("if (a) {", 0),
            mk("if (b) {", 4),
            mk("Inner1()", 8),
            mk("} else {", 4),
            mk("Inner2()", 8),
            mk("}", 4),
            mk("} else {", 0),
            mk("Outer2()", 4),
            mk("}", 0),
        ];
        let (then_body, else_body) = split_if_body(&lines, 0).expect("split");
        // Then-body is lines 1..6 (the nested if through its `}`).
        assert_eq!(then_body.len(), 5);
        assert_eq!(then_body[0].text, "if (b) {");
        assert_eq!(then_body[4].text, "}");
        let else_body = else_body.expect("else present");
        assert_eq!(else_body.len(), 1);
        assert_eq!(else_body[0].text, "Outer2()");
    }

    #[test]
    fn matching_closer_handles_deeply_nested_else() {
        let lines = vec![
            mk("DoOnce(X) {", 0),
            mk("if (a) {", 4),
            mk("if (b) {", 8),
            mk("Leaf()", 12),
            mk("} else {", 8),
            mk("Other()", 12),
            mk("}", 8),
            mk("}", 4),
            mk("}", 0),
        ];
        assert_eq!(find_matching_closer(&lines, 0), Some(8));
    }
}
