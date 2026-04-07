//! Post-processing filter for summary output. Parses the formatted text into
//! sections and items, then keeps only items matching the filter terms.

use std::collections::HashSet;
use std::fmt::Write;

use crate::helpers::indent_of;

/// Section header labels used in summary output.
const SECTION_HEADERS: &[&str] = &[
    "Components:",
    "Variables:",
    "Default values:",
    "Call graph:",
    "Functions:",
];

/// Filter a formatted summary, keeping only items that match the filter terms.
///
/// Runs as a post-processing step on fully formatted text. Each section type
/// is split into items (indent-grouped for most sections, blank-line-separated
/// for Functions) and items are kept when any line matches a filter term.
///
/// The call graph additionally includes entries whose caller or callee appears
/// in a matched function block, so filtering by a variable name surfaces the
/// call relationships between functions that reference it.
pub fn filter_summary(text: &str, filters: &[String]) -> String {
    if filters.is_empty() {
        return text.to_string();
    }

    let lines: Vec<&str> = text.lines().collect();
    let sections = find_sections(&lines);
    let header_end = sections.first().map(|s| s.start).unwrap_or(lines.len());

    // First pass: collect matched function names for call graph cross-referencing
    let matched_funcs = collect_matched_func_names(&lines, &sections, filters);

    let mut buf = String::new();
    for line in &lines[..header_end] {
        writeln!(buf, "{}", line).unwrap();
    }

    for section in &sections {
        let content = &lines[section.start + 1..section.end];
        emit_filtered_section(&mut buf, section.header, content, filters, &matched_funcs);
    }

    buf
}

struct Section<'a> {
    start: usize,
    end: usize,
    header: &'a str,
}

/// Find section boundaries from the formatted output lines.
fn find_sections<'a>(lines: &[&'a str]) -> Vec<Section<'a>> {
    let mut sections: Vec<Section> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim_end();
        if SECTION_HEADERS.contains(&trimmed) {
            sections.push(Section {
                start: i,
                end: 0,
                header: trimmed,
            });
        }
    }
    for idx in 0..sections.len() {
        sections[idx].end = sections
            .get(idx + 1)
            .map(|s| s.start)
            .unwrap_or(lines.len());
    }
    sections
}

/// Scan the Functions section to find names of function blocks that match the filter.
fn collect_matched_func_names(
    lines: &[&str],
    sections: &[Section],
    filters: &[String],
) -> HashSet<String> {
    let mut matched = HashSet::new();
    if let Some(section) = sections.iter().find(|s| s.header == "Functions:") {
        for block in split_by_blank_lines(&lines[section.start + 1..section.end]) {
            if block_matches_filter(&block, filters) {
                if let Some(name) = extract_func_name(&block) {
                    matched.insert(name.to_string());
                }
            }
        }
    }
    matched
}

/// Filter and emit a single section's matching items.
fn emit_filtered_section(
    buf: &mut String,
    header: &str,
    content: &[&str],
    filters: &[String],
    matched_funcs: &HashSet<String>,
) {
    if header == "Functions:" {
        let matching: Vec<Vec<&str>> = split_by_blank_lines(content)
            .into_iter()
            .filter(|block| block_matches_filter(block, filters))
            .collect();
        if !matching.is_empty() {
            writeln!(buf, "Functions:").unwrap();
            for (i, block) in matching.iter().enumerate() {
                if i > 0 {
                    writeln!(buf).unwrap();
                }
                for line in block {
                    writeln!(buf, "{}", line).unwrap();
                }
            }
            writeln!(buf).unwrap();
        }
    } else {
        let is_call_graph = header == "Call graph:";
        let matching: Vec<Vec<&str>> = split_by_indent(content)
            .into_iter()
            .filter(|item| {
                block_matches_filter(item, filters)
                    || (is_call_graph
                        && item
                            .iter()
                            .any(|line| call_graph_references(line, matched_funcs)))
            })
            .collect();
        if !matching.is_empty() {
            writeln!(buf, "{}", header).unwrap();
            for item in &matching {
                for line in item {
                    writeln!(buf, "{}", line).unwrap();
                }
            }
            writeln!(buf).unwrap();
        }
    }
}

/// Split lines into groups separated by blank lines.
fn split_by_blank_lines<'a>(lines: &[&'a str]) -> Vec<Vec<&'a str>> {
    let mut groups: Vec<Vec<&str>> = Vec::new();
    let mut current: Vec<&str> = Vec::new();
    for line in lines {
        if line.trim().is_empty() {
            if !current.is_empty() {
                groups.push(std::mem::take(&mut current));
            }
        } else {
            current.push(line);
        }
    }
    if !current.is_empty() {
        groups.push(current);
    }
    groups
}

/// Split lines into groups by top-level indent. A new group starts whenever
/// the indent level equals the minimum indent in the section.
fn split_by_indent<'a>(lines: &[&'a str]) -> Vec<Vec<&'a str>> {
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| indent_of(l))
        .min()
        .unwrap_or(0);

    let mut groups: Vec<Vec<&str>> = Vec::new();
    for line in lines {
        if line.trim().is_empty() {
            continue;
        }
        if indent_of(line) <= min_indent {
            groups.push(vec![line]);
        } else if let Some(last) = groups.last_mut() {
            last.push(line);
        }
    }
    groups
}

/// True if any line in the block contains any filter term (case-insensitive).
fn block_matches_filter(block: &[&str], filters: &[String]) -> bool {
    block.iter().any(|line| {
        let lower = line.to_lowercase();
        filters.iter().any(|f| lower.contains(f.as_str()))
    })
}

/// Extract the function/event name from a function block.
/// Finds the first non-comment line and returns the identifier before `(`.
fn extract_func_name<'a>(block: &[&'a str]) -> Option<&'a str> {
    for line in block {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.is_empty() {
            continue;
        }
        if let Some(paren) = trimmed.find('(') {
            return Some(trimmed[..paren].trim());
        }
    }
    None
}

/// True if a call graph line references any of the given function names.
/// Lines have the format `  Caller \u{2192} Callee1, Callee2`.
fn call_graph_references(line: &str, func_names: &HashSet<String>) -> bool {
    let trimmed = line.trim();
    let Some((caller, callees)) = trimmed.split_once(" \u{2192} ") else {
        return false;
    };
    if func_names.contains(caller) {
        return true;
    }
    callees
        .split(", ")
        .any(|callee| func_names.contains(callee))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_filters_returns_input_unchanged() {
        let text = "Blueprint: Test_BP\n\nFunctions:\n  Foo():\n    bar\n";
        assert_eq!(filter_summary(text, &[]), text);
    }

    #[test]
    fn filters_functions_by_name() {
        let text = "Blueprint: Test_BP\n\n\
            Functions:\n  Foo():\n    x = 1\n\n  Bar():\n    y = 2\n\n";
        let result = filter_summary(text, &["foo".to_string()]);
        assert!(result.contains("Foo()"));
        assert!(!result.contains("Bar()"));
    }

    #[test]
    fn filters_functions_by_body_content() {
        let text = "Blueprint: Test_BP\n\n\
            Variables:\n  Health: float\n  Mana: float\n\n\
            Functions:\n  TakeDamage():\n    self.Health = self.Health - 10\n\n  \
            Heal():\n    self.Mana = self.Mana + 5\n\n";
        let result = filter_summary(text, &["health".to_string()]);
        assert!(result.contains("Health: float"));
        assert!(!result.contains("Mana: float"));
        assert!(result.contains("TakeDamage()"));
        assert!(!result.contains("Heal()"));
    }

    #[test]
    fn call_graph_cross_references_matched_functions() {
        let text = "Blueprint: Test_BP\n\n\
            Call graph:\n  A \u{2192} B\n  C \u{2192} D\n\n\
            Functions:\n  A():\n    self.MyVar = 1\n\n  C():\n    other\n\n";
        let result = filter_summary(text, &["myvar".to_string()]);
        assert!(result.contains("A \u{2192} B"));
        assert!(!result.contains("C \u{2192} D"));
    }

    #[test]
    fn components_grouped_with_properties() {
        let text = "Blueprint: Test_BP\n\n\
            Components:\n  MyMesh (StaticMeshComponent)\n    Mobility: Movable\n  \
            Other (BoxCollision)\n\n";
        let result = filter_summary(text, &["movable".to_string()]);
        assert!(result.contains("MyMesh (StaticMeshComponent)"));
        assert!(result.contains("Mobility: Movable"));
        assert!(!result.contains("BoxCollision"));
    }

    #[test]
    fn no_matches_returns_header_only() {
        let text = "Blueprint: Test_BP\n\n\
            Variables:\n  X: int\n\nFunctions:\n  Foo():\n    bar\n\n";
        let result = filter_summary(text, &["nonexistent".to_string()]);
        assert!(result.contains("Blueprint: Test_BP"));
        assert!(!result.contains("Variables:"));
        assert!(!result.contains("Functions:"));
    }

    #[test]
    fn extract_func_name_skips_comments() {
        let block = vec!["  // called by: X", "  MyFunc(a: int):"];
        assert_eq!(extract_func_name(&block), Some("MyFunc"));
    }

    #[test]
    fn split_by_indent_groups_children() {
        let lines = ["  Parent (Comp)", "    Prop: val", "  Other (Comp)"];
        let groups = split_by_indent(&lines);
        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].len(), 2); // Parent + Prop
        assert_eq!(groups[1].len(), 1); // Other
    }
}
