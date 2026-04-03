//! Generic text and string utilities shared across modules.

/// Number of leading whitespace characters in a line.
pub fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// True if the byte is an ASCII identifier character (alphanumeric or `_`).
pub fn is_ident_char(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// Find the position of the closing `)` matching the `(` at position 0.
pub fn find_matching_paren(input: &str) -> Option<usize> {
    if !input.starts_with('(') {
        return None;
    }
    let mut depth = 0i32;
    for (i, ch) in input.chars().enumerate() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Find the position of `needle` in `input` at paren/brace depth 0.
pub fn find_at_depth_zero(input: &str, needle: &str) -> Option<usize> {
    let mut depth = 0i32;
    let bytes = input.as_bytes();
    let needle_bytes = needle.as_bytes();
    let nlen = needle_bytes.len();
    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && i + nlen <= bytes.len() && &bytes[i..i + nlen] == needle_bytes {
            return Some(i);
        }
    }
    None
}

/// Strip one layer of redundant outer parentheses if they match.
pub fn strip_outer_parens(input: &str) -> &str {
    if let Some(close) = find_matching_paren(input) {
        if close == input.len() - 1 {
            return &input[1..close];
        }
    }
    input
}

/// True if the expression contains an infix operator or leading `!`, meaning it
/// should be parenthesized when embedded in a larger expression.
pub fn expr_is_compound(expr: &str) -> bool {
    const OPERATORS: &[&str] = &[
        "&&", "||", "+", "-", "*", "/", "%", ">=", "<=", "==", "!=", ">>", "<<", ">", "<", "?",
    ];
    OPERATORS
        .iter()
        .any(|op| expr.contains(&format!(" {} ", op)))
        || expr.starts_with('!')
}

/// Section separator prefix used in structured output (e.g. `--- FunctionName ---`).
pub const SECTION_SEPARATOR: &str = "---";

/// True if the trimmed line is a section separator (`--- ... ---`).
pub fn is_section_separator(trimmed: &str) -> bool {
    trimmed.starts_with(SECTION_SEPARATOR) && trimmed.ends_with(SECTION_SEPARATOR)
}

/// True if the trimmed line opens a block (`... {` or bare `{`).
pub fn opens_block(trimmed: &str) -> bool {
    trimmed.ends_with(" {") || trimmed == "{"
}

/// True if the trimmed line closes a block (`}` or `} else ...`).
pub fn closes_block(trimmed: &str) -> bool {
    trimmed == "}" || trimmed.starts_with("} ")
}

/// True if the trimmed line is a block boundary (opening or closing brace).
pub fn is_block_boundary(trimmed: &str) -> bool {
    opens_block(trimmed) || closes_block(trimmed)
}

/// Header prefix for `while` loops.
pub const WHILE_PREFIX: &str = "while (";
/// Header prefix for `for` loops (both ForEach and ForLoopWithBreak output).
pub const FOR_PREFIX: &str = "for (";
/// Header prefix for flow-confirmed ForEach loops (before text-level rewriting).
pub const FOREACH_PREFIX: &str = "foreach (";

/// True if the trimmed line is a loop header.
pub fn is_loop_header(trimmed: &str) -> bool {
    trimmed.starts_with(WHILE_PREFIX)
        || trimmed.starts_with(FOR_PREFIX)
        || trimmed.starts_with(FOREACH_PREFIX)
}

/// Split comma-separated arguments respecting nested parens, brackets, and braces.
pub fn split_args(input: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, ch) in input.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                result.push(input[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = input[start..].trim();
    if !last.is_empty() {
        result.push(last);
    }
    result
}
