//! Break/Make struct folding, struct construction, and large Break call compaction.

use super::{
    count_var_refs, is_ident_char, is_var_boundary, parse_temp_assignment, split_args,
    BREAK_FUNC_PREFIX, MAKE_STRUCT_PREFIX,
};

/// Max output args for a Break* call to be fully inlined (replaced with dot access).
/// Above this threshold, the call is compacted instead (named params, skip underscores).
const BREAK_INLINE_MAX_ARGS: usize = 4;

/// Parse a `Break*(...args...)` call from a trimmed line.
/// Returns (func_name, args) where args[0] is the source and args[1..] are outputs.
fn parse_break_call(trimmed: &str) -> Option<(&str, Vec<&str>)> {
    let paren_start = trimmed.find('(')?;
    let func_name = &trimmed[..paren_start];
    if !func_name.starts_with(BREAK_FUNC_PREFIX) || !trimmed.ends_with(')') {
        return None;
    }
    let args_str = &trimmed[paren_start + 1..trimmed.len() - 1];
    let args = split_args(args_str);
    if args.len() < 2 {
        return None;
    }
    Some((func_name, args))
}

/// Fold small Break* calls into field accessors using dynamic field name inference.
/// `BreakTransform($src, $BreakTransform_Location, ...)` -> replace with `$src.Location` etc.
/// Only applies when output arg count <= BREAK_INLINE_MAX_ARGS and all outputs are `$temp`.
pub(super) fn fold_break_patterns(lines: &mut Vec<String>) {
    let mut to_remove: Vec<usize> = Vec::new();

    for i in 0..lines.len() {
        let trimmed = lines[i].trim().to_string();
        let Some((func_name, args)) = parse_break_call(&trimmed) else {
            continue;
        };

        let output_args = &args[1..];
        if output_args.len() > BREAK_INLINE_MAX_ARGS {
            continue;
        }

        // All output vars must be $temp
        if !output_args.iter().all(|a| a.starts_with('$')) {
            continue;
        }

        let source = args[0].to_string();
        let prefix = format!("${}_", func_name);

        // Infer field names from $BreakName_FieldName convention.
        // All args must resolve to a field name, otherwise skip this Break call.
        let raw_fields: Vec<&str> = output_args
            .iter()
            .filter_map(|a| a.strip_prefix(&prefix))
            .collect();
        if raw_fields.len() != output_args.len() {
            continue;
        }

        // Detect shared disambiguation suffix (_1, _2, etc.)
        // If all fields end with the same _N, strip it
        let fields: Vec<&str> = if let Some(common_suffix) = detect_common_suffix(&raw_fields) {
            raw_fields
                .iter()
                .map(|f| &f[..f.len() - common_suffix.len()])
                .collect()
        } else {
            raw_fields
        };

        // Replace each output var in subsequent lines with source.FieldName
        for (idx, &out_var) in output_args.iter().enumerate() {
            let replacement = format!("{}.{}", source, fields[idx]);

            for line in lines.iter_mut().skip(i + 1) {
                if count_var_refs(line.trim(), out_var) > 0 {
                    *line = replace_all_var_refs(line.trim(), out_var, &replacement);
                }
            }
        }

        to_remove.push(i);
    }

    for idx in to_remove.into_iter().rev() {
        lines.remove(idx);
    }
}

/// Collapse `$MakeStruct_TYPE.Field = Value` runs into `TARGET = TYPE(fields...)`.
pub(super) fn fold_struct_construction(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let Some((struct_var, _, _)) = parse_make_struct_field(lines[i].trim()) else {
            i += 1;
            continue;
        };

        let run_start = i;
        let struct_var = struct_var.to_string();
        let (fields, next) = collect_struct_fields(lines, i, &struct_var);
        i = next;

        if fields.is_empty() {
            i += 1;
            continue;
        }

        // Check if next line is TARGET = $MakeStruct_TYPE
        if let Some(new_line) = lines
            .get(i)
            .and_then(|l| l.trim().split_once(" = "))
            .filter(|(_, src)| *src == struct_var)
            .map(|(target, _)| format_struct_constructor(target, &struct_var, &fields))
        {
            lines.splice(run_start..i + 1, std::iter::once(new_line));
            i = run_start + 1;
        }
    }
}

/// Collect consecutive `$MakeStruct_TYPE.Field = Value` assignments, tolerating
/// interleaved `$MakeStruct_*` intermediate temps (UE5 pattern: temp assigned
/// first, then stored into the struct field on the next line).
/// Returns (resolved_fields, next_line_index).
fn collect_struct_fields(
    lines: &[String],
    start: usize,
    struct_var: &str,
) -> (Vec<(String, String)>, usize) {
    let mut fields: Vec<(String, String)> = Vec::new();
    let mut intermediate_temps: Vec<(String, String)> = Vec::new();
    let mut i = start;

    while i < lines.len() {
        let trimmed = lines[i].trim();
        if let Some((sv, field, value)) = parse_make_struct_field(trimmed) {
            if sv == struct_var {
                fields.push((field.to_string(), value.to_string()));
                i += 1;
                continue;
            }
        }
        if let Some((var, expr)) = parse_temp_assignment(trimmed) {
            if var.starts_with(MAKE_STRUCT_PREFIX) {
                intermediate_temps.push((var.to_string(), expr.to_string()));
                i += 1;
                continue;
            }
        }
        break;
    }

    // Resolve intermediate temps in field values
    for (_, value) in &mut fields {
        for (temp_var, temp_expr) in &intermediate_temps {
            if count_var_refs(value, temp_var) > 0 {
                *value = replace_all_var_refs(value, temp_var, temp_expr);
            }
        }
    }

    (fields, i)
}

/// Format a struct constructor: `TARGET = TYPE(field1: val1, field2: val2)`.
/// Omits the label when field name matches the value (positional shorthand).
fn format_struct_constructor(
    target: &str,
    struct_var: &str,
    fields: &[(String, String)],
) -> String {
    let type_name = struct_var
        .strip_prefix(MAKE_STRUCT_PREFIX)
        .unwrap_or(struct_var);
    let args: Vec<String> = fields
        .iter()
        .map(|(field, value)| {
            if field == value {
                value.clone()
            } else {
                format!("{}: {}", field, value)
            }
        })
        .collect();
    format!("{} = {}({})", target, type_name, args.join(", "))
}

/// Compact large Break* calls by removing unused out-params and adding field labels.
pub(super) fn compact_large_break_calls(lines: &mut [String]) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        let Some((func_name, args)) = parse_break_call(trimmed) else {
            i += 1;
            continue;
        };

        // Only compact large Break calls (small ones are handled by fold_break_patterns)
        let output_count = args.len() - 1;
        if output_count <= BREAK_INLINE_MAX_ARGS {
            i += 1;
            continue;
        }

        // Check which out-param args are actually used elsewhere in the section
        let source = args[0];
        let prefix = format!("${}_", func_name);
        let call_prefix = format!("{}(", func_name);
        let mut parts = vec![source.to_string()];
        let mut any_unused = false;

        for &arg in &args[1..] {
            // An arg is "used" if it appears on a line that isn't another
            // call to the same Break function (those just re-extract the same fields)
            let used = lines.iter().enumerate().any(|(j, line)| {
                j != i
                    && count_var_refs(line.trim(), arg) > 0
                    && !line.trim().starts_with(&call_prefix)
            });
            if used {
                if let Some(field) = arg.strip_prefix(&prefix) {
                    parts.push(format!("{}: {}", field, arg));
                } else {
                    parts.push(arg.to_string());
                }
            } else {
                any_unused = true;
            }
        }

        // Only rewrite if at least some params are unused (otherwise keep original)
        if any_unused {
            lines[i] = format!("{}({})", func_name, parts.join(", "));
        }
        i += 1;
    }
}

/// Rename Make* functions by stripping the `Make` prefix: MakeVector -> Vector, etc.
pub(super) fn rename_make_functions(lines: &mut [String]) {
    for line in lines.iter_mut() {
        *line = strip_make_prefix(line);
    }
}

/// Find `Make<Name>(` patterns and strip the `Make` prefix.
/// Only matches when preceded by a non-ident char (or start of string),
/// and when the char after `Make` is uppercase (avoids false positives).
pub(super) fn strip_make_prefix(text: &str) -> String {
    let make_len = "Make".len();
    let mut result = String::with_capacity(text.len());
    let mut start = 0;
    while let Some(pos) = text[start..].find("Make") {
        let abs_pos = start + pos;
        let after_make = abs_pos + make_len;
        if after_make >= text.len() {
            break;
        }

        let preceded_ok = abs_pos == 0 || {
            let prev = text.as_bytes()[abs_pos - 1];
            !is_ident_char(prev) && prev != b'$'
        };
        let followed_by_upper = text.as_bytes()[after_make].is_ascii_uppercase();
        let followed_by_call = text[after_make..].find('(').is_some_and(|paren| {
            text[after_make..after_make + paren]
                .chars()
                .all(|ch| ch.is_alphanumeric() || ch == '_')
        });

        // When strippable, copy up to "Make" (omitting it); otherwise include it
        let copy_end = if preceded_ok && followed_by_upper && followed_by_call {
            abs_pos
        } else {
            after_make
        };
        result.push_str(&text[start..copy_end]);
        start = after_make;
    }
    result.push_str(&text[start..]);
    result
}

/// Detect a shared `_N` disambiguation suffix across all field names.
/// Returns Some("_1") if all fields end with "_1", etc.
pub(super) fn detect_common_suffix<'a>(fields: &[&'a str]) -> Option<&'a str> {
    if fields.is_empty() {
        return None;
    }
    let first = fields[0];
    let last_underscore = first.rfind('_')?;
    let suffix = &first[last_underscore..];
    if suffix.len() < 2 || !suffix[1..].chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    if fields
        .iter()
        .all(|f| f.ends_with(suffix) && f.len() > suffix.len())
    {
        Some(suffix)
    } else {
        None
    }
}

/// Parse `$MakeStruct_TYPE.FIELD = VALUE`.
fn parse_make_struct_field(text: &str) -> Option<(&str, &str, &str)> {
    if !text.starts_with(MAKE_STRUCT_PREFIX) {
        return None;
    }
    let (struct_var, rest) = text.split_once('.')?;
    let (field, value) = rest.split_once(" = ")?;
    Some((struct_var, field, value))
}

/// Replace all occurrences of a variable reference in text (word-boundary aware).
pub(super) fn replace_all_var_refs(text: &str, var: &str, replacement: &str) -> String {
    let mut result = String::with_capacity(text.len());
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        let after = abs_pos + var.len();
        if is_var_boundary(text, abs_pos, var) {
            result.push_str(&text[start..abs_pos]);
            result.push_str(replacement);
        } else {
            result.push_str(&text[start..after]);
        }
        start = after;
    }
    result.push_str(&text[start..]);
    result
}
