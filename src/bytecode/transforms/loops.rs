//! Loop pattern rewriting: ForEach (confirmed and unconfirmed) and ForLoopWithBreak.
//!
//! Converts UE loop boilerplate into readable for-loop syntax:
//! - ForEach: `while (COUNTER < ARRAY.Length()) { INDEX = COUNTER; ITEM = ARRAY[INDEX]; ... }`
//!   becomes `for (ITEM in ARRAY) { ... }`
//! - ForLoopWithBreak: `while (VAR <= LIMIT) { ...; VAR = VAR + 1 }`
//!   becomes `for (idx = START to LIMIT) { ... }`

use super::{
    closes_block, count_var_refs, is_block_boundary, opens_block, parse_temp_assignment,
    strip_outer_parens, substitute_var, BREAK_HIT_VAR, TEMP_INT_PREFIX,
};
use crate::helpers::{is_section_separator, FOREACH_PREFIX, WHILE_PREFIX};

/// Run all loop rewriting passes in order.
pub(super) fn rewrite_loops(lines: &mut Vec<String>) {
    strip_break_hit_from_while(lines);
    rewrite_confirmed_foreach(lines);
    rewrite_foreach_loops(lines);
    rewrite_forloop_with_break(lines);
    downgrade_unconverted_foreach(lines);
}

/// Strip UE ForEach break-hit flags from while/foreach conditions.
///
/// Catches flags that survived temp inlining (when the flag was behind a temp
/// variable, `strip_break_hit_flag` in flow.rs couldn't strip it at detection time).
fn strip_break_hit_from_while(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let trimmed = line.trim();
        let (keyword, rest) = if let Some(rest) = trimmed.strip_prefix(WHILE_PREFIX) {
            ("while", rest)
        } else if let Some(rest) = trimmed.strip_prefix(FOREACH_PREFIX) {
            ("foreach", rest)
        } else {
            continue;
        };
        let Some(rest) = rest.strip_prefix("((!").or_else(|| rest.strip_prefix("(!")) else {
            continue;
        };
        if !rest.starts_with(BREAK_HIT_VAR)
            && !rest.starts_with("false")
            && !rest.starts_with("true")
        {
            continue;
        }
        let Some((_, after)) = rest.split_once(") && ") else {
            continue;
        };
        let Some(cond) = after.strip_suffix(") {") else {
            continue;
        };
        let cond = strip_outer_parens(cond);
        *line = format!("{} ({}) {{", keyword, cond);
    }
}

/// Rewrite `foreach (COND) {` markers (emitted by the flow layer for confirmed
/// ForEach loops) into `for (ITEM in ARRAY)`.
///
/// The flow layer already suppressed init lines and the increment. The condition
/// carries `COUNTER < ARRAY.Length()` (after temp inlining). The body uses
/// `ARRAY[INDEX]` directly (temp inlining collapsed `INDEX = COUNTER`).
fn rewrite_confirmed_foreach(lines: &mut Vec<String>) {
    // Process innermost loops first (last occurrence) so outer loop cleanup
    // doesn't remove body lines that inner loops need (e.g. .Length() calls).
    loop {
        let Some(i) = lines
            .iter()
            .rposition(|l| l.trim().starts_with(FOREACH_PREFIX))
        else {
            break;
        };
        let Some(close_idx) = find_loop_close(lines, i) else {
            lines[i] = lines[i].replace(FOREACH_PREFIX, WHILE_PREFIX);
            continue;
        };

        let resolved = resolve_foreach_array(lines, i, close_idx);
        let Some((array, index_var)) = resolved else {
            lines[i] = lines[i].replace(FOREACH_PREFIX, WHILE_PREFIX);
            continue;
        };

        let (item, to_remove) = resolve_item(lines, i, close_idx, &array, &index_var);
        lines[i] = format!("for ({} in {}) {{", item, array);
        for idx in to_remove.into_iter().rev() {
            lines.remove(idx);
        }
        strip_leading_init_lines(lines, i);
        remove_redundant_gets(lines, i, &item, &array, &index_var);
        remove_dead_preamble(lines, i);
    }
}

/// Extract the array name and index variable for a confirmed foreach loop.
/// Tries the condition first (`COUNTER < ARRAY.Length()`), then falls back to
/// scanning the preamble and body for `.Length()` calls.
fn resolve_foreach_array(
    lines: &[String],
    header_idx: usize,
    close_idx: usize,
) -> Option<(String, String)> {
    parse_foreach_header(lines[header_idx].trim())
        .and_then(|array| {
            find_foreach_index_var(lines, header_idx + 1, close_idx, &array).map(|idx| (array, idx))
        })
        .or_else(|| find_array_access_in_body(lines, header_idx + 1, close_idx))
}

/// Determine the item variable name for a foreach loop. If the first body line
/// is `ITEM = ARRAY[INDEX]` (explicit get), use that name and mark the line for
/// removal. Otherwise generate a synthetic name and substitute `ARRAY[INDEX]`
/// references throughout the body.
fn resolve_item(
    lines: &mut [String],
    header_idx: usize,
    close_idx: usize,
    array: &str,
    index_var: &str,
) -> (String, Vec<usize>) {
    let access_pattern = format!("{}[{}]", array, index_var);
    if let Some((get_idx, item)) =
        find_explicit_get(lines, header_idx + 1, close_idx, &access_pattern)
    {
        // Compiler temp names ($Array_Get_Item etc.) are noisy, derive a
        // clean name instead while still removing the explicit get line.
        let item = if item.starts_with('$') {
            let derived = derive_item_name(array, lines, header_idx, close_idx);
            for line in &mut lines[header_idx + 1..close_idx] {
                while count_var_refs(line, &item) > 0 {
                    *line = substitute_var(line, &item, &derived);
                }
            }
            derived
        } else {
            item
        };
        (item, vec![get_idx])
    } else {
        let item = derive_item_name(array, lines, header_idx, close_idx);
        for line in &mut lines[header_idx + 1..close_idx] {
            if line.contains(&access_pattern) {
                *line = line.replace(&access_pattern, &item);
            }
        }
        (item, vec![])
    }
}

/// Parse `foreach (COND) {` and extract the array from `COUNTER < ARRAY.Length()`.
/// Assumes break-hit flags were already stripped by `strip_break_hit_from_while`.
fn parse_foreach_header(trimmed: &str) -> Option<String> {
    let cond = trimmed.strip_prefix(FOREACH_PREFIX)?.strip_suffix(") {")?;
    let cond = strip_outer_parens(cond);
    let (_, rhs) = cond.split_once(" < ")?;
    let array = rhs.strip_suffix(".Length()")?;
    Some(array.to_string())
}

/// Find the INDEX variable from `ARRAY[INDEX]` occurrences in the body.
fn find_foreach_index_var(
    lines: &[String],
    start: usize,
    close_idx: usize,
    array: &str,
) -> Option<String> {
    let prefix = format!("{}[", array);
    for line in &lines[start..close_idx] {
        let trimmed = line.trim();
        if let Some(pos) = trimmed.find(&prefix) {
            let after_bracket = &trimmed[pos + prefix.len()..];
            let index = after_bracket.split(']').next()?;
            if !index.is_empty() {
                return Some(index.to_string());
            }
        }
    }
    None
}

/// Discover the array and index variable when the condition doesn't contain
/// `COUNTER < ARRAY.Length()`. Searches the preamble and body for a `.Length()`
/// call to identify the array.
fn find_array_access_in_body(
    lines: &[String],
    start: usize,
    close_idx: usize,
) -> Option<(String, String)> {
    // Scan backward past the foreach header to the enclosing block boundary.
    // Condition computation temps like `$Array_Length = X.Length()` are placed
    // before the loop by the structurer.
    let foreach_idx = start.saturating_sub(1);
    let preamble_start = (0..foreach_idx)
        .rev()
        .find(|&j| {
            let trimmed = lines[j].trim();
            is_block_boundary(trimmed) || is_section_separator(trimmed)
        })
        .map_or(0, |j| j + 1);
    let search_range = (preamble_start..foreach_idx).chain(start..close_idx);
    for idx in search_range {
        let trimmed = lines[idx].trim();
        if let Some((_, rhs)) = trimmed.split_once(" = ") {
            if let Some(array) = rhs.strip_suffix(".Length()") {
                let index = find_foreach_index_var(lines, start, close_idx, array)?;
                return Some((array.to_string(), index));
            }
        }
    }
    None
}

/// Remove `Temp_int_* = 0` init lines at the top of the loop body.
/// These are index inits that the flow layer couldn't suppress (e.g. when
/// they're inside a displaced body block).
fn strip_leading_init_lines(lines: &mut Vec<String>, loop_idx: usize) {
    let mut j = loop_idx + 1;
    while j < lines.len() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            j += 1;
            continue;
        }
        if trimmed
            .strip_suffix(" = 0")
            .is_some_and(|v| v.starts_with(TEMP_INT_PREFIX))
        {
            lines.remove(j);
            continue;
        }
        break;
    }
}

/// Check if the first non-comment body line is `ITEM = ACCESS_PATTERN`.
fn find_explicit_get(
    lines: &[String],
    start: usize,
    close_idx: usize,
    access_pattern: &str,
) -> Option<(usize, String)> {
    let (rel, line) = lines[start..close_idx].iter().enumerate().find(|(_, l)| {
        let trimmed = l.trim();
        !trimmed.is_empty() && !trimmed.starts_with("//")
    })?;
    let trimmed = line.trim();
    let (item, rhs) = trimmed.split_once(" = ")?;
    (rhs == access_pattern).then(|| (start + rel, item.to_string()))
}

/// Rewrite unconfirmed ForEach loops: `while (COUNTER < ARRAY.Length()) {`
/// where the flow layer didn't tag the loop.
///
/// Requires both COUNTER = 0 and INDEX = 0 init lines, and either an explicit
/// `ITEM = ARRAY[INDEX]` body pattern or an increment to confirm iteration.
fn rewrite_foreach_loops(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if !trimmed.starts_with(WHILE_PREFIX) {
            i += 1;
            continue;
        }
        let Some(close_idx) = find_loop_close(lines, i) else {
            i += 1;
            continue;
        };
        let Some((item, array, index_var, mut to_remove)) = try_match_foreach(lines, i, close_idx)
        else {
            i += 1;
            continue;
        };

        lines[i] = format!("for ({} in {}) {{", item, array);
        to_remove.sort_unstable();
        to_remove.dedup();
        let removed_before_i = to_remove.iter().filter(|&&idx| idx < i).count();
        for idx in to_remove.into_iter().rev() {
            if idx < close_idx {
                lines.remove(idx);
            }
        }

        let for_idx = i - removed_before_i;
        remove_redundant_gets(lines, for_idx, &item, &array, &index_var);
        i = 0;
    }
}

/// Try to match the while loop at `header_idx` as a ForEach pattern.
/// Returns (item_name, array, index_var, line_indices_to_remove) on success.
fn try_match_foreach(
    lines: &mut [String],
    header_idx: usize,
    close_idx: usize,
) -> Option<(String, String, String, Vec<usize>)> {
    let trimmed = lines[header_idx].trim();
    let (counter, array) = parse_foreach_while(trimmed)?;
    let (counter_idx, index_idx, index_var) = find_foreach_init(lines, header_idx, &counter)?;
    let incr_idx = find_reachable_increment(lines, header_idx, close_idx, &counter);

    // Explicit-get path (strong signal, always allowed)
    if let Some((assign_idx, get_idx, item)) =
        validate_body_start(lines, header_idx + 1, &index_var, &counter, &array)
    {
        let mut to_remove = vec![get_idx, assign_idx, index_idx, counter_idx];
        if let Some(idx) = incr_idx {
            to_remove.push(idx);
        }
        return Some((item, array, index_var, to_remove));
    }

    // Inline-access fallback (requires increment to avoid false positives)
    let incr_idx = incr_idx?;
    let (assign_idx, item) =
        try_inline_access_rewrite(lines, header_idx, close_idx, &index_var, &array)?;
    let to_remove = vec![assign_idx, index_idx, counter_idx, incr_idx];
    Some((item, array, index_var, to_remove))
}

/// Parse `while (COUNTER < ARRAY.Length()) {` into (counter, array).
fn parse_foreach_while(trimmed: &str) -> Option<(String, String)> {
    let cond = trimmed.strip_prefix(WHILE_PREFIX)?.strip_suffix(") {")?;
    let (counter, rhs) = cond.split_once(" < ")?;
    let array = rhs.strip_suffix(".Length()")?;
    Some((counter.to_string(), array.to_string()))
}

/// Scan backward from while_idx for COUNTER = 0 and INDEX = 0 init lines.
fn find_foreach_init(
    lines: &[String],
    while_idx: usize,
    counter: &str,
) -> Option<(usize, usize, String)> {
    let mut counter_idx = None;
    let mut index_idx = None;
    let mut index_var = None;

    for j in (0..while_idx).rev() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() || is_block_boundary(trimmed) {
            continue;
        }
        if is_section_separator(trimmed) {
            break;
        }
        if let Some(var) = trimmed
            .strip_suffix(" = 0")
            .filter(|v| v.starts_with(TEMP_INT_PREFIX))
        {
            if var == counter {
                counter_idx = Some(j);
            } else if index_idx.is_none() {
                index_var = Some(var.to_string());
                index_idx = Some(j);
            }
        } else if trimmed.starts_with('$') || trimmed.starts_with("//") {
            continue;
        } else {
            break;
        }
        if counter_idx.is_some() && index_idx.is_some() {
            break;
        }
    }

    Some((counter_idx?, index_idx?, index_var?))
}

/// Validate first two body lines: INDEX = COUNTER, then ITEM = ARRAY[INDEX].
fn validate_body_start(
    lines: &[String],
    start: usize,
    index: &str,
    counter: &str,
    array: &str,
) -> Option<(usize, usize, String)> {
    let mut body_iter = lines[start..]
        .iter()
        .enumerate()
        .filter(|(_, l)| !l.trim().is_empty())
        .map(|(rel, l)| (start + rel, l.trim()));
    let (assign_idx, first) = body_iter.next()?;
    if first == "}" {
        return None;
    }
    let (get_idx, second) = body_iter.next()?;
    if second == "}" {
        return None;
    }

    let expected_assign = format!("{} = {}", index, counter);
    if first != expected_assign {
        return None;
    }

    let (item, rhs) = second.split_once(" = ")?;
    let expected_get = format!("{}[{}]", array, index);
    if rhs != expected_get {
        return None;
    }

    Some((assign_idx, get_idx, item.to_string()))
}

/// Fallback for loops without an explicit `ITEM = ARRAY[INDEX]` line.
/// Generates a synthetic item name and substitutes all `ARRAY[INDEX]` in the body.
fn try_inline_access_rewrite(
    lines: &mut [String],
    while_idx: usize,
    close_idx: usize,
    index_var: &str,
    array: &str,
) -> Option<(usize, String)> {
    let assign_prefix = format!("{} = ", index_var);
    let access_pattern = format!("{}[{}]", array, index_var);

    let assign_idx = lines[while_idx + 1..close_idx]
        .iter()
        .enumerate()
        .find(|(_, l)| {
            let trimmed = l.trim();
            !trimmed.is_empty() && !trimmed.starts_with("//")
        })
        .filter(|(_, l)| l.trim().starts_with(&assign_prefix))
        .map(|(rel, _)| rel + while_idx + 1)?;

    if !lines[while_idx + 1..close_idx]
        .iter()
        .any(|l| l.contains(&access_pattern))
    {
        return None;
    }

    let item = derive_item_name(array, lines, while_idx, close_idx);

    for line in &mut lines[while_idx + 1..close_idx] {
        if line.contains(&access_pattern) {
            *line = line.replace(&access_pattern, &item);
        }
    }

    Some((assign_idx, item))
}

/// Rewrite UE ForLoopWithBreak boilerplate into `for (idx = START to END)`.
fn rewrite_forloop_with_break(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        let Some((counter, limit)) = parse_forloop_while(trimmed) else {
            i += 1;
            continue;
        };

        let Some(init_idx) = find_forloop_init(lines, i, &counter) else {
            i += 1;
            continue;
        };
        let start_val = lines[init_idx]
            .trim()
            .split_once(" = ")
            .map_or("0", |(_, rhs)| rhs);

        let Some(close_idx) = find_loop_close(lines, i) else {
            i += 1;
            continue;
        };
        let Some(incr_idx) = find_reachable_increment(lines, i, close_idx, &counter) else {
            i += 1;
            continue;
        };

        let short_name = derive_loop_var_name(&counter, lines, i, close_idx);

        lines[i] = format!("for ({} = {} to {}) {{", short_name, start_val, limit);

        if short_name != counter {
            for line in &mut lines[i + 1..close_idx] {
                while count_var_refs(line, &counter) > 0 {
                    *line = substitute_var(line, &counter, &short_name);
                }
            }
        }

        debug_assert!(init_idx < i && i < incr_idx);
        lines.remove(incr_idx);
        lines.remove(init_idx);

        i = 0;
    }
}

/// Parse `while (VAR <= LIMIT) {` into (counter, limit).
fn parse_forloop_while(trimmed: &str) -> Option<(String, String)> {
    let rest = trimmed.strip_prefix(WHILE_PREFIX)?.strip_suffix(") {")?;
    let (counter, limit) = rest.split_once(" <= ")?;
    if !counter.starts_with(TEMP_INT_PREFIX) {
        return None;
    }
    Some((counter.to_string(), limit.to_string()))
}

/// Find the `VAR = VALUE` init line scanning backward from the while header.
fn find_forloop_init(lines: &[String], while_idx: usize, counter: &str) -> Option<usize> {
    let init_prefix = format!("{} = ", counter);
    for j in (0..while_idx).rev() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        if is_section_separator(trimmed) || is_block_boundary(trimmed) {
            break;
        }
        if trimmed.starts_with(&init_prefix) {
            return Some(j);
        }
    }
    None
}

/// Choose a short variable name for the loop counter.
fn derive_loop_var_name(
    counter: &str,
    lines: &[String],
    while_idx: usize,
    close_idx: usize,
) -> String {
    if !counter.starts_with(TEMP_INT_PREFIX) {
        return counter.to_string();
    }
    let body_text: String = lines[while_idx..close_idx].join("\n");
    let no_collision = |name: &str| count_var_refs(&body_text, name) == 0;
    for candidate in ["idx", "_idx"] {
        if no_collision(candidate) {
            return candidate.to_string();
        }
    }
    counter.to_string()
}

/// Choose an item variable name for a ForEach loop. Uses "hit" for
/// hit-result arrays, de-pluralizes simple trailing 's' (Actors -> Actor),
/// falls back to "item".
fn derive_item_name(array: &str, lines: &[String], while_idx: usize, close_idx: usize) -> String {
    let base = array
        .strip_prefix('$')
        .or_else(|| array.strip_prefix("out "))
        .unwrap_or(array);

    let candidate = if base.ends_with("_OutHits") || base.ends_with("_Hits") {
        "hit".to_string()
    } else if base.len() >= 4
        && base.ends_with('s')
        && base.as_bytes()[base.len() - 2].is_ascii_lowercase()
    {
        base[..base.len() - 1].to_string()
    } else {
        "item".to_string()
    };

    let body_text: String = lines[while_idx..close_idx].join("\n");
    if count_var_refs(&body_text, &candidate) > 0 {
        return "item".to_string();
    }
    candidate
}

/// Find the closing `}` that matches the opening brace.
fn find_loop_close(lines: &[String], header_idx: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (j, line) in lines.iter().enumerate().skip(header_idx) {
        let trimmed = line.trim();
        if opens_block(trimmed) {
            depth += 1;
        }
        if closes_block(trimmed) {
            depth -= 1;
            if depth == 0 {
                return Some(j);
            }
        }
    }
    None
}

/// Find the `COUNTER = COUNTER + 1` increment in the loop body.
/// Returns `None` if absent or unreachable (preceded by unconditional break).
fn find_reachable_increment(
    lines: &[String],
    header_idx: usize,
    close_idx: usize,
    counter: &str,
) -> Option<usize> {
    let expected_incr = format!("{} = {} + 1", counter, counter);
    let incr_idx = lines[header_idx + 1..close_idx]
        .iter()
        .rposition(|l| l.trim() == expected_incr)
        .map(|rel| rel + header_idx + 1)?;

    let mut depth = 0i32;
    for line in &lines[header_idx + 1..incr_idx] {
        let trimmed = line.trim();
        if opens_block(trimmed) {
            depth += 1;
        }
        if closes_block(trimmed) {
            depth -= 1;
        }
        if depth == 0 && trimmed == "break" {
            return None;
        }
    }

    Some(incr_idx)
}

/// Remove redundant `ITEM = ARRAY[INDEX]` re-fetches after a ForEach rewrite.
fn remove_redundant_gets(
    lines: &mut Vec<String>,
    for_idx: usize,
    item: &str,
    array: &str,
    index_var: &str,
) {
    let Some(mut close) = find_loop_close(lines, for_idx) else {
        return;
    };
    let redundant_get = format!("{} = {}[{}]", item, array, index_var);
    let mut j = for_idx + 1;
    while j < close {
        if lines[j].trim() == redundant_get {
            lines.remove(j);
            close -= 1;
        } else {
            j += 1;
        }
    }
}

/// Remove dead `$`-prefixed temp assignments immediately before a `for` header.
/// Iterates to handle chains where removing one makes another dead.
fn remove_dead_preamble(lines: &mut Vec<String>, mut for_idx: usize) {
    loop {
        let Some(j) = (0..for_idx).rev().find(|&j| !lines[j].trim().is_empty()) else {
            break;
        };
        let trimmed = lines[j].trim();
        let Some((var, _)) = parse_temp_assignment(trimmed) else {
            break;
        };
        if !var.starts_with('$') {
            break;
        }
        let var = var.to_string();
        let has_refs = lines
            .iter()
            .enumerate()
            .any(|(idx, line)| idx != j && count_var_refs(line.trim(), &var) > 0);
        if has_refs {
            break;
        }
        lines.remove(j);
        for_idx -= 1;
    }
}

/// Downgrade any unconverted `foreach (` markers back to `while (` (prefix-only).
fn downgrade_unconverted_foreach(lines: &mut [String]) {
    for line in lines.iter_mut() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix(FOREACH_PREFIX) {
            *line = format!("{}{}", WHILE_PREFIX, rest);
        }
    }
}
