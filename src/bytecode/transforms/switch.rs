//! Switch/enum cascade folding: converts nested if-else chains from UE's
//! "Switch on Enum" node into `switch (VAR) { case N: { ... } }` pseudocode.
//!
//! Two entry points:
//! - [`fold_switch_enum_cascade`]: text-level fold for cascades within a single section
//! - [`fold_cascade_across_sequences`]: BcStatement-level fold for cascades whose
//!   jump targets span across `// sequence [N]:` markers

use std::collections::BTreeMap;

use super::SWITCH_ENUM_PREFIX;
use crate::bytecode::decode::{parse_stmt, BcStatement, Expr, Stmt};
use crate::bytecode::flow::find_last_unmatched_pop;
use crate::bytecode::{JUMP_OFFSET_TOLERANCE, POP_FLOW, RETURN_NOP};
use crate::helpers::{closes_block, is_comment_or_empty, opens_block};

/// Fold `$SwitchEnum_CmpSuccess` cascades into `switch (VAR) { case: ... }`.
///
/// UE's "Switch on Enum" node compiles to cascading comparisons:
///   `$SwitchEnum_CmpSuccess = VAR != N` / `if (!...) return` or `if (...) { ... }`
/// After structuring, this produces deeply nested if-blocks with case bodies at
/// decreasing indent levels. This pass detects the cascade, collects case
/// bodies (correctly handling `} else {` boundaries), and emits proper
/// `switch/case` pseudocode with braces for `apply_indentation`.
pub fn fold_switch_enum_cascade(lines: &mut Vec<String>) {
    let mut i = 0;
    while i < lines.len() {
        let Some((switch_var, compared_var, first_value)) =
            parse_switch_enum_assign(lines[i].trim())
        else {
            i += 1;
            continue;
        };

        let cascade_start = i;
        let (case_values, scaffold_end, mut brace_depth) =
            scan_cascade_scaffold(lines, i + 1, &switch_var, &compared_var, first_value);

        if case_values.len() < 2 {
            i += 1;
            continue;
        }

        let (body_groups, construct_end) =
            collect_case_bodies(lines, scaffold_end, &mut brace_depth);

        if body_groups.iter().all(Vec::is_empty) {
            i = construct_end;
            continue;
        }

        let replacement = build_switch_replacement(&compared_var, &case_values, body_groups);
        let replacement_len = replacement.len();
        lines.splice(cascade_start..construct_end, replacement);
        i = cascade_start + replacement_len;
    }
}

/// Scan the cascade scaffold: consecutive `$SwitchEnum_CmpSuccess = VAR != N`
/// assignments followed by if-checks and braces that reference the switch var.
/// Returns (case_values, next_line_index, brace_depth).
///
/// Subsequent case-value assignments are only accepted when the preceding
/// meaningful line is not a bare block closer. This rejects detached cascade
/// assignments that sit after a closed if-block at cascade depth (the shape
/// produced by sibling-flat `if (!$SwitchEnum_CmpSuccess) { body }` patterns
/// when the structurer sees un-inlined scaffolding), which would otherwise be
/// mis-attributed as additional cases without bodies.
fn scan_cascade_scaffold(
    lines: &[String],
    start: usize,
    switch_var: &str,
    compared_var: &str,
    first_value: String,
) -> (Vec<String>, usize, i32) {
    let mut case_values = vec![first_value];
    let mut j = start;
    let mut brace_depth = 0i32;

    while j < lines.len() {
        let trimmed = lines[j].trim();
        if let Some((sv, cv, val)) = parse_switch_enum_assign(trimmed) {
            if sv == switch_var && cv == compared_var && prior_accepts_cascade_assign(lines, j) {
                case_values.push(val);
                j += 1;
                continue;
            }
            break;
        }
        if trimmed.contains(switch_var) {
            if opens_block(trimmed) {
                brace_depth += 1;
            }
            j += 1;
            continue;
        }
        if trimmed == "}" && brace_depth > 0 {
            brace_depth -= 1;
            j += 1;
            continue;
        }
        break;
    }

    (case_values, j, brace_depth)
}

/// True if the line immediately before `idx` is compatible with another
/// cascade assignment: either an open-block header (or `} else {` chain) or
/// another cascade assign. Blank lines and comments are skipped when looking
/// backward. Reject bare `}` and compacted `if ... { body }` closers, which
/// indicate the prior case body has already closed.
fn prior_accepts_cascade_assign(lines: &[String], idx: usize) -> bool {
    let mut k = idx;
    while k > 0 {
        k -= 1;
        let trimmed = lines[k].trim();
        if is_comment_or_empty(trimmed) {
            continue;
        }
        if opens_block(trimmed) {
            return true;
        }
        if parse_switch_enum_assign(trimmed).is_some() {
            return true;
        }
        return !closes_block(trimmed) && !trimmed.ends_with('}');
    }
    true
}

/// Collect case bodies from the nested if/else structure after the scaffold.
/// Bodies are separated by `} else {` at the cascade level; nested braces within
/// bodies are tracked with body_depth to avoid splitting on inner if/else blocks.
/// Returns (body_groups, construct_end_index).
fn collect_case_bodies(
    lines: &[String],
    start: usize,
    brace_depth: &mut i32,
) -> (Vec<Vec<String>>, usize) {
    let mut body_groups: Vec<Vec<String>> = Vec::new();
    let mut current_body: Vec<String> = Vec::new();
    let mut body_depth = 0i32;
    let mut j = start;

    while j < lines.len() && *brace_depth > 0 {
        let trimmed = lines[j].trim();
        let is_open = opens_block(trimmed);
        let is_close = trimmed == "}";
        let is_else_chain = trimmed.starts_with("} ") && trimmed.ends_with('{');

        if body_depth > 0 && (is_close || is_else_chain) {
            body_depth -= 1;
            current_body.push(lines[j].clone());
            if is_else_chain {
                body_depth += 1;
            }
        } else if body_depth == 0 && (is_close || is_else_chain) {
            if !current_body.is_empty() {
                body_groups.push(std::mem::take(&mut current_body));
            }
            // Only bare `}` decrements brace_depth; `} else {` is neutral
            // because the opening `{` immediately re-enters the cascade
            if is_close {
                *brace_depth -= 1;
            }
        } else if is_open {
            current_body.push(lines[j].clone());
            body_depth += 1;
        } else if !trimmed.is_empty() {
            current_body.push(lines[j].clone());
        }
        j += 1;
    }

    // Outermost body (after cascade braces close)
    while j < lines.len() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() || trimmed == "return" || trimmed == "}" || trimmed == "break" {
            break;
        }
        current_body.push(lines[j].clone());
        j += 1;
    }
    if !current_body.is_empty() {
        body_groups.push(current_body);
    }

    (body_groups, j)
}

/// Build the switch/case replacement lines from collected bodies.
fn build_switch_replacement(
    compared_var: &str,
    case_values: &[String],
    mut body_groups: Vec<Vec<String>>,
) -> Vec<String> {
    // Cascade nesting produces bodies in reverse order (outermost = last case),
    // so flip them to get natural case ordering: case 0, case 1, ..., default
    body_groups.reverse();

    // Recursively fold inner switch cascades
    for body in &mut body_groups {
        fold_switch_enum_cascade(body);
    }

    // When there's one more body than case values, the extra one is the default branch
    let has_default = body_groups.len() == case_values.len() + 1;

    let mut replacement = vec![format!("switch ({}) {{", compared_var)];
    for (idx, body) in body_groups.iter().enumerate() {
        let label = if has_default && idx == body_groups.len() - 1 {
            "default: {".to_string()
        } else if idx < case_values.len() {
            format!("case {}: {{", case_values[idx])
        } else {
            format!("case {}: {{", idx)
        };
        replacement.push(label);
        for line in body {
            replacement.push(line.trim().to_string());
        }
        replacement.push("}".to_string());
    }
    replacement.push("}".to_string());
    replacement
}

/// Parse `$SwitchEnum_CmpSuccess... = VAR != VALUE` from a trimmed line.
///
/// Uses `parse_stmt` to extract the cascade-start shape from the typed IR,
/// then falls back to the legacy substring split if the parser couldn't
/// classify either side (TODO(5d.2): extend `parse_expr` to cover any
/// cascade RHS shape the decoder emits but the parser currently rejects).
fn parse_switch_enum_assign(trimmed: &str) -> Option<(String, String, String)> {
    if !trimmed.starts_with(SWITCH_ENUM_PREFIX) {
        return None;
    }
    if let Some(parts) = parse_switch_enum_assign_typed(trimmed) {
        return Some(parts);
    }
    parse_switch_enum_assign_substring(trimmed)
}

/// Typed classifier: match `Stmt::Assignment` with an `Expr::Binary("!=", ...)`
/// RHS whose LHS is a bare `Var`. Returns `None` on any other shape.
fn parse_switch_enum_assign_typed(trimmed: &str) -> Option<(String, String, String)> {
    let Stmt::Assignment { lhs, rhs } = parse_stmt(trimmed) else {
        return None;
    };
    let Expr::Var(switch_var) = lhs else {
        return None;
    };
    if !switch_var.starts_with(SWITCH_ENUM_PREFIX) {
        return None;
    }
    let Expr::Binary {
        op,
        lhs: cmp_lhs,
        rhs: cmp_rhs,
    } = rhs
    else {
        return None;
    };
    if op != "!=" {
        return None;
    }
    let compared_var = expr_to_source(*cmp_lhs)?;
    let value = expr_to_source(*cmp_rhs)?;
    Some((switch_var, compared_var, value))
}

/// Legacy substring fallback, kept verbatim for shapes `parse_expr` returns
/// `Unknown` on (tracked by TODO(5d.2)).
fn parse_switch_enum_assign_substring(trimmed: &str) -> Option<(String, String, String)> {
    let (switch_var, rhs) = trimmed.split_once(" = ")?;
    let (compared_var, value) = rhs.split_once(" != ")?;
    Some((
        switch_var.to_string(),
        compared_var.to_string(),
        value.to_string(),
    ))
}

/// Render a typed `Expr` back to its source text for the narrow shapes the
/// cascade scaffold produces: bare vars, literals, and simple dotted field
/// accesses. Anything else returns `None` so the caller drops back to the
/// substring path.
fn expr_to_source(expr: Expr) -> Option<String> {
    match expr {
        Expr::Var(name) | Expr::Literal(name) => Some(name),
        Expr::FieldAccess { recv, field } => {
            let recv_text = expr_to_source(*recv)?;
            Some(format!("{recv_text}.{field}"))
        }
        _ => None,
    }
}

// BcStatement-level cascade fold (pre-split)

/// A detected cascade case: value and jump target offset from the if-jump.
struct CascadeCase {
    value: String,
    target_offset: usize,
}

/// Detect a `$SwitchEnum_CmpSuccess` cascade that spans across
/// `// sequence [N]:` markers, and produce structured switch/case text.
///
/// Each case body is structured independently to avoid cross-case if-block
/// nesting. Returns `Some(lines)` with the fully structured output, or
/// `None` if no cascade-across-sequence pattern was found.
pub fn fold_cascade_across_sequences(
    stmts: &[BcStatement],
    first_marker_idx: usize,
    structure_fn: impl Fn(&[BcStatement]) -> Vec<String>,
) -> Option<Vec<String>> {
    // Scan prefix for cascade scaffold.
    let (compared_var, _switch_var, cases, _scaffold_range) =
        detect_cascade_in_prefix(stmts, first_marker_idx)?;

    if cases.len() < 2 {
        return None;
    }

    // Resolve each case's jump target to a statement index at or after the
    // first sequence marker. Direct search avoids OffsetMap hash collisions
    // when multiple sequence markers share the same mem_offset.
    let mut resolved_cases: Vec<(String, usize)> = Vec::new();
    for case in &cases {
        if let Some(target_idx) = resolve_target_after(stmts, case.target_offset, first_marker_idx)
        {
            resolved_cases.push((case.value.clone(), target_idx));
        }
    }
    if resolved_cases.len() < 2 {
        return None;
    }

    // Group cases by target index.
    let mut groups: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for (value, target_idx) in &resolved_cases {
        groups.entry(*target_idx).or_default().push(value.clone());
    }

    // Need exactly 2 groups: a "main" group (most cases, targeting the
    // sequence area) and an "alternate" group (targeting a push_flow block
    // for case-specific code). More complex layouts are not handled.
    if groups.len() != 2 {
        return None;
    }

    let content_end = find_content_end(stmts);
    let group_keys: Vec<usize> = groups.keys().copied().collect();
    let main_start = group_keys[0];
    let alt_start = group_keys[1];

    // The alternate group should start at a push_flow (sequence dispatch
    // infrastructure for the case-specific code).
    stmts[alt_start].push_flow_target()?;

    // Detect the push_flow/jump block at the alternate target and extract
    // the exclusive body range (the jump target body, e.g. landing sounds).
    let (alt_exclusive, alt_inline) = extract_push_jump_bodies(stmts, alt_start, content_end)?;

    // Find the shared boundary: code reachable from both case groups.
    // Scan case 0,1,2 body for if-jump targets that land in the unused area
    // (past the sequence markers). The first such target marks shared code.
    let shared_start = find_shared_boundary(stmts, main_start, alt_start, content_end);

    // Build case bodies:
    // Main cases: sequence content + shared code (skipping push_flow block + exclusive body)
    // Alt case: exclusive body + inline body
    let main_body = collect_main_body(stmts, main_start, alt_start, shared_start, content_end);
    let alt_body = collect_alt_body(stmts, &alt_exclusive, &alt_inline);

    // Structure each body independently.
    let mut output: Vec<String> = Vec::new();
    output.push(format!("switch ({}) {{", compared_var));

    let main_values = &groups[&main_start];
    output.push(format!("case {}: {{", main_values.join(", ")));
    if !main_body.is_empty() {
        output.extend(structure_fn(&main_body));
    }
    output.push("}".to_string());

    let alt_values = &groups[&alt_start];
    output.push(format!("case {}: {{", alt_values.join(", ")));
    if !alt_body.is_empty() {
        output.extend(structure_fn(&alt_body));
    }
    output.push("}".to_string());

    output.push("}".to_string());
    Some(output)
}

/// Extract the exclusive and inline bodies from a push_flow/jump block.
/// Returns (exclusive_range, inline_range) as index ranges into stmts.
fn extract_push_jump_bodies(
    stmts: &[BcStatement],
    push_idx: usize,
    max_idx: usize,
) -> Option<(std::ops::Range<usize>, std::ops::Range<usize>)> {
    if push_idx + 1 >= max_idx {
        return None;
    }
    let jump_target = stmts[push_idx + 1].jump_target()?;

    // Inline body: between jump and first pop_flow after it.
    let inline_start = push_idx + 2;
    let inline_pop = stmts[inline_start..max_idx]
        .iter()
        .position(|s| s.text.trim() == POP_FLOW)
        .map(|p| p + inline_start)?;

    // Exclusive body start: resolve the jump target.
    let exclusive_start = stmts[inline_pop + 1..max_idx]
        .iter()
        .position(|s| s.mem_offset.abs_diff(jump_target) <= JUMP_OFFSET_TOLERANCE)
        .map(|p| p + inline_pop + 1)?;

    // Exclusive body end: the last pop_flow at depth 0 exits the block.
    let last_exit_pop =
        find_last_unmatched_pop(stmts, exclusive_start, max_idx).unwrap_or(exclusive_start);
    let exclusive_end = last_exit_pop + 1;

    Some((exclusive_start..exclusive_end, inline_start..inline_pop))
}

/// Find the shared code boundary: the first stmt in the unused area whose
/// offset matches an if-jump target from the main case body.
fn find_shared_boundary(
    stmts: &[BcStatement],
    main_start: usize,
    alt_start: usize,
    content_end: usize,
) -> usize {
    // Collect if-jump targets from the main case body.
    let mut targets: Vec<usize> = Vec::new();
    for stmt in stmts[main_start..alt_start].iter() {
        if let Some((_, target)) = stmt.if_jump() {
            targets.push(target);
        }
    }

    // Find the first stmt past the alt_start whose offset matches a target.
    for (idx, stmt) in stmts.iter().enumerate().take(content_end).skip(alt_start) {
        for &target in &targets {
            if stmt.mem_offset.abs_diff(target) <= JUMP_OFFSET_TOLERANCE {
                return idx;
            }
        }
    }

    // No shared boundary found: all remaining content stays with alt case.
    content_end
}

/// Collect main case body: sequence content + shared code, excluding
/// sentinels, push_flow block, and the exclusive alt body.
fn collect_main_body(
    stmts: &[BcStatement],
    main_start: usize,
    alt_start: usize,
    shared_start: usize,
    content_end: usize,
) -> Vec<BcStatement> {
    let mut body: Vec<BcStatement> = Vec::new();

    // Part 1: sequence content (main_start to alt_start).
    for stmt in stmts[main_start..alt_start].iter() {
        if !should_strip_from_case_body(&stmt.text) {
            body.push(stmt.clone());
        }
    }

    // Part 2: shared code (shared_start to content_end).
    for stmt in stmts[shared_start..content_end].iter() {
        if !should_strip_from_case_body(&stmt.text) {
            body.push(stmt.clone());
        }
    }

    body
}

/// Collect alt case body: exclusive target body (linearised) + inline body.
fn collect_alt_body(
    stmts: &[BcStatement],
    exclusive: &std::ops::Range<usize>,
    inline: &std::ops::Range<usize>,
) -> Vec<BcStatement> {
    let mut body: Vec<BcStatement> = Vec::new();
    body.extend_from_slice(&stmts[exclusive.start..exclusive.end]);
    body.extend_from_slice(&stmts[inline.start..inline.end]);
    body
}

/// Scan the prefix (stmts before first_marker_idx) for a cascade scaffold.
/// Returns (compared_var, switch_var, cases, scaffold_index_range).
fn detect_cascade_in_prefix(
    stmts: &[BcStatement],
    first_marker_idx: usize,
) -> Option<(String, String, Vec<CascadeCase>, std::ops::Range<usize>)> {
    let mut compared_var: Option<String> = None;
    let mut switch_var: Option<String> = None;
    let mut cases: Vec<CascadeCase> = Vec::new();
    let mut scaffold_start: Option<usize> = None;
    let mut scaffold_end: usize = 0;

    let mut idx = 0;
    while idx < first_marker_idx {
        let trimmed = stmts[idx].text.trim();

        // Try to parse a cascade assignment.
        if let Some((sv, cv, val)) = parse_switch_enum_assign(trimmed) {
            // Verify consistency with previously seen cascade assignments.
            if let Some(ref existing_sv) = switch_var {
                if sv != *existing_sv {
                    break;
                }
            }
            if let Some(ref existing_cv) = compared_var {
                if cv != *existing_cv {
                    break;
                }
            }
            switch_var = Some(sv);
            compared_var = Some(cv);
            if scaffold_start.is_none() {
                scaffold_start = Some(idx);
            }

            // The if-jump should follow immediately.
            if idx + 1 < first_marker_idx {
                if let Some((cond, target)) = stmts[idx + 1].if_jump() {
                    if cond.contains(switch_var.as_deref().unwrap_or("")) {
                        cases.push(CascadeCase {
                            value: val,
                            target_offset: target,
                        });
                        scaffold_end = idx + 2;
                        idx += 2;
                        continue;
                    }
                }
            }
        }

        idx += 1;
    }

    let scaffold_start = scaffold_start?;
    let compared_var = compared_var?;
    let switch_var = switch_var?;
    if cases.len() < 2 {
        return None;
    }

    Some((
        compared_var,
        switch_var,
        cases,
        scaffold_start..scaffold_end,
    ))
}

/// Find the end of meaningful content (skip trailing `return nop`).
fn find_content_end(stmts: &[BcStatement]) -> usize {
    let mut end = stmts.len();
    while end > 0 && stmts[end - 1].text.trim() == RETURN_NOP {
        end -= 1;
    }
    end
}

/// Resolve a jump target offset to the first statement at or after
/// `start_idx` whose mem_offset is within `JUMP_OFFSET_TOLERANCE`.
/// Skips synthetic `return nop` sentinels injected by the sequence emitter,
/// which borrow offsets from nearby real statements and steal fuzzy matches.
fn resolve_target_after(
    stmts: &[BcStatement],
    target_offset: usize,
    start_idx: usize,
) -> Option<usize> {
    let mut best: Option<(usize, usize)> = None; // (distance, index)
    for (idx, stmt) in stmts.iter().enumerate().skip(start_idx) {
        if stmt.text.trim() == RETURN_NOP {
            continue;
        }
        let dist = target_offset.abs_diff(stmt.mem_offset);
        if dist <= JUMP_OFFSET_TOLERANCE {
            match best {
                Some((best_dist, _)) if dist >= best_dist => {}
                _ => best = Some((dist, idx)),
            }
            if dist == 0 {
                break;
            }
        }
    }
    best.map(|(_, idx)| idx)
}

/// Stmts to strip when building case bodies: synthetic sentinels from
/// sequence emission that would create spurious `return` in the output.
fn should_strip_from_case_body(text: &str) -> bool {
    text.trim() == RETURN_NOP
}

#[cfg(test)]
mod switch_typed_tests {
    use super::{parse_switch_enum_assign, parse_switch_enum_assign_typed};

    #[test]
    fn typed_matches_simple_cascade_start() {
        let line = "$SwitchEnum_CmpSuccess = EnumVar != 0";
        let parsed = parse_switch_enum_assign_typed(line);
        assert_eq!(
            parsed,
            Some((
                "$SwitchEnum_CmpSuccess".to_string(),
                "EnumVar".to_string(),
                "0".to_string(),
            ))
        );
    }

    #[test]
    fn typed_matches_dotted_compared_var() {
        let line = "$SwitchEnum_CmpSuccess_1 = self.State != 3";
        let parsed = parse_switch_enum_assign_typed(line);
        assert_eq!(
            parsed,
            Some((
                "$SwitchEnum_CmpSuccess_1".to_string(),
                "self.State".to_string(),
                "3".to_string(),
            ))
        );
    }

    #[test]
    fn rejects_non_cascade_line() {
        // An `==` comparison (not `!=`) is not a cascade start.
        assert_eq!(
            parse_switch_enum_assign("$SwitchEnum_CmpSuccess = EnumVar == 0"),
            None,
        );
        // An assignment whose LHS does not start with the cascade prefix.
        assert_eq!(parse_switch_enum_assign("Other = EnumVar != 0"), None);
        // A bare line that isn't an assignment.
        assert_eq!(parse_switch_enum_assign("return"), None);
    }

    #[test]
    fn public_entry_matches_same_shape_as_typed() {
        let line = "$SwitchEnum_CmpSuccess_2 = MyVar != 7";
        assert_eq!(
            parse_switch_enum_assign(line),
            parse_switch_enum_assign_typed(line),
        );
    }
}
