//! Scope-aware sibling of `inline_single_use_temps_text`.
//!
//! The text pass in `temps.rs` reasons about block boundaries via indent
//! walking, which is fast but blind to a few shapes, notably duplicate
//! assignments at the same depth and references that sit in a sibling
//! branch rather than a true ancestor/descendant.
//!
//! This module uses `region_tree::build_region_tree` to reason about
//! block scope explicitly. It runs in parallel with the text pass during
//! the 5d.13 branch-by-abstraction rollout: 5d.13b wires both passes
//! with divergence logging, the text pass stays authoritative, 5d.13c
//! flips authoritativeness and retires the old pass.
//!
//! Invariants that mirror the text pass:
//! - fixpoint loop (up to `MAX_PASSES` rewrites per call).
//! - length guard: skip inlines that exceed `MAX_LINE_WIDTH` unless the
//!   result shortens or the expression is trivial.
//! - uses `substitute_var` from the shared helper so byte-for-byte
//!   output matches the text pass where both agree.

use std::collections::HashMap;

use super::region_tree::{build_region_tree, LineRegion};
use super::{
    count_var_refs, indent_prefix, is_trivial_expr, parse_temp_assignment, substitute_var,
};

/// Scope-aware version of `inline_single_use_temps_text`. Uses
/// `region_tree::build_region_tree` to reason about block scope
/// explicitly, avoiding the ordering inversion that manifests when
/// a temp's sole reference is inside a guard cond and a sibling
/// duplicate assignment gets re-scoped into the guard body.
///
/// Returns true when at least one line was rewritten. Mirrors the
/// text pass's fixpoint loop and length-guard budget so the two can
/// run in parallel during 5d.13 branch-by-abstraction.
pub(crate) fn inline_single_use_temps_scoped(lines: &mut Vec<String>) -> bool {
    const MAX_PASSES: usize = 6;
    let mut any_change = false;

    for _ in 0..MAX_PASSES {
        if !run_one_pass(lines) {
            break;
        }
        any_change = true;
    }
    any_change
}

/// One fixpoint iteration. Returns true when at least one line was
/// rewritten so the caller can loop until quiescent.
fn run_one_pass(lines: &mut Vec<String>) -> bool {
    let tree = build_region_tree(lines);

    // Collect every $Temp / Temp_* assignment with its line index and
    // the range of the lexical region that contains it.
    let mut assignments: Vec<Assignment> = Vec::new();
    collect_assignments(&tree, lines, &mut assignments);

    // Count how many times the same var name appears on the LHS of
    // an assignment across the whole buffer. When >1, skip: this is
    // the duplicate-assignment class the text pass silently filtered.
    let mut assign_counts: HashMap<&str, usize> = HashMap::new();
    for assignment in &assignments {
        *assign_counts.entry(assignment.var.as_str()).or_default() += 1;
    }

    let mut removed: Vec<bool> = vec![false; lines.len()];
    let mut inlined_any = false;

    for assignment in &assignments {
        if assign_counts
            .get(assignment.var.as_str())
            .copied()
            .unwrap_or(0)
            != 1
        {
            continue;
        }
        if removed[assignment.line] {
            continue;
        }

        // Re-read the assignment RHS from the current buffer: an earlier
        // iteration in this pass may have rewritten the assignment line
        // via a nested-var inline that targeted this line's RHS.
        let current_rhs = match parse_temp_assignment(lines[assignment.line].trim()) {
            Some((var, rhs)) if var == assignment.var => rhs.to_string(),
            _ => continue,
        };

        let Some(outcome) = plan_inline(lines, &tree, assignment, &removed) else {
            continue;
        };
        let replacement_trimmed = substitute_var(
            lines[outcome.consumer].trim(),
            &assignment.var,
            &current_rhs,
        );
        if !inline_fits_budget(&replacement_trimmed, &assignment.var, &current_rhs) {
            continue;
        }

        // Mutate the consumer line immediately so subsequent plans in
        // this iteration see the updated text. Buffering rewrites in a
        // side array drops substitutions when multiple assignments
        // target the same consumer (e.g. both sides of a ternary).
        let new_line = format!(
            "{}{}",
            indent_prefix(&lines[outcome.consumer]),
            replacement_trimmed
        );
        lines[outcome.consumer] = new_line;
        removed[assignment.line] = true;
        inlined_any = true;
    }

    if !inlined_any {
        return false;
    }

    let mut idx = 0;
    lines.retain(|_| {
        let keep = !removed[idx];
        idx += 1;
        keep
    });
    true
}

#[derive(Clone, Debug)]
struct Assignment {
    line: usize,
    var: String,
    /// Half-open range of the region that contains the assignment line.
    /// For a top-level assignment this is `0..lines.len()`.
    scope: std::ops::Range<usize>,
}

struct InlineOutcome {
    consumer: usize,
}

/// Decide whether `assignment` can be inlined, and where.
///
/// Returns `None` when reference-count analysis deems the assignment
/// unsafe to touch: multiple references, zero references, the sole
/// reference lives strictly inside a child region (the scoped pass
/// leaves those as hoisted assignments for readability), or the
/// reference sits in a sibling branch.
fn plan_inline(
    lines: &[String],
    tree: &LineRegion,
    assignment: &Assignment,
    removed: &[bool],
) -> Option<InlineOutcome> {
    // Count references inside the scope range, excluding the assignment
    // line itself.
    let mut same_scope_ref: Option<usize> = None;
    let mut total = 0usize;

    let scope_region = find_region_by_range(tree, &assignment.scope).unwrap_or(tree);

    for line_idx in assignment.scope.clone() {
        if line_idx == assignment.line || removed[line_idx] {
            continue;
        }
        let trimmed = lines[line_idx].trim();
        let count = count_var_refs(trimmed, &assignment.var);
        if count == 0 {
            continue;
        }
        total += count;
        if total > 1 {
            return None;
        }
        if !line_is_in_child(scope_region, line_idx) {
            same_scope_ref = Some(line_idx);
        }
        // Nested references (strictly inside a child region) are left
        // alone. Inlining into a nested consumer while keeping the
        // outer assignment would orphan the assignment, which the
        // downstream `discard_unused_assignments_text` then strips
        // into a bare statement. Leaving the pair as-is preserves the
        // "hoisted assignment over guard cond" shape the text pass
        // would otherwise collapse.
    }

    if total != 1 {
        return None;
    }

    same_scope_ref.map(|consumer| InlineOutcome { consumer })
}

/// Walk the tree and locate the region whose `stmt_range` matches
/// `range` exactly. Returns the root for root-scoped assignments.
fn find_region_by_range<'a>(
    tree: &'a LineRegion,
    range: &std::ops::Range<usize>,
) -> Option<&'a LineRegion> {
    if tree.stmt_range == *range {
        return Some(tree);
    }
    for child in &tree.children {
        if let Some(found) = find_region_by_range(child, range) {
            return Some(found);
        }
    }
    None
}

/// Return true when `line_idx` sits inside one of `region`'s children
/// (strictly nested relative to `region` itself).
fn line_is_in_child(region: &LineRegion, line_idx: usize) -> bool {
    region
        .children
        .iter()
        .any(|child| child.stmt_range.contains(&line_idx))
}

/// Walk the tree and record `$Temp = RHS` assignments with their
/// enclosing region's stmt_range. Assignments at the root sit in the
/// synthetic `0..lines.len()` range.
fn collect_assignments(tree: &LineRegion, lines: &[String], out: &mut Vec<Assignment>) {
    walk_region(tree, &tree.stmt_range, lines, out);
}

fn walk_region(
    region: &LineRegion,
    current_scope: &std::ops::Range<usize>,
    lines: &[String],
    out: &mut Vec<Assignment>,
) {
    for line_idx in region.stmt_range.clone() {
        if line_is_in_child(region, line_idx) {
            continue;
        }
        if let Some((var, _)) = parse_temp_assignment(lines[line_idx].trim()) {
            out.push(Assignment {
                line: line_idx,
                var: var.to_string(),
                scope: current_scope.clone(),
            });
        }
    }
    for child in &region.children {
        walk_region(child, &child.stmt_range, lines, out);
    }
}

/// Length budget mirror of the text pass. Reject an inline whose
/// result overruns `MAX_LINE_WIDTH` unless it shortens the consumer
/// or the rhs is trivial (bare identifier / literal).
fn inline_fits_budget(replacement: &str, var: &str, rhs: &str) -> bool {
    use crate::bytecode::MAX_LINE_WIDTH;
    let shortens = rhs.len() + 2 <= var.len();
    let trivial = is_trivial_expr(rhs);
    shortens || trivial || replacement.len() <= MAX_LINE_WIDTH
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(src: &[&str]) -> Vec<String> {
        src.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn same_block_inline_and_remove() {
        let mut input = lines(&["$T = 1", "y = $T + 1"]);
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(changed);
        assert_eq!(input, vec!["y = 1 + 1".to_string()]);
    }

    #[test]
    fn guard_header_with_body_reuse_is_skipped() {
        // `$T` appears in the guard cond AND inside the body: not
        // single-use. Scoped pass must skip, leaving input unchanged.
        // This is the bug class 5d.13 targets.
        let original = lines(&[
            "$T = complex_expr",
            "if (IsValid($T.X)) {",
            "    y = $T.Y",
            "}",
        ]);
        let mut input = original.clone();
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(!changed);
        assert_eq!(input, original);
    }

    #[test]
    fn single_use_into_guard_cond_is_left_alone() {
        // `$T` appears exactly once, in the guard cond of an `if (...) {`
        // opener that the region tree classifies as a child region. The
        // text pass inlines this aggressively and drops the assignment;
        // the scoped pass preserves the `$T = RHS; if ($T) { ... }` shape
        // so downstream `discard_unused_assignments_text` can't orphan
        // the assignment into a bare expression statement.
        let original = lines(&["$T = simple", "if (IsValid($T)) {", "    tick()", "}"]);
        let mut input = original.clone();
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(!changed);
        assert_eq!(input, original);
    }

    #[test]
    fn duplicate_assignment_at_same_depth_is_skipped() {
        // Two assignments to $T at the same depth: not single-use
        // regardless of how many references exist.
        let original = lines(&["$T = A", "use($T)", "$T = A", "use_again($T)"]);
        let mut input = original.clone();
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(!changed);
        assert_eq!(input, original);
    }

    #[test]
    fn nested_use_is_left_alone() {
        // One reference, inside a nested If. The scoped pass no longer
        // inlines across region boundaries: inlining here while leaving
        // the outer assignment would let
        // `discard_unused_assignments_text` collapse the now-unused
        // assignment into a bare statement.
        let original = lines(&["$T = X", "if (cond) {", "    use($T)", "}"]);
        let mut input = original.clone();
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(!changed);
        assert_eq!(input, original);
    }

    #[test]
    fn empty_input_is_a_noop() {
        let mut input: Vec<String> = Vec::new();
        let changed = inline_single_use_temps_scoped(&mut input);
        assert!(!changed);
        assert!(input.is_empty());
    }
}
