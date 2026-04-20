//! Text-level transforms: temp inlining, expression cleanup, loop/struct/switch
//! pattern folding, and line formatting.

mod cleanup;
mod fold;
mod loops;
mod pipeline;
mod structs;
mod switch;
mod temps;

pub use cleanup::{
    cleanup_structured_output, eliminate_constant_condition_branches, rename_loop_temp_vars,
    strip_implicit_returns, strip_inlined_break_calls, strip_orphaned_blocks,
    strip_unmatched_braces,
};
pub use fold::fold_long_lines;
pub use pipeline::fold_summary_patterns;
pub use switch::{fold_cascade_across_sequences, fold_switch_enum_cascade};
pub use temps::{
    collect_jump_targets, discard_unused_assignments, discard_unused_assignments_text,
    inline_constant_temps, inline_constant_temps_text, inline_single_use_temps,
    inline_single_use_temps_text,
};

// UE compiler-generated variable/function prefixes shared across transforms.

/// Prefix for `$MakeStruct_TYPE` temp variables and field assignments.
pub(super) const MAKE_STRUCT_PREFIX: &str = "$MakeStruct_";

/// Prefix for `Break*` struct decomposition function calls.
pub(super) const BREAK_FUNC_PREFIX: &str = "Break";

/// Prefix for `$SwitchEnum_CmpSuccess` cascade comparison variables.
pub(super) const SWITCH_ENUM_PREFIX: &str = "$SwitchEnum_CmpSuccess";

/// UE break-hit flag variable name (may have numeric suffixes like `_1`).
pub(super) const BREAK_HIT_VAR: &str = "Temp_bool_True_if_break_was_hit_Variable";

/// Prefix for compiler-generated integer temp variables (loop counters, indices).
pub(super) const TEMP_INT_PREFIX: &str = "Temp_int_";

/// ForEach loop counter variable name.
pub(super) const LOOP_COUNTER_VAR: &str = "Temp_int_Loop_Counter_Variable";

/// ForEach array index variable name.
pub(super) const ARRAY_INDEX_VAR: &str = "Temp_int_Array_Index_Variable";

// Shared helpers

/// Parse `$VarName = expression` or `Temp_* = expression` assignments.
pub(super) fn parse_temp_assignment(text: &str) -> Option<(&str, &str)> {
    if !text.starts_with('$') && !text.starts_with("Temp_") {
        return None;
    }
    let eq_pos = text.find(" = ")?;
    let var = &text[..eq_pos];
    // Must be a simple $name (no dots, brackets, etc.)
    if var.contains('.') || var.contains('[') {
        return None;
    }
    let expr = &text[eq_pos + 3..];
    // Must not be a persistent frame assignment
    if expr.ends_with("[persistent]") {
        return None;
    }
    // Reject function call argument continuations (expression ends with comma)
    if expr.ends_with(',') {
        return None;
    }
    Some((var, expr))
}

/// Count non-overlapping occurrences of `var` in `text` at word boundaries.
pub(super) fn count_var_refs(text: &str, var: &str) -> usize {
    let mut count = 0;
    let mut start = 0;
    while let Some(pos) = text[start..].find(var) {
        let abs_pos = start + pos;
        if is_var_boundary(text, abs_pos, var) {
            count += 1;
        }
        start = abs_pos + var.len();
    }
    count
}

pub(super) use crate::helpers::{
    closes_block, expr_is_compound, find_at_depth_zero, find_matching_paren, is_block_boundary,
    is_ident_char, is_loop_header, opens_block, split_args, strip_outer_parens,
};

/// Check if `var` appears at a word boundary at position `pos` in `text`.
pub(super) fn is_var_boundary(text: &str, pos: usize, var: &str) -> bool {
    let after = pos + var.len();
    let at_start = var.starts_with('$') || pos == 0 || !is_ident_char(text.as_bytes()[pos - 1]);
    let at_end = after >= text.len() || !is_ident_char(text.as_bytes()[after]);
    at_start && at_end
}

/// Substitute `var` with `expr` in `text`, adding parens if needed. First match only.
pub(super) fn substitute_var(text: &str, var: &str, expr: &str) -> String {
    let mut start = 0;
    while let Some(rel) = text[start..].find(var) {
        let pos = start + rel;
        let after = pos + var.len();
        if is_var_boundary(text, pos, var) {
            let needs_wrap = expr_is_compound(expr) && used_in_operator_context(text, pos, after);
            let sub = if needs_wrap {
                format!("({})", expr)
            } else {
                expr.to_string()
            };
            return format!("{}{}{}", &text[..pos], sub, &text[after..]);
        }
        start = after;
    }
    text.to_string()
}

/// Check if an expression contains a function/method call.
pub(super) fn expr_has_call(expr: &str) -> bool {
    let bytes = expr.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'(' && i > 0 {
            // Walk backward to find the identifier before the paren
            let mut j = i;
            while j > 0 && (bytes[j - 1].is_ascii_alphanumeric() || bytes[j - 1] == b'_') {
                j -= 1;
            }
            let word = &expr[j..i];
            if !word.is_empty() && word != "switch" && word != "if" && word != "bool" {
                return true;
            }
        }
    }
    false
}

/// True if `expr` is trivial enough to inline regardless of line length (no calls, operators, or brackets).
pub(super) fn is_trivial_expr(expr: &str) -> bool {
    !expr.is_empty() && !expr.contains(['(', ')', '[', ']']) && !expr_is_compound(expr)
}

fn used_in_operator_context(text: &str, pos: usize, after: usize) -> bool {
    const OPERATORS: &[&str] = &[
        "&&", "||", "+", "-", "*", "/", "%", ">=", "<=", "==", "!=", ">>", "<<", ">", "<", "?",
    ];
    let before = text[..pos].trim_end();
    let after_text = text[after..].trim_start();

    let before_op = before.ends_with("!(")
        || before.ends_with('!')
        || OPERATORS.iter().any(|op| before.ends_with(op));
    let after_op = OPERATORS.iter().any(|op| after_text.starts_with(op));
    before_op || after_op
}

// Tests for private functions (clean_line, parse_temp_assignment,
// substitute_var, split_args, etc.) that aren't accessible from tests/.
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
