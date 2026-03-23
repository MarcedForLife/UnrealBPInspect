//! Temp variable inlining, expression cleanup, and summary pattern folding.

mod cleanup;
mod patterns;
mod temps;

pub use cleanup::{cleanup_structured_output, strip_orphaned_blocks, strip_unmatched_braces};
pub use patterns::fold_summary_patterns;
pub use temps::{discard_unused_assignments, inline_constant_temps, inline_single_use_temps};

// ============================================================
// Shared helpers used by multiple sub-modules (pub(super))
// ============================================================

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

pub(super) fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

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

const OPERATORS: &[&str] = &[
    "&&", "||", "+", "-", "*", "/", "%", ">=", "<=", "==", "!=", ">>", "<<", ">", "<", "?",
];

pub(super) fn expr_is_compound(expr: &str) -> bool {
    OPERATORS
        .iter()
        .any(|op| expr.contains(&format!(" {} ", op)))
        || expr.starts_with('!')
}

/// True if `expr` is trivial enough to inline regardless of line length (no calls, operators, or brackets).
pub(super) fn is_trivial_expr(expr: &str) -> bool {
    !expr.is_empty() && !expr.contains(['(', ')', '[', ']']) && !expr_is_compound(expr)
}

fn used_in_operator_context(text: &str, pos: usize, after: usize) -> bool {
    let before = text[..pos].trim_end();
    let after_text = text[after..].trim_start();

    let before_op = before.ends_with("!(")
        || before.ends_with("! ")
        || OPERATORS.iter().any(|op| before.ends_with(op));
    let after_op = OPERATORS.iter().any(|op| after_text.starts_with(op));
    before_op || after_op
}

pub(super) fn find_matching_paren(input: &str) -> Option<usize> {
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

pub(super) fn find_at_depth_zero(input: &str, needle: &str) -> Option<usize> {
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

pub(super) fn strip_outer_parens(input: &str) -> &str {
    if let Some(close) = find_matching_paren(input) {
        if close == input.len() - 1 {
            return &input[1..close];
        }
    }
    input
}

// Inline tests: these test private functions (clean_line, parse_temp_assignment,
// substitute_var, split_args, etc.) that aren't accessible from tests/.
#[cfg(test)]
mod tests {
    use super::cleanup::*;
    use super::patterns::*;
    use super::temps::*;
    use super::*;

    // split_args
    #[test]
    fn split_args_empty() {
        assert_eq!(split_args(""), Vec::<&str>::new());
    }

    #[test]
    fn split_args_single() {
        assert_eq!(split_args("foo"), vec!["foo"]);
    }

    #[test]
    fn split_args_multiple() {
        assert_eq!(split_args("a, b, c"), vec!["a", "b", "c"]);
    }

    #[test]
    fn split_args_nested_parens() {
        assert_eq!(split_args("foo(a, b), bar"), vec!["foo(a, b)", "bar"]);
    }

    #[test]
    fn split_args_nested_brackets() {
        assert_eq!(split_args("a[0, 1], b"), vec!["a[0, 1]", "b"]);
    }

    #[test]
    fn split_args_whitespace_trimmed() {
        assert_eq!(split_args(" a , b "), vec!["a", "b"]);
    }

    // detect_common_suffix
    #[test]
    fn detect_suffix_shared() {
        let fields = vec!["Location_1", "Rotation_1", "Scale_1"];
        assert_eq!(detect_common_suffix(&fields), Some("_1"));
    }

    #[test]
    fn detect_suffix_mixed() {
        let fields = vec!["Location_1", "Rotation_2"];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    #[test]
    fn detect_suffix_none() {
        let fields = vec!["Location", "Rotation"];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    #[test]
    fn detect_suffix_empty() {
        let fields: Vec<&str> = vec![];
        assert_eq!(detect_common_suffix(&fields), None);
    }

    // strip_make_prefix
    #[test]
    fn strip_make_vector() {
        assert_eq!(strip_make_prefix("MakeVector(1, 2, 3)"), "Vector(1, 2, 3)");
    }

    #[test]
    fn strip_make_no_uppercase() {
        // "Makefile", no uppercase after "Make"
        assert_eq!(strip_make_prefix("Makefile"), "Makefile");
    }

    #[test]
    fn strip_make_preceded_by_dollar() {
        assert_eq!(strip_make_prefix("$MakeStruct_Foo"), "$MakeStruct_Foo");
    }

    #[test]
    fn strip_make_preceded_by_ident() {
        assert_eq!(strip_make_prefix("SomeMakeVector(x)"), "SomeMakeVector(x)");
    }

    #[test]
    fn strip_make_mid_line() {
        assert_eq!(
            strip_make_prefix("x = MakeRotator(1, 2, 3)"),
            "x = Rotator(1, 2, 3)"
        );
    }

    #[test]
    fn strip_make_no_paren() {
        assert_eq!(strip_make_prefix("MakeVector"), "MakeVector");
    }

    // clean_line
    #[test]
    fn clean_line_bool_strip() {
        assert_eq!(clean_line("bool(X)"), "X");
    }

    #[test]
    fn clean_line_bool_compound() {
        assert_eq!(clean_line("bool(A && B)"), "A && B");
    }

    #[test]
    fn clean_line_double_negation() {
        assert_eq!(clean_line("!(!X)"), "X");
    }

    #[test]
    fn clean_line_negation_compound_inner_safe() {
        // !(!A && B), inner ! only negates A, should NOT simplify
        assert_eq!(clean_line("!(!A && B)"), "!(!A && B)");
    }

    #[test]
    fn clean_line_outer_parens_if() {
        assert_eq!(clean_line("if ((X)) {"), "if (X) {");
    }

    #[test]
    fn clean_line_no_change() {
        assert_eq!(clean_line("self.Foo.Bar()"), "self.Foo.Bar()");
    }

    // has_toplevel_logical_op
    #[test]
    fn toplevel_op_simple_and() {
        assert!(has_toplevel_logical_op("A && B"));
    }

    #[test]
    fn toplevel_op_inside_parens() {
        assert!(!has_toplevel_logical_op("(A && B)"));
    }

    #[test]
    fn toplevel_op_none() {
        assert!(!has_toplevel_logical_op("A"));
    }

    #[test]
    fn toplevel_op_mixed() {
        assert!(has_toplevel_logical_op("A || (B && C)"));
    }

    // parse_temp_assignment
    #[test]
    fn parse_temp_dollar_var() {
        assert_eq!(parse_temp_assignment("$Foo = bar"), Some(("$Foo", "bar")));
    }

    #[test]
    fn parse_temp_with_dot() {
        assert_eq!(parse_temp_assignment("$Foo.bar = x"), None);
    }

    #[test]
    fn parse_temp_non_temp() {
        assert_eq!(parse_temp_assignment("x = y"), None);
    }

    #[test]
    fn parse_temp_persistent() {
        assert_eq!(parse_temp_assignment("$X = foo [persistent]"), None);
    }

    #[test]
    fn parse_temp_underscore_var() {
        assert_eq!(parse_temp_assignment("Temp_0 = x"), Some(("Temp_0", "x")));
    }

    // count_var_refs
    #[test]
    fn count_refs_zero() {
        assert_eq!(count_var_refs("hello world", "$Foo"), 0);
    }

    #[test]
    fn count_refs_one() {
        assert_eq!(count_var_refs("$Foo + 1", "$Foo"), 1);
    }

    #[test]
    fn count_refs_multiple() {
        assert_eq!(count_var_refs("$Foo + $Foo", "$Foo"), 2);
    }

    #[test]
    fn count_refs_partial_no_match() {
        // $Foo in $FooBar should not match
        assert_eq!(count_var_refs("$FooBar + 1", "$Foo"), 0);
    }

    // substitute_var
    #[test]
    fn substitute_simple() {
        assert_eq!(substitute_var("$X + 1", "$X", "42"), "42 + 1");
    }

    #[test]
    fn substitute_compound_gets_parens() {
        assert_eq!(substitute_var("$X + 1", "$X", "A + B"), "(A + B) + 1");
    }

    #[test]
    fn substitute_no_match() {
        assert_eq!(substitute_var("$Y + 1", "$X", "42"), "$Y + 1");
    }

    // expr_is_compound
    #[test]
    fn compound_addition() {
        assert!(expr_is_compound("A + B"));
    }

    #[test]
    fn compound_negation() {
        assert!(expr_is_compound("!X"));
    }

    #[test]
    fn compound_function_call() {
        assert!(!expr_is_compound("foo()"));
    }

    #[test]
    fn compound_simple_var() {
        assert!(!expr_is_compound("$X"));
    }

    // find_matching_paren
    #[test]
    fn paren_balanced() {
        assert_eq!(find_matching_paren("(abc)"), Some(4));
    }

    #[test]
    fn paren_nested() {
        assert_eq!(find_matching_paren("(a(b)c)"), Some(6));
    }

    #[test]
    fn paren_no_open() {
        assert_eq!(find_matching_paren("abc"), None);
    }

    #[test]
    fn paren_unbalanced() {
        assert_eq!(find_matching_paren("(abc"), None);
    }

    // strip_outer_parens
    #[test]
    fn outer_parens_simple() {
        assert_eq!(strip_outer_parens("(X)"), "X");
    }

    #[test]
    fn outer_parens_double() {
        assert_eq!(strip_outer_parens("((X))"), "(X)");
    }

    #[test]
    fn outer_parens_not_matching() {
        // (A)(B), the outer ( doesn't match the outer )
        assert_eq!(strip_outer_parens("(A)(B)"), "(A)(B)");
    }

    #[test]
    fn outer_parens_not_wrapped() {
        assert_eq!(strip_outer_parens("A + B"), "A + B");
    }

    // preceding boundary checks
    #[test]
    fn count_refs_temp_no_prefix_match() {
        assert_eq!(count_var_refs("SomeTemp_0 + 1", "Temp_0"), 0);
    }

    #[test]
    fn count_refs_temp_standalone() {
        assert_eq!(count_var_refs("Temp_0 + 1", "Temp_0"), 1);
    }

    #[test]
    fn substitute_temp_no_prefix_match() {
        assert_eq!(
            substitute_var("SomeTemp_0 + 1", "Temp_0", "42"),
            "SomeTemp_0 + 1"
        );
    }

    #[test]
    fn count_refs_dollar_prefix_safe() {
        assert_eq!(count_var_refs("pre$Foo + 1", "$Foo"), 1);
    }

    // inline_constant_temps
    #[test]
    fn inline_constant_temps_same_expr() {
        use crate::bytecode::decode::BcStatement;
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "x = switch(Temp_bool_Variable) { false: A, true: B }".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 30,
                text: "y = switch(Temp_bool_Variable) { false: C, true: D }".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "x = switch(LeftHand) { false: A, true: B }");
        assert_eq!(stmts[1].text, "y = switch(LeftHand) { false: C, true: D }");
    }

    #[test]
    fn inline_constant_temps_different_exprs_skipped() {
        use crate::bytecode::decode::BcStatement;
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_bool_Variable = LeftHand".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "x = Temp_bool_Variable".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "Temp_bool_Variable = RightHand".into(),
            },
            BcStatement {
                mem_offset: 30,
                text: "y = Temp_bool_Variable".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        // Different exprs -> not inlined, all 4 remain
        assert_eq!(stmts.len(), 4);
    }

    #[test]
    fn inline_constant_temps_single_assign_multi_ref() {
        use crate::bytecode::decode::BcStatement;
        // Single Temp_* assignment, multiple references; should be inlined
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "Temp_0 = foo".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "bar(Temp_0)".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "baz(Temp_0)".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "bar(foo)");
        assert_eq!(stmts[1].text, "baz(foo)");
    }

    #[test]
    fn inline_constant_temps_dollar_single_assign_skipped() {
        use crate::bytecode::decode::BcStatement;
        // $-prefixed single assignment may be out-param, skip
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Param = _".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "Foo($Param)".into(),
            },
            BcStatement {
                mem_offset: 20,
                text: "x = $Param + 1".into(),
            },
        ];
        inline_constant_temps(&mut stmts);
        assert_eq!(stmts.len(), 3); // unchanged
    }

    // discard_unused_assignments: pure expression removal
    #[test]
    fn discard_removes_pure_unused_assignment() {
        use crate::bytecode::decode::BcStatement;
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = SomeValue".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].text, "DoWork()");
    }

    #[test]
    fn discard_keeps_call_unused_assignment() {
        use crate::bytecode::decode::BcStatement;
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = SomeCall()".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 2);
        assert_eq!(stmts[0].text, "SomeCall()");
    }

    #[test]
    fn discard_removes_switch_unused_assignment() {
        use crate::bytecode::decode::BcStatement;
        let mut stmts = vec![
            BcStatement {
                mem_offset: 0,
                text: "$Temp = switch(X) { false: A, true: B }".into(),
            },
            BcStatement {
                mem_offset: 10,
                text: "DoWork()".into(),
            },
        ];
        discard_unused_assignments(&mut stmts);
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].text, "DoWork()");
    }

    // expr_has_call
    #[test]
    fn expr_has_call_function() {
        assert!(expr_has_call("IsValid(x)"));
    }

    #[test]
    fn expr_has_call_method() {
        assert!(expr_has_call("Foo.Bar()"));
    }

    #[test]
    fn expr_has_call_switch() {
        assert!(!expr_has_call("switch(X) { false: A, true: B }"));
    }

    #[test]
    fn expr_has_call_parens() {
        assert!(!expr_has_call("(A + B)"));
    }

    #[test]
    fn expr_has_call_none() {
        assert!(!expr_has_call("SomeValue"));
    }

    // cleanup_structured_output: return before sequence marker
    #[test]
    fn cleanup_strips_return_before_sequence_marker() {
        let mut lines = vec![
            "AdjustStatus(x, 0)".to_string(),
            "return".to_string(),
            "// sequence [1]:".to_string(),
            "AdjustStatus(y, 1)".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert!(!lines.iter().any(|l| l.trim() == "return"));
        assert!(lines.iter().any(|l| l.trim() == "// sequence [1]:"));
    }

    // cleanup_structured_output: trailing unmatched braces
    #[test]
    fn cleanup_strips_trailing_unmatched_braces() {
        let mut lines = vec![
            "if (cond) {".to_string(),
            "    do_something()".to_string(),
            "}".to_string(),
            "}".to_string(),
            "}".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert_eq!(lines, vec!["if (cond) {", "    do_something()", "}",]);
    }

    #[test]
    fn cleanup_keeps_matched_braces() {
        let mut lines = vec![
            "if (a) {".to_string(),
            "    if (b) {".to_string(),
            "        code()".to_string(),
            "    }".to_string(),
            "}".to_string(),
        ];
        cleanup_structured_output(&mut lines);
        assert_eq!(lines.len(), 5); // all lines preserved
    }

    // ========== rewrite_bool_switches tests ==========

    #[test]
    fn bool_switch_basic() {
        assert_eq!(
            rewrite_bool_switches("switch(LeftHand) { false: self.Right, true: self.Left }"),
            "LeftHand ? self.Left : self.Right"
        );
    }

    #[test]
    fn bool_switch_true_first() {
        assert_eq!(
            rewrite_bool_switches("switch(X) { true: A, false: B }"),
            "X ? A : B"
        );
    }

    #[test]
    fn bool_switch_method_chain() {
        assert_eq!(
            rewrite_bool_switches(
                "switch(LeftHand) { false: self.RightHandle, true: self.LeftHandle }.SetTarget(x)"
            ),
            "(LeftHand ? self.LeftHandle : self.RightHandle).SetTarget(x)"
        );
    }

    #[test]
    fn bool_switch_compound_condition() {
        assert_eq!(
            rewrite_bool_switches("switch(self.Hunger == 0.0000) { false: 0.0000, true: rate }"),
            "(self.Hunger == 0.0000) ? rate : 0.0000"
        );
    }

    #[test]
    fn bool_switch_nested() {
        // Inner switch rewrites first (left-to-right), then outer.
        // Result is right-associative: X ? C : (Y ? B : A) ≡ X ? C : Y ? B : A
        assert_eq!(
            rewrite_bool_switches("switch(X) { false: switch(Y) { false: A, true: B }, true: C }"),
            "X ? C : Y ? B : A"
        );
    }

    #[test]
    fn bool_switch_in_assignment() {
        assert_eq!(
            rewrite_bool_switches(
                "Grip = switch(LeftHand) { false: self.RightGrip, true: self.LeftGrip }"
            ),
            "Grip = LeftHand ? self.LeftGrip : self.RightGrip"
        );
    }

    #[test]
    fn bool_switch_non_bool_not_rewritten() {
        let input = "switch(X) { 0: A, 1: B, 2: C }";
        assert_eq!(rewrite_bool_switches(input), input);
    }

    #[test]
    fn bool_switch_default_not_rewritten() {
        let input = "switch(X) { false: A, true: B, default: C }";
        assert_eq!(rewrite_bool_switches(input), input);
    }

    #[test]
    fn bool_switch_multiple_per_line() {
        assert_eq!(
            rewrite_bool_switches(
                "Foo(switch(A) { false: X, true: Y }, switch(B) { false: P, true: Q })"
            ),
            "Foo(A ? Y : X, B ? Q : P)"
        );
    }

    #[test]
    fn bool_switch_identical_branches() {
        assert_eq!(
            rewrite_bool_switches("out X = switch(IsValid) { false: src.Field, true: src.Field }"),
            "out X = src.Field"
        );
    }

    #[test]
    fn bool_switch_in_arithmetic_context() {
        assert_eq!(
            rewrite_bool_switches("0.0 + switch(A) { false: 0, true: X }"),
            "0.0 + (A ? X : 0)"
        );
    }

    #[test]
    fn bool_switch_chained_arithmetic() {
        assert_eq!(
            rewrite_bool_switches(
                "switch(A) { false: 0, true: X } + switch(B) { false: 0, true: Y }"
            ),
            "(A ? X : 0) + (B ? Y : 0)"
        );
    }

    #[test]
    fn bool_switch_simple_assignment_no_wrap() {
        assert_eq!(
            rewrite_bool_switches("x = switch(C) { false: A, true: B }"),
            "x = C ? B : A"
        );
    }

    // ========== fold_cast_inline tests ==========

    #[test]
    fn cast_inline_basic() {
        let mut lines = vec![
            "$Cast = cast<MyType>(GetObj())".to_string(),
            "if ($Cast) {".to_string(),
            "    self.Foo = $Cast".to_string(),
            "}".to_string(),
        ];
        fold_cast_inline(&mut lines);
        assert_eq!(lines[0], "if (cast<MyType>(GetObj())) {");
        assert_eq!(lines[1], "    self.Foo = cast<MyType>(GetObj())");
        assert_eq!(lines[2], "}");
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn cast_inline_too_many_refs() {
        let mut lines = vec![
            "$Cast = cast<T>(expr)".to_string(),
            "if ($Cast) {".to_string(),
            "    A($Cast)".to_string(),
            "    B($Cast)".to_string(),
            "    C($Cast)".to_string(),
            "}".to_string(),
        ];
        fold_cast_inline(&mut lines);
        // 4 refs (if + 3 body) > 3, should NOT inline
        assert_eq!(lines.len(), 6);
        assert_eq!(lines[0], "$Cast = cast<T>(expr)");
    }

    #[test]
    fn cast_inline_already_else_return() {
        let mut lines = vec![
            "$Cast = cast<T>(expr) else return".to_string(),
            "self.Foo = $Cast".to_string(),
        ];
        fold_cast_inline(&mut lines);
        // Should not touch "else return" lines
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0], "$Cast = cast<T>(expr) else return");
    }

    // ========== hoist_repeated_ternaries tests ==========

    #[test]
    fn hoist_repeated_ternary_3_uses() {
        let mut lines = vec![
            "    A((X ? self.Left : self.Right).Foo())".to_string(),
            "    B((X ? self.Left : self.Right).Bar())".to_string(),
            "    C((X ? self.Left : self.Right).Baz())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines.len(), 4);
        assert!(lines[0].contains(" = X ? self.Left : self.Right"));
        assert!(!lines[1].contains("X ? self.Left"));
        assert!(!lines[2].contains("X ? self.Left"));
        assert!(!lines[3].contains("X ? self.Left"));
    }

    #[test]
    fn hoist_no_change_for_2_uses() {
        let mut lines = vec![
            "    A((X ? L : R).Foo())".to_string(),
            "    B((X ? L : R).Bar())".to_string(),
        ];
        let original = lines.clone();
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines, original);
    }

    #[test]
    fn hoist_left_right_naming() {
        let mut lines = vec![
            "    A((H ? self.LeftVRHand : self.RightVRHand).M())".to_string(),
            "    B((H ? self.LeftVRHand : self.RightVRHand).N())".to_string(),
            "    C((H ? self.LeftVRHand : self.RightVRHand).O())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert_eq!(lines.len(), 4);
        assert!(lines[0].contains("$VRHand = "));
        assert!(lines[1].contains("$VRHand.M()"));
    }

    #[test]
    fn hoist_preserves_indent() {
        let mut lines = vec![
            "        A((X ? L : R).F())".to_string(),
            "        B((X ? L : R).G())".to_string(),
            "        C((X ? L : R).H())".to_string(),
        ];
        hoist_repeated_ternaries(&mut lines);
        assert!(lines[0].starts_with("        $"));
    }

    #[test]
    fn extract_ternaries_basic() {
        let result = extract_parenthesized_ternaries("A((X ? L : R).Foo(), (Y ? A : B))");
        assert_eq!(result.len(), 2);
        assert!(result.contains(&"(X ? L : R)".to_string()));
        assert!(result.contains(&"(Y ? A : B)".to_string()));
    }

    #[test]
    fn extract_left_right_suffix_test() {
        assert_eq!(
            extract_left_right_suffix("self.LeftVRHand", "self.RightVRHand"),
            Some("VRHand".to_string())
        );
        assert_eq!(
            extract_left_right_suffix("self.LeftMotionController", "self.RightMotionController"),
            Some("MotionController".to_string())
        );
        assert_eq!(extract_left_right_suffix("self.Foo", "self.Bar"), None);
    }

    // ========== simplify_bool_comparisons tests ==========

    #[test]
    fn simplify_not_call_eq_1() {
        let mut lines = vec!["    if (!GetIsHMDWorn() == 1) {".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    if (!GetIsHMDWorn()) {");
    }

    #[test]
    fn simplify_not_call_eq_0() {
        let mut lines = vec!["    if (!GetIsHMDWorn() == 0) {".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    if (GetIsHMDWorn()) {");
    }

    #[test]
    fn simplify_not_call_ne_0() {
        let mut lines = vec!["    x = !Func() != 0".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    x = !Func()");
    }

    #[test]
    fn simplify_not_call_ne_1() {
        let mut lines = vec!["    x = !Func() != 1".to_string()];
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines[0], "    x = Func()");
    }

    #[test]
    fn simplify_does_not_match_member_access() {
        let mut lines = vec!["    if (!self.Flag == 1) {".to_string()];
        let original = lines.clone();
        simplify_bool_comparisons(&mut lines);
        assert_eq!(lines, original);
    }

    // ========== fold_outparam_calls tests ==========

    #[test]
    fn outparam_basic_fold() {
        let mut lines = vec![
            "self.Constraint.GetRotationAlpha($GetRotation_Alpha)".to_string(),
            "out Angle = ($GetRotation_Alpha * 2.0) - 1.0".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        assert_eq!(lines.len(), 1);
        assert_eq!(
            lines[0],
            "out Angle = (self.Constraint.GetRotationAlpha() * 2.0) - 1.0"
        );
    }

    #[test]
    fn outparam_multiple_dollar_args_skipped() {
        let mut lines = vec!["Func($A, $B)".to_string(), "x = $A + $B".to_string()];
        fold_outparam_calls(&mut lines);
        // Multiple $-args -> skip
        assert_eq!(lines.len(), 2);
    }

    #[test]
    fn outparam_referenced_twice_skipped() {
        let mut lines = vec![
            "Func($Out)".to_string(),
            "x = $Out + 1".to_string(),
            "y = $Out + 2".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        // Used twice -> skip
        assert_eq!(lines.len(), 3);
    }

    #[test]
    fn outparam_with_assignment_skipped() {
        let mut lines = vec![
            "$Out = someExpr".to_string(),
            "Func($Out)".to_string(),
            "x = $Out".to_string(),
        ];
        fold_outparam_calls(&mut lines);
        // Has assignment -> it's a regular temp, not an out-param
        assert_eq!(lines.len(), 3);
    }

    // is_unused_outparam: requires var name to match function name
    #[test]
    fn unused_outparam_matching_name() {
        let lines = vec![
            "BreakHitResult(src, $BreakHitResult_Location)".to_string(),
            "x = $BreakHitResult_Location".to_string(),
        ];
        // $BreakHitResult_Location starts with "BreakHitResult" -> not suppressed
        // (it appears in non-arg context too, so it returns false anyway)
        assert!(!is_unused_outparam(&lines, "$BreakHitResult_Location"));
    }

    #[test]
    fn unused_outparam_non_matching_name() {
        let lines = vec!["FClamp($Add_FloatFloat, 0.0, 1.0)".to_string()];
        // $Add_FloatFloat doesn't start with "FClamp" -> false
        assert!(!is_unused_outparam(&lines, "$Add_FloatFloat"));
    }

    #[test]
    fn unused_outparam_genuine() {
        let lines = vec![
            "GetFoo($GetFoo_Result)".to_string(),
            "GetFoo($GetFoo_Result)".to_string(),
        ];
        // $GetFoo_Result starts with "GetFoo", only appears as arg -> true
        assert!(is_unused_outparam(&lines, "$GetFoo_Result"));
    }

    // fold_switch_enum_cascade
    #[test]
    fn switch_enum_cascade_flat() {
        let mut lines = vec![
            "$SwitchEnum_CmpSuccess = Status != 0".to_string(),
            "if ($SwitchEnum_CmpSuccess) {".to_string(),
            "    $SwitchEnum_CmpSuccess = Status != 1".to_string(),
            "    if (!$SwitchEnum_CmpSuccess) return".to_string(),
            "}".to_string(),
            "body_after_cascade()".to_string(),
        ];
        fold_switch_enum_cascade(&mut lines);
        assert!(lines[0].contains("// switch (Status)"));
        assert!(lines[1].contains("// case Status == 0:"));
        assert_eq!(lines[2], "body_after_cascade()");
    }

    #[test]
    fn switch_enum_cascade_no_body() {
        let mut lines = vec![
            "$SwitchEnum_CmpSuccess = X != 0".to_string(),
            "if ($SwitchEnum_CmpSuccess) {".to_string(),
            "    $SwitchEnum_CmpSuccess = X != 1".to_string(),
            "    if (!$SwitchEnum_CmpSuccess) return".to_string(),
            "}".to_string(),
            "return".to_string(),
        ];
        fold_switch_enum_cascade(&mut lines);
        assert!(lines[0].contains("// switch (X)"));
        // No case label before return
        assert_eq!(lines[1], "return");
    }
}
