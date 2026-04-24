//! Expression and statement printer, inverse of `parse_expr` / `parse_stmt`.
//!
//! `fmt_expr` walks an `Expr` tree and renders decoder-output text.
//! The invariant is idempotence under parse-print-parse: for any
//! `parsed = parse_expr(input)`, `parse_expr(&fmt_expr(&parsed))` is
//! equal to `parsed`. Byte equality with the original decoder text is
//! a separate goal; `tests/snapshots/ir_roundtrip_divergences.txt`
//! records shapes where parse-print normalises whitespace or redundant
//! parens without changing the tree.
//!
//! `fmt_stmt` mirrors the same invariant for `Stmt` and delegates each
//! embedded `Expr` back through `fmt_expr`. `Stmt::Unknown(raw)`
//! prints verbatim so comments, block delimiters, and other
//! non-statement lines round-trip byte-for-byte.
//!
//! Parenthesization is minimal: an operand gets parens when its own
//! precedence is lower than the enclosing operator's, or when its
//! shape could re-bind a postfix form on re-parse.

use super::types::{Expr, Stmt, SwitchArm};
use std::fmt;

/// Render an `Expr` as a string suitable for `parse_expr`.
pub fn fmt_expr(expr: &Expr) -> String {
    let mut out = String::new();
    write_expr(&mut out, expr);
    out
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&fmt_expr(self))
    }
}

/// Render a `Stmt` as a decoder-output line suitable for `parse_stmt`.
///
/// Hex targets use `{:x}` unpadded, matching the decoder's own
/// `push_flow 0x{:x}` / `jump 0x{:x}` emission in `decode/match_op.rs`
/// and the CFG linearizer in `cfg/block/linearize.rs`.
pub fn fmt_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::PopFlow => "pop_flow".to_owned(),
        Stmt::PopFlowIfNot { cond } => format!("pop_flow_if_not({})", fmt_expr(cond)),
        Stmt::PushFlow { target } => format!("push_flow 0x{target:x}"),
        Stmt::ContinueIfNot { cond } => format!("continue_if_not({})", fmt_expr(cond)),
        Stmt::IfJump { cond, target } => format!("if !({}) jump 0x{target:x}", fmt_expr(cond)),
        Stmt::Jump { target } => format!("jump 0x{target:x}"),
        Stmt::JumpComputed { expr } => format!("jump_computed({})", fmt_expr(expr)),
        Stmt::ReturnNop => "return nop".to_owned(),
        Stmt::BareReturn => "return".to_owned(),
        Stmt::Assignment { lhs, rhs } => format!("{} = {}", fmt_expr(lhs), fmt_expr(rhs)),
        Stmt::CompoundAssign { op, lhs, rhs } => {
            format!("{} {} {}", fmt_expr(lhs), op, fmt_expr(rhs))
        }
        Stmt::Call { expr } => fmt_expr(expr),
        Stmt::WithTrailer { inner, trailer } => {
            let mut out = fmt_stmt(inner);
            out.push_str(trailer);
            out
        }
        Stmt::Comment(text) => text.clone(),
        Stmt::BlockClose => "}".to_owned(),
        Stmt::Break => "break".to_owned(),
        Stmt::IfOpen { cond } => format!("if ({}) {{", fmt_expr(cond)),
        Stmt::Else => "} else {".to_owned(),
        Stmt::Unknown(raw) => raw.clone(),
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&fmt_stmt(self))
    }
}

fn write_expr(out: &mut String, expr: &Expr) {
    match expr {
        Expr::Literal(s) | Expr::Var(s) | Expr::Unknown(s) => out.push_str(s),
        Expr::Call { name, args } => {
            out.push_str(name);
            write_args(out, args);
        }
        Expr::MethodCall { recv, name, args } => {
            write_postfix_recv(out, recv);
            out.push('.');
            out.push_str(name);
            write_args(out, args);
        }
        Expr::FieldAccess { recv, field } => {
            write_postfix_recv(out, recv);
            out.push('.');
            out.push_str(field);
        }
        Expr::Index { recv, idx } => {
            write_postfix_recv(out, recv);
            out.push('[');
            write_expr(out, idx);
            out.push(']');
        }
        Expr::Binary { op, lhs, rhs } => {
            let prec = binary_prec(op);
            write_binary_operand(out, lhs, prec, Side::Left);
            out.push(' ');
            out.push_str(op);
            out.push(' ');
            write_binary_operand(out, rhs, prec, Side::Right);
        }
        Expr::Unary { op, operand } => {
            out.push_str(op);
            if needs_unary_parens(operand) {
                out.push('(');
                write_expr(out, operand);
                out.push(')');
            } else {
                write_expr(out, operand);
            }
        }
        Expr::Cast { ty, inner } => {
            // Preserve `kind<ty>` when the parser re-packed a non-default
            // cast kind into `Cast.ty`. In that case `ty` already contains
            // `kind<...>`, so splitting it back out keeps round-trip clean.
            if let Some((kind, inner_ty)) = split_packed_cast_kind(ty) {
                out.push_str(kind);
                out.push('<');
                out.push_str(inner_ty);
                out.push('>');
            } else {
                out.push_str("icast<");
                out.push_str(ty);
                out.push('>');
            }
            out.push('(');
            write_expr(out, inner);
            out.push(')');
        }
        Expr::StructConstruct { ty, fields } => {
            // TODO(5d.x): confirm shape against decoder when StructConstruct
            // gets a parser path. Current renderer is a placeholder.
            out.push_str(ty);
            out.push_str("{ ");
            for (i, (field, value)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(field);
                out.push_str(": ");
                write_expr(out, value);
            }
            out.push_str(" }");
        }
        Expr::Select {
            cond,
            then_expr,
            else_expr,
        } => {
            out.push_str("select(");
            write_expr(out, cond);
            out.push_str(", ");
            write_expr(out, then_expr);
            out.push_str(", ");
            write_expr(out, else_expr);
            out.push(')');
        }
        Expr::Switch {
            scrut,
            arms,
            default,
        } => {
            out.push_str("switch(");
            write_expr(out, scrut);
            out.push_str(") { ");
            let mut first = true;
            for SwitchArm { pat, body } in arms {
                if !first {
                    out.push_str(", ");
                }
                first = false;
                write_expr(out, pat);
                out.push_str(": ");
                write_expr(out, body);
            }
            if let Some(default_expr) = default {
                if !first {
                    out.push_str(", ");
                }
                out.push_str("_: ");
                write_expr(out, default_expr);
            }
            out.push_str(" }");
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            write_ternary_operand(out, cond);
            out.push_str(" ? ");
            write_ternary_operand(out, then_expr);
            out.push_str(" : ");
            // The else branch is right-associative, nested ternary on
            // the right doesn't need parens.
            write_expr(out, else_expr);
        }
        Expr::Trailer { inner, trailer } => {
            write_expr(out, inner);
            out.push_str(trailer);
        }
        Expr::Out(inner) => {
            out.push_str("out ");
            write_expr(out, inner);
        }
        Expr::ArrayLit(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_expr(out, item);
            }
            out.push(']');
        }
    }
}

fn write_args(out: &mut String, args: &[Expr]) {
    out.push('(');
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        write_expr(out, arg);
    }
    out.push(')');
}

#[derive(Clone, Copy)]
enum Side {
    Left,
    Right,
}

/// Write a binary operand, parenthesizing only when necessary to
/// preserve the original tree on re-parse. All binaries in this IR
/// are left-associative, so a same-precedence operand on the right
/// must be parenthesized.
fn write_binary_operand(out: &mut String, expr: &Expr, parent_prec: u8, side: Side) {
    if let Expr::Binary { op, .. } = expr {
        let child_prec = binary_prec(op);
        let needs = match side {
            Side::Left => child_prec < parent_prec,
            Side::Right => child_prec <= parent_prec,
        };
        if needs {
            out.push('(');
            write_expr(out, expr);
            out.push(')');
            return;
        }
    }
    // Ternary inside a binary always needs parens, ternary binds
    // looser than any binary op.
    if matches!(expr, Expr::Ternary { .. }) {
        out.push('(');
        write_expr(out, expr);
        out.push(')');
        return;
    }
    write_expr(out, expr);
}

/// A ternary operand wraps if it's a nested ternary in the cond or
/// then position (else is right-associative and safe bare). Binary
/// operands are fine bare because `?` and `:` don't bind inside any
/// binary expression the parser recognises.
fn write_ternary_operand(out: &mut String, expr: &Expr) {
    if matches!(expr, Expr::Ternary { .. }) {
        out.push('(');
        write_expr(out, expr);
        out.push(')');
    } else {
        write_expr(out, expr);
    }
}

/// The receiver of a postfix form (`.field`, `.method(...)`, `[idx]`)
/// needs parens when the underlying expression doesn't self-close on
/// its right edge. Bare names, calls, field accesses, indexes, and
/// casts all end in an identifier or `)`/`]`, so they need no parens.
fn write_postfix_recv(out: &mut String, expr: &Expr) {
    if needs_postfix_parens(expr) {
        out.push('(');
        write_expr(out, expr);
        out.push(')');
    } else {
        write_expr(out, expr);
    }
}

fn needs_postfix_parens(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Binary { .. } | Expr::Unary { .. } | Expr::Ternary { .. } | Expr::Select { .. }
    )
}

/// A unary operand wraps when its shape would otherwise re-bind. A
/// binary or ternary must be parenthesized, everything else is fine
/// bare because the parser's unary applies tightly to the next
/// postfix form.
fn needs_unary_parens(expr: &Expr) -> bool {
    matches!(expr, Expr::Binary { .. } | Expr::Ternary { .. })
}

/// Binary operator precedence mirror of the parser's climb. Higher
/// value binds tighter. Unknown ops default to the loosest tier so
/// round-trip remains safe even for ops the parser doesn't recognise.
fn binary_prec(op: &str) -> u8 {
    match op {
        "||" => 1,
        "&&" => 2,
        "|" => 3,
        "^" => 4,
        "&" => 5,
        "==" | "!=" => 6,
        "<" | "<=" | ">" | ">=" => 7,
        "<<" | ">>" => 8,
        "+" | "-" => 9,
        "*" | "/" | "%" => 10,
        _ => 1,
    }
}

/// If `ty` is `kind<inner_ty>`, return `(kind, inner_ty)`. The parser
/// packs non-default cast kinds into `Cast.ty` as `kind<ty>` so the
/// printer can unpack them here for byte-equal round-trip. Balanced
/// angle-bracket scanning mirrors the parser's cast parser.
fn split_packed_cast_kind(ty: &str) -> Option<(&str, &str)> {
    let lt = ty.find('<')?;
    if !ty.ends_with('>') {
        return None;
    }
    let kind = &ty[..lt];
    if kind.is_empty() || !kind.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }
    let inner = &ty[lt + 1..ty.len() - 1];
    Some((kind, inner))
}

#[cfg(test)]
mod tests {
    use super::super::parse::{parse_expr, parse_stmt};
    use super::*;

    fn roundtrip(input: &str) {
        let parsed = parse_expr(input);
        let printed = fmt_expr(&parsed);
        let reparsed = parse_expr(&printed);
        assert_eq!(
            parsed, reparsed,
            "parse-print-parse diverged:\ninput:   {input}\nprinted: {printed}"
        );
    }

    #[test]
    fn roundtrip_identifiers_and_literals() {
        for input in [
            "42",
            "3.14",
            "\"hello\"",
            "'Foo'",
            "Self",
            "$Tmp_1",
            "true",
            "false",
        ] {
            roundtrip(input);
        }
    }

    #[test]
    fn roundtrip_calls() {
        roundtrip("GetThing(a, b)");
        roundtrip("Add(Mul(a, b), c)");
        roundtrip("NoArgs()");
    }

    #[test]
    fn roundtrip_field_access() {
        roundtrip("self.VRMovementReference.MovementMode");
    }

    #[test]
    fn roundtrip_method_chains() {
        roundtrip("a.b.c()");
        roundtrip("obj.Field.Method(arg)");
        roundtrip("KismetMathLibrary.VSize(v)");
    }

    #[test]
    fn roundtrip_index() {
        roundtrip("arr[idx]");
        roundtrip("arr[i + 1]");
    }

    #[test]
    fn roundtrip_cast() {
        roundtrip("icast<Interactable_BI_C>(GetThing())");
    }

    #[test]
    fn roundtrip_binary() {
        roundtrip("a + b");
        roundtrip("a + b * c");
        roundtrip("(a + b) * c");
        roundtrip("a - b - c");
        roundtrip("a && b || c");
        roundtrip("a == b");
        roundtrip("a <= b");
    }

    #[test]
    fn roundtrip_unary() {
        roundtrip("!x");
        roundtrip("!(a && b)");
        roundtrip("~x");
    }

    #[test]
    fn roundtrip_ternary() {
        roundtrip("cond ? a : b");
        roundtrip("a ? b : c ? d : e");
    }

    #[test]
    fn roundtrip_switch() {
        roundtrip("switch(x) { 0: a, 1: b, _: c }");
        roundtrip("switch(idx) { 0: a, 1: b }");
    }

    #[test]
    fn roundtrip_garbage_inputs_stay_unknown() {
        for input in [
            "",
            "(",
            "a b c",
            "a + ",
            ")",
            "a ? b",
            "switch(x) {",
            "icast<Foo(",
        ] {
            // Parse garbage, then ensure fmt_expr + reparse gives the
            // same `Unknown(...)` tree back.
            roundtrip(input);
        }
    }

    #[test]
    fn shape_bare_call() {
        assert_eq!(
            fmt_expr(&Expr::Call {
                name: "Foo".into(),
                args: vec![Expr::Literal("1".into())]
            }),
            "Foo(1)"
        );
    }

    #[test]
    fn shape_var_and_literal() {
        assert_eq!(fmt_expr(&Expr::Var("x".into())), "x");
        assert_eq!(fmt_expr(&Expr::Literal("42".into())), "42");
    }

    #[test]
    fn shape_binary_no_extra_parens() {
        assert_eq!(
            fmt_expr(&Expr::Binary {
                op: "+".into(),
                lhs: Box::new(Expr::Var("a".into())),
                rhs: Box::new(Expr::Binary {
                    op: "*".into(),
                    lhs: Box::new(Expr::Var("b".into())),
                    rhs: Box::new(Expr::Var("c".into())),
                }),
            }),
            "a + b * c"
        );
    }

    #[test]
    fn shape_binary_wraps_lower_prec_on_left() {
        assert_eq!(
            fmt_expr(&Expr::Binary {
                op: "*".into(),
                lhs: Box::new(Expr::Binary {
                    op: "+".into(),
                    lhs: Box::new(Expr::Var("a".into())),
                    rhs: Box::new(Expr::Var("b".into())),
                }),
                rhs: Box::new(Expr::Var("c".into())),
            }),
            "(a + b) * c"
        );
    }

    #[test]
    fn shape_icast() {
        assert_eq!(
            fmt_expr(&Expr::Cast {
                ty: "Foo".into(),
                inner: Box::new(Expr::Var("x".into())),
            }),
            "icast<Foo>(x)"
        );
    }

    #[test]
    fn shape_method_call() {
        assert_eq!(
            fmt_expr(&Expr::MethodCall {
                recv: Box::new(Expr::Var("obj".into())),
                name: "Do".into(),
                args: vec![Expr::Var("x".into())],
            }),
            "obj.Do(x)"
        );
    }

    /// Byte-equality probe: handpicked parser-test inputs that must
    /// parse-print byte-identical. A separate divergent set documents
    /// shapes where parse-print normalises output (paren elision,
    /// whitespace) without changing the tree.
    #[test]
    fn byte_equality_probe() {
        let expected_equal = [
            "42",
            "3.14",
            "\"hello\"",
            "'Foo'",
            "Self",
            "arr[idx]",
            "GetThing(a, b)",
            "a.b.c()",
            "obj.Field.Method(arg)",
            "KismetMathLibrary.VSize(v)",
            "icast<Interactable_BI_C>(GetThing())",
            "a + b",
            "a + b * c",
            "!x",
            "cond ? a : b",
            "switch(idx) { 0: a, 1: b }",
            "switch(x) { 0: a, 1: b, _: c }",
            "a - b - c",
        ];
        for input in expected_equal {
            let printed = fmt_expr(&parse_expr(input));
            assert_eq!(printed, input, "byte-equal probe failed for {input:?}");
        }

        // Known divergences. Each parses cleanly and is
        // round-trip-idempotent, but the printed form normalises
        // whitespace or redundant parens so byte equality fails.
        let divergent_inputs = [
            // Redundant parens collapse: `((a))` prints as `a`.
            "((a))", // Outer-paren stripping on literals: `(42)` prints as `42`.
            "(42)",
        ];
        for input in divergent_inputs {
            let parsed = parse_expr(input);
            let printed = fmt_expr(&parsed);
            let reparsed = parse_expr(&printed);
            assert_eq!(
                parsed, reparsed,
                "divergent input {input:?} must still round-trip idempotently"
            );
            // Not asserting byte equality on purpose.
            let _ = printed;
        }
    }

    fn roundtrip_stmt(stmt: Stmt) {
        let printed = fmt_stmt(&stmt);
        let reparsed = parse_stmt(&printed);
        assert_eq!(
            stmt, reparsed,
            "stmt parse-print-parse diverged:\nprinted: {printed}"
        );
    }

    #[test]
    fn stmt_roundtrip_pop_flow() {
        roundtrip_stmt(Stmt::PopFlow);
    }

    #[test]
    fn stmt_roundtrip_pop_flow_if_not() {
        roundtrip_stmt(Stmt::PopFlowIfNot {
            cond: Expr::Var("x".into()),
        });
    }

    #[test]
    fn stmt_roundtrip_push_flow() {
        roundtrip_stmt(Stmt::PushFlow { target: 0x1234 });
    }

    #[test]
    fn stmt_roundtrip_continue_if_not() {
        roundtrip_stmt(Stmt::ContinueIfNot {
            cond: Expr::Binary {
                op: "==".into(),
                lhs: Box::new(Expr::Var("a".into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
        });
    }

    #[test]
    fn stmt_roundtrip_if_jump() {
        roundtrip_stmt(Stmt::IfJump {
            cond: Expr::Var("cond".into()),
            target: 0x20,
        });
    }

    #[test]
    fn stmt_roundtrip_jump() {
        roundtrip_stmt(Stmt::Jump { target: 0x40 });
    }

    #[test]
    fn stmt_roundtrip_jump_computed() {
        roundtrip_stmt(Stmt::JumpComputed {
            expr: Expr::Var("idx".into()),
        });
    }

    #[test]
    fn stmt_roundtrip_return_nop() {
        roundtrip_stmt(Stmt::ReturnNop);
    }

    #[test]
    fn stmt_roundtrip_bare_return() {
        roundtrip_stmt(Stmt::BareReturn);
    }

    #[test]
    fn stmt_roundtrip_assignment() {
        roundtrip_stmt(Stmt::Assignment {
            lhs: Expr::Var("x".into()),
            rhs: Expr::Call {
                name: "Foo".into(),
                args: vec![Expr::Literal("1".into())],
            },
        });
    }

    #[test]
    fn stmt_roundtrip_compound_assign() {
        roundtrip_stmt(Stmt::CompoundAssign {
            op: "+=".into(),
            lhs: Expr::FieldAccess {
                recv: Box::new(Expr::Var("obj".into())),
                field: "OnEvent_Bind".into(),
            },
            rhs: Expr::Var("$Delegate".into()),
        });
        roundtrip_stmt(Stmt::CompoundAssign {
            op: "-=".into(),
            lhs: Expr::Var("x".into()),
            rhs: Expr::Var("y".into()),
        });
    }

    #[test]
    fn stmt_roundtrip_call() {
        roundtrip_stmt(Stmt::Call {
            expr: Expr::Call {
                name: "DoThing".into(),
                args: vec![Expr::Var("arg".into())],
            },
        });
    }

    #[test]
    fn stmt_roundtrip_unknown() {
        // `L_1234:` has no typed variant yet and must round-trip as
        // Unknown. `} else {` landed in 5d.11b as `Stmt::Else`, see
        // `stmt_roundtrip_else` below.
        roundtrip_stmt(Stmt::Unknown("L_1234:".to_owned()));
    }

    #[test]
    fn stmt_roundtrip_if_open() {
        roundtrip_stmt(Stmt::IfOpen {
            cond: Expr::Var("cond".into()),
        });
        roundtrip_stmt(Stmt::IfOpen {
            cond: Expr::Binary {
                op: "&&".into(),
                lhs: Box::new(Expr::Var("a".into())),
                rhs: Box::new(Expr::Var("b".into())),
            },
        });
    }

    #[test]
    fn stmt_roundtrip_else() {
        roundtrip_stmt(Stmt::Else);
    }

    #[test]
    fn stmt_roundtrip_comment() {
        roundtrip_stmt(Stmt::Comment("// comment".to_owned()));
        roundtrip_stmt(Stmt::Comment("// with $symbols and punctuation".to_owned()));
    }

    #[test]
    fn stmt_roundtrip_block_close() {
        roundtrip_stmt(Stmt::BlockClose);
    }

    #[test]
    fn stmt_roundtrip_break() {
        roundtrip_stmt(Stmt::Break);
    }

    #[test]
    fn stmt_parse_never_panics_on_garbage() {
        for input in [
            "",
            "  ",
            "pop_flow_if_not(",
            "if !(x) jump ",
            "{",
            "L_1234:",
            "for (x in xs) {",
        ] {
            let parsed = parse_stmt(input);
            // No input above matches a valid variant; every case should
            // fall through to Unknown and preserve the raw input.
            assert_eq!(
                parsed,
                Stmt::Unknown(input.to_owned()),
                "expected Unknown for input {input:?}, got {parsed:?}"
            );
        }
    }

    #[test]
    fn stmt_unknown_roundtrip_is_verbatim() {
        // `} else {` is now `Stmt::Else`, check it still prints as the
        // exact source line byte-for-byte.
        assert_eq!(fmt_stmt(&parse_stmt("} else {")), "} else {");
        assert_eq!(fmt_stmt(&parse_stmt("")), "");
    }
}
