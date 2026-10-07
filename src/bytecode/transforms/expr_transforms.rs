//! Adjacent temporary substitution with preserved evaluation order.

use std::collections::BTreeMap;

use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::name_shape::is_compiler_temp_name;
use crate::bytecode::transforms::var_refs::{collect_loop_items, count_all_var_uses, Defs};
use crate::bytecode::transforms::visit::{any_expr, walk_stmt_children_mut};

const MAX_INLINE_ITERATIONS: usize = 16;

/// Substitute a uniquely defined, single-use temporary into the immediately
/// following statement's first evaluated operand. Counts cover the whole
/// function, including assignment receivers, out arguments and loop items.
/// Nested bodies can simplify locally but never exchange evaluations.
pub fn inline_single_use_temps(body: &mut Vec<Stmt>) {
    for _ in 0..MAX_INLINE_ITERATIONS {
        let mut references = count_all_var_uses(body, Defs::VisitLhs);
        collect_loop_items(body, &mut references);
        if !inline_at_scope(body, &references) {
            return;
        }
    }
}

fn inline_at_scope(body: &mut Vec<Stmt>, references: &BTreeMap<String, usize>) -> bool {
    let mut changed = false;
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut |children| {
            changed |= inline_at_scope(children, references);
        });
    }
    for assign_idx in (0..body.len().saturating_sub(1)).rev() {
        let (name, replacement) = match &body[assign_idx] {
            Stmt::Assignment {
                lhs: Expr::Var(name),
                rhs,
                ..
            } if is_inline_candidate_name(name)
                && references.get(name) == Some(&2)
                && !any_expr(rhs, &mut |expr| {
                    matches!(
                        expr,
                        Expr::Out(_)
                            | Expr::Persistent(_)
                            | Expr::Resume { .. }
                            | Expr::Interface(_)
                            | Expr::Unknown { .. }
                    )
                }) =>
            {
                (name.clone(), rhs.clone())
            }
            _ => continue,
        };
        if substitute_var_in_stmt(&mut body[assign_idx + 1], &name, &replacement) {
            crate::bytecode::body_origins::BodyOrigins::record(
                body[assign_idx].offset(),
                body[assign_idx + 1].offset(),
            );
            body.remove(assign_idx);
            changed = true;
        }
    }
    changed
}

fn substitute_var_in_stmt(stmt: &mut Stmt, name: &str, replacement: &Expr) -> bool {
    match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(_),
            rhs,
            ..
        }
        | Stmt::Return {
            value: Some(rhs), ..
        }
        | Stmt::Branch { cond: rhs, .. }
        | Stmt::Switch { expr: rhs, .. } => substitute_var_in_expr(rhs, name, replacement),
        Stmt::Call { func, args, .. } => {
            if matches!(func, Expr::Var(handle) if handle == name) {
                *func = replacement.clone();
                return true;
            }
            // A plain function symbol has no receiver evaluation. Bound or
            // computed call targets must keep their evaluation before arguments.
            if !matches!(func, Expr::Var(symbol)
                if !symbol.contains('.') && !is_compiler_temp_name(symbol))
            {
                return false;
            }
            substitute_var_in_operands(args.iter_mut(), name, replacement)
        }
        // A loop condition executes repeatedly, unlike a preceding assignment.
        _ => false,
    }
}

fn substitute_var_in_operands<'expr>(
    operands: impl IntoIterator<Item = &'expr mut Expr>,
    name: &str,
    replacement: &Expr,
) -> bool {
    for operand in operands {
        if substitute_var_in_expr(operand, name, replacement) {
            return true;
        }
        if !matches!(operand, Expr::Literal(_)) {
            return false;
        }
    }
    false
}

/// Only literals may precede the replacement. This preserves calls before
/// reads as well as before other calls, without assuming any callee is pure.
fn substitute_var_in_expr(expr: &mut Expr, name: &str, replacement: &Expr) -> bool {
    match expr {
        Expr::Var(other) if other == name => {
            *expr = replacement.clone();
            true
        }
        Expr::Call { args, .. } | Expr::ArrayLit(args) => {
            substitute_var_in_operands(args.iter_mut(), name, replacement)
        }
        Expr::MethodCall { recv, .. } | Expr::FieldAccess { recv, .. } => {
            substitute_var_in_expr(recv, name, replacement)
        }
        Expr::Unary { operand, .. } | Expr::Cast { inner: operand, .. } => {
            substitute_var_in_expr(operand, name, replacement)
        }
        Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            lhs,
            ..
        } => substitute_var_in_expr(lhs, name, replacement),
        Expr::Binary { lhs, rhs, .. }
        | Expr::Index {
            recv: lhs,
            idx: rhs,
        } => substitute_var_in_operands([lhs.as_mut(), rhs.as_mut()], name, replacement),
        Expr::Ternary { cond, .. } => substitute_var_in_expr(cond, name, replacement),
        Expr::Switch { index, .. } => substitute_var_in_expr(index, name, replacement),
        Expr::StructConstruct { fields, .. } => {
            substitute_var_in_operands(fields.iter_mut().map(|(_, value)| value), name, replacement)
        }
        _ => false,
    }
}

fn is_inline_candidate_name(name: &str) -> bool {
    !matches!(name, "Self" | "None") && !name.contains('.') && is_compiler_temp_name(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::LiteralValue;
    use crate::bytecode::expr::{BinaryOp, Expr};
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign, lit, var};

    fn make_call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            name: name.to_string(),
            args,
        }
    }

    fn call_stmt(func_name: &str, args: Vec<Expr>) -> Stmt {
        Stmt::Call {
            func: Expr::Var(func_name.to_string()),
            args,
            offset: 0,
        }
    }

    #[test]
    fn single_use_temp_inlines() {
        // Tmp_3 = Foo(); Bar(Tmp_3)  =>  Bar(Foo())
        let mut body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        match &body[0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], make_call("Foo", vec![]));
            }
            _ => panic!("expected Call statement after inlining"),
        }
    }

    #[test]
    fn multi_use_temp_does_not_inline() {
        // Tmp_3 = Foo(); Bar(Tmp_3); Baz(Tmp_3)  =>  unchanged
        let mut body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
            call_stmt("Baz", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(
            body.len(),
            original_len,
            "multi-use temp must not be inlined"
        );
    }

    #[test]
    fn chain_inlines_to_fixed_point() {
        // Temp_a = 1; Temp_b = Temp_a; Bar(Temp_b)  =>  Bar(1)
        // Temp_-prefixed so both names are compiler-temp-shaped under the
        // shared allow-list (`Tmp_` is not a recognised prefix).
        let mut body = vec![
            assign("Temp_a", lit("1")),
            assign("Temp_b", var("Temp_a")),
            call_stmt("Bar", vec![var("Temp_b")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        match &body[0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], lit("1"));
            }
            _ => panic!("expected Call statement after chain inlining"),
        }
    }

    #[test]
    fn unknown_rhs_does_not_inline() {
        let unknown_expr = Expr::Unknown {
            reason: "test".into(),
            raw_bytes: vec![0xff],
            offset: 0,
        };
        let mut body = vec![
            assign("Tmp_3", unknown_expr),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), original_len, "Unknown rhs must not be inlined");
    }

    #[test]
    fn out_param_does_not_inline() {
        let mut body = vec![
            assign("Tmp_3", Expr::Out(Box::new(var("X")))),
            call_stmt("Foo", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), original_len, "Out rhs must not be inlined");
    }

    #[test]
    fn dotted_name_does_not_inline() {
        // Field writes render as Var("self.Field") (see decode/expr_decode.rs:286).
        // Inlining `self.Hunger = $FClamp` into `(self.Hunger + ...)` would drop
        // the observable field write and produce a self-referencing assignment.
        // Regression captured during the recursive-into-Sequence-pin landing.
        let mut body = vec![
            assign(
                "$Add",
                Expr::Binary {
                    op: BinaryOp::Add,
                    lhs: Box::new(var("self.Hunger")),
                    rhs: Box::new(lit("1")),
                },
            ),
            assign("$FClamp", make_call("FClamp", vec![var("$Add")])),
            assign("self.Hunger", var("$FClamp")),
        ];
        inline_single_use_temps(&mut body);
        // Field write must survive.
        let last = body.last().expect("non-empty body");
        let Stmt::Assignment { lhs, .. } = last else {
            panic!("expected trailing field write assignment");
        };
        assert!(
            matches!(lhs, Expr::Var(name) if name == "self.Hunger"),
            "field write self.Hunger must remain"
        );
    }

    #[test]
    fn sequence_pin_temps_inline() {
        // P2 unblock: temps defined inside a Sequence pin body should
        // inline like top-level temps within their pin scope.
        use crate::bytecode::stmt::Stmt;
        let pin_body = vec![
            assign("Tmp_3", make_call("Foo", vec![])),
            call_stmt("Bar", vec![var("Tmp_3")]),
        ];
        let mut body = vec![Stmt::Sequence {
            pins: vec![pin_body],
            offset: 0,
        }];
        inline_single_use_temps(&mut body);
        let Stmt::Sequence { pins, .. } = &body[0] else {
            panic!("expected Sequence");
        };
        assert_eq!(pins[0].len(), 1, "pin scope inlining should drop the temp");
        match &pins[0][0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args[0], make_call("Foo", vec![]));
            }
            _ => panic!("expected pin-body Call after inlining"),
        }
    }

    #[test]
    fn reassigned_temp_does_not_corrupt_lhs() {
        // Regression: `Temp_X = 0; Temp_X = counter` previously got
        // `count_var_uses(Temp_X) == 2` (both lhs hits), then qualified for
        // inlining and substituted `0` into the second lhs, producing
        // `0 = counter`. With lhs no longer counted as a use, the dead
        // first assignment has count 0 (never read), and the second has
        // count 0 too, so neither inlines.
        let mut body = vec![assign("Temp_X", lit("0")), assign("Temp_X", var("counter"))];
        inline_single_use_temps(&mut body);
        // Whatever the outcome, must NOT contain `0 = counter`.
        for stmt in &body {
            if let Stmt::Assignment { lhs, rhs, .. } = stmt {
                assert!(
                    !matches!((lhs, rhs), (Expr::Literal(LiteralValue::Text(literal)), Expr::Var(_)) if literal == "0"),
                    "must not produce literal-on-lhs corruption"
                );
            }
        }
    }

    fn field_access(recv_name: &str, field: &str) -> Expr {
        Expr::FieldAccess {
            recv: Box::new(var(recv_name)),
            field: field.to_string(),
        }
    }

    #[test]
    fn method_handle_single_use_inlines() {
        // $Play = self.Comp.Play; $Play(0.0)  =>  self.Comp.Play(0.0)
        let mut body = vec![
            assign("$Play", field_access("self.Comp", "Play")),
            call_stmt("$Play", vec![lit("0.0")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1, "binding should be dropped");
        let Stmt::Call { func, .. } = &body[0] else {
            panic!("expected Call");
        };
        assert_eq!(func, &field_access("self.Comp", "Play"));
    }

    #[test]
    fn method_handle_multiple_calls_preserve_captured_receiver() {
        let mut body = vec![
            assign("$Stop", field_access("self.Comp", "Stop")),
            call_stmt("$Stop", vec![]),
            call_stmt("$Stop", vec![]),
        ];
        let original = body.clone();
        inline_single_use_temps(&mut body);
        assert_eq!(
            serde_json::to_value(&body).unwrap(),
            serde_json::to_value(&original).unwrap()
        );
    }

    #[test]
    fn method_handle_value_use_inlined_only_by_single_use_path() {
        // An adjacent field value stays an argument when its binding is inlined.
        let mut body = vec![
            assign("$Ref", field_access("self.Obj", "Field")),
            call_stmt("Bar", vec![var("$Ref")]),
        ];
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Call { func, args, .. } = &body[0] else {
            panic!("expected Call");
        };
        // The outer call's func must remain `Var("Bar")` — the
        // method-handle pass should not have grabbed it.
        assert_eq!(func, &var("Bar"));
        assert_eq!(args[0], field_access("self.Obj", "Field"));
    }

    #[test]
    fn method_handle_branch_arms_preserve_captured_receiver() {
        let mut body = vec![
            assign("$Set", field_access("self.Move", "SetMode")),
            Stmt::Branch {
                cond: lit("true"),
                then_body: vec![call_stmt("$Set", vec![lit("true")])],
                else_body: vec![call_stmt("$Set", vec![lit("false")])],
                offset: 0,
            },
        ];
        let original = body.clone();
        inline_single_use_temps(&mut body);
        assert_eq!(
            serde_json::to_value(&body).unwrap(),
            serde_json::to_value(&original).unwrap()
        );
    }

    #[test]
    fn method_handle_rhs_with_non_var_recv_skipped() {
        // rhs is FieldAccess { recv: Call(...), .. } — a method-on-call.
        // The receiver Call has side effects, so inlining at multiple
        // sites would change evaluation count. Pass must skip.
        let rhs = Expr::FieldAccess {
            recv: Box::new(Expr::Call {
                name: "GetThing".to_string(),
                args: vec![],
            }),
            field: "DoIt".to_string(),
        };
        let mut body = vec![
            assign("$X", rhs),
            call_stmt("$X", vec![]),
            call_stmt("$X", vec![]),
        ];
        inline_single_use_temps(&mut body);
        // Binding must survive at index 0; the call-handle uses must
        // remain `Var("$X")` rather than the inlined FieldAccess.
        assert_eq!(body.len(), 3, "binding with side-effect recv must stay");
        let Stmt::Assignment { lhs, .. } = &body[0] else {
            panic!("expected Assignment at index 0");
        };
        assert_eq!(lhs, &var("$X"));
        for stmt in &body[1..] {
            let Stmt::Call { func, .. } = stmt else {
                panic!("expected Call");
            };
            assert_eq!(func, &var("$X"));
        }
    }

    #[test]
    fn iteration_cap_warns_does_not_panic() {
        // Construct a body where a temp is genuinely used twice so no
        // inlining happens — the pass should terminate cleanly at the
        // fixed-point check after the first no-change pass, never hitting
        // the cap. This test verifies the function doesn't panic on such
        // a body.
        let mut body = vec![
            assign(
                "Tmp_3",
                Expr::Binary {
                    op: BinaryOp::Add,
                    lhs: Box::new(lit("1")),
                    rhs: Box::new(lit("2")),
                },
            ),
            call_stmt("Bar", vec![var("Tmp_3"), var("Tmp_3")]),
        ];
        // Should return quickly (no change on first pass) and not panic.
        inline_single_use_temps(&mut body);
        assert_eq!(body.len(), 2);
    }
}
