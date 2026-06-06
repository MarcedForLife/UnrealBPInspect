//! Lower math-library calls to typed `Expr::Binary` nodes.
//!
//! Handles UE4/UE5 math function names like `Less_IntInt`, `Add_FloatFloat`,
//! `GreaterEqual_DoubleDouble`, `BooleanAND`, etc. Covers arithmetic
//! (Add, Sub, Mul, Div, Mod), comparison (Lt, Le, Gt, Ge, Eq, Ne), and logical
//! operators (And, Or, Xor). Only two-argument calls are lowered; any
//! other arity passes through unchanged.
//!
//! The pass runs before recognition (`refine_loops`, `latch_recognition`,
//! `cascade_fold`) so downstream matchers see typed `Expr::Binary` nodes
//! rather than opaque `Expr::Call` strings. The single-use temp inliner
//! runs after recognition.

use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{walk_body_exprs_mut_visit_lhs, Action};

/// Lower all math-library calls in `body` to `Expr::Binary` in place.
///
/// Drives the shared lhs-visiting expr walker rather than a hand-rolled
/// traversal. Pre-order visitation is equivalent to the former post-order
/// here: once a `Call` is rewritten to `Binary`, the walker descends into
/// the new node's operands, so a nested `Less_IntInt(Add_IntInt(a, 1), b)`
/// still fully lowers. The lhs-visiting variant keeps lowering calls that
/// sit inside an Assignment lhs (e.g. an index expression).
pub fn lower_binary_ops(body: &mut [Stmt]) {
    walk_body_exprs_mut_visit_lhs(body, &mut |node| {
        if let Expr::Call { name, args } = node {
            if args.len() == 2 {
                if let Some(op) = classify_binary_op(name) {
                    let mut drained = args.drain(..);
                    let lhs = drained.next().unwrap();
                    let rhs = drained.next().unwrap();
                    drop(drained);
                    *node = Expr::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    };
                }
            }
        }
        Action::Continue
    });
}

/// Static lookup table mapping name prefixes to `BinaryOp`.
///
/// Entries are checked via `name.starts_with(prefix)` so type-suffixed
/// variants (`Less_IntInt`, `Less_FloatFloat`, `Less_DoubleDouble`) all
/// hit the same arm. Longer prefixes are listed before shorter ones that
/// share a common root (`GreaterEqual` before `Greater`, `LessEqual`
/// before `Less`) to avoid short-circuit shadowing.
static BINARY_OP_TABLE: &[(&str, BinaryOp)] = &[
    // Arithmetic
    ("Add_", BinaryOp::Add),
    ("Subtract_", BinaryOp::Sub),
    ("Sub_", BinaryOp::Sub),
    ("Multiply_", BinaryOp::Mul),
    ("Mul_", BinaryOp::Mul),
    ("Divide_", BinaryOp::Div),
    ("Div_", BinaryOp::Div),
    ("Modulo_", BinaryOp::Mod),
    ("Mod_", BinaryOp::Mod),
    // Comparison — longer prefix variants listed before shorter
    ("LessEqual_", BinaryOp::Le),
    ("LessOrEqual_", BinaryOp::Le),
    ("Less_", BinaryOp::Lt),
    ("GreaterEqual_", BinaryOp::Ge),
    ("GreaterOrEqual_", BinaryOp::Ge),
    ("Greater_", BinaryOp::Gt),
    ("EqualEqual_", BinaryOp::Eq),
    ("Equal_", BinaryOp::Eq),
    ("NotEqual_", BinaryOp::Ne),
    // Logical — full names, no trailing underscore
    ("BooleanAND", BinaryOp::And),
    ("BooleanOR", BinaryOp::Or),
    ("BooleanXOR", BinaryOp::Xor),
];

fn classify_binary_op(name: &str) -> Option<BinaryOp> {
    for (prefix, op) in BINARY_OP_TABLE {
        if name.starts_with(prefix) {
            return Some(*op);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::{BinaryOp, Expr};
    use crate::bytecode::stmt::{Stmt, SwitchCase};
    use crate::bytecode::transforms::test_fixtures::var;

    fn call(name: &str, args: Vec<Expr>) -> Expr {
        Expr::Call {
            name: name.to_string(),
            args,
        }
    }

    fn assign(rhs: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: var("result"),
            rhs,
            offset: 0,
        }
    }

    fn expect_binary_op(rhs: &Expr) -> BinaryOp {
        match rhs {
            Expr::Binary { op, .. } => *op,
            other => panic!("expected Binary, got {other:?}"),
        }
    }

    fn expect_assignment_rhs(body: &[Stmt]) -> &Expr {
        match &body[0] {
            Stmt::Assignment { rhs, .. } => rhs,
            _ => panic!("expected Assignment as first statement"),
        }
    }

    #[test]
    fn lt_int_lowers_to_binary_lt() {
        let mut body = vec![assign(call("Less_IntInt", vec![var("a"), var("b")]))];
        lower_binary_ops(&mut body);
        assert_eq!(expect_binary_op(expect_assignment_rhs(&body)), BinaryOp::Lt);
    }

    #[test]
    fn add_int_lowers_to_binary_add() {
        let mut body = vec![assign(call("Add_IntInt", vec![var("x"), var("y")]))];
        lower_binary_ops(&mut body);
        assert_eq!(
            expect_binary_op(expect_assignment_rhs(&body)),
            BinaryOp::Add
        );
    }

    #[test]
    fn nested_calls_fully_lower() {
        // Less_IntInt(Add_IntInt(a, 1), b) => (a + 1) < b
        let inner = call("Add_IntInt", vec![var("a"), Expr::Literal("1".into())]);
        let outer = call("Less_IntInt", vec![inner, var("b")]);
        let mut body = vec![assign(outer)];
        lower_binary_ops(&mut body);
        match expect_assignment_rhs(&body) {
            Expr::Binary {
                op: BinaryOp::Lt,
                lhs,
                ..
            } => match lhs.as_ref() {
                Expr::Binary {
                    op: BinaryOp::Add, ..
                } => {}
                other => panic!("expected inner Add Binary, got {other:?}"),
            },
            other => panic!("expected outer Lt Binary, got {other:?}"),
        }
    }

    #[test]
    fn boolean_and_lowers() {
        let mut body = vec![assign(call("BooleanAND", vec![var("a"), var("b")]))];
        lower_binary_ops(&mut body);
        assert_eq!(
            expect_binary_op(expect_assignment_rhs(&body)),
            BinaryOp::And
        );
    }

    #[test]
    fn non_math_call_unchanged() {
        let mut body = vec![assign(call("Array_Length", vec![var("arr")]))];
        lower_binary_ops(&mut body);
        match expect_assignment_rhs(&body) {
            Expr::Call { name, .. } => assert_eq!(name, "Array_Length"),
            other => panic!("expected unchanged Call, got {other:?}"),
        }
    }

    #[test]
    fn single_arg_call_not_lowered() {
        // One-argument math call must not be lowered.
        let mut body = vec![assign(call("Add_IntInt", vec![var("a")]))];
        lower_binary_ops(&mut body);
        match expect_assignment_rhs(&body) {
            Expr::Call { .. } => {} // still a Call
            other => panic!("expected unchanged Call, got {other:?}"),
        }
    }

    #[test]
    fn ge_float_lowers() {
        let mut body = vec![assign(call(
            "GreaterEqual_FloatFloat",
            vec![var("x"), var("y")],
        ))];
        lower_binary_ops(&mut body);
        assert_eq!(expect_binary_op(expect_assignment_rhs(&body)), BinaryOp::Ge);
    }

    #[test]
    fn lowering_recurses_into_branch() {
        let body_stmt = assign(call("Less_IntInt", vec![var("a"), var("b")]));
        let branch = Stmt::Branch {
            cond: call(
                "EqualEqual_IntInt",
                vec![var("x"), Expr::Literal("0".into())],
            ),
            then_body: vec![body_stmt],
            else_body: vec![],
            offset: 0,
        };
        let mut body = vec![branch];
        lower_binary_ops(&mut body);
        match &body[0] {
            Stmt::Branch {
                cond, then_body, ..
            } => {
                assert_eq!(expect_binary_op(cond), BinaryOp::Eq);
                assert_eq!(
                    expect_binary_op(expect_assignment_rhs(then_body)),
                    BinaryOp::Lt
                );
            }
            _ => panic!("expected Branch as first statement"),
        }
    }

    #[test]
    fn switch_case_bodies_lowered() {
        let switch = Stmt::Switch {
            expr: var("val"),
            cases: vec![SwitchCase {
                values: vec![Expr::Literal("1".into())],
                body: vec![assign(call("Add_IntInt", vec![var("a"), var("b")]))],
            }],
            default: None,
            offset: 0,
        };
        let mut body = vec![switch];
        lower_binary_ops(&mut body);
        match &body[0] {
            Stmt::Switch { cases, .. } => {
                assert_eq!(
                    expect_binary_op(expect_assignment_rhs(&cases[0].body)),
                    BinaryOp::Add
                );
            }
            _ => panic!("expected Switch as first statement"),
        }
    }
}
