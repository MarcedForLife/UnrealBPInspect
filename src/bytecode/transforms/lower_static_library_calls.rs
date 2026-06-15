//! Lower static-library `MethodCall` expressions to canonical `Call`.
//!
//! Blueprint static-library functions (KismetArrayLibrary.Array_Length,
//! KismetMathLibrary.Add_IntInt, etc.) decode through `EX_CONTEXT` as
//! `Expr::MethodCall { recv: Literal("KismetArrayLibrary"), name, args }`.
//! Downstream matchers expect the canonical free-function shape
//! `Expr::Call { name, args }`, instance-method calls keep the
//! `MethodCall` shape because the receiver carries semantic information.
//!
//! The pass walks the tree post-order and rewrites only when the
//! receiver is a `Literal` matching one of the recognised static-library
//! class names. The list is data-driven, extending it is one entry.
//!
//! Pipeline position: runs right after `lower_binary_ops`, before
//! recognition (`refine_loops`, `latch_recognition`, `cascade_fold`)
//! and before `inline_single_use_temps`. This keeps the canonical-shape
//! invariant (each static-library call surfaces as a `Call`) intact for
//! every later pass.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{walk_body_exprs_mut_visit_lhs, Action};

/// Class names recognised as static-library receivers. A `MethodCall`
/// whose receiver is `Expr::Literal(name)` for any of these collapses
/// to a free `Call`.
pub(crate) const STATIC_LIBRARY_CLASSES: &[&str] = &[
    "KismetArrayLibrary",
    "KismetMathLibrary",
    "KismetStringLibrary",
    "KismetSystemLibrary",
    "KismetTextLibrary",
    "KismetGuidLibrary",
    "KismetMaterialLibrary",
    "KismetInputLibrary",
    "KismetRenderingLibrary",
    "GameplayStatics",
];

/// True when `expr` is a `Literal(name)` whose name appears in the
/// static-library class list. Shared with `decode_call` so the
/// statement-level decoder produces the canonical free-function
/// shape directly, removing the need for downstream rewrites.
pub(crate) fn is_static_library_class_literal(expr: &Expr) -> bool {
    is_static_library_receiver(expr)
}

/// Rewrite all static-library `MethodCall`s in `body` to canonical `Call` shape.
///
/// Drives the shared lhs-visiting expr walker. Pre-order is equivalent to
/// the former post-order: a rewritten `Call` is never a valid static-library
/// receiver (that test matches a `Literal` class name, which lowering never
/// touches), so the order in which inner and outer nodes lower cannot change
/// which ones match.
pub fn lower_static_library_calls(body: &mut [Stmt]) {
    walk_body_exprs_mut_visit_lhs(body, &mut |node| {
        if let Expr::MethodCall { recv, name, args } = node {
            if is_static_library_receiver(recv) {
                let function_name = std::mem::take(name);
                let function_args = std::mem::take(args);
                *node = Expr::Call {
                    name: function_name,
                    args: function_args,
                };
            }
        }
        Action::Continue
    });
}

/// True when `expr` is `Expr::Literal(name)` for a recognised static-library class.
fn is_static_library_receiver(expr: &Expr) -> bool {
    let Expr::Literal(name) = expr else {
        return false;
    };
    STATIC_LIBRARY_CLASSES.iter().any(|cls| cls == name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{lit, var};

    fn assign(rhs: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: var("result"),
            rhs,
            offset: 0,
        }
    }

    fn assignment_rhs(body: &[Stmt]) -> &Expr {
        match &body[0] {
            Stmt::Assignment { rhs, .. } => rhs,
            _ => panic!("expected Assignment as first statement"),
        }
    }

    #[test]
    fn static_library_method_call_lowers_to_call() {
        let method = Expr::MethodCall {
            recv: Box::new(lit("KismetArrayLibrary")),
            name: "Array_Length".into(),
            args: vec![var("arr")],
        };
        let mut body = vec![assign(method)];
        lower_static_library_calls(&mut body);
        match assignment_rhs(&body) {
            Expr::Call { name, args } => {
                assert_eq!(name, "Array_Length");
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn instance_method_call_unchanged() {
        let method = Expr::MethodCall {
            recv: Box::new(var("self_obj")),
            name: "Foo".into(),
            args: vec![var("a")],
        };
        let mut body = vec![assign(method)];
        lower_static_library_calls(&mut body);
        match assignment_rhs(&body) {
            Expr::MethodCall { name, .. } => assert_eq!(name, "Foo"),
            other => panic!("expected unchanged MethodCall, got {other:?}"),
        }
    }

    #[test]
    fn nested_method_call_inside_call_args_lowers() {
        // outer_call(KismetArrayLibrary.Array_Length(arr))
        let inner = Expr::MethodCall {
            recv: Box::new(lit("KismetArrayLibrary")),
            name: "Array_Length".into(),
            args: vec![var("arr")],
        };
        let outer = Expr::Call {
            name: "Outer".into(),
            args: vec![inner],
        };
        let mut body = vec![assign(outer)];
        lower_static_library_calls(&mut body);
        match assignment_rhs(&body) {
            Expr::Call { name, args } => {
                assert_eq!(name, "Outer");
                match &args[0] {
                    Expr::Call { name, .. } => assert_eq!(name, "Array_Length"),
                    other => panic!("expected nested Call, got {other:?}"),
                }
            }
            other => panic!("expected outer Call, got {other:?}"),
        }
    }

    #[test]
    fn math_library_lowers() {
        let method = Expr::MethodCall {
            recv: Box::new(lit("KismetMathLibrary")),
            name: "Add_IntInt".into(),
            args: vec![var("x"), var("y")],
        };
        let mut body = vec![assign(method)];
        lower_static_library_calls(&mut body);
        assert!(matches!(assignment_rhs(&body), Expr::Call { .. }));
    }

    #[test]
    fn unknown_class_literal_unchanged() {
        let method = Expr::MethodCall {
            recv: Box::new(lit("SomeRandomClass")),
            name: "Foo".into(),
            args: vec![],
        };
        let mut body = vec![assign(method)];
        lower_static_library_calls(&mut body);
        assert!(matches!(assignment_rhs(&body), Expr::MethodCall { .. }));
    }

    #[test]
    fn lowering_recurses_into_branch() {
        let method = Expr::MethodCall {
            recv: Box::new(lit("KismetArrayLibrary")),
            name: "Array_Length".into(),
            args: vec![var("arr")],
        };
        let branch = Stmt::Branch {
            cond: Expr::Literal("true".into()),
            then_body: vec![assign(method)],
            else_body: vec![],
            offset: 0,
        };
        let mut body = vec![branch];
        lower_static_library_calls(&mut body);
        match &body[0] {
            Stmt::Branch { then_body, .. } => {
                assert!(matches!(assignment_rhs(then_body), Expr::Call { .. }));
            }
            _ => panic!("expected Branch"),
        }
    }
}
