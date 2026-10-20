//! Strip the trailing `MakeLatentActionInfo` argument from latent
//! function calls.
//!
//! Latent UFUNCTION calls in Blueprint (`Delay`, `LoadStreamLevel`,
//! project-defined latent functions, etc.) take a compiler-emitted
//! `FLatentActionInfo` struct as their final argument. The struct carries
//! the resume offset and the ubergraph function name, both of which are
//! internal plumbing the editor never shows. Without this pass the decoder
//! emits the full
//! `MakeLatentActionInfo(skip_offset(0xHEX), ..., 'ExecuteUbergraph_*', self)`
//! call expression verbatim, so this pass elides the wrapper before
//! rendering.
//!
//! The pass walks the statement tree, finds `Stmt::Call` and `Expr::Call`
//! and drops the trailing argument when it is a `MakeLatentActionInfo`
//! struct whose `Linkage` field is an `EX_SKIP_OFFSET_CONST` operand
//! (`skip_offset(..)`). The compiler only emits that opcode for the
//! linkage of a latent call, so the evidence comes from the bytecode
//! rather than the callee's name. Any other shape leaves the argument
//! untouched, including ordinary calls named like a latent function.
//!
//! Pipeline position: runs after `lower_static_library_calls` so the
//! function name is already in its canonical free-function form, and
//! before the recognisers and inliner so downstream passes see the
//! cleaner argument list.

use crate::bytecode::expr::{Expr, LiteralValue};
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::{rewrite_stmts_preorder, walk_body_exprs_mut, Action};

/// Name of the synthetic struct constructor the decoder emits for
/// `FLatentActionInfo` arguments.
const LATENT_INFO_STRUCT: &str = "MakeLatentActionInfo";

/// Literal prefix the expression decoder gives an `EX_SKIP_OFFSET_CONST`
/// operand.
const SKIP_OFFSET_PREFIX: &str = "skip_offset(";

/// Walk `body`, strip the trailing `MakeLatentActionInfo` arg from
/// every latent call (both `Stmt::Call` and nested `Expr::Call`), and
/// recurse through every nested body so latent calls inside branches,
/// sequences, loops, switches, and latches are covered.
pub fn strip_latent_action_info(body: &mut [Stmt]) {
    // Preorder; strip_in_stmt at each node also walks the node's own call
    // expressions. The order is irrelevant to output (try_strip_call is
    // idempotent: a re-walk finds no trailing MakeLatentActionInfo to drop).
    rewrite_stmts_preorder(body, &mut |stmt| strip_in_stmt(stmt));
}

/// Apply the strip to the call at the statement layer (`Stmt::Call`)
/// and to every nested call expression the statement owns. The
/// expression walker already skips `Assignment::lhs`, which is the
/// only place a Call shape is conceptually a definition rather than a
/// use.
fn strip_in_stmt(stmt: &mut Stmt) {
    if let Stmt::Call { args, .. } = stmt {
        try_strip_call(args);
    }
    walk_body_exprs_mut(std::slice::from_mut(stmt), &mut |expr: &mut Expr| {
        if let Expr::Call { args, .. } = expr {
            try_strip_call(args);
        }
        Action::Continue
    });
}

/// Drop the last element of `args` when it is a compiler-emitted latent
/// action info struct. Any other trailing argument leaves `args` untouched.
fn try_strip_call(args: &mut Vec<Expr>) {
    if args.last().is_some_and(is_latent_action_info) {
        args.pop();
    }
}

/// True for `MakeLatentActionInfo(skip_offset(..), ..)`. The linkage is
/// the struct's first field, and a `skip_offset` literal only comes from
/// the `EX_SKIP_OFFSET_CONST` opcode the compiler writes for it. A
/// `MakeLatentActionInfo` value built any other way is ordinary data.
fn is_latent_action_info(expr: &Expr) -> bool {
    let Expr::Call { name, args } = expr else {
        return false;
    };
    name == LATENT_INFO_STRUCT
        && matches!(
            args.first(),
            Some(Expr::Literal(LiteralValue::Text(linkage))) if linkage.starts_with(SKIP_OFFSET_PREFIX)
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::transforms::test_fixtures::{lit, var};

    fn lai_call() -> Expr {
        lai_with_linkage(lit("skip_offset(0xf)"))
    }

    fn lai_with_linkage(linkage: Expr) -> Expr {
        Expr::Call {
            name: "MakeLatentActionInfo".into(),
            args: vec![
                linkage,
                lit("-984220974"),
                lit("'ExecuteUbergraph_X'"),
                var("self"),
            ],
        }
    }

    fn stripped_arg_count(name: &str, args: Vec<Expr>) -> usize {
        let mut body = vec![stmt_call(name, args)];
        strip_latent_action_info(&mut body);
        match &body[0] {
            Stmt::Call { args, .. } => args.len(),
            _ => panic!("expected Stmt::Call"),
        }
    }

    fn stmt_call(name: &str, args: Vec<Expr>) -> Stmt {
        Stmt::Call {
            func: Expr::Var(name.into()),
            args,
            offset: 0,
        }
    }

    #[test]
    fn delay_strips_trailing_lai() {
        let mut body = vec![stmt_call(
            "Delay",
            vec![var("self"), lit("2.0000"), lai_call()],
        )];
        strip_latent_action_info(&mut body);
        match &body[0] {
            Stmt::Call { args, .. } => {
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], var("self"));
                assert_eq!(args[1], lit("2.0000"));
            }
            _ => panic!("expected Stmt::Call"),
        }
    }

    #[test]
    fn retriggerable_delay_strips() {
        let mut body = vec![stmt_call(
            "RetriggerableDelay",
            vec![var("self"), lit("0.5"), lai_call()],
        )];
        strip_latent_action_info(&mut body);
        if let Stmt::Call { args, .. } = &body[0] {
            assert_eq!(args.len(), 2);
        } else {
            panic!("expected Stmt::Call");
        }
    }

    #[test]
    fn move_component_to_strips() {
        let mut body = vec![stmt_call(
            "MoveComponentTo",
            vec![
                var("comp"),
                var("loc"),
                var("rot"),
                lit("false"),
                lit("true"),
                lit("1.0"),
                lit("false"),
                lit("0"),
                lai_call(),
            ],
        )];
        strip_latent_action_info(&mut body);
        if let Stmt::Call { args, .. } = &body[0] {
            assert_eq!(args.len(), 8);
        } else {
            panic!("expected Stmt::Call");
        }
    }

    #[test]
    fn unfamiliar_latent_name_strips() {
        // Engine and project latent functions are recognised by the
        // compiler-written linkage, not by a list of known names.
        for name in ["LoadStreamLevel", "WaitForProjectSignal"] {
            assert_eq!(
                stripped_arg_count(name, vec![var("self"), lit("1.0"), lai_call()]),
                2,
                "{name} must lose its latent action info"
            );
        }
    }

    #[test]
    fn no_continuation_sentinel_strips() {
        // An unwired Completed pin still compiles a skip-offset linkage, with
        // the -1 sentinel as its value.
        let lai = lai_with_linkage(lit("skip_offset(0xffffffff)"));
        assert_eq!(stripped_arg_count("Delay", vec![var("self"), lai]), 1);
    }

    #[test]
    fn latent_info_without_linkage_evidence_unchanged() {
        // A struct value built from ordinary data is a real argument, even
        // on a call that shares a latent function's name.
        for linkage in [lit("12"), var("Linkage"), lit("\"skip_offset(0x1)\"")] {
            assert_eq!(
                stripped_arg_count("Delay", vec![var("self"), lai_with_linkage(linkage)]),
                2
            );
        }
        let user_struct = Expr::Call {
            name: "MakeLatentActionInfo".into(),
            args: vec![],
        };
        assert_eq!(
            stripped_arg_count("Delay", vec![var("self"), user_struct]),
            2
        );
    }

    #[test]
    fn latent_info_before_last_arg_unchanged() {
        assert_eq!(
            stripped_arg_count("DrawDebugLine", vec![lai_call(), var("end")]),
            2
        );
    }

    #[test]
    fn delay_without_lai_unchanged() {
        // If the last arg isn't structurally a MakeLatentActionInfo Call,
        // don't strip. Defends against future shape changes.
        let mut body = vec![stmt_call(
            "Delay",
            vec![var("self"), lit("2.0"), var("custom_var")],
        )];
        strip_latent_action_info(&mut body);
        if let Stmt::Call { args, .. } = &body[0] {
            assert_eq!(args.len(), 3, "non-LAI tail must not be stripped");
        } else {
            panic!("expected Stmt::Call");
        }
    }

    #[test]
    fn set_timer_by_event_unchanged() {
        // SetTimerByEvent returns a TimerHandle, not a latent call;
        // explicitly check it's not on the list.
        let mut body = vec![stmt_call(
            "SetTimerByEvent",
            vec![var("self"), var("evt"), lit("1.0"), lit("false")],
        )];
        strip_latent_action_info(&mut body);
        if let Stmt::Call { args, .. } = &body[0] {
            assert_eq!(args.len(), 4);
        } else {
            panic!("expected Stmt::Call");
        }
    }

    #[test]
    fn nested_call_inside_branch_strips() {
        let inner = stmt_call("Delay", vec![var("self"), lit("0.1"), lai_call()]);
        let mut body = vec![Stmt::Branch {
            cond: lit("true"),
            then_body: vec![inner],
            else_body: vec![],
            offset: 0,
        }];
        strip_latent_action_info(&mut body);
        if let Stmt::Branch { then_body, .. } = &body[0] {
            if let Stmt::Call { args, .. } = &then_body[0] {
                assert_eq!(args.len(), 2);
            } else {
                panic!("expected nested Stmt::Call");
            }
        } else {
            panic!("expected Branch");
        }
    }

    #[test]
    fn delay_as_expr_inside_assignment_strips() {
        // If a latent call ever shows up at expression position (rhs of
        // an Assignment), the strip should still fire so the rendered
        // expression matches the canonical shape.
        let mut body = vec![Stmt::Assignment {
            lhs: var("x"),
            rhs: Expr::Call {
                name: "Delay".into(),
                args: vec![var("self"), lit("1.0"), lai_call()],
            },
            offset: 0,
        }];
        strip_latent_action_info(&mut body);
        if let Stmt::Assignment { rhs, .. } = &body[0] {
            if let Expr::Call { args, .. } = rhs {
                assert_eq!(args.len(), 2);
            } else {
                panic!("expected Expr::Call rhs");
            }
        } else {
            panic!("expected Assignment");
        }
    }
}
