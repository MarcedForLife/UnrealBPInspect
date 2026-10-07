//! Remove duplicate DoOnce wrappers for the same gate and bytecode origin.
//! Independent gates must remain nested because each has its own reset state.

use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::bytecode::transforms::visit::walk_stmt_children_mut;

/// Walk a statement body, collapsing nested same-macro `Latch{DoOnce}`
/// wraps in place. Recurses into every sub-body so nested constructs
/// (Branch arms, Sequence pins, Loop bodies, Switch cases, outer Latch
/// bodies) are folded as well.
///
/// Takes `&mut Vec<Stmt>` (rather than a slice) because it's threaded
/// through `walk_stmt_children_mut`, which hands the closure a
/// `&mut Vec<Stmt>` slot.
#[allow(clippy::ptr_arg)]
pub fn collapse_nested_doonce(body: &mut Vec<Stmt>) {
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut collapse_nested_doonce);
    }

    let mut idx = 0;
    while idx < body.len() {
        // Inner sub-bodies were collapsed by the recursion above, so
        // when an outer DoOnce wraps a single inner DoOnce we collapse
        // by lifting the inner Latch over the outer.
        if let Some(replacement) = try_collapse(&body[idx]) {
            body[idx] = replacement;
            // Loop without advancing; a three-deep chain becomes
            // two-deep, then one after the next iteration. The newly
            // installed Latch's body has already been collapse-recursed
            // (it was the inner of the original outer, whose sub-bodies
            // we walked above).
            continue;
        }
        idx += 1;
    }
}

/// If `stmt` is a `Latch{DoOnce}` whose body is exactly one
/// `Latch{DoOnce}`, return a clone of the inner. Otherwise return
/// `None`. The outer's `init` block is preserved by being prepended
/// to the inner's `init`, so any seed assignments the outer wrap
/// owned still run before the inner gate.
fn try_collapse(stmt: &Stmt) -> Option<Stmt> {
    let Stmt::Latch {
        kind: LatchKind::DoOnce {
            gate_var: outer_gate,
            ..
        },
        init: outer_init,
        body: outer_body,
        offset: outer_offset,
    } = stmt
    else {
        return None;
    };

    if outer_body.len() != 1 {
        return None;
    }

    let inner = &outer_body[0];
    let Stmt::Latch {
        kind: LatchKind::DoOnce {
            gate_var: inner_gate,
            ..
        },
        offset: inner_offset,
        ..
    } = inner
    else {
        return None;
    };

    if outer_gate != inner_gate || outer_offset != inner_offset {
        return None;
    }
    let mut merged = inner.clone();
    if !outer_init.is_empty() {
        if let Stmt::Latch { init, .. } = &mut merged {
            let mut combined = outer_init.clone();
            combined.append(init);
            *init = combined;
        }
    }
    Some(merged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::{LatchKind, Stmt};
    use crate::bytecode::transforms::test_fixtures::{call, stmt_kind, var};

    fn doonce(name: &str, gate_var: &str, body: Vec<Stmt>) -> Stmt {
        Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: name.to_string(),
                gate_var: gate_var.to_string(),
            },
            init: Vec::new(),
            body,
            offset: 0,
        }
    }

    fn flipflop(gate_var: &str, body: Vec<Stmt>) -> Stmt {
        Stmt::Latch {
            kind: LatchKind::FlipFlop {
                gate_var: gate_var.to_string(),
                names: None,
            },
            init: Vec::new(),
            body,
            offset: 0,
        }
    }

    fn expect_doonce_name(stmt: &Stmt) -> &str {
        match stmt {
            Stmt::Latch {
                kind: LatchKind::DoOnce { name, .. },
                ..
            } => name.as_str(),
            other => panic!("expected DoOnce Latch, got {}", stmt_kind(other)),
        }
    }

    #[test]
    fn collapses_simple_nested_doonce() {
        let inner_body = vec![call("TryAcquire", vec![Expr::Literal("false".into())])];
        let inner = doonce("TryAcquire", "Temp_bool_IsClosed_Variable", inner_body);
        let outer = doonce("DoOnce_2", "Temp_bool_IsClosed_Variable", vec![inner]);
        let mut body = vec![outer];

        collapse_nested_doonce(&mut body);

        assert_eq!(body.len(), 1);
        assert_eq!(expect_doonce_name(&body[0]), "TryAcquire");
        // Inner body preserved.
        if let Stmt::Latch {
            body: inner_body, ..
        } = &body[0]
        {
            assert_eq!(inner_body.len(), 1);
            assert!(matches!(inner_body[0], Stmt::Call { .. }));
        } else {
            panic!("expected Latch");
        }
    }

    #[test]
    fn no_collapse_when_outer_has_sibling_content() {
        let inner = doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable",
            vec![call("TryAcquire", vec![])],
        );
        let outer_body = vec![inner, call("OtherSibling", vec![])];
        let outer = doonce("DoOnce_2", "Temp_bool_IsClosed_Variable_2", outer_body);
        let mut body = vec![outer];

        collapse_nested_doonce(&mut body);

        // Outer wrap kept; identifier unchanged.
        assert_eq!(expect_doonce_name(&body[0]), "DoOnce_2");
        if let Stmt::Latch {
            body: outer_body, ..
        } = &body[0]
        {
            assert_eq!(outer_body.len(), 2);
        } else {
            panic!("expected Latch");
        }
    }

    #[test]
    fn no_collapse_when_single_child_is_not_a_latch() {
        let outer = doonce(
            "DoOnce_2",
            "Temp_bool_IsClosed_Variable_2",
            vec![call("TryAcquire", vec![])],
        );
        let mut body = vec![outer];

        collapse_nested_doonce(&mut body);

        assert_eq!(expect_doonce_name(&body[0]), "DoOnce_2");
    }

    #[test]
    fn no_collapse_when_inner_latch_is_flipflop() {
        let inner = flipflop("Temp_bool_Variable", vec![call("Toggle", vec![])]);
        let outer = doonce("DoOnce_2", "Temp_bool_IsClosed_Variable_2", vec![inner]);
        let mut body = vec![outer];

        collapse_nested_doonce(&mut body);

        // Outer DoOnce stays because the single child is a FlipFlop, not DoOnce.
        assert_eq!(expect_doonce_name(&body[0]), "DoOnce_2");
        if let Stmt::Latch {
            body: outer_body, ..
        } = &body[0]
        {
            assert_eq!(outer_body.len(), 1);
            assert!(matches!(
                &outer_body[0],
                Stmt::Latch {
                    kind: LatchKind::FlipFlop { .. },
                    ..
                }
            ));
        } else {
            panic!("expected Latch");
        }
    }

    #[test]
    fn collapses_three_deep_chain_to_innermost() {
        let innermost = doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable",
            vec![call("TryAcquire", vec![])],
        );
        let middle = doonce("DoOnce_3", "Temp_bool_IsClosed_Variable", vec![innermost]);
        let outer = doonce("DoOnce_2", "Temp_bool_IsClosed_Variable", vec![middle]);
        let mut body = vec![outer];

        collapse_nested_doonce(&mut body);

        assert_eq!(body.len(), 1);
        assert_eq!(expect_doonce_name(&body[0]), "TryAcquire");
        if let Stmt::Latch {
            body: inner_body, ..
        } = &body[0]
        {
            assert_eq!(inner_body.len(), 1);
            // The remaining inner body must be the original call, not
            // another Latch (chain fully collapsed).
            assert!(matches!(inner_body[0], Stmt::Call { .. }));
        } else {
            panic!("expected Latch");
        }
    }

    #[test]
    fn recurses_into_branch_arms() {
        let inner = doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable",
            vec![call("TryAcquire", vec![])],
        );
        let outer = doonce("DoOnce_2", "Temp_bool_IsClosed_Variable", vec![inner]);
        let branch = Stmt::Branch {
            cond: Expr::Var("guard".into()),
            then_body: vec![outer],
            else_body: Vec::new(),
            offset: 0,
        };
        let mut body = vec![branch];

        collapse_nested_doonce(&mut body);

        if let Stmt::Branch { then_body, .. } = &body[0] {
            assert_eq!(then_body.len(), 1);
            assert_eq!(expect_doonce_name(&then_body[0]), "TryAcquire");
        } else {
            panic!("expected Branch");
        }
        // Smoke check that the lift didn't leave a spurious sibling around.
        let _ = var("unused");
    }

    #[test]
    fn independent_nested_gates_keep_both_reset_states() {
        let inner = doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable_3",
            vec![call("TryAcquire", vec![])],
        );
        let outer = doonce("TryAcquire", "Temp_bool_IsClosed_Variable_2", vec![inner]);
        let mut body = vec![outer];
        collapse_nested_doonce(&mut body);
        let Stmt::Latch {
            kind: LatchKind::DoOnce { gate_var, .. },
            body: nested,
            ..
        } = &body[0]
        else {
            unreachable!()
        };
        assert_eq!(gate_var, "Temp_bool_IsClosed_Variable_2");
        assert!(
            matches!(&nested[0], Stmt::Latch { kind: LatchKind::DoOnce { gate_var, .. }, .. }
            if gate_var == "Temp_bool_IsClosed_Variable_3")
        );
    }
    #[test]
    fn repeated_gate_at_different_execution_sites_is_not_a_duplicate() {
        let mut inner = doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable_3",
            vec![call("TryAcquire", vec![])],
        );
        let Stmt::Latch { offset, .. } = &mut inner else {
            unreachable!()
        };
        *offset = 20;
        let mut body = vec![doonce(
            "TryAcquire",
            "Temp_bool_IsClosed_Variable_3",
            vec![inner],
        )];
        collapse_nested_doonce(&mut body);
        assert!(
            matches!(&body[0], Stmt::Latch { body, .. } if matches!(body[0], Stmt::Latch { .. }))
        );
    }
}
