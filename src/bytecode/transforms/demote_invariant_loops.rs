//! Demote `LoopKind::While` nodes whose condition is a single variable
//! that is never mutated inside the body to plain `Stmt::Branch` nodes.
//!
//! Some control-flow shapes (Sequence pins wrapping a Branch, DoOnce or
//! IsValid macros above a Branch) emit a back-edge in the bytecode that
//! `try_decode_loop` accepts as a While. The user-visible Blueprint
//! graph for those shapes is an `if`, not a `while`. A real `while`
//! always mutates its cond var inside the body, so an invariant cond is
//! a reliable falsifier.
//!
//! Today this pass runs after `inline_single_use_temps`, so genuine loops
//! with a probe-temp cond (`Var($Less_IntInt)`) have already been
//! rewritten to the underlying binary expression (`Counter < $Length`)
//! before the gate runs. If the inliner ever moves to post-recognition,
//! every `LoopKind::While` cond will reach this pass as `Var($probe)`
//! and a chain-aware mutation check is needed.
//!
//! Two gates run in order. The first classifies the cond chain's
//! terminal expression: comparison and logical `Binary` shapes
//! (`Lt`/`Le`/`Gt`/`Ge`/`Eq`/`Ne`/`And`/`Or`) are real iteration
//! conds by construction, their operands (counter, array length,
//! etc.) change between iterations even when the body never writes
//! the cond temp directly. The loop is preserved without consulting
//! body mutation. Other terminals (`Call` macros like IsValid, bare
//! `Var` with no def, `Literal`, `FieldAccess`) fall through to the
//! body-mutation gate.
//!
//! The body-mutation gate walks `Var($X)` through any number of
//! body-level temp aliases (`$X = $Y; $Y = i < n`) and treats EVERY
//! name visited along the chain as a candidate for the
//! body-mutation check. A real `while(i < n)` un-inlined has its
//! cond-temp definition sitting AT BODY HEAD (`$Less_IntInt = i < n`),
//! which Blueprint re-emits each iteration before the back-edge JUMP.
//! That definition is itself a body-level assignment to the cond
//! name, so the chain's first hop already lights up the mutation
//! check and the loop is preserved. Fake IsValid / Sequence-pin
//! wrappers don't write the cond name in body, so the chain
//! short-circuits with no mutation found and the demote fires.
//!
//! The terminal-shape gate covers the case where the body-mutation
//! gate misses: a `for (i = 0 to ...) { ... i = i + 1 }` whose cond
//! resolves to `Binary{Le, counter, length}` but whose body mutates
//! the counter directly without ever writing the cond temp's chain
//! names. The body-mutation walker has no path from `$cond` back to
//! the counter, so it would demote the loop incorrectly. Classifying
//! the terminal first short-circuits that case.
//!
//! Parent-body access isn't needed here. The IsValid recognizer
//! emits its `$IsValid_N = IsValid(...)` definition into the parent
//! body, which means the chain dead-ends inside the loop body's
//! scope. Today's gate already handles that case correctly because
//! the loop body never writes the cond name. The chain extension
//! only adds coverage for the body-head probe-rewrite shape that
//! genuine loops emit.

use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit::{
    resolve_var_chain, scope_stack, walk_bodies_with_ancestors_mut, walk_stmt_children_mut,
};

/// Walk `stmts` and demote any While whose cond is a bare `Expr::Var`
/// that is not assigned anywhere in the loop body.
pub fn demote_invariant_loops(stmts: &mut [Stmt]) {
    demote_in_body(stmts, &[]);
}

/// `ancestors` is innermost-first: each slice is the preceding-siblings
/// view at one outer nesting level. Alias lookups follow chains across
/// the full scope stack, the mutation check still scans only the loop
/// body (see `any_chain_name_is_assigned`).
fn demote_in_body(stmts: &mut [Stmt], ancestors: &[&[Stmt]]) {
    walk_bodies_with_ancestors_mut(stmts, ancestors, &mut |stmt, child_ancestors| {
        demote_in_stmt(stmt, child_ancestors);
    });
}

fn demote_in_stmt(stmt: &mut Stmt, ancestors: &[&[Stmt]]) {
    walk_stmt_children_mut(stmt, &mut |sub_body| demote_in_body(sub_body, ancestors));

    let Stmt::Loop {
        kind: LoopKind::While,
        cond: Some(cond_expr),
        body,
        completion: None,
        offset,
    } = stmt
    else {
        return;
    };

    let Expr::Var(cond_name) = cond_expr else {
        return;
    };
    // Belt-and-braces: an empty-body Loop should never reach this pass
    // (try_decode_loop rejects fully claim-owned bodies upstream). If
    // some other path ever produces one, demoting it would emit an
    // empty Branch, which is the bug we're trying to avoid.
    if body.is_empty() {
        return;
    }
    // Build the scope stack used for alias-chain hops: loop body
    // innermost, then the loop's ancestors. The mutation check itself
    // stays body-local (see helper docs).
    let scopes = scope_stack(body.as_slice(), ancestors);
    // Classify the chain's terminal expression. Comparison/logical Binary
    // shapes (Lt/Le/Gt/Ge/Eq/Ne/And/Or) are real iteration conds by
    // construction: their operands (counter, array length, etc.) change
    // between iterations even when the body never writes the cond temp
    // directly. Preserve the loop without consulting body mutation.
    // Other terminals (Call macros like IsValid, bare Var with no def,
    // Literal, FieldAccess) fall through to today's body-mutation gate.
    if let Some(terminal) = resolve_var_chain(&scopes, cond_name) {
        if is_iteration_cond_shape(terminal) {
            return;
        }
    }
    if any_chain_name_is_assigned(body, cond_name, &scopes) {
        return;
    }

    let cond_taken = std::mem::replace(cond_expr, Expr::Var(String::new()));
    let body_taken = std::mem::take(body);
    let head_offset = *offset;
    *stmt = Stmt::Branch {
        cond: cond_taken,
        then_body: body_taken,
        else_body: Vec::new(),
        offset: head_offset,
    };
}

/// Returns true when `terminal` is a comparison or logical Binary
/// shape that, by construction, can change between iterations even
/// when the loop body does not write the cond temp directly. Used
/// before the body-mutation gate to preserve genuine iteration
/// conds whose chain dead-ends in `Var($cond) -> Binary{Lt, counter,
/// ArrayLen}` and similar shapes.
///
/// Arithmetic Binary shapes (Add/Sub/Mul/Div/Mod) are NOT iteration
/// conds, they would produce a non-bool value that the surrounding
/// `JUMP_IF_NOT` could not consume. Bitwise shapes are excluded for
/// the same reason. Comparison + logical cover every legitimate cond
/// shape Blueprint emits as a `Binary` terminal.
fn is_iteration_cond_shape(terminal: &Expr) -> bool {
    match terminal {
        Expr::Binary { op, .. } => matches!(
            op,
            BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::And
                | BinaryOp::Or
        ),
        _ => false,
    }
}

/// Returns true when the cond name OR any temp alias the cond chain
/// passes through is mutated somewhere in `body`.
///
/// The walk follows `$X = $Y` Var-aliasing hops one step at a time,
/// checking `body_assigns_var` at every step before advancing. It
/// stops as soon as the chain dead-ends (the current name has no
/// top-level Var-aliasing assignment in any scope), reaches a non-`Var`
/// rhs (the terminal definition the inliner would eventually substitute
/// in), or finds a mutation. A `Vec<String>` of visited names guards
/// against cycles in the (rare) `$X = $Y; $Y = $X` shape.
///
/// Conceptually a chain-aware extension of `body_assigns_var(body,
/// cond_name)`. Where the original gate only checks the cond name
/// itself, this one ALSO checks every alias temp the cond would walk
/// through to reach its terminal definition. Sibling helper of
/// `transforms::visit::resolve_var_chain`, which returns the terminal
/// `&Expr`; here we need every hop's name, so the walk is open-coded.
///
/// `scopes` is innermost-first and used only for ALIAS lookup (finding
/// `name = Var(other)` defs). The mutation check still scans only the
/// loop body, not parent scopes, because:
/// - Genuine pre-inline loops emit the cond-temp definition AT BODY
///   HEAD (Blueprint re-evaluates the comparison each iteration), so a
///   real `while (i < n)` has its `$Less_IntInt = i < n` write inside
///   `body` and the gate keeps the loop.
/// - IsValid / Sequence-pin shapes that the decoder mis-classifies as
///   loops have their cond definition in a parent scope, but their
///   body never writes the cond name. Mutation in a parent scope would
///   be unrelated to the loop's iteration, so checking parent bodies
///   would only produce false positives.
fn any_chain_name_is_assigned(body: &[Stmt], cond_name: &str, scopes: &[&[Stmt]]) -> bool {
    let mut visited: Vec<String> = Vec::new();
    let mut current: String = cond_name.to_string();
    loop {
        if visited.iter().any(|name| name == &current) {
            return false;
        }
        if body_assigns_var(body, &current) {
            return true;
        }
        visited.push(current.clone());
        match find_var_alias_rhs(scopes, &current) {
            Some(next_name) => current = next_name,
            None => return false,
        }
    }
}

/// Search `scopes` (innermost-first) for the first top-level
/// `name = Var(other)` assignment and return `other`. Returns `None` for
/// non-Var rhs, missing definitions, or any deeper structural shape.
/// Top-level only, matching `resolve_var_chain`'s scope rule
/// (sub-body assignments are not consulted).
fn find_var_alias_rhs(scopes: &[&[Stmt]], name: &str) -> Option<String> {
    for scope in scopes {
        let hit = scope.iter().find_map(|stmt| match stmt {
            Stmt::Assignment {
                lhs: Expr::Var(lhs_name),
                rhs: Expr::Var(rhs_name),
                ..
            } if lhs_name == name => Some(rhs_name.clone()),
            _ => None,
        });
        if let Some(name_clone) = hit {
            return Some(name_clone);
        }
    }
    None
}

/// Recursive scan: returns `true` if any statement in `stmts` (or any
/// nested sub-body) is an assignment whose LHS resolves to `name`, or a
/// call whose argument list contains an `Out`-wrapped write to `name`.
fn body_assigns_var(stmts: &[Stmt], name: &str) -> bool {
    stmts.iter().any(|stmt| stmt_assigns_var(stmt, name))
}

fn stmt_assigns_var(stmt: &Stmt, name: &str) -> bool {
    match stmt {
        Stmt::Assignment { lhs, .. } => assignment_targets_var(lhs, name),
        Stmt::Call { args, .. } => args.iter().any(|arg| out_arg_targets_var(arg, name)),
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => body_assigns_var(then_body, name) || body_assigns_var(else_body, name),
        Stmt::Sequence { pins, .. } => pins.iter().any(|pin| body_assigns_var(pin, name)),
        Stmt::Loop {
            body, completion, ..
        } => {
            body_assigns_var(body, name)
                || completion
                    .as_deref()
                    .is_some_and(|c| body_assigns_var(c, name))
        }
        Stmt::Switch { cases, default, .. } => {
            cases.iter().any(|case| body_assigns_var(&case.body, name))
                || default
                    .as_deref()
                    .is_some_and(|d| body_assigns_var(d, name))
        }
        Stmt::Latch { init, body, .. } => {
            body_assigns_var(init, name) || body_assigns_var(body, name)
        }
        Stmt::Return { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => false,
    }
}

/// Match a bare `Var(name)` LHS. `FieldAccess` LHS shapes are not
/// matched, the rejector only fires on cond shapes that are also bare
/// `Var`, which never legitimately appear on a member-write LHS.
fn assignment_targets_var(lhs: &Expr, name: &str) -> bool {
    matches!(lhs, Expr::Var(lhs_name) if lhs_name == name)
}

/// Match an `Out(Var(name))` call argument. Models the call-site
/// mutation that `func(out $X)` performs on `$X`.
fn out_arg_targets_var(arg: &Expr, name: &str) -> bool {
    let Expr::Out(inner) = arg else {
        return false;
    };
    matches!(inner.as_ref(), Expr::Var(inner_name) if inner_name == name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::BinaryOp;

    fn make_while(cond: Expr, body: Vec<Stmt>) -> Stmt {
        Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(cond),
            body,
            completion: None,
            offset: 0x10,
        }
    }

    fn assign_var(name: &str) -> Stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name.into()),
            rhs: Expr::Literal("1".into()),
            offset: 0x20,
        }
    }

    fn call_with_args(args: Vec<Expr>) -> Stmt {
        Stmt::Call {
            func: Expr::Var("Foo".into()),
            args,
            offset: 0x30,
        }
    }

    /// Single-var cond, no body assignment to that var: rejector fires
    /// and the While becomes a Branch.
    #[test]
    fn flat_invariant_var_demotes_to_branch() {
        let cond = Expr::Var("$IsValid_2".into());
        let body = vec![Stmt::Call {
            func: Expr::Var("DoWork".into()),
            args: vec![],
            offset: 0x40,
        }];
        let mut stmts = vec![make_while(cond.clone(), body)];

        demote_invariant_loops(&mut stmts);

        let Stmt::Branch {
            cond: branch_cond,
            then_body,
            else_body,
            ..
        } = &stmts[0]
        else {
            panic!("expected Branch after demotion");
        };
        assert!(matches!(branch_cond, Expr::Var(name) if name == "$IsValid_2"));
        assert_eq!(then_body.len(), 1);
        assert!(else_body.is_empty());
    }

    /// Single-var cond with a flat body assignment to the cond var:
    /// rejector does NOT fire, the loop stays a While.
    #[test]
    fn flat_assignment_to_cond_var_keeps_loop() {
        let cond = Expr::Var("Counter".into());
        let body = vec![assign_var("Counter")];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Single-var cond with an assignment buried inside a nested branch
    /// body: rejector does NOT fire, the nested write counts.
    #[test]
    fn nested_branch_assignment_keeps_loop() {
        let cond = Expr::Var("Counter".into());
        let inner_branch = Stmt::Branch {
            cond: Expr::Literal("true".into()),
            then_body: vec![assign_var("Counter")],
            else_body: vec![],
            offset: 0x50,
        };
        let mut stmts = vec![make_while(cond, vec![inner_branch])];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Complex cond (binary op): rejector does NOT fire even when no
    /// body statement names the inner vars. Conservative gate keeps
    /// genuine `while (i < n)` shapes intact.
    #[test]
    fn complex_cond_skips_rejector() {
        let cond = Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var("Counter".into())),
            rhs: Box::new(Expr::Literal("10".into())),
        };
        // Body never writes Counter; rejector still must skip because
        // cond is not a bare Var.
        let body = vec![Stmt::Call {
            func: Expr::Var("Tick".into()),
            args: vec![],
            offset: 0x40,
        }];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// An `Out`-wrapped call argument writing to the cond var counts as
    /// mutation: `Foo(false, out $Climbing)` inside the
    /// body keeps the loop a While.
    #[test]
    fn out_param_write_counts_as_mutation() {
        let cond = Expr::Var("$Climbing".into());
        let body = vec![call_with_args(vec![
            Expr::Literal("false".into()),
            Expr::Out(Box::new(Expr::Var("$Climbing".into()))),
        ])];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// A While with a populated `completion` block (ForEach trampoline
    /// shape) is left alone, demoting it would lose the completion
    /// statements.
    #[test]
    fn loop_with_completion_is_not_demoted() {
        let cond = Expr::Var("$Done".into());
        let mut stmts = vec![Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(cond),
            body: vec![],
            completion: Some(vec![Stmt::Call {
                func: Expr::Var("Tail".into()),
                args: vec![],
                offset: 0x60,
            }]),
            offset: 0x10,
        }];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Pre-inline shape of a real `while (i < n)`. Cond is the opaque
    /// `Var($Less_IntInt)` produced by the un-inlined IR. The cond
    /// definition lives at body head as `$Less_IntInt = i < n`, which
    /// Blueprint re-emits each iteration before the back-edge JUMP.
    /// The first chain hop hits an assignment to the cond name itself,
    /// so the gate must NOT demote.
    #[test]
    fn pre_inline_real_while_keeps_loop() {
        let cond = Expr::Var("$Less_IntInt".into());
        let cond_definition = Stmt::Assignment {
            lhs: Expr::Var("$Less_IntInt".into()),
            rhs: Expr::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(Expr::Var("n".into())),
            },
            offset: 0x20,
        };
        let work = Stmt::Call {
            func: Expr::Var("Work".into()),
            args: vec![],
            offset: 0x30,
        };
        let increment = Stmt::Assignment {
            lhs: Expr::Var("i".into()),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0x40,
        };
        let body = vec![cond_definition, work, increment];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Pre-inline shape of an IsValid macro mis-classified as a loop.
    /// Cond is `Var($IsValid)`, the IsValid call's definition lives in
    /// the parent scope (not modeled here, the loop body alone has no
    /// definition). The body uses but never writes the cond name, so
    /// the gate must demote to Branch.
    #[test]
    fn pre_inline_fake_isvalid_demotes_to_branch() {
        let cond = Expr::Var("$IsValid".into());
        let body = vec![
            // Body uses $IsValid as the inner-if cond, not writing it.
            Stmt::Branch {
                cond: Expr::Var("$IsValid".into()),
                then_body: vec![Stmt::Call {
                    func: Expr::Var("DoWork".into()),
                    args: vec![],
                    offset: 0x50,
                }],
                else_body: vec![],
                offset: 0x40,
            },
        ];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        let Stmt::Branch {
            cond: branch_cond, ..
        } = &stmts[0]
        else {
            panic!("expected Branch after demotion");
        };
        assert!(matches!(branch_cond, Expr::Var(name) if name == "$IsValid"));
    }

    /// Pre-inline shape of a complex break-flag-guarded cond reached
    /// via a chain. Cond is `Var($BooleanAND)`, the body has aliasing
    /// hops `$BooleanAND = $Less_IntInt` (Var-to-Var) and a real
    /// definition of `$Less_IntInt` AT BODY HEAD. The chain walks
    /// through `$BooleanAND` to `$Less_IntInt`; the second chain step
    /// finds a body assignment to `$Less_IntInt`, so the gate must NOT
    /// demote.
    #[test]
    fn pre_inline_chained_alias_keeps_loop() {
        let cond = Expr::Var("$BooleanAND".into());
        let alias = Stmt::Assignment {
            lhs: Expr::Var("$BooleanAND".into()),
            rhs: Expr::Var("$Less_IntInt".into()),
            offset: 0x18,
        };
        let cond_definition = Stmt::Assignment {
            lhs: Expr::Var("$Less_IntInt".into()),
            rhs: Expr::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(Expr::Var("n".into())),
            },
            offset: 0x20,
        };
        let work = Stmt::Call {
            func: Expr::Var("Work".into()),
            args: vec![],
            offset: 0x30,
        };
        let body = vec![alias, cond_definition, work];
        let mut stmts = vec![make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[0],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Pre-inline shape where the cond chain hops from the loop body into
    /// the PARENT scope. The Loop's cond is `$X`, with no def for `$X` in
    /// the loop body; the alias `$X = $Y` lives in the PARENT scope as a
    /// sibling of the Loop, and `$Y` is mutated inside the loop body.
    /// The chain-aware gate must:
    /// 1. miss `$X` in body, walk to parent scope to find `$X = $Y`,
    /// 2. continue with `$Y`, find that body mutates `$Y`,
    /// 3. keep the Loop as a While.
    ///
    /// Without parent-scope chain following, the gate would dead-end at
    /// `$X` and demote to Branch.
    #[test]
    fn pre_inline_chain_crosses_scope_before_mutation_keeps_loop() {
        let cond = Expr::Var("$X".into());
        // Loop body: write `$Y` (the chain's terminal name) and do work.
        let mutate_y = Stmt::Assignment {
            lhs: Expr::Var("$Y".into()),
            rhs: Expr::Literal("42".into()),
            offset: 0x40,
        };
        let work = Stmt::Call {
            func: Expr::Var("Work".into()),
            args: vec![],
            offset: 0x50,
        };
        let body = vec![mutate_y, work];
        // Parent scope: alias hop $X = $Y lives here, NOT in body.
        let alias = Stmt::Assignment {
            lhs: Expr::Var("$X".into()),
            rhs: Expr::Var("$Y".into()),
            offset: 0x10,
        };
        let mut stmts = vec![alias, make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        // Gate must keep the loop: chain walk crosses parent to discover
        // $Y, then body mutation of $Y triggers preservation.
        assert!(matches!(
            &stmts[1],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Companion: the chain hops from body to parent, the chain's terminal
    /// def is non-`Var` (a `Binary{Lt, ..}`), and NEITHER the alias name
    /// nor the parent's terminal name is mutated in body. The gate must
    /// demote to Branch even though the chain crosses scope.
    /// Without parent-scope chain crossing, the gate would dead-end at
    /// `$X` and (since body never assigns `$X`) demote anyway, which is
    /// the SAME outcome by accident. To make this test discriminating,
    /// we also need the chain to find at least one alias hop in the
    /// parent scope, then verify the gate still demotes when no mutation
    /// is found anywhere. The `pre_inline_fake_isvalid_demotes_to_branch`
    /// test covers the in-body case; this one covers the cross-scope
    /// case.
    #[test]
    fn pre_inline_chain_crosses_scope_no_mutation_demotes() {
        let cond = Expr::Var("$X".into());
        let body = vec![Stmt::Branch {
            cond: Expr::Var("$X".into()),
            then_body: vec![Stmt::Call {
                func: Expr::Var("DoWork".into()),
                args: vec![],
                offset: 0x50,
            }],
            else_body: vec![],
            offset: 0x40,
        }];
        let alias = Stmt::Assignment {
            lhs: Expr::Var("$X".into()),
            rhs: Expr::Var("$Y".into()),
            offset: 0x10,
        };
        let mut stmts = vec![alias, make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        let Stmt::Branch {
            cond: branch_cond, ..
        } = &stmts[1]
        else {
            panic!("expected Branch after demotion");
        };
        assert!(matches!(branch_cond, Expr::Var(name) if name == "$X"));
    }

    /// Terminal-shape gate: a `for (i = 0 to N) { ... i = i + 1 }`-style
    /// loop whose cond resolves to `Binary{Le, counter, length}` is
    /// preserved without any body mutation of the cond temp's chain
    /// names. Models a counter-driven for-loop shape where the chain
    /// terminal is a real comparison even though the body only mutates
    /// the counter directly.
    #[test]
    fn pre_inline_for_loop_with_comparison_terminal_keeps_loop() {
        let cond = Expr::Var("$cond".into());
        // $cond resolves through one alias hop to a comparison terminal.
        let cond_def = Stmt::Assignment {
            lhs: Expr::Var("$cond".into()),
            rhs: Expr::Binary {
                op: BinaryOp::Le,
                lhs: Box::new(Expr::Var("Temp_int_Variable".into())),
                rhs: Box::new(Expr::Var("$Subtract_IntInt".into())),
            },
            offset: 0x18,
        };
        // Body mutates the COUNTER, never the cond temp's chain names.
        // Today's body-mutation gate would demote here without the
        // terminal-shape classifier.
        let work = Stmt::Call {
            func: Expr::Var("DoWork".into()),
            args: vec![],
            offset: 0x30,
        };
        let increment = Stmt::Assignment {
            lhs: Expr::Var("Temp_int_Variable".into()),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var("Temp_int_Variable".into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0x40,
        };
        let body = vec![work, increment];
        let mut stmts = vec![cond_def, make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[1],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Terminal-shape gate covers `&&` / `||` shapes too. A break-flag
    /// guarded ForC cond resolves to `Binary{And, !flag, cmp}` whose
    /// inner comparison is the iteration discriminator. Body never
    /// writes the cond temp's chain names directly, but the loop must
    /// be preserved because the terminal is a logical Binary.
    #[test]
    fn pre_inline_logical_binary_terminal_keeps_loop() {
        let cond = Expr::Var("$BooleanAND".into());
        let cond_def = Stmt::Assignment {
            lhs: Expr::Var("$BooleanAND".into()),
            rhs: Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(Expr::Unary {
                    op: crate::bytecode::expr::UnaryOp::Not,
                    operand: Box::new(Expr::Var("$BreakFlag".into())),
                }),
                rhs: Box::new(Expr::Binary {
                    op: BinaryOp::Lt,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(Expr::Var("n".into())),
                }),
            },
            offset: 0x18,
        };
        let work = Stmt::Call {
            func: Expr::Var("Work".into()),
            args: vec![],
            offset: 0x30,
        };
        let body = vec![work];
        let mut stmts = vec![cond_def, make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        assert!(matches!(
            &stmts[1],
            Stmt::Loop {
                kind: LoopKind::While,
                ..
            }
        ));
    }

    /// Terminal-shape gate must NOT fire on Call terminals. An IsValid
    /// macro mis-classified as a loop has its cond resolving to
    /// `Call("IsValid", ...)`, the classifier returns false and the
    /// body-mutation gate demotes to Branch as before. Companion to
    /// `pre_inline_fake_isvalid_demotes_to_branch`, where the cond
    /// dead-ends as bare `Var`; this one exercises the case where the
    /// chain reaches a Call terminal.
    #[test]
    fn pre_inline_call_terminal_demotes_when_body_invariant() {
        let cond = Expr::Var("$IsValid".into());
        let cond_def = Stmt::Assignment {
            lhs: Expr::Var("$IsValid".into()),
            rhs: Expr::Call {
                name: "IsValid".into(),
                args: vec![Expr::Var("self.Target".into())],
            },
            offset: 0x18,
        };
        let body = vec![Stmt::Call {
            func: Expr::Var("DoWork".into()),
            args: vec![],
            offset: 0x30,
        }];
        let mut stmts = vec![cond_def, make_while(cond, body)];

        demote_invariant_loops(&mut stmts);

        let Stmt::Branch {
            cond: branch_cond, ..
        } = &stmts[1]
        else {
            panic!("expected Branch after demotion");
        };
        assert!(matches!(branch_cond, Expr::Var(name) if name == "$IsValid"));
    }
}
