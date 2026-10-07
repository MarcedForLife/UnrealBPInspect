//! Removal of unreferenced temporary assignments.

use std::collections::BTreeMap;

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::var_refs::collect_loop_items;
use crate::bytecode::transforms::visit::{
    any_expr, walk_body_exprs_visit_lhs, walk_stmt_children, walk_stmt_children_mut,
};

/// Count references across the function because a nested definition can feed
/// a sibling branch, later statement, or the next loop iteration. Only bare
/// assignment definitions are excluded, so compound destinations remain live.
pub fn remove_dead_assignments(body: &mut Vec<Stmt>) {
    for _ in 0..16 {
        let mut references = BTreeMap::new();
        walk_body_exprs_visit_lhs(body, &mut |expr| {
            if let Expr::Var(name) = expr {
                *references.entry(name.clone()).or_insert(0) += 1;
            }
        });
        collect_loop_items(body, &mut references);
        collect_assigned_names(body, &mut references);
        if !remove_in_body(body, &references) {
            break;
        }
    }
}

fn collect_assigned_names(body: &[Stmt], references: &mut BTreeMap<String, usize>) {
    for stmt in body {
        if let Stmt::Assignment {
            lhs: Expr::Var(name),
            ..
        } = stmt
        {
            *references.get_mut(name).expect("definition was counted") -= 1;
        }
        walk_stmt_children(stmt, &mut |children| {
            collect_assigned_names(children, references)
        });
    }
}

/// Drop a terminal `Stmt::Return { value: None }` from a function body.
///
/// Function bodies return implicitly at their tail, so the explicit
/// trailing return left over from the literal opcode walk is visual
/// noise. Only applied at the top level of a function body, never
/// recursed into nested blocks (nested returns are real early exits).
/// Returns with values are preserved.
///
/// Also strips the same synthetic return when it lives at the tail of a
/// tail `Stmt::Branch`. When the function body's last statement is a
/// Branch, both arms reach function exit, so a bare trailing return in
/// either arm is as redundant as a top-level one:
/// - then-arm: a `Stmt::Return { value: None }` as its last statement is
///   popped (e.g. an `if (IsValid) { ... return }` shape).
/// - else-arm: cleared when it is exactly `[Stmt::Return { value: None }]`
///   (the synthetic inverted-`else { return }` shape), and only when
///   `then_body` is non-empty (an empty `then` with a return-`else` is the
///   inverted-condition early-out shape and means something different).
///   An else-arm with real work before the return is left intact.
pub fn strip_implicit_trailing_return(body: &mut Vec<Stmt>) {
    if matches!(body.last(), Some(Stmt::Return { value: None, .. })) {
        body.pop();
    }
    if let Some(Stmt::Branch {
        then_body,
        else_body,
        ..
    }) = body.last_mut()
    {
        if matches!(then_body.last(), Some(Stmt::Return { value: None, .. })) {
            then_body.pop();
        }
        if !then_body.is_empty() && is_single_bare_return(else_body) {
            else_body.clear();
        }
    }
}

/// True when `body` is exactly `[Stmt::Return { value: None, .. }]`.
fn is_single_bare_return(body: &[Stmt]) -> bool {
    matches!(body, [Stmt::Return { value: None, .. }])
}

fn remove_in_body(body: &mut Vec<Stmt>, references: &BTreeMap<String, usize>) -> bool {
    let mut changed = false;
    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut |children| {
            changed |= remove_in_body(children, references);
        });
    }
    // Keep graph-state assignments preceding a break, including compiler
    // latch flags whose next use may live outside the decoded body.
    let contains_break = body.iter().any(|stmt| matches!(stmt, Stmt::Break { .. }));
    let original_len = body.len();
    body.retain(|stmt| {
        let Stmt::Assignment {
            lhs: Expr::Var(name),
            rhs,
            ..
        } = stmt
        else {
            return true;
        };
        contains_break
            || !is_dead_candidate_name(name)
            || references.get(name) != Some(&0)
            || expr_has_side_effects(rhs)
    });
    changed || body.len() != original_len
}

/// Field/index reads and casts may fail. Without effect metadata only
/// literal and variable values, and containers of them, are discardable.
fn expr_has_side_effects(expr: &Expr) -> bool {
    any_expr(expr, &mut |node| {
        !matches!(
            node,
            Expr::Literal(_) | Expr::Var(_) | Expr::ArrayLit(_) | Expr::StructConstruct { .. }
        )
    })
}

/// Keep persistent fields and locals even when they have no explicit reads.
/// Only compiler-generated temporary names are candidates for removal.
fn is_dead_candidate_name(name: &str) -> bool {
    if matches!(name, "Self" | "None") {
        return false;
    }
    // Field writes (`self.Thirst`, `Component.Health`, etc.) are
    // observable side effects, other code reads the field. Never
    // eliminate them, even when local visibility makes them look
    // unused within the surrounding case/branch.
    if name.contains('.') {
        return false;
    }
    if name.len() == 1 && name.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
        return false;
    }
    // Bare persistent variables (member graph variables and function
    // locals) render as `Var("RotationDifference")` with no qualifying
    // receiver. Writing one is observable: a later sibling (often after a
    // Branch, not inside an arm) reads it, so the same-scope liveness scan
    // can miss the read and sweep a live writeback. Restrict candidates to
    // compiler-temp shapes so persistent writebacks are never swept.
    crate::bytecode::transforms::name_shape::is_compiler_temp_name(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{assign, call, lit, var};

    #[test]
    fn unused_pure_assignment_removed() {
        let mut body = vec![assign("Tmp_3", lit("5")), call("Foo", vec![])];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Call { .. }));
    }

    #[test]
    fn unused_call_assignment_kept() {
        // Tmp_3 = Foo() with no later use of Tmp_3 -> assignment must
        // stay because Foo() has observable side effects.
        let mut body = vec![
            assign(
                "Tmp_3",
                Expr::Call {
                    name: "Foo".into(),
                    args: vec![],
                },
            ),
            call("Bar", vec![]),
        ];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
    }

    #[test]
    fn used_assignment_kept() {
        let mut body = vec![assign("Tmp_3", lit("5")), call("Foo", vec![var("Tmp_3")])];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
    }

    #[test]
    fn nested_in_branch() {
        let then_body = vec![assign("Tmp_3", lit("1")), call("Foo", vec![])];
        let mut body = vec![Stmt::Branch {
            cond: lit("true"),
            then_body,
            else_body: vec![],
            offset: 0,
        }];

        remove_dead_assignments(&mut body);

        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
        assert!(matches!(then_body[0], Stmt::Call { .. }));
    }

    #[test]
    fn unknown_rhs_kept() {
        let unknown = Expr::Unknown {
            reason: "test".into(),
            raw_bytes: vec![],
            offset: 0,
        };
        let mut body = vec![assign("Tmp_3", unknown), call("Foo", vec![])];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 2);
    }

    #[test]
    fn member_field_assignment_kept() {
        // self.Health = Tmp with no later use of self.Health in this
        // body still has observable side effects, other code reads the
        // field. Field writes (any name containing `.`) are never dead.
        let mut body = vec![assign("self.Health", lit("100")), call("Foo", vec![])];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 2);
        assert!(matches!(&body[0], Stmt::Assignment { .. }));
    }

    #[test]
    fn out_param_assignment_kept() {
        // `out X = 5` with no later use -> kept because the Expr::Out lhs
        // wrapper marks the slot as a function out-parameter return write.
        // The bare-Var match in pure_dead_assignment_name naturally fails
        // on an Out-wrapped lhs, so the assignment survives.
        let mut body = vec![
            Stmt::Assignment {
                lhs: Expr::Out(Box::new(var("X"))),
                rhs: lit("5"),
                offset: 0,
            },
            call("Foo", vec![]),
        ];
        remove_dead_assignments(&mut body);
        assert_eq!(body.len(), 2);
        assert!(matches!(&body[0], Stmt::Assignment { .. }));
    }

    #[test]
    fn strip_tail_branch_synthetic_else_return() {
        // `if (cond) { body } else { return }` at function tail -> drop
        // the synthetic else-arm.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![call("Foo", vec![])],
            else_body: vec![Stmt::Return {
                value: None,
                offset: 10,
            }],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
        assert!(
            else_body.is_empty(),
            "synthetic else-return must be stripped"
        );
    }

    #[test]
    fn strip_tail_branch_then_trailing_return() {
        // `if (cond) { work; return }` at function tail -> drop the
        // redundant trailing return inside the then-arm.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![
                call("Foo", vec![]),
                Stmt::Return {
                    value: None,
                    offset: 10,
                },
            ],
            else_body: vec![],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1, "trailing then-return must be stripped");
        assert!(matches!(then_body[0], Stmt::Call { .. }));
    }

    #[test]
    fn keep_then_valued_trailing_return() {
        // A valued return at the then-arm tail is user-written, not synthetic.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![
                call("Foo", vec![]),
                Stmt::Return {
                    value: Some(lit("7")),
                    offset: 10,
                },
            ],
            else_body: vec![],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 2, "valued then-return must be preserved");
    }

    #[test]
    fn strip_separate_then_branch_else_return() {
        // Pre-existing trailing-Return strip combined with the branch
        // wrapper strip: when the trailing Return sits AFTER a Branch
        // whose else-arm is also `[Return{None}]`, both should clear.
        let mut body = vec![
            Stmt::Branch {
                cond: lit("cond"),
                then_body: vec![call("Foo", vec![])],
                else_body: vec![Stmt::Return {
                    value: None,
                    offset: 10,
                }],
                offset: 0,
            },
            Stmt::Return {
                value: None,
                offset: 20,
            },
        ];
        strip_implicit_trailing_return(&mut body);
        assert_eq!(body.len(), 1);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert!(else_body.is_empty());
    }

    #[test]
    fn keep_empty_then_branch_else_return() {
        // Inverted early-out shape: empty then-arm with a return in the
        // else-arm is `if (cond) {} else { return }`, semantically
        // distinct from `if (cond) { body }`. Must not fire.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![],
            else_body: vec![Stmt::Return {
                value: None,
                offset: 10,
            }],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(
            else_body.len(),
            1,
            "empty-then branch must keep its else-return"
        );
    }

    #[test]
    fn keep_else_with_real_work() {
        // Else-arm with statements beyond a bare return is real code.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![call("Foo", vec![])],
            else_body: vec![
                call("Bar", vec![]),
                Stmt::Return {
                    value: None,
                    offset: 10,
                },
            ],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(else_body.len(), 2, "real else-body work must be preserved");
    }

    #[test]
    fn keep_return_with_value() {
        // Returns carrying a value are user-written, never synthetic.
        let mut body = vec![Stmt::Branch {
            cond: lit("cond"),
            then_body: vec![call("Foo", vec![])],
            else_body: vec![Stmt::Return {
                value: Some(lit("42")),
                offset: 10,
            }],
            offset: 0,
        }];
        strip_implicit_trailing_return(&mut body);
        let Stmt::Branch { else_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(else_body.len(), 1, "valued return must be preserved");
    }

    #[test]
    fn forc_increment_not_swept() {
        // ForC counter var appears only inside the loop kind fields.
        // dead_stmt must not remove the increment even though
        // `counter` has no use after it in the increment sub-vec.
        use crate::bytecode::expr::BinaryOp;
        use crate::bytecode::stmt::LoopKind;

        let counter = "Temp_int_Loop_Counter_Variable_0";
        let increment = vec![Stmt::Assignment {
            lhs: var(counter),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
            offset: 0,
        }];
        let init = vec![assign(counter, lit("0"))];
        let mut body = vec![Stmt::Loop {
            kind: LoopKind::ForC { init, increment },
            cond: Some(Expr::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("10")),
            }),
            body: vec![call("Work", vec![])],
            completion: None,
            offset: 0,
        }];

        remove_dead_assignments(&mut body);

        let Stmt::Loop {
            kind: LoopKind::ForC { init, increment },
            ..
        } = &body[0]
        else {
            panic!("expected ForC Loop");
        };
        assert_eq!(init.len(), 1, "init must not be swept by dead_stmt");
        assert_eq!(
            increment.len(),
            1,
            "increment must not be swept by dead_stmt"
        );
    }
}
