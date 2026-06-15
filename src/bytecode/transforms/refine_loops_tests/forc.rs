//! ForC recognizer tests, including init absorption that fires through
//! the orchestrator. Strip-trailing-cond-recomputation tests live in
//! `init_absorption.rs`; `_unchanged` cases live in `negatives.rs`.

use super::super::refine_loops::refine_loops;
use super::super::test_fixtures::{assign_expr as assign, lit};
use super::*;
use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};

/// Where the condition gets defined relative to the loop. Drives the
/// chain-aware orchestrator through three resolution paths.
#[derive(Clone, Copy)]
enum CondDefLocation {
    /// Cond is the canonical Binary directly on the Loop.
    Direct,
    /// Cond is a `Var($temp)` opaque ref, with the temp's def at the
    /// head of the loop body.
    BodyHead,
    /// Cond is a `Var($temp)` ref, with the temp's def in the parent
    /// scope (preceding sibling).
    ParentScope,
}

/// Drives ForC promotion across cond-def-location variants. The loop
/// always has body=[Work(), counter_inc(counter)] before refinement.
/// `expected_body_len_after_refine` accounts for any cond-temp def that
/// stays in the body (BodyHead variant retains it).
#[test]
fn while_refines_to_forc_cases() {
    struct Case {
        label: &'static str,
        cond_def: CondDefLocation,
        // 1 = increment stripped, body has Work() only.
        // 2 = increment stripped, body retains cond-temp def + Work().
        expected_body_len: usize,
        // Index of the loop in the parent stmts vector after refinement.
        loop_idx: usize,
    }
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let cond_temp = "$Less_IntInt_1";
    let bound_temp = "$LoopBound";
    let cases = vec![
        Case {
            label: "post_inline_direct_cond",
            cond_def: CondDefLocation::Direct,
            expected_body_len: 1,
            loop_idx: 0,
        },
        Case {
            label: "pre_inline_body_head_cond_def",
            cond_def: CondDefLocation::BodyHead,
            expected_body_len: 2,
            loop_idx: 0,
        },
        Case {
            label: "pre_inline_parent_scope_cond_def",
            cond_def: CondDefLocation::ParentScope,
            expected_body_len: 1,
            loop_idx: 2,
        },
    ];

    for case in cases {
        let mut body = vec![call_stmt("Work"), counter_inc(counter)];
        let cond_definition = || {
            assign(
                var(cond_temp),
                Expr::Binary {
                    op: BinaryOp::Lt,
                    lhs: Box::new(var(counter)),
                    rhs: Box::new(lit("10")),
                },
            )
        };
        let mut stmts = match case.cond_def {
            CondDefLocation::Direct => vec![while_loop(counter_lt_n(counter, "10"), body)],
            CondDefLocation::BodyHead => {
                body.insert(0, cond_definition());
                vec![while_loop(var(cond_temp), body)]
            }
            // Bound is a numeric length temp (a copy of a plain int), NOT
            // `Array_Length(arr)`: that keeps this a genuine ForC chain-
            // resolution test. An `Array_Length`-bounded counter loop with an
            // unused element is a ForEach (the unused-item promotion), so
            // using `Array_Length` here would flip the case out of ForC.
            CondDefLocation::ParentScope => vec![
                assign(var(bound_temp), lit("10")),
                assign(
                    var(cond_temp),
                    Expr::Binary {
                        op: BinaryOp::Lt,
                        lhs: Box::new(var(counter)),
                        rhs: Box::new(var(bound_temp)),
                    },
                ),
                while_loop(var(cond_temp), body),
            ],
        };

        refine_loops(&mut stmts);

        let Stmt::Loop {
            kind,
            body: loop_body,
            ..
        } = &stmts[case.loop_idx]
        else {
            panic!(
                "case {}: expected Loop at idx {}",
                case.label, case.loop_idx
            );
        };
        assert!(
            matches!(kind, LoopKind::ForC { .. }),
            "case {}: should refine to ForC, got {}",
            case.label,
            loop_kind_name(kind)
        );
        assert_eq!(
            loop_body.len(),
            case.expected_body_len,
            "case {}: body length after refine",
            case.label
        );
    }
}

/// Nested loops: inner While inside outer body also gets refined.
#[test]
fn nested_while_refines() {
    let inner_counter = "Temp_int_Loop_Counter_Variable_1";
    let inner_loop = while_loop(
        counter_lt_n(inner_counter, "5"),
        vec![call_stmt("Inner"), counter_inc(inner_counter)],
    );
    let outer_body = vec![inner_loop, call_stmt("Outer")];
    // Outer stays While (no counter reference in cond).
    let outer_cond = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("OtherFlag")),
        rhs: Box::new(lit("1")),
    };
    let mut stmts = vec![while_loop(outer_cond, outer_body)];

    refine_loops(&mut stmts);

    let Stmt::Loop {
        body: outer_body, ..
    } = &stmts[0]
    else {
        panic!("expected outer Loop");
    };
    let Stmt::Loop {
        kind: inner_kind, ..
    } = &outer_body[0]
    else {
        panic!("expected inner Loop");
    };
    assert!(
        matches!(inner_kind, LoopKind::ForC { .. }),
        "inner should refine to ForC"
    );
}

/// A ForC loop with an immediately-preceding counter assignment absorbs it
/// into `init`, and the predecessor is removed from the parent list.
#[test]
fn forc_absorbs_immediate_predecessor_init() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let init_assign = assign(var(counter), lit("0"));
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![init_assign, while_loop(counter_lt_n(counter, "10"), body)];

    refine_loops(&mut stmts);

    // The predecessor assignment should have been absorbed: only the loop remains.
    assert_eq!(
        stmts.len(),
        1,
        "predecessor should be removed from parent list"
    );
    let Stmt::Loop { kind, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    let LoopKind::ForC { init, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    assert_eq!(init.len(), 1, "init should contain the absorbed assignment");
    let Stmt::Assignment { lhs, rhs, .. } = &init[0] else {
        panic!("expected Assignment in init");
    };
    assert_eq!(*lhs, var(counter), "init lhs should be the counter var");
    assert_eq!(*rhs, lit("0"), "init rhs should be the initial value");
}

/// A ForC loop absorbs the counter init even when a `$`-prefixed temp
/// probe assignment sits between the init and the loop. Real bytecode
/// often has `$Array_Length = MethodCall(...)` between `counter = 0` and
/// the loop header.
#[test]
fn forc_absorbs_init_past_dollar_temp_probe() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let init_assign = assign(var(counter), lit("0"));
    // Simulate the array-length probe that Blueprint emits between init
    // and the loop: `$Array_Length = Array_Length(Items)`.
    let probe = assign(
        var("$Array_Length"),
        Expr::Call {
            name: "Array_Length".into(),
            args: vec![var("Items")],
        },
    );
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![
        init_assign,
        probe,
        while_loop(counter_lt_n(counter, "10"), body),
    ];

    refine_loops(&mut stmts);

    // The probe stays; the counter init is absorbed into the loop.
    assert_eq!(stmts.len(), 2, "probe should remain, counter init absorbed");
    let Stmt::Loop { kind, .. } = &stmts[1] else {
        panic!("expected Loop");
    };
    let LoopKind::ForC { init, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    assert_eq!(init.len(), 1, "init should contain the absorbed assignment");
    let Stmt::Assignment { lhs, rhs, .. } = &init[0] else {
        panic!("expected Assignment in init");
    };
    assert_eq!(*lhs, var(counter), "init lhs should be the counter var");
    assert_eq!(*rhs, lit("0"), "init rhs should be 0");
}

/// When the immediate predecessor is not a counter assignment, `init` stays empty.
#[test]
fn forc_leaves_init_empty_when_predecessor_is_not_counter_assign() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let unrelated = call_stmt("DoSomethingElse");
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![unrelated, while_loop(counter_lt_n(counter, "10"), body)];

    refine_loops(&mut stmts);

    // Both statements remain: the call is not absorbed.
    assert_eq!(stmts.len(), 2, "unrelated predecessor must not be removed");
    let Stmt::Loop { kind, .. } = &stmts[1] else {
        panic!("expected Loop at index 1");
    };
    let LoopKind::ForC { init, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    assert!(
        init.is_empty(),
        "init should be empty when predecessor is not a counter assign"
    );
}

/// Pre-inline shape: the increment USE (`counter = $Add_IntInt_1`)
/// sits at the body tail; the increment DEF (`$Add_IntInt_1 = counter +
/// 1`) sits earlier in the same body. After refinement the increment slot
/// must be self-contained, the chain-substitution lifts the def's RHS into
/// the increment expression and removes the now-orphaned def from body.
#[test]
fn forc_increment_self_contained_when_def_lives_in_body() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let add_temp = "$Add_IntInt_1";
    let body = vec![
        assign(
            var(add_temp),
            Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
        ),
        call_stmt("Work"),
        assign(var(counter), var(add_temp)),
    ];
    let mut stmts = vec![while_loop(counter_lt_n(counter, "10"), body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, body, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    let LoopKind::ForC { increment, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    // Increment is self-contained: `counter = counter + 1`, no temp ref.
    assert_eq!(increment.len(), 1);
    let Stmt::Assignment { rhs: inc_rhs, .. } = &increment[0] else {
        panic!("expected Assignment in increment");
    };
    assert!(
        matches!(
            inc_rhs,
            Expr::Binary {
                op: BinaryOp::Add,
                ..
            }
        ),
        "increment rhs should be the resolved Binary, got {:?}",
        inc_rhs
    );
    // The orphan def is gone from body (only Work() remains).
    assert_eq!(body.len(), 1, "body should only retain Work() after lift");
    assert!(
        !body.iter().any(
            |stmt| matches!(stmt, Stmt::Assignment { lhs: Expr::Var(name), .. } if name == add_temp)
        ),
        "the body-local temp def should have been removed",
    );
}

/// Negative case: when the increment temp has more than one body use
/// (e.g. user code reads it too), the substitution must NOT fire, that
/// would drop an observable use. The increment slot stays opaque
/// (`counter = $Add_IntInt_1`) and the def stays in body.
#[test]
fn forc_increment_substitution_skips_multi_use_temp() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let add_temp = "$Add_IntInt_1";
    let body = vec![
        assign(
            var(add_temp),
            Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
        ),
        // Extra use of the temp inside body: the substitution must skip
        // because removing the def would drop this consumer.
        Stmt::Call {
            func: var("LogValue"),
            args: vec![var(add_temp)],
            offset: 0,
        },
        assign(var(counter), var(add_temp)),
    ];
    let mut stmts = vec![while_loop(counter_lt_n(counter, "10"), body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, body, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    // Loop still becomes ForC — extract_increment matches via the
    // chain-aware reference walk — but the body retains the def AND the
    // extra use because substitution can't safely fire.
    let LoopKind::ForC { increment, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    // Increment opaque: the rhs is still the Var ref.
    let Stmt::Assignment { rhs, .. } = &increment[0] else {
        panic!("expected Assignment in increment");
    };
    assert!(
        matches!(rhs, Expr::Var(name) if name == add_temp),
        "increment rhs should remain the opaque temp var",
    );
    // Body keeps both the def and the LogValue() consumer.
    assert_eq!(body.len(), 2);
}

/// Pre-inline shape: the counter init (`counter = 0`) sits before
/// the loop, with a `$X = ...; Temp_int_Y = $X` chain wedged between the
/// init and the loop header. The predecessor scan must skip past both
/// intermediate temps to reach and absorb the actual init line. The
/// intermediate temps stay as siblings (the inliner cleans them up later).
#[test]
fn forc_absorbs_init_past_chain_alias_temp() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let init_assign = assign(var(counter), lit("0"));
    let dollar_temp = assign(
        var("$Array_Length"),
        Expr::Call {
            name: "Array_Length".into(),
            args: vec![var("Items")],
        },
    );
    let alias_temp = assign(var("Temp_int_Mirror_Variable"), var("$Array_Length"));
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![
        init_assign,
        dollar_temp,
        alias_temp,
        while_loop(counter_lt_n(counter, "10"), body),
    ];

    refine_loops(&mut stmts);

    // Both intermediates remain; only the counter init is absorbed.
    assert_eq!(
        stmts.len(),
        3,
        "intermediate temps should remain, counter init absorbed",
    );
    let Stmt::Assignment { lhs, .. } = &stmts[0] else {
        panic!("expected dollar-temp Assignment at index 0");
    };
    let Some(name0) = (match lhs {
        Expr::Var(name) => Some(name.as_str()),
        _ => None,
    }) else {
        panic!("expected Var lhs");
    };
    assert_eq!(name0, "$Array_Length");

    let Stmt::Assignment { lhs, .. } = &stmts[1] else {
        panic!("expected alias-temp Assignment at index 1");
    };
    let Some(name1) = (match lhs {
        Expr::Var(name) => Some(name.as_str()),
        _ => None,
    }) else {
        panic!("expected Var lhs");
    };
    assert_eq!(name1, "Temp_int_Mirror_Variable");

    let Stmt::Loop { kind, .. } = &stmts[2] else {
        panic!("expected Loop at index 2");
    };
    let LoopKind::ForC { init, .. } = kind else {
        panic!("expected ForC, got {}", loop_kind_name(kind));
    };
    assert_eq!(init.len(), 1, "init should contain the absorbed assignment");
    let Stmt::Assignment { lhs, rhs, .. } = &init[0] else {
        panic!("expected Assignment in init");
    };
    assert_eq!(*lhs, var(counter), "init lhs should be the counter var");
    assert_eq!(*rhs, lit("0"), "init rhs should be 0");
}
