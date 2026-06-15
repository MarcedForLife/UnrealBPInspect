//! Trailing-cond-recomputation strip pass tests. These exercise the
//! `strip_trailing_cond_recomputation` helper plus its end-to-end effect
//! during ForC promotion.

use super::super::refine_loops::{refine_loops, strip_trailing_cond_recomputation};
use super::super::test_fixtures::assign_expr as assign;
use super::*;
use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};

/// A body with a trailing cond recomputation.
/// The canonical cond def lives in the parent scope (sibling of the
/// loop). The loop body ends with a duplicate of that def. Strip must
/// peel the recomputation so `extract_increment` reaches the actual
/// counter increment and ForC promotion fires.
#[test]
fn forc_strips_trailing_cond_recomputation_single_stmt() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let cond_temp = "$cond";
    let canonical_cond_def = counter_lt_n(counter, "10");
    let body = vec![
        call_stmt("Work"),
        counter_inc(counter),
        assign(var(cond_temp), canonical_cond_def.clone()),
    ];
    let mut stmts = vec![
        assign(var(cond_temp), canonical_cond_def.clone()),
        while_loop(var(cond_temp), body),
    ];

    refine_loops(&mut stmts);

    // The parent-scope cond def survives at stmts[0]; the loop refines
    // to ForC after the recomputation peel exposes the counter
    // increment as the trailing body stmt.
    assert_eq!(stmts.len(), 2, "parent cond def must remain");
    let Stmt::Loop { kind, body, .. } = &stmts[1] else {
        panic!("expected Loop at stmts[1]");
    };
    assert!(
        matches!(kind, LoopKind::ForC { .. }),
        "should refine to ForC after recomputation strip, got {}",
        loop_kind_name(kind)
    );
    // Body retains only Work() once the recomputation is stripped and
    // the counter increment is moved out.
    assert_eq!(body.len(), 1, "body should retain Work() only");
}

/// A ForEach body with a multi-stmt trailing
/// recomputation (sub-expression temp `$Array_Length` plus `$cond`).
/// Strip must peel both before extract_increment runs.
#[test]
fn forc_strips_trailing_cond_recomputation_multi_stmt() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let cond_temp = "$cond";
    let length_temp = "$Array_Length";
    let length_def = Expr::Call {
        name: "Array_Length".into(),
        args: vec![var("arr")],
    };
    let canonical_cond_def = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var(counter)),
        rhs: Box::new(var(length_temp)),
    };
    let body = vec![
        call_stmt("Work"),
        counter_inc(counter),
        assign(var(length_temp), length_def.clone()),
        assign(var(cond_temp), canonical_cond_def.clone()),
    ];
    let mut stmts = vec![
        assign(var(length_temp), length_def.clone()),
        assign(var(cond_temp), canonical_cond_def.clone()),
        while_loop(var(cond_temp), body),
    ];

    refine_loops(&mut stmts);

    // The bound is `Array_Length(arr)` and the body never reads an element,
    // so this promotes to a ForEach over `arr` (the unused-item shape):
    // the parent-scope bound-expr leak is then absorbed, shifting the loop's
    // index. Locate the loop wherever it lands.
    let loop_stmt = stmts
        .iter()
        .find(|stmt| matches!(stmt, Stmt::Loop { .. }))
        .expect("a refined Loop must remain");
    let Stmt::Loop { kind, body, .. } = loop_stmt else {
        unreachable!();
    };
    assert!(
        matches!(kind, LoopKind::ForC { .. } | LoopKind::ForEach { .. }),
        "should refine away from While, got {}",
        loop_kind_name(kind)
    );
    // Recomputation peeled, increment moved out. Only Work() remains in the
    // body.
    assert_eq!(body.len(), 1, "body should retain Work() only");
}

/// Negative: the trailing assignment targets a name OUTSIDE the
/// cond chain. The strip must not touch the body, the loop refines via
/// the normal increment path (the trailing stmt is the counter
/// increment, no recomputation present).
#[test]
fn strip_leaves_body_alone_when_trailing_name_outside_cond_chain() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let cond_temp = "$cond";
    let canonical_cond_def = counter_lt_n(counter, "10");
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![
        assign(var(cond_temp), canonical_cond_def.clone()),
        while_loop(var(cond_temp), body),
    ];

    refine_loops(&mut stmts);

    // ForC promotion fires through the normal cond-chain path; the
    // strip pass is a no-op (no trailing recomputation present).
    assert_eq!(stmts.len(), 2, "parent cond def must remain");
    let Stmt::Loop { kind, body, .. } = &stmts[1] else {
        panic!("expected Loop at stmts[1]");
    };
    assert!(
        matches!(kind, LoopKind::ForC { .. }),
        "should refine to ForC, got {}",
        loop_kind_name(kind)
    );
    // Body retains Work() only after the increment is moved out, the
    // strip pass did not touch anything else.
    assert_eq!(body.len(), 1, "body should retain Work() only");
}

/// Negative: byte-identical equality gate. The trailing
/// assignment's lhs is in the cond chain BUT its rhs differs from the
/// canonical def. Strip must NOT remove the stmt. Tested directly
/// against `strip_trailing_cond_recomputation` to isolate the gate
/// from `extract_increment`'s downstream extraction logic.
#[test]
fn strip_does_not_fire_when_rhs_differs_from_canonical() {
    let cond_temp = "$cond";
    let canonical_cond_def = counter_lt_n("counter", "10");
    let bogus_rhs = counter_lt_n("counter", "99");
    let mut body = vec![
        call_stmt("Work"),
        // Trailing stmt: same lhs as the canonical, but rhs differs
        // (literal 10 vs. 99). Byte-identical equality must reject.
        assign(var(cond_temp), bogus_rhs.clone()),
    ];
    let ancestor = vec![assign(var(cond_temp), canonical_cond_def.clone())];
    let ancestors: Vec<&[Stmt]> = vec![&ancestor];

    let cond = var(cond_temp);
    strip_trailing_cond_recomputation(&mut body, &cond, &ancestors);

    assert_eq!(body.len(), 2, "strip must NOT remove the bogus stmt");
    let Stmt::Assignment { rhs: tail_rhs, .. } = &body[1] else {
        panic!("expected Assignment at tail");
    };
    assert_eq!(
        *tail_rhs, bogus_rhs,
        "bogus tail rhs must be intact after strip rejects it",
    );
}

/// Direct: strip peels a single trailing recomputation against
/// a parent-scope canonical def, leaving the body's earlier stmts
/// untouched.
#[test]
fn strip_peels_single_recomputation_against_parent_canonical() {
    let cond_temp = "$cond";
    let counter = "counter";
    let canonical = counter_lt_array_length(counter, var("arr"));
    let mut body = vec![
        call_stmt("Work"),
        counter_inc(counter),
        assign(var(cond_temp), canonical.clone()),
    ];
    let ancestor = vec![assign(var(cond_temp), canonical.clone())];
    let ancestors: Vec<&[Stmt]> = vec![&ancestor];

    let cond = var(cond_temp);
    strip_trailing_cond_recomputation(&mut body, &cond, &ancestors);

    // Tail recomputation peeled, the counter increment and Work() remain.
    assert_eq!(body.len(), 2);
    assert!(
        matches!(&body[1], Stmt::Assignment { lhs: Expr::Var(name), .. } if name == counter),
        "trailing body stmt should be the counter increment after strip",
    );
}

/// Direct: strip peels a multi-stmt trailing recomputation,
/// the sub-expression temp `$Array_Length` plus the cond temp `$cond`,
/// against parent-scope canonical defs.
#[test]
fn strip_peels_multi_stmt_recomputation_with_sub_expr_temp() {
    let cond_temp = "$cond";
    let length_temp = "$Array_Length";
    let counter = "counter";
    let length_def = Expr::Call {
        name: "Array_Length".into(),
        args: vec![var("arr")],
    };
    let cond_def = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var(counter)),
        rhs: Box::new(var(length_temp)),
    };
    let mut body = vec![
        call_stmt("Work"),
        counter_inc(counter),
        assign(var(length_temp), length_def.clone()),
        assign(var(cond_temp), cond_def.clone()),
    ];
    let ancestor = vec![
        assign(var(length_temp), length_def.clone()),
        assign(var(cond_temp), cond_def.clone()),
    ];
    let ancestors: Vec<&[Stmt]> = vec![&ancestor];

    let cond = var(cond_temp);
    strip_trailing_cond_recomputation(&mut body, &cond, &ancestors);

    // Both recomputation stmts peeled; Work() and counter increment remain.
    assert_eq!(body.len(), 2);
    assert!(
        matches!(&body[1], Stmt::Assignment { lhs: Expr::Var(name), .. } if name == counter),
        "trailing body stmt should be the counter increment after strip",
    );
}
