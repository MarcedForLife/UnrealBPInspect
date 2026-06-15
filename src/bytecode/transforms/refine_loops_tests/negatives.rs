//! Negative-path tests: shapes that must NOT be promoted away from While
//! and ForEach matchers that must reject mismatched arrays. Cases that
//! exercise a successful refinement plus a sub-conjunct that doesn't fire
//! live in their respective recognizer modules.

use super::super::refine_loops::refine_loops;
use super::*;
use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};

/// A While loop that doesn't match ForC or ForEach stays While.
#[test]
fn while_without_counter_stays_while() {
    let body = vec![call_stmt("Work"), call_stmt("MoreWork")];
    // Cond references something not in body assignments.
    let cond = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("SomeCond")),
        rhs: Box::new(super::super::test_fixtures::lit("0")),
    };
    let mut stmts = vec![while_loop(cond, body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    assert!(
        matches!(kind, LoopKind::While),
        "should stay While, got {}",
        loop_kind_name(kind)
    );
}

/// A fetch indexes a DIFFERENT array (`Other[i]`) than the loop's
/// `Array_Length(Outer)` bound, and no fetch reads the bound array. The counter
/// is still live (it indexes the parallel `Other` array), and the ForEach
/// rendering cannot expose the iteration index, so promoting to a ForEach over
/// `Outer` would orphan the `Other[i]` fetch. The loop must stay an index-`for`
/// (ForC), NOT promote, the unused-element ForEach path is gated on the counter
/// being dead scaffolding (see `body_indexes_with_counter`).
#[test]
fn while_with_parallel_fetch_stays_index_for() {
    let counter = "Temp_int_Loop_Counter_Variable";
    let outer_array = var("Outer");
    let other_array = var("Other");
    let body = vec![
        // Fetch from a different array, indexed by the live counter.
        super::super::test_fixtures::assign_expr(
            var("$Array_Get_Item"),
            Expr::Index {
                recv: Box::new(other_array.clone()),
                idx: Box::new(var(counter)),
            },
        ),
        call_stmt("Work"),
        counter_inc(counter),
    ];
    let cond = counter_lt_array_length(counter, outer_array.clone());
    let mut stmts = vec![while_loop(cond, body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    assert!(
        matches!(kind, LoopKind::ForC { .. }),
        "a counter-indexed parallel fetch must keep the loop an index-for (ForC), \
         not promote to a ForEach that would orphan the index; got {}",
        loop_kind_name(kind)
    );
}

/// Step 5d: simple `while (i < n)` with no trailing cond recomputation.
/// The strip must NOT touch the trailing counter increment, the loop
/// still refines to ForC.
#[test]
fn while_without_trailing_recomputation_unaffected() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let body = vec![call_stmt("Work"), counter_inc(counter)];
    let mut stmts = vec![while_loop(counter_lt_n(counter, "10"), body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, body, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    assert!(
        matches!(kind, LoopKind::ForC { .. }),
        "should refine to ForC, got {}",
        loop_kind_name(kind)
    );
    // Body retains Work() only, the strip pass should NOT remove the
    // counter increment (it's not a recomputation, just the counter
    // increment that extract_increment moves into the increment slot).
    assert_eq!(body.len(), 1);
}
