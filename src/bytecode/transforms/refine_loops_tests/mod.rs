//! Tests for `refine_loops`. Extracted from the production module so the
//! pass file stays focused on the post-inline matcher chain.
//!
//! Sub-modules group tests by recognizer family. Common fixture builders
//! live here at `pub(super)` visibility so each sub-module can pull them
//! in via `use super::*`.

mod forc;
mod foreach;
mod init_absorption;
mod negatives;

use super::test_fixtures::{assign_expr as assign, lit, var};
use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};

pub(super) fn call_stmt(name: &str) -> Stmt {
    Stmt::Call {
        func: var(name),
        args: vec![],
        offset: 0,
    }
}

pub(super) fn counter_lt_n(counter: &str, limit: &str) -> Expr {
    Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var(counter)),
        rhs: Box::new(lit(limit)),
    }
}

pub(super) fn counter_lt_array_length(counter: &str, array: Expr) -> Expr {
    Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var(counter)),
        rhs: Box::new(Expr::Call {
            name: "Array_Length".into(),
            args: vec![array],
        }),
    }
}

pub(super) fn counter_inc(counter: &str) -> Stmt {
    assign(
        var(counter),
        Expr::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(var(counter)),
            rhs: Box::new(lit("1")),
        },
    )
}

pub(super) fn while_loop(cond: Expr, body: Vec<Stmt>) -> Stmt {
    Stmt::Loop {
        kind: LoopKind::While,
        cond: Some(cond),
        body,
        completion: None,
        offset: 0,
    }
}

pub(super) fn loop_kind_name(kind: &LoopKind) -> &'static str {
    match kind {
        LoopKind::While => "While",
        LoopKind::ForC { .. } => "ForC",
        LoopKind::ForEach { .. } => "ForEach",
    }
}
