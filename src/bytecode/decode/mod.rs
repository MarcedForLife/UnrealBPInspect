//! Expression decoder: raw Kismet bytecode into [`BcStatement`]s.
//!
//! `mem_adj` tracks the cumulative on-disk vs in-memory FName size difference
//! so jump targets resolve correctly.

mod entry;
mod expr;
mod funcs;
mod helpers;
mod ir;
mod match_op;
mod types;

#[cfg(test)]
mod tests;

pub use entry::decode_bytecode;
pub use expr::decode_expr;
pub use ir::{
    fmt_expr, fmt_stmt, parse_expr, parse_stmt, top_level_compound_assign_split,
    top_level_eq_split, Expr, Stmt, SwitchArm,
};
pub use types::{BcStatement, BcStatementSliceExt, DecodeCtx, StmtKind};
