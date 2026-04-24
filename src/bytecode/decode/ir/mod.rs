//! Typed expression and statement IR for the decoder's output form.
//!
//! Split across `types` (AST shapes), `parse` (text -> tree), and
//! `print` (tree -> text). `parse_expr` / `parse_stmt` never panic;
//! anything they can't classify returns as `Expr::Unknown` /
//! `Stmt::Unknown` wrapping the original text. `fmt_expr` / `fmt_stmt`
//! are idempotent under parse-print-parse: the printed form re-parses
//! to an equal tree.

mod parse;
mod print;
mod types;

pub use parse::{parse_expr, parse_stmt, top_level_compound_assign_split, top_level_eq_split};
pub use print::{fmt_expr, fmt_stmt};
pub use types::{Expr, Stmt, SwitchArm};
