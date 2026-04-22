//! Expression decoder: raw Kismet bytecode into [`BcStatement`]s.
//!
//! `mem_adj` tracks the cumulative on-disk vs in-memory FName size difference
//! so jump targets resolve correctly.

mod entry;
mod expr;
mod funcs;
mod helpers;
mod match_op;
mod types;

#[cfg(test)]
mod tests;

pub use entry::decode_bytecode;
pub use expr::decode_expr;
pub use types::{BcStatement, DecodeCtx};
