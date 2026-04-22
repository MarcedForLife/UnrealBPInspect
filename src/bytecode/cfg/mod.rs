//! Control flow graph layer over decoded bytecode.
//!
//! - [`stmt`] - statement-level CFG used by ubergraph event partitioning.
//! - [`block`] - basic-block CFG used by flow reordering and the structurer.

pub mod block;
pub mod stmt;

pub use stmt::{
    build_stmt_cfg, extract_partition_stmts, partition_by_reachability, EventPartition, StmtCfg,
};

pub(crate) use block::{linearize_blocks, BlockCfg, BlockExit, BlockId, ReturnKind};
