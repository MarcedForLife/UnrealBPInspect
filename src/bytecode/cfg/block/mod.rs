//! Block-level CFG over decoded bytecode.
//!
//! Built twice with different configs: for flow reorder linearization
//! (tight jump tolerance, Sequence dispatches collapsed into super-blocks
//! so DFS doesn't tear the pattern), and for the structurer's else-branch
//! detection (relaxed tolerance, raw layout). Post-latch artifacts (`}`
//! body-end markers, `DoOnce(name)` / `FlipFlop(name)` headers) are
//! recognized during construction.

mod analysis;
mod build;
mod collapse;
mod linearize;
mod types;

#[cfg(test)]
mod tests;

pub(crate) use linearize::linearize_blocks;
pub(crate) use types::{BlockCfg, BlockExit, BlockId, ReturnKind};
