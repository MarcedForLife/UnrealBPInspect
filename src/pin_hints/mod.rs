//! Pin-aware branch hint analyzer.
//!
//! Walks the EdGraph (Unreal Editor node graph) pin topology starting from
//! each event or function entry point, locates every `K2Node_IfThenElse`
//! (Branch) node, and records the set of callee function names reachable
//! through the Then-pin subgraph vs the Else-pin subgraph.
//!
//! The BFS is pin-aware: instead of treating every exec-output pin as
//! reachable whenever any exec-input is hit, it consults a routing table per
//! node class ([`routing`]). This fixes false equivalences caused by DoOnce
//! macros whose Reset pin is not a real flow predecessor of Completed.
//!
//! Submodule layout:
//!
//! - [`types`] — core data types ([`BranchSide`], [`BranchInfo`], [`BranchHints`]).
//! - [`collect`] — BFS over pins to build [`BranchHints`].
//! - [`routing`] — per-class exec-successor rules.
//! - [`bytecode_map`] — map bytecode if-offsets to Branch exports.
//! - [`detect`] — pin-aware else-branch classifier.

mod bytecode_map;
mod collect;
mod detect;
mod routing;
mod types;

pub use bytecode_map::{build_bytecode_branch_map, BytecodeBranchMap};
pub use collect::build_branch_hints;
pub use detect::{
    detect_else_branch_via_pins, detect_else_branch_via_pins_scoped, ElseBranchAnswer,
};
pub use types::{BranchHints, BranchInfo, BranchSide};

#[cfg(test)]
mod tests;
