//! Asset decoder entry point.
//!
//! Converts a parsed Blueprint asset into the typed statement tree
//! intermediate representation (IR). Recognises Assignment, Call, and
//! Return opcodes and decodes their expression operands into typed
//! `Expr` trees; out-of-scope opcodes surface as `Expr::Unknown`.
//!
//! The decoder still takes the raw asset bytes (`asset_data`) so it can
//! re-read the package-header and name-table sections it needs for
//! resolution. Bytecode bytes themselves are sourced from
//! `ParsedAsset::bytecode_by_export`, populated during the prologue walk.
//!
//! The module root holds only declarations and re-exports. The decode
//! orchestration lives in sibling files: `orchestrate` (entry point and
//! body decode drivers), `transform_stack` (the body transform
//! pipeline), `header` (version/name-table reads), `ubergraph_scan`
//! (event-entry discovery and skeleton construction), and `probe`
//! (test-only reproductions of partition slices).

mod block;
#[cfg(test)]
mod block_tests;
pub(crate) mod branch;
#[cfg(test)]
mod branch_tests;
mod cascade_decode;
#[cfg(test)]
mod cascade_decode_tests;
pub(crate) mod cross_event_inline;
#[cfg(test)]
mod cross_event_inline_tests;
pub(crate) mod ctx;
pub(crate) mod expr_decode;
mod header;
mod k2node_macro_audit;
mod loop_decode;
#[cfg(test)]
mod loop_decode_tests;
mod mem_disk;
mod naked_if;
#[cfg(test)]
mod naked_if_tests;
mod orchestrate;
mod probe;
mod region_decode;
mod sequence;
mod switch_decode;
#[cfg(test)]
pub(crate) mod test_fixtures;
mod transform_stack;
mod ubergraph_scan;
pub(crate) mod walker;
#[cfg(test)]
mod walker_tests;

// Re-exported for test harnesses (the cfg reaching-condition probes and
// the private-fixtures `partition_tests::local_tests`); production
// callers reach it through `super::mem_disk` directly.
#[cfg(test)]
pub(crate) use mem_disk::build_mem_to_disk_map;

pub use orchestrate::decode_asset;
pub(crate) use orchestrate::{
    build_event_cfg_and_region_tree, build_inline_cfg_and_region_tree_flow_scoped,
    decode_region_body, synthesize_owner_doonce_name, synthesize_owner_flipflop,
};
// The canonical event-name -> entry-K2Node derivation, also consumed by the
// summary comment classifier (placement.rs) so EventWrapping detection and
// decode agree on the event-node set (including the InputAction pattern).
pub(crate) use ubergraph_scan::build_event_node_index;

// Re-exported for test harnesses (the cfg reaching-condition probes and
// the private-fixtures `partition_tests::local_tests`); production
// callers reach it through `super::header` directly.
#[cfg(test)]
pub(crate) use header::read_version_and_name_table;

// Crate-public so the `tests/local_*` integration harness (e.g.
// `local_linear_region_extraction`) can reproduce the decoder's address
// space; integration tests link against the lib and cannot see
// `#[cfg(test)]` items, so this cannot be test-gated. Not used by the
// production decode pipeline.
pub use probe::{probe_ubergraph_partition, UbergraphProbeData};

// `K2NodeByteMapForTest` stays internal to `probe` (its only use is that
// function's return type); only the helper is reached as `decode::*`.
#[cfg(all(test, feature = "private-fixtures"))]
pub(crate) use probe::build_k2node_byte_map_for_test;
