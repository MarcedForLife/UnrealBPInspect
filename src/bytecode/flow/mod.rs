//! Flow pattern detection and bytecode reordering.
//!
//! Detects Sequence nodes, ForLoop, ForEach, and convergence patterns in flat
//! bytecode, then reorders so downstream structuring sees natural control flow.
//!
//! Split by concern:
//! - `parsers`     — push/pop depth + unmatched-pop helpers over BcStatement
//! - `sequence`    — Sequence-span detection entry + public span type
//! - `loops`       — ForLoop/ForEach detection
//! - `emit`        — Sequence/loop body emission
//! - `latch_strip` — pre-structuring latch boilerplate removal
//! - `reorder`     — top-level reordering pipeline

/// Offset tolerance for ForEach loop body detection. Jump targets use in-memory
/// offsets but we index by on-disk offsets + cumulative mem_adj. The drift
/// accumulates from FFieldPath (variable length on disk, 8-byte pointer in
/// memory) and obj-ref (+4 each).
pub(crate) const FORLOOP_OFFSET_TOLERANCE: usize = 64;

/// Max gap (in statements) between an if_jump and its push_flow/jump pair.
/// Filtered opcodes (wire_trace, tracepoint) can appear between them.
pub(crate) const FORLOOP_PUSHFLOW_WINDOW: usize = 4;

mod emit;
mod latch_strip;
mod loops;
mod parsers;
mod reorder;
mod sequence;

pub use latch_strip::strip_latch_boilerplate;
pub(crate) use loops::{detect_grouped_sequences, detect_interleaved_sequences};
pub use parsers::{find_first_unmatched_pop, find_last_unmatched_pop, flow_depth};
pub use reorder::{reorder_convergence, reorder_flow_patterns};
pub(crate) use sequence::{detect_sequence_spans, SequenceNode};
