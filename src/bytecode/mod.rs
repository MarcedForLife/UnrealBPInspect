//! Kismet bytecode: shared foundation plus the decoder producing a typed
//! statement tree intermediate representation (IR).
//!
//! Foundation:
//! - [`opcodes`] - opcode byte constants
//! - [`readers`] - low-level operand readers
//! - [`names`] - name normalization (LWC variants, display cleanup)
//! - [`resolve`] - import/export index resolution for bytecode operands
//! - [`transforms`] - long-line folding plus the IR transform passes
//!
//! Decoder: [`cfg`], [`decode`], [`structure`], [`emit`], and the supporting
//! modules ([`asset`], [`partition`], [`stmt`], etc.) build and lower the IR.

pub mod names;
pub mod opcodes;
pub mod readers;
pub mod resolve;
pub mod transforms;

pub mod asset;
pub mod call_graph;
pub mod cfg;
pub mod decode;
pub mod doonce_wrap_synthesis;
pub mod dump_bridge;
pub mod emit;
pub mod expr;
pub mod k2node_byte_map;
pub mod partition;
pub mod pin_attribution;
pub mod stmt;
pub mod structure;

#[cfg(test)]
mod partition_tests;

/// Target line width for pseudocode readability. Used by line folding.
pub const MAX_LINE_WIDTH: usize = 120;
