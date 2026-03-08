pub mod decode;
pub mod flow;
pub mod inline;
pub mod names;
pub mod opcodes;
pub mod readers;
pub mod resolve;
pub mod structure;

pub use decode::{decode_bytecode, BcStatement};
pub use flow::{
    parse_if_jump, parse_jump, parse_push_flow, reorder_convergence, reorder_flow_patterns,
};
pub use inline::{
    cleanup_structured_output, discard_unused_assignments, fold_summary_patterns,
    inline_single_use_temps,
};
pub use structure::structure_bytecode;
