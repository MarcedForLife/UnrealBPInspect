//! Bytecode transforms: text-level long-line folding plus the expression
//! and statement tree passes for the typed IR.
//!
//! Text transforms operate on rendered pseudocode lines (long-line folding).
//! IR passes each operate on a `Vec<Stmt>` body and mutate it in place; they
//! are composable and `decode_asset` applies them in order after the initial
//! decode.

mod fold;

pub use fold::fold_long_lines;

pub(super) use crate::helpers::indent_of;

pub mod cascade_fold;
pub mod collapse_nested_doonce;
pub mod cse_projections;
pub mod cse_pure_calls;
pub mod dead_stmt;
pub mod demote_invariant_loops;
pub mod expr_transforms;
pub mod flipflop_naming;
pub mod invert_empty_then;
pub mod latch_recognition;
pub mod lower_array_get_out;
pub mod lower_binary_ops;
pub mod lower_sentinel_cascade;
pub mod lower_static_library_calls;
pub mod name_shape;
pub mod refine_loops;
pub mod rename_outparam;
pub mod strip_latent_action_info;
pub mod strip_scaffold_residue;
pub mod struct_fold;
pub mod ternary_fold;
pub mod var_names;
pub mod var_refs;
pub mod visit;

#[cfg(test)]
mod cse_projections_tests;
#[cfg(test)]
mod flipflop_naming_tests;
#[cfg(test)]
mod latch_recognition_tests;
#[cfg(test)]
mod refine_loops_tests;
#[cfg(test)]
pub(crate) mod test_fixtures;
#[cfg(test)]
mod var_names_tests;
#[cfg(test)]
mod visit_tests;
