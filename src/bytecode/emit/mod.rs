//! Emit layer — one walker per output mode (summary, dump, JSON, diff).

pub(crate) mod comments;
pub mod diff;
pub mod dump;
pub mod json;
mod scoped_value;
mod sections;
pub mod summary;

#[cfg(test)]
mod summary_tests;

pub use diff::emit_diff;
pub use dump::emit_dump;
pub use json::emit_json;
pub use summary::{emit_summary, emit_summary_with_asset, render_body_lines};
