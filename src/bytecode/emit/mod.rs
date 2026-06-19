//! Emit layer. Renders the decoded statement tree as summary pseudocode and
//! exposes the body-line bridge the --dump/--json property override reuses.

pub(crate) mod comments;
mod scoped_value;
mod sections;
pub mod summary;

#[cfg(test)]
mod summary_tests;

pub use summary::{emit_summary_with_asset, render_body_lines};
