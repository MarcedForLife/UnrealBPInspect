//! Summary output mode (default).
//!
//! Function and event bodies are rendered from the typed statement IR by
//! `bytecode::emit`; this module holds the surrounding section formatting,
//! the post-processing filter, and event display-name helpers.

pub(crate) mod call_graph;
pub(crate) mod comments;
mod filter;
pub(crate) mod format;
pub(crate) mod ubergraph;

pub use filter::filter_summary;

/// Width (in spaces) of one indent level in summary output.
pub(crate) const INDENT_WIDTH: usize = 2;
/// One indent level (`INDENT_WIDTH` spaces) as a string literal for cheap prefixing.
pub(crate) const INDENT: &str = "  ";
/// Two indent levels (used for event bodies under an event signature).
pub(crate) const BODY_INDENT: &str = "    ";
// Keep the string literals and width constant in sync.
const _: () = assert!(INDENT.len() == INDENT_WIDTH);
const _: () = assert!(BODY_INDENT.len() == INDENT_WIDTH * 2);
