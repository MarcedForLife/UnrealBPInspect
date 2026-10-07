//! Item matching shared by summary section renderers.

pub use crate::bytecode::emit::summary::filter_summary;

pub(crate) fn block_matches_filter(text: &str, filters: &[String]) -> bool {
    filters.is_empty() || {
        let lower = text.to_lowercase();
        filters.iter().any(|filter| lower.contains(filter))
    }
}
