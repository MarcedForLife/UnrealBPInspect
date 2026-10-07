//! Per-export bytecode captured during asset parsing.

use crate::types::ParsedAsset;

/// Look up the raw bytecode bytes for an export captured during
/// `parse_asset`'s prologue walk. Returns `None` for non-function exports
/// or any export whose serialized stream had no bytecode block.
pub(super) fn lookup_export_bytecode(asset: &ParsedAsset, export_index: usize) -> Option<Vec<u8>> {
    asset
        .bytecode_by_export
        .get(&export_index)
        .map(|(bytes, _)| bytes.clone())
}
