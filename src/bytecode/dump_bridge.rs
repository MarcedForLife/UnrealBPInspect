//! Source the `--dump`/`--json` per-function bytecode summary from the
//! decoder.
//!
//! The `--dump` and `--json` renderers (`output_text`, `output_json`) emit a
//! `BytecodeSummary` property per function export. The parser no longer
//! decodes bytecode (it only captures the raw bytes), so this module
//! populates `BytecodeSummary` from the decoded `DecodedAsset`, keying each
//! decoded body back to the export it was decoded from by export index.
//! Some parity gaps versus the parse-level renderer remain.

use std::collections::HashMap;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::emit::render_body_lines;
use crate::bytecode::stmt::Stmt;
use crate::types::{ParsedAsset, PropValue, Property};

/// Populate the per-function `BytecodeSummary` property from the decoder's
/// output, for the `--dump` and `--json` renderers.
///
/// Keys each decoded `Function`/`Event` body to its originating export by the
/// `export_index` the decoder carried from event-entry collection through
/// partition. Looking the body up by export identity (rather than re-joining
/// by `object_name`) avoids two name-join hazards that the old keying had to
/// work around:
///
/// - EdGraph node exports share an `object_name` with their function export
///   (both carry the function's name); only the function export should carry
///   the summary. Decoded bodies record a `.Function`-class export index by
///   construction, so an EdGraph export's index is never a map key.
/// - A standalone function and an ubergraph event could share a name. Their
///   export sets are disjoint (an ubergraph stub export becomes an `Event`;
///   every other `.Function` export becomes a `Function`), so their indices
///   never collide and no insertion-precedence ordering is needed.
///
/// Exports with no decoded body (notably `ExecuteUbergraph_*`, which split
/// into separate `events`) are left untouched, so no content is fabricated.
/// Some parity gaps versus the parse-level renderer remain.
pub fn inject_v2_bytecode_props(asset: &mut ParsedAsset, decoded: &DecodedAsset) {
    // Body lookup keyed by 1-based package export index (the
    // `bytecode_by_export` convention). Events and functions occupy disjoint
    // export indices, so insertion order is irrelevant.
    let mut bodies: HashMap<usize, &[Stmt]> = HashMap::new();
    for event in &decoded.events {
        if let Some(export_index) = event.export_index {
            bodies.insert(export_index, event.body.as_slice());
        }
    }
    for function in &decoded.functions {
        if let Some(export_index) = function.export_index {
            bodies.insert(export_index, function.body.as_slice());
        }
    }

    for (zero_based_index, (_header, props)) in asset.exports.iter_mut().enumerate() {
        let Some(body) = bodies.get(&(zero_based_index + 1)) else {
            continue;
        };
        let lines = render_body_lines(body, &decoded.resume_bodies);
        let value = PropValue::Array {
            inner_type: "StrProperty".into(),
            items: lines.into_iter().map(PropValue::Str).collect(),
        };
        if let Some(existing) = props.iter_mut().find(|prop| prop.name == "BytecodeSummary") {
            existing.value = value;
        } else {
            // The parser emits FunctionFlags after the bytecode props, so
            // insert before it to preserve the original prop order.
            let summary = Property {
                name: "BytecodeSummary".into(),
                value,
            };
            match props.iter().position(|prop| prop.name == "FunctionFlags") {
                Some(flags_index) => props.insert(flags_index, summary),
                None => props.push(summary),
            }
        }
    }
}
