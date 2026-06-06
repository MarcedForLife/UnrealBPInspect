//! Source the `--dump`/`--json` per-function bytecode summary from the
//! decoder.
//!
//! The `--dump` and `--json` renderers (`output_text`, `output_json`) emit a
//! `BytecodeSummary` property per function export. The parser no longer
//! decodes bytecode (it only captures the raw bytes), so this module
//! populates `BytecodeSummary` from the decoded `DecodedAsset` for each
//! function export whose `object_name` matches a decoded function/event body.
//! Some parity gaps versus the parse-level renderer remain.

use std::collections::HashMap;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::emit::render_body_lines;
use crate::bytecode::stmt::Stmt;
use crate::resolve::resolve_index;
use crate::types::{ParsedAsset, PropValue, Property};

/// Populate the per-function `BytecodeSummary` property from the decoder's
/// output, for the `--dump` and `--json` renderers.
///
/// Restricts to function-class exports (class resolves to `.Function`, with
/// captured bytecode in `bytecode_by_export`) whose `object_name` matches a
/// decoded `Function`/`Event` body of the same name, then sets
/// `BytecodeSummary` to the rendered body lines (the same content the
/// summary mode emits for that body). The function-class restriction matters
/// because EdGraph node exports share an `object_name` with their function
/// (both the `EdGraph` and the `Function` export carry the function's name);
/// only the function export should carry the summary. The class check is
/// needed because `bytecode_by_export` also holds other UStruct-derived
/// exports (`BlueprintGeneratedClass`, plain structs) whose script block is
/// captured. Exports with no matching body (notably `ExecuteUbergraph_*`,
/// which split into separate `events`) are left untouched, so no content is
/// fabricated. Some parity gaps versus the parse-level renderer remain.
pub fn inject_v2_bytecode_props(asset: &mut ParsedAsset, decoded: &DecodedAsset) {
    // Events first so a same-named standalone function takes precedence:
    // a function export's own decoded body always outranks an ubergraph
    // event that happens to share its name.
    let mut bodies: HashMap<&str, &[Stmt]> = HashMap::new();
    for event in &decoded.events {
        bodies.insert(event.name.as_str(), event.body.as_slice());
    }
    for function in &decoded.functions {
        bodies.insert(function.name.as_str(), function.body.as_slice());
    }

    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let is_function_class: Vec<bool> = asset
        .exports
        .iter()
        .map(|(header, _)| {
            resolve_index(&asset.imports, &export_names, header.class_index).ends_with(".Function")
        })
        .collect();

    let captured_exports = &asset.bytecode_by_export;
    for (export_index, (header, props)) in asset.exports.iter_mut().enumerate() {
        if !is_function_class[export_index] || !captured_exports.contains_key(&(export_index + 1)) {
            continue;
        }
        let Some(body) = bodies.get(header.object_name.as_str()) else {
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
