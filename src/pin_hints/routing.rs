//! Per-node-class exec successor routing.
//!
//! Given a node and which exec-input pin was hit, return the exec-output
//! successors that should be followed. The routing table handles Branch,
//! ExecutionSequence, and DoOnce macros specifically; everything else falls
//! back to "enqueue every exec-output pin", the pre-routing behavior.

use std::collections::BTreeSet;

use crate::prop_query::{find_prop, find_struct_field_str};
use crate::resolve::{resolve_index, short_class};
use crate::types::{EdGraphPin, NodePinData, ParsedAsset, PropValue};

/// Short class name for a 1-based export index, or `None` if out of range.
pub(super) fn node_class(
    asset: &ParsedAsset,
    export_names: &[String],
    export_idx: usize,
) -> Option<String> {
    let zero_based = export_idx.checked_sub(1)?;
    let (hdr, _) = asset.exports.get(zero_based)?;
    let full = resolve_index(&asset.imports, export_names, hdr.class_index);
    Some(short_class(&full))
}

/// Return the `FunctionReference.MemberName` of a K2Node_CallFunction export.
pub(super) fn call_function_member_name(asset: &ParsedAsset, export_idx: usize) -> Option<String> {
    let zero_based = export_idx.checked_sub(1)?;
    let (_, props) = asset.exports.get(zero_based)?;
    find_struct_field_str(props, "FunctionReference", "MemberName")
}

/// Return `(successor_node, incoming_pin_name)` pairs reachable from
/// `node_export` when its `incoming_pin` exec-input is hit. The routing
/// respects class-specific rules so DoOnce::Reset does not leak into the
/// Completed subtree and ExecutionSequence fans out to every `then_N`.
pub(super) fn exec_successors_for(
    asset: &ParsedAsset,
    node_export: usize,
    class: &str,
    incoming_pin: &str,
) -> Vec<(usize, String)> {
    let Some(pd) = asset.pin_data.get(&node_export) else {
        return Vec::new();
    };

    match (class, incoming_pin) {
        ("K2Node_IfThenElse", "execute") => {
            targets_from_pins(asset, pd, |pin| pin.name == "then" || pin.name == "else")
        }
        ("K2Node_ExecutionSequence", "execute") => {
            targets_from_pins(asset, pd, |pin| pin.name.starts_with("then_"))
        }
        ("K2Node_MacroInstance", _) => macro_successors(asset, node_export, pd, incoming_pin),
        _ => targets_from_pins(asset, pd, |_| true),
    }
}

/// Route exec successors for a `K2Node_MacroInstance`, only deviating from
/// the default when we recognize the macro. Currently recognized: DoOnce.
fn macro_successors(
    asset: &ParsedAsset,
    node_export: usize,
    pd: &NodePinData,
    incoming_pin: &str,
) -> Vec<(usize, String)> {
    let macro_name = macro_instance_name(asset, node_export);
    match (macro_name.as_deref(), incoming_pin) {
        (Some("DoOnce"), "Start") => targets_from_pins(asset, pd, |pin| pin.name == "Completed"),
        (Some("DoOnce"), "Reset") => Vec::new(),
        _ => targets_from_pins(asset, pd, |_| true),
    }
}

/// Collect `(target_node, target_pin_name)` from every exec-output pin on
/// `pd` that satisfies `accept`, deduplicated while preserving first-seen
/// order for determinism.
fn targets_from_pins(
    asset: &ParsedAsset,
    pd: &NodePinData,
    accept: impl Fn(&EdGraphPin) -> bool,
) -> Vec<(usize, String)> {
    let mut seen: BTreeSet<(usize, String)> = BTreeSet::new();
    let mut ordered: Vec<(usize, String)> = Vec::new();
    for pin in &pd.pins {
        if !pin.is_exec_output() || !accept(pin) {
            continue;
        }
        for link in &pin.linked_to {
            let incoming = incoming_pin_name(asset, link.node, &link.pin_id);
            let entry = (link.node, incoming);
            if seen.insert(entry.clone()) {
                ordered.push(entry);
            }
        }
    }
    ordered
}

/// Look up the name of the pin on `target_node` whose `pin_id` matches.
/// Returns empty string if lookup fails, which causes the router to fall
/// back to the default "enqueue all exec outputs" behavior.
pub(super) fn incoming_pin_name(
    asset: &ParsedAsset,
    target_node: usize,
    pin_id: &[u8; 16],
) -> String {
    let Some(pd) = asset.pin_data.get(&target_node) else {
        return String::new();
    };
    pd.pins
        .iter()
        .find(|pin| &pin.pin_id == pin_id)
        .map(|pin| pin.name.clone())
        .unwrap_or_default()
}

/// Resolve a macro instance's macro name (e.g. "DoOnce") from its
/// `MacroGraphReference.MacroGraph` object property. Returns the final path
/// segment of the resolved object name, or `None` if the reference is
/// missing.
fn macro_instance_name(asset: &ParsedAsset, node_export: usize) -> Option<String> {
    let zero_based = node_export.checked_sub(1)?;
    let (_, props) = asset.exports.get(zero_based)?;
    let macro_ref = find_prop(props, "MacroGraphReference")?;
    let PropValue::Struct { fields, .. } = &macro_ref.value else {
        return None;
    };
    let graph = find_prop(fields, "MacroGraph")?;
    let PropValue::Object(idx) = graph.value else {
        return None;
    };
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();
    let full = resolve_index(&asset.imports, &export_names, idx);
    // Resolved path looks like `...StandardMacros:DoOnce` or `...StandardMacros.DoOnce`;
    // the trailing name component is the macro name.
    full.rsplit(['.', ':']).next().map(str::to_string)
}
