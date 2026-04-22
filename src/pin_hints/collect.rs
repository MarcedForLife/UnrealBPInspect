//! BFS that walks EdGraph pin topology to collect per-branch callee sets.
//!
//! For every event or function entry point, BFS outward through exec pins
//! and record each `K2Node_IfThenElse`'s Then vs Else callee sets.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::prop_query::{find_prop_str, find_struct_field_str};
use crate::resolve::{resolve_index, short_class};
use crate::types::{ParsedAsset, PropValue, Property};

use super::routing::{
    call_function_member_name, exec_successors_for, incoming_pin_name, node_class,
};
use super::types::{BranchHints, BranchInfo};

/// Pin name substring identifying the true-branch exec output of a Branch
/// node. Matches the convention used elsewhere in the crate.
const THEN_PIN_SUBSTRING: &str = "then";

/// Build branch hints for every event and function entry point in `asset`.
pub fn build_branch_hints(asset: &ParsedAsset) -> BranchHints {
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let entry_to_function = map_function_entries(asset, &export_names);

    let mut hints = BranchHints::default();
    let mut globally_processed: BTreeSet<usize> = BTreeSet::new();

    for (export_idx_zero, (hdr, props)) in asset.exports.iter().enumerate() {
        let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
        let short = short_class(&class);
        let entry_export = export_idx_zero + 1;

        let Some(key) = entry_point_key(&short, props, entry_export, &entry_to_function) else {
            continue;
        };

        let branches = collect_branches_from_entry(
            asset,
            &export_names,
            entry_export,
            &mut globally_processed,
        );
        if !branches.is_empty() {
            hints.by_function.entry(key).or_default().extend(branches);
        }
    }

    hints
}

/// Determine whether `node_class` + its properties identify an entry point,
/// and return the stable key used to group branches.
fn entry_point_key(
    node_class: &str,
    node_props: &[Property],
    entry_export: usize,
    entry_to_function: &BTreeMap<usize, String>,
) -> Option<String> {
    match node_class {
        "K2Node_InputAxisEvent"
        | "K2Node_InputActionEvent"
        | "K2Node_InputKeyEvent"
        | "K2Node_Event"
        | "K2Node_CustomEvent"
        | "K2Node_ComponentBoundEvent" => find_prop_str(node_props, "CustomFunctionName")
            .or_else(|| find_struct_field_str(node_props, "EventReference", "MemberName")),
        "K2Node_FunctionEntry" => entry_to_function.get(&entry_export).cloned(),
        _ => None,
    }
}

/// Map each `K2Node_FunctionEntry` 1-based export index to its enclosing
/// Function export's `object_name`. Built once per asset for O(1) lookup.
fn map_function_entries(asset: &ParsedAsset, export_names: &[String]) -> BTreeMap<usize, String> {
    let mut mapping = BTreeMap::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        for child_idx in node_indices_from_function(props) {
            mapping.insert(child_idx, hdr.object_name.clone());
        }
    }
    mapping
}

/// Extract positive 1-based export indices from a Function export's
/// `Nodes`/`AllNodes` array.
fn node_indices_from_function(props: &[Property]) -> Vec<usize> {
    let Some(prop) = props
        .iter()
        .find(|p| p.name == "Nodes" || p.name == "AllNodes")
    else {
        return Vec::new();
    };
    let PropValue::Array { items, .. } = &prop.value else {
        return Vec::new();
    };
    items
        .iter()
        .filter_map(|v| match v {
            PropValue::Object(idx) if *idx > 0 => Some(*idx as usize),
            _ => None,
        })
        .collect()
}

/// BFS outward from `entry_export` through exec-output pins, recording
/// per-Branch then/else callee sets. `globally_processed` prevents recording
/// the same Branch twice when it is reachable from multiple entry points.
fn collect_branches_from_entry(
    asset: &ParsedAsset,
    export_names: &[String],
    entry_export: usize,
    globally_processed: &mut BTreeSet<usize>,
) -> Vec<BranchInfo> {
    let mut visited: BTreeSet<(usize, String)> = BTreeSet::new();
    let mut queue: VecDeque<(usize, String)> = VecDeque::new();
    let mut branches = Vec::new();

    // Entry nodes are seeded with an empty incoming-pin name; the router
    // falls back to "enqueue all exec outputs" for the empty name.
    let entry_key = (entry_export, String::new());
    visited.insert(entry_key.clone());
    queue.push_back(entry_key);

    while let Some((current, incoming)) = queue.pop_front() {
        let Some(class) = node_class(asset, export_names, current) else {
            continue;
        };

        if class == "K2Node_IfThenElse" && globally_processed.insert(current) {
            if let Some(info) = analyze_branch(asset, export_names, current) {
                branches.push(info);
            }
        }

        for (target_node, target_pin) in exec_successors_for(asset, current, &class, &incoming) {
            let key = (target_node, target_pin);
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
    }

    branches
}

/// Analyze a single Branch node: run a sub-BFS from each of its Then/Else
/// exec-output pins and collect reachable CallFunction member names.
fn analyze_branch(
    asset: &ParsedAsset,
    export_names: &[String],
    branch_export: usize,
) -> Option<BranchInfo> {
    let pin_data = asset.pin_data.get(&branch_export)?;
    let mut then_seeds: Vec<(usize, String)> = Vec::new();
    let mut else_seeds: Vec<(usize, String)> = Vec::new();
    for pin in &pin_data.pins {
        if !pin.is_exec_output() {
            continue;
        }
        let bucket = if pin.name.contains(THEN_PIN_SUBSTRING) {
            &mut then_seeds
        } else {
            &mut else_seeds
        };
        for link in &pin.linked_to {
            let target_pin = incoming_pin_name(asset, link.node, &link.pin_id);
            bucket.push((link.node, target_pin));
        }
    }

    let then_callees = collect_side_callees(asset, export_names, branch_export, &then_seeds);
    let else_callees = collect_side_callees(asset, export_names, branch_export, &else_seeds);

    Some(BranchInfo {
        branch_export_idx: branch_export,
        then_callees,
        else_callees,
    })
}

/// Walk forward from `seeds` (not re-entering `branch_export`) and collect
/// every CallFunction `MemberName` encountered. Successors are filtered by
/// the per-class pin routing rules so DoOnce::Reset does not pull in the
/// Completed subtree.
fn collect_side_callees(
    asset: &ParsedAsset,
    export_names: &[String],
    branch_export: usize,
    seeds: &[(usize, String)],
) -> BTreeSet<String> {
    let mut callees: BTreeSet<String> = BTreeSet::new();
    let mut visited: BTreeSet<(usize, String)> = BTreeSet::new();
    // Block re-entry into the owning Branch node regardless of incoming pin.
    visited.insert((branch_export, String::new()));
    let mut queue: VecDeque<(usize, String)> = VecDeque::new();
    for seed in seeds {
        if seed.0 == branch_export {
            continue;
        }
        if visited.insert(seed.clone()) {
            queue.push_back(seed.clone());
        }
    }

    while let Some((current, incoming)) = queue.pop_front() {
        let Some(class) = node_class(asset, export_names, current) else {
            continue;
        };

        // Stop descending at a nested Branch so the inner one is attributed
        // to its own BranchInfo; we still record our own side's reach to here.
        if class == "K2Node_IfThenElse" {
            continue;
        }

        if class == "K2Node_CallFunction" {
            if let Some(name) = call_function_member_name(asset, current) {
                callees.insert(name);
            }
        }

        for (target_node, target_pin) in exec_successors_for(asset, current, &class, &incoming) {
            if target_node == branch_export {
                continue;
            }
            let key = (target_node, target_pin);
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
    }

    callees
}
