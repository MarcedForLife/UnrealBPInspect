//! Call graph construction, ubergraph context building, and local function collection.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX;
use crate::resolve::class_of;
use crate::types::ParsedAsset;

use super::filter::block_matches_filter;
use super::ubergraph::display_event_name;

pub(crate) fn format_call_graph(
    buf: &mut String,
    callees_map: &mut HashMap<String, Vec<String>>,
    action_key_events: &HashMap<String, String>,
    filters: &[String],
    matched_funcs: &HashSet<String>,
) {
    if callees_map.is_empty() {
        return;
    }
    let mut entries: Vec<(&String, &mut Vec<String>)> = callees_map.iter_mut().collect();
    entries.sort_by_key(|(a, _)| *a);
    let mut items = String::new();
    for (caller, callees) in &mut entries {
        callees.sort();
        let caller_display = display_event_name(caller, action_key_events);
        let callees_display: Vec<String> = callees
            .iter()
            .map(|c| display_event_name(c, action_key_events))
            .collect();
        let item = format!(
            "  {} \u{2192} {}\n",
            caller_display,
            callees_display.join(", ")
        );
        if block_matches_filter(&item, filters)
            || matched_funcs.contains(caller.as_str())
            || callees.iter().any(|callee| matched_funcs.contains(callee))
        {
            items.push_str(&item);
        }
    }
    if !items.is_empty() {
        writeln!(buf, "Call graph:").unwrap();
        buf.push_str(&items);
        writeln!(buf).unwrap();
    }
}

/// Collect the set of local function names, including ubergraph event names.
/// `event_names` supplies the ubergraph event labels (the decoded events'
/// names).
pub(crate) fn collect_local_functions(
    asset: &ParsedAsset,
    export_names: &[String],
    event_names: &[&str],
) -> HashSet<String> {
    let mut names: HashSet<String> = asset
        .exports
        .iter()
        .filter(|(hdr, _)| {
            let class = class_of(&asset.imports, export_names, hdr);
            class.ends_with(".Function") && !hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX)
        })
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();
    for event_name in event_names {
        names.insert((*event_name).to_string());
    }
    names
}
