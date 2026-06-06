//! Call graph construction, ubergraph context building, and local function collection.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX;
use crate::resolve::resolve_index;
use crate::types::ParsedAsset;

use super::ubergraph::display_event_name;

pub(crate) fn format_call_graph(
    buf: &mut String,
    callees_map: &mut HashMap<String, Vec<String>>,
    action_key_events: &HashMap<String, String>,
) {
    if callees_map.is_empty() {
        return;
    }
    let mut entries: Vec<(&String, &mut Vec<String>)> = callees_map.iter_mut().collect();
    entries.sort_by_key(|(a, _)| *a);
    writeln!(buf, "Call graph:").unwrap();
    for (caller, callees) in &mut entries {
        callees.sort();
        let caller_display = display_event_name(caller, action_key_events);
        let callees_display: Vec<String> = callees
            .iter()
            .map(|c| display_event_name(c, action_key_events))
            .collect();
        writeln!(
            buf,
            "  {} \u{2192} {}",
            caller_display,
            callees_display.join(", ")
        )
        .unwrap();
    }
    writeln!(buf).unwrap();
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
            let class = resolve_index(&asset.imports, export_names, hdr.class_index);
            class.ends_with(".Function") && !hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX)
        })
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();
    for event_name in event_names {
        names.insert((*event_name).to_string());
    }
    names
}
