//! Ubergraph event splitting, latent resume block matching, and structured output processing.

use std::collections::{HashMap, HashSet};

use crate::bytecode::{BARE_RETURN, RETURN_NOP};
use crate::prop_query::find_prop_str_items_any;
use crate::types::Property;

use super::find_local_calls;

mod comment_placement;
mod emit;
mod events;
mod linearize;

#[cfg(test)]
mod tests;

pub(super) use emit::emit_ubergraph_events;
pub(super) use events::{compute_action_key_events, display_event_name};
pub(super) use linearize::{build_ubergraph_structured, split_ubergraph_sections};

/// Scan structured ubergraph output for local-function calls, attributing
/// them to the enclosing `--- EventName ---` section. `Delay()` lines with
/// `/*resume:0xHEX*/` pull in their latent resume block.
pub(super) fn scan_structured_calls(
    lines: &[String],
    local_functions: &HashSet<String>,
    callees_map: &mut HashMap<String, Vec<String>>,
    callers_map: &mut HashMap<String, Vec<String>>,
) {
    let (sections, resume_blocks) = split_ubergraph_sections(lines);

    // Associate each Delay+resume annotation with its resume block, in order.
    let mut resume_idx = 0usize;
    let mut event_resume_lines: HashMap<String, Vec<String>> = HashMap::new();
    for section in &sections {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            if line.contains("/*resume:0x") && resume_idx < resume_blocks.len() {
                event_resume_lines
                    .entry(section.name.clone())
                    .or_default()
                    .extend(resume_blocks[resume_idx].lines.iter().cloned());
                resume_idx += 1;
            }
        }
    }

    let mut record_call = |caller: &str, callee: &str| {
        let entry = callees_map.entry(caller.to_string()).or_default();
        if !entry.contains(&callee.to_string()) {
            entry.push(callee.to_string());
        }
        let entry = callers_map.entry(callee.to_string()).or_default();
        if !entry.contains(&caller.to_string()) {
            entry.push(caller.to_string());
        }
    };

    for section in &sections {
        if !section.is_event() {
            continue;
        }
        for line in &section.lines {
            for callee in find_local_calls(line.trim(), local_functions) {
                if callee != section.name {
                    record_call(&section.name, &callee);
                }
            }
        }
        if let Some(resume_lines) = event_resume_lines.get(&section.name) {
            for line in resume_lines {
                for callee in find_local_calls(line.trim(), local_functions) {
                    if callee != section.name {
                        record_call(&section.name, &callee);
                    }
                }
            }
        }
    }
}

/// True if a function is a stub that only dispatches to the ubergraph
/// (`ExecuteUbergraph_X(N)` + optional return/persistent-frame lines).
pub(super) fn is_ubergraph_stub(props: &[Property], ug_name: &str) -> bool {
    let lines = find_prop_str_items_any(props, &["BytecodeSummary", "Bytecode"]);
    let meaningful: Vec<&str> = lines
        .iter()
        .map(|line| super::strip_offset_prefix(line).trim())
        .filter(|code| !matches!(*code, "" | BARE_RETURN | RETURN_NOP))
        .collect();
    if meaningful.is_empty() {
        return false;
    }
    let prefix = format!("{}(", ug_name);
    meaningful.iter().any(|line| line.starts_with(&prefix))
        && meaningful
            .iter()
            .all(|line| line.starts_with(&prefix) || line.contains("[persistent]"))
}
