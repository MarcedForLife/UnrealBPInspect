//! Call graph construction, ubergraph context building, and local function collection.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::bytecode::BcStatement;
use crate::resolve::{find_prop_str_items, find_prop_str_items_any, resolve_index};
use crate::types::ParsedAsset;

use super::ubergraph::{build_ubergraph_structured, is_ubergraph_stub, scan_structured_calls};
use super::{find_local_calls, strip_offset_prefix};

/// Parse a stored bytecode line (`"XXXX: text"`) into a `BcStatement`.
pub(super) fn parse_bytecode_line(line: &str) -> Option<BcStatement> {
    let hex_len = 4;
    let separator = ": ";
    let prefix_len = hex_len + separator.len();
    if line.len() <= prefix_len || line.as_bytes()[hex_len] != b':' {
        return None;
    }
    let offset = usize::from_str_radix(&line[..hex_len], 16).ok()?;
    Some(BcStatement {
        mem_offset: offset,
        text: line[prefix_len..].to_string(),
    })
}

/// Parse a single bytecode line for a call to the ubergraph entry point,
/// returning the offset argument if found.
fn parse_ubergraph_call(line: &str, call_prefix: &str) -> Option<usize> {
    let start = line.find(call_prefix)?;
    let after = &line[start + call_prefix.len()..];
    let end = after.find(')')?;
    after[..end].trim().parse::<usize>().ok()
}

/// Scan non-ubergraph function bytecode for calls to the ubergraph entry point,
/// returning a bytecode offset to event name mapping.
pub(super) fn find_ubergraph_labels(
    asset: &ParsedAsset,
    export_names: &[String],
    ubergraph_name: &str,
) -> HashMap<usize, String> {
    let mut labels = HashMap::new();
    let call_prefix = format!("{}(", ubergraph_name);

    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") || hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }
        for line in find_prop_str_items_any(props, &["BytecodeSummary", "Bytecode"]) {
            if let Some(offset) = parse_ubergraph_call(line, &call_prefix) {
                labels.insert(offset, hdr.object_name.clone());
            }
        }
    }
    labels
}

/// Build the call graph by scanning function bytecodes for cross-references.
///
/// Returns `(callees_map, callers_map)` where each maps a function name to the
/// list of local functions it calls (or is called by).
pub(super) fn build_call_graph(
    asset: &ParsedAsset,
    export_names: &[String],
    local_functions: &HashSet<String>,
    ubergraph_name: Option<&str>,
    ubergraph_structured: Option<&[String]>,
) -> (HashMap<String, Vec<String>>, HashMap<String, Vec<String>>) {
    let mut callees_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut callers_map: HashMap<String, Vec<String>> = HashMap::new();

    // Scan non-ubergraph functions for calls to local functions
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }
        if ubergraph_name.is_some() && is_ubergraph_stub(props, ubergraph_name.unwrap_or("")) {
            continue;
        }

        let bc_lines = find_prop_str_items_any(props, &["Bytecode", "BytecodeSummary"]);
        if bc_lines.is_empty() {
            continue;
        }

        for line in bc_lines {
            let code = strip_offset_prefix(line);
            for callee in find_local_calls(code, local_functions) {
                if callee == hdr.object_name {
                    continue;
                }
                let entry = callees_map.entry(hdr.object_name.clone()).or_default();
                if !entry.contains(&callee) {
                    entry.push(callee.clone());
                }
                let entry = callers_map.entry(callee.clone()).or_default();
                if !entry.contains(&hdr.object_name) {
                    entry.push(hdr.object_name.clone());
                }
            }
        }
    }

    // Scan structured ubergraph output for local calls per event section
    if let Some(structured) = ubergraph_structured {
        scan_structured_calls(
            structured,
            local_functions,
            &mut callees_map,
            &mut callers_map,
        );
    }

    (callees_map, callers_map)
}

pub(super) fn format_call_graph(buf: &mut String, callees_map: &mut HashMap<String, Vec<String>>) {
    if callees_map.is_empty() {
        return;
    }
    let mut entries: Vec<(&String, &mut Vec<String>)> = callees_map.iter_mut().collect();
    entries.sort_by(|(a, _), (b, _)| a.cmp(b));
    writeln!(buf, "Call graph:").unwrap();
    for (caller, callees) in &mut entries {
        callees.sort();
        writeln!(buf, "  {} \u{2192} {}", caller, callees.join(", ")).unwrap();
    }
    writeln!(buf).unwrap();
}

/// Context for ubergraph (EventGraph) processing, built once and shared
/// across call graph scanning and function emission.
pub(super) struct UbergraphCtx {
    pub name: String,
    pub labels: HashMap<usize, String>,
    pub structured: Vec<String>,
}

/// Build the ubergraph context if an ExecuteUbergraph function exists.
pub(super) fn build_ubergraph_ctx(
    asset: &ParsedAsset,
    export_names: &[String],
) -> Option<UbergraphCtx> {
    let (hdr, props) = asset
        .exports
        .iter()
        .find(|(hdr, _)| hdr.object_name.starts_with("ExecuteUbergraph_"))?;
    let name = hdr.object_name.clone();
    let labels = find_ubergraph_labels(asset, export_names, &name);
    if labels.is_empty() {
        return None;
    }
    let stmts: Vec<BcStatement> = find_prop_str_items(props, "Bytecode")
        .iter()
        .filter_map(|line| parse_bytecode_line(line))
        .collect();
    let structured = build_ubergraph_structured(stmts, &labels)?;
    Some(UbergraphCtx {
        name,
        labels,
        structured,
    })
}

/// Collect the set of local function names, including ubergraph event names.
pub(super) fn collect_local_functions(
    asset: &ParsedAsset,
    export_names: &[String],
    ubergraph_ctx: Option<&UbergraphCtx>,
) -> HashSet<String> {
    let mut names: HashSet<String> = asset
        .exports
        .iter()
        .filter(|(hdr, _)| {
            let class = resolve_index(&asset.imports, export_names, hdr.class_index);
            class.ends_with(".Function") && !hdr.object_name.starts_with("ExecuteUbergraph_")
        })
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();
    if let Some(ctx) = ubergraph_ctx {
        for event_name in ctx.labels.values() {
            names.insert(event_name.clone());
        }
    }
    names
}
