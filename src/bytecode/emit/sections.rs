//! Top-level summary sections (Blueprint header, Components, Variables,
//! Call graph) and the `Functions:` header line, plus per-function
//! header/caller rendering shared by the summary emitter.
//!
//! These sections reuse the parse-level section formatters directly
//! because they operate on `ParsedAsset` data the decoder has not
//! displaced. This keeps the four sections byte-identical without
//! porting their full property-rendering logic.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::call_graph::build_call_graph as build_typed_call_graph;
use crate::bytecode::emit::comments::CommentEmitPlan;
use crate::output_summary::call_graph::{collect_local_functions, format_call_graph};
use crate::output_summary::filter::block_matches_filter;
use crate::output_summary::format::{format_component_tree, format_header, format_variables};
use crate::output_summary::ubergraph::{compute_action_key_events, display_event_name};
use crate::prop_query::find_prop_str;
use crate::types::ParsedAsset;

/// Function-header metadata shared between the prefix-section pass and
/// the per-function emit pass. Built once per asset.
pub(crate) struct EmitCtx {
    /// `caller_name -> [callee_name, ...]` keyed by display-normalised
    /// caller. This is what backs `// Called by:` trailers. BTreeMap so
    /// the key set is deterministic even though current consumers only do
    /// keyed lookups.
    pub callers_map: BTreeMap<String, Vec<String>>,
    /// `raw_section_name -> "Pressed" | "Released"` for the InputAction
    /// events. Used to resolve event display names that compress to
    /// `InputAction_<Action>_<Pressed|Released>`.
    pub action_key_events: HashMap<String, String>,
    /// `function_name -> "MyFunc(arg: T)"` raw signature line from the
    /// export property stream. Missing entries fall back to
    /// `<name>()` at render time.
    pub signatures: HashMap<String, String>,
    /// `function_name -> "Public|BlueprintPure"` raw flags string from
    /// the export property stream. Missing or noise-only entries leave
    /// the bracket suffix off entirely.
    pub flags: HashMap<String, String>,
    /// Placed comment annotations (event-wrapping, function-level, inline)
    /// for this asset, consumed only by the summary block emitters. Empty
    /// for assets that author no comment boxes.
    pub comments: CommentEmitPlan,
}

/// Render prefix items and return the selected function/event blocks.
/// Each item keeps its identity until filtering has finished.
pub(crate) fn emit_prefix_sections(
    output: &mut String,
    decoded: &DecodedAsset,
    parsed: &ParsedAsset,
    filters: &[String],
) -> Vec<String> {
    let export_names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    format_header(output, parsed, &export_names);
    let components = format_component_tree(output, parsed, &export_names, filters);
    format_variables(output, parsed, &export_names, &components, filters);

    let event_names: Vec<&str> = decoded
        .events
        .iter()
        .map(|event| event.name.as_str())
        .collect();
    let local_functions = collect_local_functions(parsed, &export_names, &event_names);
    let (mut callees_map, mut callers_map) = build_call_graph(decoded, &local_functions);
    let action_key_events = compute_action_key_events(&event_names);
    for callers in callers_map.values_mut() {
        for caller in callers {
            *caller = display_event_name(caller, &action_key_events);
        }
    }
    let (signatures, flags) = collect_function_metadata(parsed);
    let context = EmitCtx {
        callers_map,
        action_key_events,
        signatures,
        flags,
        comments: CommentEmitPlan::build(decoded, parsed),
    };
    let mut matched_funcs = HashSet::new();
    let mut blocks = Vec::new();
    for function in &decoded.functions {
        let mut block = String::new();
        super::summary::emit_function_block(
            &mut block,
            &function.name,
            &function.body,
            &context,
            &decoded.resume_bodies,
        );
        if block_matches_filter(&block, filters) {
            matched_funcs.insert(function.name.clone());
            blocks.push(block);
        }
    }
    for event in &decoded.events {
        let mut block = String::new();
        super::summary::emit_event_block(
            &mut block,
            &event.name,
            &event.body,
            &context,
            &decoded.resume_bodies,
        );
        if block_matches_filter(&block, filters) {
            matched_funcs.insert(event.name.clone());
            blocks.push(block);
        }
    }
    format_call_graph(
        output,
        &mut callees_map,
        &context.action_key_events,
        filters,
        &matched_funcs,
    );
    let unresolved = context.comments.unresolved_lines(filters);
    if !unresolved.is_empty() {
        output.push_str("Graph comments (location unresolved):\n");
        for line in unresolved {
            output.push_str(&line);
            output.push('\n');
        }
        output.push('\n');
    }
    if !blocks.is_empty() || filters.is_empty() {
        output.push_str("Functions:\n");
    }
    blocks
}

/// Build the displayed call graph from the typed IR (`call_graph::build_call_graph`),
/// the single source for the emit path. Returns `(callees_map, callers_map)`
/// keyed by raw caller/callee name; caller-display normalisation and callee
/// sorting happen at format time.
///
/// Edges are filtered to real local functions (drops macro/intrinsic callees)
/// and non-self, matching the attribution the displayed call graph expects.
/// Because the typed callee/caller sets are `BTreeSet`-ordered, the resulting
/// caller lists (which back the unsorted `// Called by:` trailers) are sorted.
fn build_call_graph(
    decoded: &DecodedAsset,
    local_functions: &HashSet<String>,
) -> (HashMap<String, Vec<String>>, BTreeMap<String, Vec<String>>) {
    let (typed_callees, _) = build_typed_call_graph(decoded);
    let mut callees_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut callers_map: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (caller, callees) in &typed_callees {
        for callee in callees {
            if callee == caller || !local_functions.contains(callee.as_str()) {
                continue;
            }
            callees_map
                .entry(caller.clone())
                .or_default()
                .push(callee.clone());
            callers_map
                .entry(callee.clone())
                .or_default()
                .push(caller.clone());
        }
    }
    (callees_map, callers_map)
}

/// Collect the `Signature` and `FunctionFlags` properties from every
/// `.Function` export, keyed by export object name.
fn collect_function_metadata(
    parsed: &ParsedAsset,
) -> (HashMap<String, String>, HashMap<String, String>) {
    let mut signatures = HashMap::new();
    let mut flags = HashMap::new();
    for (hdr, props) in &parsed.exports {
        if let Some(sig) = find_prop_str(props, "Signature") {
            signatures.insert(hdr.object_name.clone(), sig);
        }
        if let Some(fl) = find_prop_str(props, "FunctionFlags") {
            flags.insert(hdr.object_name.clone(), fl);
        }
    }
    (signatures, flags)
}

/// Filter the comma/pipe-joined `FunctionFlags` string to drop the
/// `BlueprintCallable` noise flag.
pub(crate) fn filter_flags_for_summary(flags: &str) -> String {
    const NOISE: &[&str] = &["BlueprintCallable"];
    flags
        .split('|')
        .filter(|flag| !NOISE.contains(&flag.trim()))
        .collect::<Vec<_>>()
        .join("|")
}
