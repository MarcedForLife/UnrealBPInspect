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
use crate::bytecode::names::K2NODE_EXECUTION_SEQUENCE;
use crate::output_summary::call_graph::{collect_local_functions, format_call_graph};
use crate::output_summary::format::{format_component_tree, format_header, format_variables};
use crate::output_summary::ubergraph::{compute_action_key_events, display_event_name};
use crate::prop_query::find_prop_str;
use crate::resolve::{enclosing_graph_name, resolve_index, short_class};
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
    /// `block_name -> connected-mask over the editor then-pins` of that
    /// block's sole `K2Node_ExecutionSequence` node, in editor pin order
    /// (`true` = pin wired, `false` = disconnected). Populated only for
    /// blocks with exactly one ExecutionSequence node, which is the gate
    /// for faithful editor-index Sequence numbering. Blocks with zero or
    /// multiple ExecutionSequence nodes are absent and fall back to the
    /// compact decoded-pin numbering.
    pub sequence_masks: HashMap<String, Vec<bool>>,
    /// Placed comment annotations (event-wrapping, function-level, inline)
    /// for this asset, consumed only by the summary block emitters. Empty
    /// for assets that author no comment boxes.
    pub comments: CommentEmitPlan,
}

/// Append the Blueprint, Components, Variables, Call graph, and
/// `Functions:` header sections to `output`. Mirrors the prefix that
/// `format_summary` (in `output_summary/format.rs`) produces before its
/// function body block. Returns the
/// shared `EmitCtx` so the per-function pass can reuse the call graph
/// and signature lookups without re-walking the asset.
///
/// The Blueprint header line is followed by a blank line. Component and
/// variable sections also end in a trailing blank line. The Call graph
/// block ends with a blank line as well. After all four sections, this
/// writes the literal `Functions:` header.
pub(crate) fn emit_prefix_sections(
    output: &mut String,
    decoded: &DecodedAsset,
    parsed: &ParsedAsset,
) -> EmitCtx {
    let export_names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let _ = format_header(output, parsed, &export_names);
    let components = format_component_tree(output, parsed, &export_names);
    format_variables(output, parsed, &export_names, &components);

    // The ubergraph event names come from the decoded events directly.
    // This keeps the local-function set (and the InputAction
    // Pressed/Released label map below) sourced from the decoder.
    let event_names: Vec<&str> = decoded.events.iter().map(|e| e.name.as_str()).collect();
    let local_functions = collect_local_functions(parsed, &export_names, &event_names);

    let (mut callees_map, mut callers_map) = build_call_graph(decoded, &local_functions);

    // `compute_action_key_events` derives the labels from the
    // event-name suffix numbers, so input order is irrelevant.
    let action_key_events = compute_action_key_events(&event_names);

    // Caller-name normalisation so `// Called by:` trailers
    // and the call graph use the same display form.
    for callers in callers_map.values_mut() {
        for caller in callers.iter_mut() {
            *caller = display_event_name(caller, &action_key_events);
        }
    }

    format_call_graph(output, &mut callees_map, &action_key_events);

    output.push_str("Functions:\n");

    let (signatures, flags) = collect_function_metadata(parsed);
    let sequence_masks = collect_sequence_masks(parsed, &export_names);
    let comments = CommentEmitPlan::build(decoded, parsed);

    EmitCtx {
        callers_map,
        action_key_events,
        signatures,
        flags,
        sequence_masks,
        comments,
    }
}

/// Build `block_name -> editor then-pin connected-mask` for every block
/// whose graph contains exactly one `K2Node_ExecutionSequence` node.
///
/// The mask records, in editor pin-array order, whether each exec-output
/// then-pin is wired (`linked_to` non-empty). Blocks with zero or multiple
/// ExecutionSequence nodes are deliberately omitted: the faithful
/// editor-index renumbering is only unambiguous when a single sequence
/// node owns the whole block, so the emitter falls back to compact
/// decoded-pin numbering elsewhere.
fn collect_sequence_masks(
    parsed: &ParsedAsset,
    export_names: &[String],
) -> HashMap<String, Vec<bool>> {
    let mut by_block: HashMap<String, Vec<Vec<bool>>> = HashMap::new();
    for (zero_based, (hdr, _)) in parsed.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class = short_class(&resolve_index(
            &parsed.imports,
            export_names,
            hdr.class_index,
        ));
        if class != K2NODE_EXECUTION_SEQUENCE {
            continue;
        }
        let Some(pin_data) = parsed.pin_data.get(&one_based) else {
            continue;
        };
        let Some(block) = enclosing_graph_name(parsed, export_names, one_based) else {
            continue;
        };
        let mask: Vec<bool> = pin_data
            .pins
            .iter()
            .filter(|pin| pin.is_exec_output())
            .map(|pin| !pin.linked_to.is_empty())
            .collect();
        by_block.entry(block).or_default().push(mask);
    }
    by_block
        .into_iter()
        .filter_map(|(block, masks)| match masks.as_slice() {
            [single] => Some((block, single.clone())),
            _ => None,
        })
        .collect()
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
