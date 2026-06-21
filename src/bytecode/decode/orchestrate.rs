//! Decode orchestration: the asset entry point and per-event/function
//! body decode drivers.
//!
//! Holds [`decode_asset`] (the lib entry), the CFG + region-tree
//! construction helpers, the per-event and standalone-function body
//! decode drivers, the transform-stack application pass, latent-call
//! resume decode, and the owner-body re-decode used for cross-event
//! FlipFlop/DoOnce synthesis.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::asset::{DecodedAsset, Event, Function};
use crate::bytecode::decode::ctx::debug_enabled;
use crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX;
use crate::bytecode::partition::{
    build_opcode_graph, build_opcode_graph_with_resume, partition_ubergraph_with_translation,
    EventEntry,
};
use crate::bytecode::structure::build_skeleton;
use crate::resolve::class_of;
use crate::types::ParsedAsset;

use super::ctx::DecodeCtx;
use super::header::{lookup_export_bytecode, read_version_and_name_table};
use super::mem_disk::build_mem_to_disk_map;
use super::transform_stack::apply_transform_stack_to_body;
use super::ubergraph_scan::{
    build_event_node_index, build_event_skeleton, build_macro_names, build_node_class_names,
    collect_event_entries, is_ubergraph_stub, prescan_event_tail_jin_arms,
    translate_entries_to_disk,
};

/// Decode a parsed Blueprint asset into the statement tree IR.
///
/// `asset_data` is the raw `.uasset` file bytes, required only to re-read
/// the version header and name table. Bytecode bytes come from
/// `asset.bytecode_by_export`, captured during `parse_asset`. The
/// `ParsedAsset` provides the already-parsed import/export tables and the
/// structured property data (including decoded bytecode text lines used
/// to locate event entry offsets).
///
/// Recognises Assignment (EX_Let*), Call (EX_*Function, EX_CallMath),
/// and Return, decoding expression operands into typed `Expr` trees.
///
/// The decode is panic-isolated at two levels: each event/function body
/// decode is caught individually (a failing body degrades to a marked
/// `Stmt::Unknown` placeholder while the rest of the asset decodes
/// normally), and the whole pipeline is caught as a last resort (the
/// asset degrades to no bytecode output instead of aborting the process,
/// which matters in batch/directory mode).
pub fn decode_asset(asset: &ParsedAsset, asset_data: &[u8]) -> DecodedAsset {
    let decode = std::panic::AssertUnwindSafe(|| decode_asset_inner(asset, asset_data));
    match std::panic::catch_unwind(decode) {
        Ok(decoded) => decoded,
        Err(payload) => {
            eprintln!(
                "decode: bytecode decode panicked ({}); omitting bytecode for this asset",
                panic_message(payload.as_ref())
            );
            DecodedAsset {
                functions: vec![],
                events: vec![],
                resume_bodies: BTreeMap::new(),
                resume_owner_events: BTreeMap::new(),
                byte_maps: Default::default(),
            }
        }
    }
}

/// Extract a readable message from a caught panic payload (`panic!` with a
/// string literal yields `&str`, with a format string yields `String`).
fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
    if let Some(message) = payload.downcast_ref::<&str>() {
        message
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message
    } else {
        "non-string panic payload"
    }
}

/// Build the placeholder body for an event/function whose decode panicked.
/// `Stmt::Unknown` renders as a clearly-marked block, so the failure is
/// visible in the output instead of masquerading as an empty body.
fn panicked_body(
    payload: &(dyn std::any::Any + Send),
    offset: usize,
) -> Vec<crate::bytecode::stmt::Stmt> {
    vec![crate::bytecode::stmt::Stmt::Unknown {
        reason: format!("decode panicked: {}", panic_message(payload)),
        raw_bytes: vec![],
        offset,
        length: 0,
    }]
}

fn decode_asset_inner(asset: &ParsedAsset, asset_data: &[u8]) -> DecodedAsset {
    let (ue5, name_table) = match read_version_and_name_table(asset_data) {
        Some(pair) => pair,
        None => {
            if debug_enabled() {
                eprintln!("probe: read_version_and_name_table returned None");
            }
            return DecodedAsset {
                functions: vec![],
                events: vec![],
                resume_bodies: BTreeMap::new(),
                resume_owner_events: BTreeMap::new(),
                byte_maps: Default::default(),
            };
        }
    };
    if debug_enabled() {
        eprintln!("probe: ue5={}", ue5);
    }

    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let mut functions = Vec::new();
    let mut events = Vec::new();
    // Graph-identity DoOnce wrap plans, resolved per event while its
    // `DecodeCtx` is alive (the only `ctx`-dependent half of the synthesis).
    // Keyed by event name. The body rewrite runs later, after the uniform
    // bulk transform pass, against the transform-stacked body.
    let mut doonce_wrap_plans: std::collections::BTreeMap<
        String,
        Vec<crate::bytecode::doonce_wrap_synthesis::SynthWrapPlan>,
    > = std::collections::BTreeMap::new();
    // Latent-call resume continuations aggregated across all events.
    // Keyed by the call's disk offset. Each ubergraph contributes its
    // own set; non-ubergraph assets leave this empty.
    let mut resume_bodies: BTreeMap<usize, Vec<crate::bytecode::stmt::Stmt>> = BTreeMap::new();
    // Owner event per latent-resume chain, range-derived where the
    // partition output is in hand. Carried on `DecodedAsset` so comment
    // placement consumes ownership instead of re-deriving it from the
    // decoded statement trees.
    let mut resume_owner_events: BTreeMap<usize, String> = BTreeMap::new();
    // K2Node-to-bytes attribution, carried out to emit so a node can be
    // resolved to the statement it produced. The ubergraph map is built inside
    // the partition-OK arm below (`None` for assets with no ubergraph); the
    // per-function maps are collected by the standalone-function loop.
    let mut ubergraph_byte_map: Option<crate::bytecode::k2node_byte_map::K2NodeByteMap> = None;
    let mut function_byte_maps: BTreeMap<String, crate::bytecode::k2node_byte_map::K2NodeByteMap> =
        BTreeMap::new();

    // Locate the ubergraph export by name prefix.
    let ubergraph_export = asset
        .exports
        .iter()
        .enumerate()
        .find(|(_, (hdr, _))| hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX));

    decode_ubergraph_events(
        asset,
        &export_names,
        &name_table,
        ue5,
        ubergraph_export,
        &mut events,
        &mut doonce_wrap_plans,
        &mut resume_bodies,
        &mut resume_owner_events,
        &mut ubergraph_byte_map,
    );

    // Decode standalone function exports (class `.Function`, not the
    // ubergraph dispatcher, and not ubergraph stubs).
    let ug_name_opt: Option<&str> = ubergraph_export.map(|(_, (hdr, _))| hdr.object_name.as_str());
    decode_standalone_functions(
        asset,
        &export_names,
        &name_table,
        ue5,
        ug_name_opt,
        &mut functions,
        &mut function_byte_maps,
    );

    // Sort for deterministic output.
    events.sort_by(|a, b| a.name.cmp(&b.name));
    functions.sort_by(|a, b| a.name.cmp(&b.name));

    apply_transform_stack(&mut functions, &mut events);

    // Graph-identity DoOnce wrap synthesis, apply half. The planning half
    // ran per event while each `DecodeCtx` was alive; now that the bulk
    // transform stack has applied uniformly to every event body, rewrite
    // each planned cross-body-unreachable DoOnce in place against the
    // transform-stacked tree (a cross-body DoOnce reached from a branch
    // arm).
    for event in events.iter_mut() {
        if let Some(plans) = doonce_wrap_plans.get(&event.name) {
            crate::bytecode::doonce_wrap_synthesis::apply_doonce_wrap_synthesis(
                &mut event.body,
                plans,
            );
        }
    }

    // Asset-wide DoOnce display-name resolution. The per-body
    // `rewrite_reset_doonce_names` pass inside `apply_transform_stack` only
    // sees Latches in the same event/function body, so a synthetic
    // `Call(ResetDoOnce(DoOnce_<N>))` whose gate variable's Latch wrap
    // lives in another body stays as the bare fallback name. This pass
    // walks every body, builds a unique `gate_var -> display_name` map
    // from non-fallback Latch names (excluding gate_vars with ambiguous
    // mappings), then rewrites surviving fallback ResetDoOnce arguments.
    crate::bytecode::transforms::latch_recognition::rewrite_asset_wide_reset_doonce_names(
        &mut functions,
        &mut events,
    );

    // Env-gated audit. No-op unless BP_GRAPH_CLAIM_AUDIT is set.
    // Label includes UE version so the same-named ubergraph across UE
    // version directories is distinguishable in the divergence log.
    let ubergraph_name = ubergraph_export
        .map(|(_, (hdr, _))| hdr.object_name.clone())
        .unwrap_or_else(|| "<no-ubergraph>".to_string());
    let asset_label = format!("ue5={} {}", ue5, ubergraph_name);
    if let Err(audit_err) = super::k2node_macro_audit::run_audit(asset, &asset_label, &events) {
        eprintln!("decode: graph-claim audit log write failed: {}", audit_err);
    }

    // Apply the same transform stack to each resume body so the
    // interleaved continuation renders consistently with the call site
    // around it (binary ops lowered, library prefixes stripped, etc.).
    for body in resume_bodies.values_mut() {
        apply_transform_stack_to_body(body);
    }

    DecodedAsset {
        functions,
        events,
        resume_bodies,
        resume_owner_events,
        byte_maps: crate::bytecode::k2node_byte_map::ByteMaps {
            ubergraph: ubergraph_byte_map,
            functions: function_byte_maps,
        },
    }
}

/// Decode every ubergraph event body. Locates the ubergraph export's
/// bytecode, partitions it into per-event owned ranges, and decodes each
/// event, appending decoded `Event`s to `events` and collecting the
/// products the post-decode passes consume:
/// - `doonce_wrap_plans`: per-event graph-identity DoOnce wrap plans;
/// - `resume_bodies`: latent-call resume continuations keyed by call offset;
/// - `resume_owner_events`: owner event per latent-resume chain;
/// - `ubergraph_byte_map`: the CommentRefined K2Node-byte attribution map.
///
/// A no-ubergraph asset, an unreadable ubergraph body, empty translated
/// entries, or a partition failure each leave every accumulator untouched.
#[allow(clippy::too_many_arguments)]
fn decode_ubergraph_events(
    asset: &ParsedAsset,
    export_names: &[String],
    name_table: &NameTable,
    ue5: i32,
    ubergraph_export: Option<(
        usize,
        &(crate::types::ExportHeader, Vec<crate::types::Property>),
    )>,
    events: &mut Vec<Event>,
    doonce_wrap_plans: &mut std::collections::BTreeMap<
        String,
        Vec<crate::bytecode::doonce_wrap_synthesis::SynthWrapPlan>,
    >,
    resume_bodies: &mut BTreeMap<usize, Vec<crate::bytecode::stmt::Stmt>>,
    resume_owner_events: &mut BTreeMap<usize, String>,
    ubergraph_byte_map: &mut Option<crate::bytecode::k2node_byte_map::K2NodeByteMap>,
) {
    if let Some((ug_idx, (ug_hdr, _ug_props))) = ubergraph_export {
        let ug_name = ug_hdr.object_name.clone();
        let ug_export_index = ug_idx + 1;

        if let Some(bytecode) = lookup_export_bytecode(asset, ug_export_index, &ug_name) {
            let entries = collect_event_entries(asset, export_names, &ug_name, name_table, ue5);

            // Event entry offsets in the Bytecode property text are memory
            // coordinates (FNames are 12 bytes in memory), but partition
            // operates on the raw disk byte slice (FNames are 8 bytes on
            // disk). Translate every entry mem -> disk before partitioning.
            let (mem_to_disk, mem_disk_err) = build_mem_to_disk_map(&bytecode, name_table, ue5);
            if let Some(err) = mem_disk_err {
                eprintln!("decode: mem-to-disk walk for {}: {}", ug_name, err);
            }
            if debug_enabled() {
                let last_disk = mem_to_disk.values().copied().max().unwrap_or(0);
                let last_mem = mem_to_disk.keys().copied().max().unwrap_or(0);
                eprintln!(
                    "probe: ug={} bytecode_len={} entries={} map_entries={} last_mem=0x{:x} last_disk=0x{:x}",
                    ug_name,
                    bytecode.len(),
                    entries.len(),
                    mem_to_disk.len(),
                    last_mem,
                    last_disk,
                );
                if let Some((first_name, first_off)) =
                    entries.first().map(|e| (&e.name, e.mem_offset))
                {
                    eprintln!(
                        "probe:  first_entry='{}' mem=0x{:x} -> disk={:?}",
                        first_name,
                        first_off,
                        mem_to_disk.get(&first_off)
                    );
                }
            }
            let translated_entries = translate_entries_to_disk(&entries, &mem_to_disk, &ug_name);

            if !entries.is_empty() && translated_entries.is_empty() {
                eprintln!(
                    "decode: dropped all event entries for {} during mem-to-disk translation",
                    ug_name
                );
            }

            if !translated_entries.is_empty() {
                let event_entries_by_mem: std::collections::BTreeMap<usize, String> = entries
                    .iter()
                    .map(|entry| (entry.mem_offset, entry.name.clone()))
                    .collect();
                // Build cross-event inline classifier state shared
                // across every event's decode. Built ahead
                // of partition so the partition's pin-attribution probe
                // can compare its lowest-offset tie-break against
                // the pin-BFS event sets these structures encode.
                let event_node_index = build_event_node_index(asset, export_names);
                let NodeClassIndices {
                    node_class_names,
                    node_classes,
                    macro_names,
                } = build_node_class_indices(asset, export_names);
                // Pre-build the per-target "reaching events" map once
                // per ubergraph; the per-jump classifier then does an
                // O(1) lookup instead of running a fresh BFS per event
                // entry every time.
                let node_to_reaching_events =
                    super::cross_event_inline::build_node_to_reaching_events(
                        &event_node_index,
                        &asset.pin_data,
                        |node_id| {
                            matches!(
                                node_classes.get(&node_id),
                                Some(super::cross_event_inline::K2NodeClass::Knot)
                            )
                        },
                    );
                // Pin-attribution probe input. Maps disk offsets of
                // K2Node_CallFunction call sites to the set of events
                // whose exec-pin tree reaches them. The partition layer
                // compares this against its lowest-offset tie-break and
                // logs divergences.
                let pin_attribution = crate::bytecode::pin_attribution::build_pin_event_attribution(
                    asset,
                    export_names,
                    &node_to_reaching_events,
                    &bytecode,
                    name_table,
                    ue5,
                );
                // Build the opcode graph (and harvest latent-call resume
                // targets) once for the whole ubergraph. Every consumer
                // rides this single instance: the partitioner, each event's
                // region walk, the K2Node-byte attribution passes, and the
                // resume-body decode. The graph is a pure function of
                // `(bytecode, ue5, name_table, mem_to_disk)`, so the same
                // instance is valid for any owned sub-range a consumer
                // walks.
                let (graph, latent_resumes) =
                    build_opcode_graph_with_resume(&bytecode, ue5, name_table, &mem_to_disk);
                match partition_ubergraph_with_translation(
                    &bytecode,
                    &translated_entries,
                    name_table,
                    ue5,
                    &graph,
                    &latent_resumes,
                    Some(&pin_attribution),
                ) {
                    Ok(partition_output) => {
                        let event_ranges = partition_output.event_ranges;
                        let resume_blocks = partition_output.resume_blocks;
                        *resume_owner_events =
                            build_resume_owner_map(&resume_blocks, &event_ranges);
                        if debug_enabled() {
                            eprintln!("probe: resume_owner_events={:?}", resume_owner_events);
                        }
                        // Decode each latent-call resume chunk into its
                        // own statement vector. The map is keyed by the
                        // originating call's disk offset (the
                        // `Stmt::Call.offset` carried through transform
                        // and emit), so the summary renderer can look
                        // up the chunk by call site and interleave its
                        // body after the latent call line.
                        let ug_resume_bodies = decode_resume_bodies(
                            asset,
                            &resume_blocks,
                            &bytecode,
                            ue5,
                            name_table,
                            &mem_to_disk,
                            &graph,
                            export_names,
                        );
                        for (call_offset, body) in ug_resume_bodies {
                            resume_bodies.insert(call_offset, body);
                        }
                        // Parallel K2Node-byte attribution map.
                        // DecodeCtx threads an optional reference so
                        // consumers can flip on additively.
                        let event_entry_disks: BTreeMap<String, usize> = translated_entries
                            .iter()
                            .map(|entry| (entry.name.clone(), entry.mem_offset))
                            .collect();
                        // Event-name to originating export index, mirroring
                        // the name-keyed collapse of `event_entry_disks`.
                        // `event_ranges` is also name-keyed, so each event
                        // name resolves to one stub export here.
                        let event_export_indices: BTreeMap<String, usize> = translated_entries
                            .iter()
                            .map(|entry| (entry.name.clone(), entry.export_index))
                            .collect();
                        let k2node_byte_map_inputs =
                            crate::bytecode::k2node_byte_map::K2NodeByteMapInputs {
                                asset,
                                export_names,
                                bytecode: &bytecode,
                                name_table,
                                ue5,
                                node_classes: &node_classes,
                                macro_names: &macro_names,
                                node_to_reaching_events: &node_to_reaching_events,
                                event_owned_ranges: &event_ranges,
                                mem_to_disk: &mem_to_disk,
                                event_entries: &event_entry_disks,
                                event_node_index: &event_node_index,
                                resume_blocks: &resume_blocks,
                                graph: &graph,
                                scope: crate::bytecode::k2node_byte_map::GraphScope::Ubergraph,
                            };
                        // The decode loop reads this map (cross-event
                        // inline + macro_region), so it uses the
                        // conservative view: comment-only attribution
                        // refinements must not move decoded structure. The
                        // CommentRefined map for placement is built once
                        // below, after the loop.
                        let k2node_byte_map =
                            crate::bytecode::k2node_byte_map::build_k2node_byte_map_conservative(
                                &k2node_byte_map_inputs,
                            );
                        let event_inputs = EventDecodeInputs {
                            asset,
                            export_names,
                            bytecode: &bytecode,
                            ue5,
                            name_table,
                            mem_to_disk: &mem_to_disk,
                            graph: &graph,
                            event_ranges: &event_ranges,
                            event_node_index: &event_node_index,
                            node_to_reaching_events: &node_to_reaching_events,
                            node_classes: &node_classes,
                            node_class_names: &node_class_names,
                            macro_names: &macro_names,
                            k2node_byte_map: &k2node_byte_map,
                            translated_entries: &translated_entries,
                            event_entries_by_mem: &event_entries_by_mem,
                        };
                        for (event_name, ranges) in &event_ranges {
                            let decode = std::panic::AssertUnwindSafe(|| {
                                decode_ubergraph_event_body(&event_inputs, event_name, ranges)
                            });
                            let (body, plans) = match std::panic::catch_unwind(decode) {
                                Ok(pair) => pair,
                                Err(payload) => {
                                    eprintln!(
                                        "decode: event '{}' panicked during decode ({}); emitting placeholder body",
                                        event_name,
                                        panic_message(payload.as_ref())
                                    );
                                    let offset =
                                        ranges.first().map(|range| range.start).unwrap_or(0);
                                    (panicked_body(payload.as_ref(), offset), None)
                                }
                            };
                            if let Some(plans) = plans {
                                doonce_wrap_plans.insert(event_name.clone(), plans);
                            }
                            events.push(Event {
                                name: event_name.clone(),
                                body,
                                export_index: event_export_indices.get(event_name).copied(),
                            });
                        }
                        // The event loop's last borrow of the conservative
                        // `k2node_byte_map` (through `event_inputs`) ends
                        // above. Comment placement consumes the
                        // CommentRefined view (the same-name group bijection
                        // applied); building it here, after decode, is what
                        // keeps comment attribution from touching structure.
                        drop(k2node_byte_map);
                        *ubergraph_byte_map =
                            Some(crate::bytecode::k2node_byte_map::build_k2node_byte_map(
                                &k2node_byte_map_inputs,
                            ));
                    }
                    Err(err) => {
                        eprintln!("decode: partition failed for {}: {}", ug_name, err);
                    }
                }
            }
        }
    }
}

/// Decode every standalone function export (class `.Function`, excluding the
/// ubergraph dispatcher and ubergraph stubs), appending each decoded
/// `Function` to `functions` and its K2Node-byte map to `function_byte_maps`.
/// `ug_name_opt` is the ubergraph export's object name when present, used to
/// skip its stub exports.
#[allow(clippy::too_many_arguments)]
fn decode_standalone_functions(
    asset: &ParsedAsset,
    export_names: &[String],
    name_table: &NameTable,
    ue5: i32,
    ug_name_opt: Option<&str>,
    functions: &mut Vec<Function>,
    function_byte_maps: &mut BTreeMap<String, crate::bytecode::k2node_byte_map::K2NodeByteMap>,
) {
    // Node-class and macro-name indices are graph-agnostic (built over all
    // asset exports), so build them once here and share across every
    // standalone-function byte-map build below. The per-function map uses the
    // same name/operand-correlation passes the ubergraph map does; only the
    // event-scoped inputs differ (empty for a single function).
    let NodeClassIndices {
        node_classes: fn_node_classes,
        macro_names: fn_macro_names,
        ..
    } = build_node_class_indices(asset, export_names);

    for (export_idx, (hdr, _props)) in asset.exports.iter().enumerate() {
        let class = class_of(&asset.imports, export_names, hdr);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX) {
            continue;
        }
        if let Some(ug_name) = ug_name_opt {
            if is_ubergraph_stub(
                asset,
                export_names,
                export_idx + 1,
                &hdr.object_name,
                ug_name,
                name_table,
                ue5,
            ) {
                continue;
            }
        }

        let export_index = export_idx + 1;
        let read_result = lookup_export_bytecode(asset, export_index, &hdr.object_name);
        if debug_enabled() {
            eprintln!(
                "probe: function '{}' serial=0x{:x}+{} -> {}",
                hdr.object_name,
                hdr.serial_offset,
                hdr.serial_size,
                read_result.as_ref().map(|b| b.len()).unwrap_or(0),
            );
        }
        if let Some(bytecode) = read_result {
            // Build a per-function mem-to-disk map so jump targets within
            // this body can be translated. Standalone function bodies use
            // the same disk vs mem split as ubergraph bytecode whenever
            // FName-bearing literals appear in the stream.
            let (fn_mem_to_disk, fn_mem_disk_err) =
                build_mem_to_disk_map(&bytecode, name_table, ue5);
            if let Some(err) = fn_mem_disk_err {
                if debug_enabled() {
                    eprintln!(
                        "decode: mem-to-disk walk for fn {}: {}",
                        hdr.object_name, err
                    );
                }
            }
            let decode = std::panic::AssertUnwindSafe(|| {
                decode_standalone_function_body(
                    asset,
                    export_names,
                    &hdr.object_name,
                    &bytecode,
                    ue5,
                    name_table,
                    &fn_mem_to_disk,
                    &fn_node_classes,
                    &fn_macro_names,
                )
            });
            let body = match std::panic::catch_unwind(decode) {
                Ok((body, byte_map)) => {
                    function_byte_maps.insert(hdr.object_name.clone(), byte_map);
                    body
                }
                Err(payload) => {
                    eprintln!(
                        "decode: function '{}' panicked during decode ({}); emitting placeholder body",
                        hdr.object_name,
                        panic_message(payload.as_ref())
                    );
                    panicked_body(payload.as_ref(), 0)
                }
            };
            functions.push(Function {
                name: hdr.object_name.clone(),
                body,
                export_index: Some(export_index),
            });
        }
    }
}

/// Graph-agnostic node-class and macro-name indices, built over all asset
/// exports and shared by both the ubergraph and standalone-function decode
/// paths. `node_classes` is the `parse_k2node_class`-resolved view of
/// `node_class_names`; the standalone path consumes only `node_classes` and
/// `macro_names`.
struct NodeClassIndices {
    node_class_names: std::collections::HashMap<usize, String>,
    node_classes: std::collections::HashMap<usize, super::cross_event_inline::K2NodeClass>,
    macro_names: std::collections::HashMap<usize, String>,
}

/// Build the node-class names, their parsed `K2NodeClass` view, and the
/// macro-name index for `asset`.
fn build_node_class_indices(asset: &ParsedAsset, export_names: &[String]) -> NodeClassIndices {
    let node_class_names = build_node_class_names(asset, export_names);
    let node_classes = node_class_names
        .iter()
        .map(|(&node_id, class)| {
            (
                node_id,
                super::cross_event_inline::parse_k2node_class(class),
            )
        })
        .collect();
    let macro_names = build_macro_names(asset, export_names);
    NodeClassIndices {
        node_class_names,
        node_classes,
        macro_names,
    }
}

/// Owner event per latent-resume chain, keyed by the originating call's
/// disk offset, derived from partition ranges: a call offset inside an
/// event's owned ranges takes that event; a call offset inside another
/// chain's resume range takes that chain's owner, resolved to a fixpoint
/// (a chained latent is a Delay-style call inside another resume chunk).
///
/// Consumed by summary comment placement (`anchor_via_owner_event`'s
/// resume-chain search) via `DecodedAsset::resume_owner_events`.
fn build_resume_owner_map(
    resume_blocks: &BTreeMap<usize, Range<usize>>,
    event_ranges: &BTreeMap<String, Vec<Range<usize>>>,
) -> BTreeMap<usize, String> {
    let mut owner: BTreeMap<usize, String> = BTreeMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &call_offset in resume_blocks.keys() {
            if owner.contains_key(&call_offset) {
                continue;
            }
            let direct = event_ranges.iter().find_map(|(name, ranges)| {
                ranges
                    .iter()
                    .any(|range| range.contains(&call_offset))
                    .then(|| name.clone())
            });
            let chained = || {
                resume_blocks
                    .iter()
                    .find(|(&parent, range)| parent != call_offset && range.contains(&call_offset))
                    .and_then(|(parent, _)| owner.get(parent).cloned())
            };
            if let Some(name) = direct.or_else(chained) {
                owner.insert(call_offset, name);
                changed = true;
            }
        }
    }
    owner
}

/// Shared inputs for decoding one ubergraph event body. Bundled because
/// every per-event iteration reads the same partition-wide maps and
/// classifier state built once per ubergraph; passing them individually
/// would be sixteen positional arguments.
struct EventDecodeInputs<'a> {
    asset: &'a ParsedAsset,
    export_names: &'a [String],
    bytecode: &'a [u8],
    ue5: i32,
    name_table: &'a NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
    graph: &'a crate::bytecode::partition::OpcodeGraph,
    event_ranges: &'a BTreeMap<String, Vec<Range<usize>>>,
    event_node_index: &'a BTreeMap<String, usize>,
    node_to_reaching_events:
        &'a std::collections::HashMap<usize, std::collections::BTreeSet<String>>,
    node_classes: &'a std::collections::HashMap<usize, super::cross_event_inline::K2NodeClass>,
    node_class_names: &'a std::collections::HashMap<usize, String>,
    macro_names: &'a std::collections::HashMap<usize, String>,
    k2node_byte_map: &'a crate::bytecode::k2node_byte_map::K2NodeByteMap,
    translated_entries: &'a [EventEntry],
    event_entries_by_mem: &'a BTreeMap<usize, String>,
}

/// Decode one ubergraph event's statement body via the region-tree walker.
///
/// Returns the decoded body plus the event's graph-identity DoOnce wrap
/// plans (if any), resolved here while the per-event `DecodeCtx` is alive.
/// The caller aggregates plans across events and applies them after the
/// bulk transform pass.
fn decode_ubergraph_event_body(
    inputs: &EventDecodeInputs,
    event_name: &str,
    ranges: &[Range<usize>],
) -> (
    Vec<crate::bytecode::stmt::Stmt>,
    Option<Vec<crate::bytecode::doonce_wrap_synthesis::SynthWrapPlan>>,
) {
    // Skeleton owner_range spans every owned range for this event.
    // Cross-range events (sibling events split a body in two) get a single
    // union span; the BFS inside `build_skeleton` respects opcode-graph
    // reachability so unreachable bytes from sibling events don't bleed in.
    let arm_boundaries = prescan_event_tail_jin_arms(
        inputs.bytecode,
        inputs.ue5,
        inputs.name_table,
        inputs.mem_to_disk,
        ranges,
        Some(inputs.graph),
    );
    let skeleton = build_event_skeleton(
        inputs.bytecode,
        inputs.ue5,
        inputs.name_table,
        inputs.mem_to_disk,
        ranges,
        &arm_boundaries,
        Some(inputs.graph),
    );
    let claimed: RefCell<BTreeMap<usize, super::ctx::Claim>> = RefCell::new(BTreeMap::new());
    let cei = super::cross_event_inline::CrossEventInlineCtx {
        current_event_name: event_name,
        event_owned_ranges: inputs.event_ranges,
        event_node_index: inputs.event_node_index,
        node_to_reaching_events: inputs.node_to_reaching_events,
        pin_data: &inputs.asset.pin_data,
        node_classes: inputs.node_classes,
        macro_names: inputs.macro_names,
        active_inline_anchors: std::cell::RefCell::new(std::collections::BTreeSet::new()),
        inlined_targets: std::cell::RefCell::new(std::collections::BTreeSet::new()),
        k2node_byte_map: Some(inputs.k2node_byte_map),
    };
    let entry_disk = inputs
        .translated_entries
        .iter()
        .find(|entry| entry.name == event_name)
        .map(|entry| entry.mem_offset);
    // Build CFG + SESE region tree once per event so recognisers can
    // compute region-aware arm extents under both the linear sweep and
    // the parallel region walk.
    let event_cfg_bundle = entry_disk.map(|entry| {
        build_event_cfg_and_region_tree(
            entry,
            ranges,
            inputs.graph,
            inputs.bytecode,
            inputs.ue5,
            inputs.name_table,
            inputs.mem_to_disk,
        )
    });
    let ctx = DecodeCtx {
        mem_to_disk: Some(inputs.mem_to_disk),
        event_entries: Some(inputs.event_entries_by_mem),
        function_signatures: Some(&inputs.asset.function_signatures),
        owned_ranges: Some(ranges),
        skeleton: Some(&skeleton),
        claimed: Some(&claimed),
        graph: Some(inputs.graph),
        cfg: event_cfg_bundle.as_ref().map(|(cfg, _, _)| cfg),
        region_tree: event_cfg_bundle.as_ref().map(|(_, tree, _)| tree),
        region_byte_ranges: event_cfg_bundle.as_ref().map(|(_, _, ranges)| ranges),
        cross_event_inline: Some(&cei),
        k2node_byte_map: Some(inputs.k2node_byte_map),
        ..DecodeCtx::new(
            inputs.bytecode,
            inputs.name_table,
            &inputs.asset.imports,
            inputs.export_names,
            inputs.ue5,
        )
    };
    let Some(_entry) = entry_disk else {
        return (Vec::new(), None);
    };
    // Region-tree walker.
    let mut prod_body = match event_cfg_bundle.as_ref() {
        Some((cfg, region_tree, _)) => decode_region_body(region_tree, cfg, &ctx),
        None => Vec::new(),
    };
    // Graph-identity DoOnce wrap synthesis, planning half. Resolves the
    // cross-body-unreachable DoOnce candidates the byte recognizer cannot
    // reach (a cross-body DoOnce reached from a branch arm) while `ctx` is
    // alive. Candidates derive from `form_event_macro_regions`, not from
    // any audit env gate. The body rewrite runs later, after the uniform
    // bulk transform pass, so the transform stack applies once to every
    // event.
    let plans = event_cfg_bundle.as_ref().and_then(|(cfg, _, _)| {
        let plans = crate::bytecode::doonce_wrap_synthesis::plan_doonce_wrap_synthesis(
            cfg,
            inputs.graph,
            inputs.k2node_byte_map,
            &ctx,
            event_name,
        );
        if plans.is_empty() {
            None
        } else {
            Some(plans)
        }
    });
    // Divergent-tail Sequence synthesis: a non-owner event whose per-event
    // Sequence then-0 became a cross-event jump (the shared body inlines
    // as a top-level statement) has no EX_PUSH_EXECUTION_FLOW chain, so it
    // decodes flat. Re-wrap from graph identity to match the owner's
    // Sequence rendering.
    super::cross_event_inline::wrap_divergent_tail_sequence(
        &mut prod_body,
        event_name,
        ranges,
        &cei,
        inputs.node_class_names,
        &inputs.asset.pin_data,
    );
    (prod_body, plans)
}

/// Decode a standalone function export's body via the region-tree walker, plus
/// the per-function K2Node-to-bytes attribution map carried out to emit.
///
/// Builds the per-function skeleton, opcode graph, and CFG/region tree over
/// the full bytecode range, then decodes. Mirrors the per-event path with
/// no cross-event inline context (standalone functions own their bytes).
///
/// The byte map uses the same name/operand-correlation attribution passes the
/// ubergraph map does (`build_k2node_byte_map`); a function has no event
/// partitions, so the event-scoped inputs are passed empty and only the
/// graph-agnostic call/let/cast passes contribute. `node_classes` and
/// `macro_names` are asset-global indices the caller builds once and shares.
#[allow(clippy::too_many_arguments)]
fn decode_standalone_function_body(
    asset: &ParsedAsset,
    export_names: &[String],
    function_name: &str,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    fn_mem_to_disk: &BTreeMap<usize, usize>,
    node_classes: &std::collections::HashMap<usize, super::cross_event_inline::K2NodeClass>,
    macro_names: &std::collections::HashMap<usize, String>,
) -> (
    Vec<crate::bytecode::stmt::Stmt>,
    crate::bytecode::k2node_byte_map::K2NodeByteMap,
) {
    let full_range = Range {
        start: 0,
        end: bytecode.len(),
    };
    // Standalone function bodies have their own bytecode and per-function
    // mem-to-disk map, so the graph is distinct from the ubergraph's.
    // Build it once here and share it across the skeleton, CFG, and region
    // tree below.
    let fn_graph = build_opcode_graph(bytecode, ue5, name_table, fn_mem_to_disk);
    let skeleton = build_skeleton(
        bytecode,
        ue5,
        name_table,
        fn_mem_to_disk,
        full_range.clone(),
        &[],
        Some(&fn_graph),
    );
    let fn_cfg_bundle = build_event_cfg_and_region_tree(
        0,
        std::slice::from_ref(&full_range),
        &fn_graph,
        bytecode,
        ue5,
        name_table,
        fn_mem_to_disk,
    );
    let claimed: RefCell<BTreeMap<usize, super::ctx::Claim>> = RefCell::new(BTreeMap::new());
    let ctx = DecodeCtx {
        mem_to_disk: Some(fn_mem_to_disk),
        function_signatures: Some(&asset.function_signatures),
        skeleton: Some(&skeleton),
        claimed: Some(&claimed),
        graph: Some(&fn_graph),
        cfg: Some(&fn_cfg_bundle.0),
        region_tree: Some(&fn_cfg_bundle.1),
        region_byte_ranges: Some(&fn_cfg_bundle.2),
        ..DecodeCtx::new(bytecode, name_table, &asset.imports, export_names, ue5)
    };
    // Region-tree walker.
    let body = decode_region_body(&fn_cfg_bundle.1, &fn_cfg_bundle.0, &ctx);

    // Per-function K2Node-to-bytes attribution. The event-scoped inputs are
    // empty for a single function (a function has no event partitions), so the
    // event passes contribute nothing and the graph-agnostic call/let/cast
    // passes carry the attribution. Wrapped with the per-function mem-to-disk
    // bridge so emit can translate a node's disk range back to a statement.
    let empty_reaching: std::collections::HashMap<usize, std::collections::BTreeSet<String>> =
        std::collections::HashMap::new();
    let empty_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    let empty_entries: BTreeMap<String, usize> = BTreeMap::new();
    let empty_node_index: BTreeMap<String, usize> = BTreeMap::new();
    let empty_resume: BTreeMap<usize, Range<usize>> = BTreeMap::new();
    let byte_map_inputs = crate::bytecode::k2node_byte_map::K2NodeByteMapInputs {
        asset,
        export_names,
        bytecode,
        name_table,
        ue5,
        node_classes,
        macro_names,
        node_to_reaching_events: &empty_reaching,
        event_owned_ranges: &empty_ranges,
        mem_to_disk: fn_mem_to_disk,
        event_entries: &empty_entries,
        event_node_index: &empty_node_index,
        resume_blocks: &empty_resume,
        graph: &fn_graph,
        scope: crate::bytecode::k2node_byte_map::GraphScope::FunctionPage(function_name),
    };
    let byte_map = crate::bytecode::k2node_byte_map::build_k2node_byte_map(&byte_map_inputs);

    (body, byte_map)
}

/// Apply the transform pipeline to every function and event body.
///
/// Transform order is documented per-pass in `apply_transform_stack_to_body`.
fn apply_transform_stack(functions: &mut [Function], events: &mut [Event]) {
    for function in functions {
        apply_transform_stack_to_body(&mut function.body);
        // Functions return implicitly at the tail; the explicit
        // Stmt::Return left over from the literal opcode walk is visual
        // noise. Events legitimately end in returns (multicast delegate
        // calls, etc.) so the strip is function-only.
        crate::bytecode::transforms::dead_stmt::strip_implicit_trailing_return(&mut function.body);
    }
    for event in events {
        apply_transform_stack_to_body(&mut event.body);
    }
}

/// Build the SESE region tree over an already-constructed `cfg`: dominators,
/// postdominators, the linear-merged region tree, and the per-region
/// disk-byte ranges. Threads `cfg` back with the tree and ranges so the
/// caller owns all three for the event decode. Shared by the two public
/// entry points, which differ only in how they build the CFG.
fn region_tree_for_cfg(
    cfg: crate::bytecode::cfg::ControlFlowGraph,
    graph: &crate::bytecode::partition::OpcodeGraph,
    bytecode: &[u8],
    ue5: i32,
    name_table: &crate::binary::NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> (
    crate::bytecode::cfg::ControlFlowGraph,
    crate::bytecode::cfg::region::RegionTree,
    std::collections::BTreeMap<crate::bytecode::cfg::region::RegionId, Vec<Range<usize>>>,
) {
    use crate::bytecode::cfg::dom::{compute_dominators, compute_postdominators};
    use crate::bytecode::cfg::region::{build_region_tree_with_linear_merges, RegionContext};
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);
    let region_ctx = RegionContext {
        bytecode,
        ue5,
        name_table,
        mem_to_disk: Some(mem_to_disk),
    };
    let region_tree =
        build_region_tree_with_linear_merges(&cfg, &idom, &ipostdom, graph, Some(region_ctx));
    let region_byte_ranges = super::ctx::build_region_byte_ranges(&cfg, &region_tree);
    (cfg, region_tree, region_byte_ranges)
}

/// Build the CFG + SESE region tree for one event. The tuple is owned
/// by the caller so the borrowed references in `DecodeCtx` stay valid
/// for the entire event decode.
pub(crate) fn build_event_cfg_and_region_tree(
    entry: usize,
    ranges: &[Range<usize>],
    graph: &crate::bytecode::partition::OpcodeGraph,
    bytecode: &[u8],
    ue5: i32,
    name_table: &crate::binary::NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> (
    crate::bytecode::cfg::ControlFlowGraph,
    crate::bytecode::cfg::region::RegionTree,
    std::collections::BTreeMap<crate::bytecode::cfg::region::RegionId, Vec<Range<usize>>>,
) {
    let cfg = crate::bytecode::cfg::build::build_cfg(graph, entry, ranges);
    region_tree_for_cfg(cfg, graph, bytecode, ue5, name_table, mem_to_disk)
}

/// Inline-scoped variant of [`build_event_cfg_and_region_tree`] that bounds
/// the CFG to the flow-stack-reachable address set (matching the decoder's
/// push/pop coverage) instead of flow-unaware forward reachability. Used
/// ONLY by the cross-event inline body decode (`decode_inlined_shared_body`)
/// so the region path stops absorbing non-flow-reachable scaffold from a
/// sibling arm. Full-event consumers (`decode_owner_event_body`,
/// `prefix_has_user_stmt`, `decode_resume_bodies`) keep using
/// `build_event_cfg_and_region_tree`, where complete forward coverage is
/// correct.
pub(crate) fn build_inline_cfg_and_region_tree_flow_scoped(
    entry: usize,
    ranges: &[Range<usize>],
    graph: &crate::bytecode::partition::OpcodeGraph,
    bytecode: &[u8],
    ue5: i32,
    name_table: &crate::binary::NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> (
    crate::bytecode::cfg::ControlFlowGraph,
    crate::bytecode::cfg::region::RegionTree,
    std::collections::BTreeMap<crate::bytecode::cfg::region::RegionId, Vec<Range<usize>>>,
) {
    let cfg = crate::bytecode::cfg::build::build_cfg_flow_reachable(graph, entry, ranges);
    region_tree_for_cfg(cfg, graph, bytecode, ue5, name_table, mem_to_disk)
}

/// Decode a single event/function body via `decode_region_tree`.
///
/// Returns an empty Vec if the CFG has no blocks.
pub(crate) fn decode_region_body(
    region_tree: &crate::bytecode::cfg::region::RegionTree,
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Vec<crate::bytecode::stmt::Stmt> {
    if cfg.blocks.is_empty() {
        return Vec::new();
    }
    super::region_decode::decode_region_tree(region_tree, cfg, ctx)
}

/// Re-decode the owning event of a shared macro and return its fully
/// recognised statement body, ready to lift a `Stmt::Latch` out of.
///
/// A shared macro that two events converge on is owned (compiled in full)
/// by exactly one of them; the non-owner reaches it via a cross-event
/// jump whose byte range covers only part of the macro footprint. The
/// owning event owns the complete footprint contiguously and folds it
/// into the canonical `Stmt::Latch` via its CFG-driven region decode plus
/// the `recognize_latches` / `derive_flipflop_names` transforms. This
/// rebuilds the owning event's CFG + region tree exactly as the main
/// per-event loop does and runs those transforms.
///
/// `cross_event_inline` is deliberately omitted from the decode ctx: the
/// owner owns the whole macro in its own bytes, so no nested cross-event
/// inline should fire, and omitting it also rules out a cycle back into
/// the calling non-owner event.
///
/// Returns `None` when the owner's entry disk can't be resolved or its CFG
/// is empty.
fn decode_owner_event_body(
    owner_event_name: &str,
    owner_ranges: &[Range<usize>],
    base_ctx: &DecodeCtx,
) -> Option<Vec<crate::bytecode::stmt::Stmt>> {
    let graph = base_ctx.graph?;
    let bytecode = base_ctx.bytecode;
    let name_table = base_ctx.name_table;
    let mem_to_disk = base_ctx.mem_to_disk?;
    let event_entries = base_ctx.event_entries?;

    // Owner entry: `event_entries` is keyed by MEM offset; translate to a
    // disk offset (the coordinate `build_cfg` walks) via `mem_to_disk`,
    // mirroring the main per-event loop's `translated_entries` entry.
    let owner_entry_mem = event_entries
        .iter()
        .find_map(|(&mem, name)| (name == owner_event_name).then_some(mem))?;
    let owner_entry_disk = *mem_to_disk.get(&owner_entry_mem)?;

    let arm_boundaries = prescan_event_tail_jin_arms(
        bytecode,
        base_ctx.ue5,
        name_table,
        mem_to_disk,
        owner_ranges,
        Some(graph),
    );
    let skeleton = build_event_skeleton(
        bytecode,
        base_ctx.ue5,
        name_table,
        mem_to_disk,
        owner_ranges,
        &arm_boundaries,
        Some(graph),
    );
    let (cfg, region_tree, region_byte_ranges) = build_event_cfg_and_region_tree(
        owner_entry_disk,
        owner_ranges,
        graph,
        bytecode,
        base_ctx.ue5,
        name_table,
        mem_to_disk,
    );
    if cfg.blocks.is_empty() {
        return None;
    }
    let claimed: RefCell<BTreeMap<usize, super::ctx::Claim>> = RefCell::new(BTreeMap::new());
    let synth_ctx = DecodeCtx {
        mem_to_disk: base_ctx.mem_to_disk,
        event_entries: base_ctx.event_entries,
        function_signatures: base_ctx.function_signatures,
        owned_ranges: Some(owner_ranges),
        skeleton: Some(&skeleton),
        claimed: Some(&claimed),
        graph: Some(graph),
        cfg: Some(&cfg),
        region_tree: Some(&region_tree),
        region_byte_ranges: Some(&region_byte_ranges),
        k2node_byte_map: base_ctx.k2node_byte_map,
        ..DecodeCtx::new(
            bytecode,
            name_table,
            base_ctx._imports,
            base_ctx._export_names,
            base_ctx.ue5,
        )
    };
    let mut body = super::region_decode::decode_region_tree(&region_tree, &cfg, &synth_ctx);
    // Latch subset of the main transform stack, run directly here and in the
    // same relative order the stack uses (asserted by transform_stack's
    // recognize_latches_before_flipflop_naming test).
    crate::bytecode::transforms::latch_recognition::recognize_latches(&mut body);
    crate::bytecode::transforms::flipflop_naming::derive_flipflop_names(&mut body);
    Some(body)
}

/// Re-decode the owning event of a shared FlipFlop and return its
/// recognised `Stmt::Latch { FlipFlop }`, cloned for inlining under a
/// non-owner converging event. See [`decode_owner_event_body`] for the
/// "owner owns the full footprint" rationale.
///
/// Returns `None` when the owner can't be decoded or produces no
/// recognised FlipFlop latch (the caller then renders empty rather than a
/// partial body).
pub(crate) fn synthesize_owner_flipflop(
    owner_event_name: &str,
    owner_ranges: &[Range<usize>],
    base_ctx: &DecodeCtx,
) -> Option<crate::bytecode::stmt::Stmt> {
    use crate::bytecode::stmt::{LatchKind, Stmt};
    let body = decode_owner_event_body(owner_event_name, owner_ranges, base_ctx)?;
    first_latch_matching(&body, |kind| matches!(kind, LatchKind::FlipFlop { .. })).map(|stmt| {
        debug_assert!(matches!(
            stmt,
            Stmt::Latch {
                kind: LatchKind::FlipFlop { .. },
                ..
            }
        ));
        stmt.clone()
    })
}

/// Re-decode the owning event of a shared DoOnce and return its recognised
/// DoOnce latch display name (e.g. `DoOnce_3`), so a non-owner inline can
/// render the same gate name the owner does instead of the first call name
/// the local synthesis would otherwise pick.
///
/// Returns `None` when the owner can't be decoded or has no recognised
/// DoOnce latch.
pub(crate) fn synthesize_owner_doonce_name(
    owner_event_name: &str,
    owner_ranges: &[Range<usize>],
    base_ctx: &DecodeCtx,
) -> Option<String> {
    use crate::bytecode::stmt::{LatchKind, Stmt};
    let body = decode_owner_event_body(owner_event_name, owner_ranges, base_ctx)?;
    let latch = first_latch_matching(&body, |kind| matches!(kind, LatchKind::DoOnce { .. }))?;
    match latch {
        Stmt::Latch {
            kind: LatchKind::DoOnce { name, .. },
            ..
        } => Some(name.clone()),
        _ => None,
    }
}

/// First `Stmt::Latch` anywhere in `stmts` (recursing through container
/// bodies) whose `LatchKind` satisfies `kind_pred`.
fn first_latch_matching(
    stmts: &[crate::bytecode::stmt::Stmt],
    kind_pred: impl Fn(&crate::bytecode::stmt::LatchKind) -> bool + Copy,
) -> Option<&crate::bytecode::stmt::Stmt> {
    use crate::bytecode::stmt::Stmt;
    for stmt in stmts {
        if let Stmt::Latch { kind, .. } = stmt {
            if kind_pred(kind) {
                return Some(stmt);
            }
        }
        for slice in stmt.child_bodies_structural() {
            if let Some(found) = first_latch_matching(slice, kind_pred) {
                return Some(found);
            }
        }
    }
    None
}

/// Decode every latent-call resume continuation harvested by the
/// partitioner.
///
/// `resume_blocks` maps each latent call's disk offset to the byte
/// range covering its resume body. For each entry, build a sub-CFG +
/// SESE region tree over the resume chunk and run the region-tree path
/// (`decode_region_body`) to recover the statement vector, mirroring
/// `decode_owner_event_body`. Returns the per-call statement vectors
/// keyed by the same disk offset, so the emitter can look up the
/// continuation by `Stmt::Call.offset` when rendering.
///
/// Resume bodies are orphans, the runtime arrives via the latent
/// action callback rather than a synchronous JUMP, so they don't carry
/// an initial flow stack (`Vec::new()`).
#[allow(clippy::too_many_arguments)]
fn decode_resume_bodies(
    asset: &ParsedAsset,
    resume_blocks: &BTreeMap<usize, Range<usize>>,
    bytecode: &[u8],
    ue5: i32,
    name_table: &crate::binary::NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
    graph: &crate::bytecode::partition::OpcodeGraph,
    export_names: &[String],
) -> BTreeMap<usize, Vec<crate::bytecode::stmt::Stmt>> {
    let mut output: BTreeMap<usize, Vec<crate::bytecode::stmt::Stmt>> = BTreeMap::new();
    for (&call_offset, range) in resume_blocks {
        if range.start >= bytecode.len() || range.is_empty() {
            continue;
        }
        let owned = [range.clone()];
        let skeleton = build_skeleton(
            bytecode,
            ue5,
            name_table,
            mem_to_disk,
            range.clone(),
            &[],
            Some(graph),
        );
        // Mirror `decode_owner_event_body`: build a sub-CFG + SESE region
        // tree for the contiguous resume range and decode via the
        // region-tree path. The resume entry is the range start (the
        // runtime arrives via the latent action callback).
        // `decode_region_body` returns an empty Vec for an empty CFG.
        let (cfg, region_tree, region_byte_ranges) = build_event_cfg_and_region_tree(
            range.start,
            &owned,
            graph,
            bytecode,
            ue5,
            name_table,
            mem_to_disk,
        );
        let claimed: RefCell<BTreeMap<usize, super::ctx::Claim>> = RefCell::new(BTreeMap::new());
        let ctx = DecodeCtx {
            mem_to_disk: Some(mem_to_disk),
            function_signatures: Some(&asset.function_signatures),
            owned_ranges: Some(&owned),
            skeleton: Some(&skeleton),
            claimed: Some(&claimed),
            graph: Some(graph),
            cfg: Some(&cfg),
            region_tree: Some(&region_tree),
            region_byte_ranges: Some(&region_byte_ranges),
            ..DecodeCtx::new(bytecode, name_table, &asset.imports, export_names, ue5)
        };
        let body = decode_region_body(&region_tree, &cfg, &ctx);
        output.insert(call_offset, body);
    }
    output
}
