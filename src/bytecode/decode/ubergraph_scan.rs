//! Ubergraph dispatch scanning and event-entry discovery.
//!
//! Decodes function-export dispatch stubs to recover event entry
//! offsets, translates them mem -> disk, builds the K2Node class/macro
//! indices the cross-event inline classifier needs, and constructs the
//! per-event structure skeleton (including tail-JIN arm prescan).

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::opcodes::EX_JUMP_IF_NOT;
use crate::bytecode::partition::{opcode_length_at, EventEntry, OpcodeGraph};
use crate::bytecode::structure::{build_skeleton, StructureSkeleton};
use crate::resolve::{class_of, resolve_index};
use crate::types::ParsedAsset;

use super::block::decode_linear;
use super::ctx::DecodeCtx;
use super::header::lookup_export_bytecode;
use crate::bytecode::names::{EXECUTE_UBERGRAPH_PREFIX, K2NODE_MACRO_INSTANCE};

/// Result of decoding one function export's flat dispatch stream looking
/// for `ExecuteUbergraph_<name>` calls.
struct UbergraphDispatchScan {
    /// Memory-coordinate entry offsets, one per `ExecuteUbergraph_<name>(N)`
    /// call, in decode order. The literal `N` is the runtime's mem
    /// coordinate, so these flow unchanged into `translate_entries_to_disk`.
    entry_offsets: Vec<usize>,
    /// True when the export's only meaningful statements are
    /// `ExecuteUbergraph_<name>` dispatch calls and `[persistent]`
    /// parameter copies (plus the trailing return). Such pure-dispatch
    /// stubs are skipped during standalone function decode so they don't
    /// duplicate the events the ubergraph partition already emits.
    is_pure_dispatch: bool,
}

/// Decode a function export's bytecode as a flat dispatch stream and
/// extract its `ExecuteUbergraph_<ug_name>` call entry offsets plus a
/// pure-dispatch verdict.
///
/// This re-sources, from the decoder's own walk of the raw bytes, the
/// two facts that ubergraph partitioning needs: which mem offsets are
/// event entries, and which function exports are pure dispatch stubs. The
/// raw bytes come from `asset.bytecode_by_export`, so this depends on no
/// pre-rendered text.
///
/// Returns `None` when the export has no captured bytecode bytes.
fn scan_ubergraph_dispatch(
    asset: &ParsedAsset,
    export_names: &[String],
    export_index: usize,
    name: &str,
    ug_name: &str,
    name_table: &NameTable,
    ue5: i32,
) -> Option<UbergraphDispatchScan> {
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    let bytecode = lookup_export_bytecode(asset, export_index, name)?;

    // Dispatch stubs are flat: `[persistent]` copies, one or more
    // `ExecuteUbergraph_*` calls, and a trailing return. No jumps, so the
    // bytecode mem and disk coordinates coincide and no mem-to-disk map is
    // needed; the int-literal argument is already the mem coordinate the
    // text path reported. `function_signatures` is threaded so OUT-param
    // wrapping matches the rest of the decoder, though dispatch stubs have
    // no OUT params in practice.
    let claimed: RefCell<BTreeMap<usize, super::ctx::Claim>> = RefCell::new(BTreeMap::new());
    let scan_ctx = DecodeCtx {
        function_signatures: Some(&asset.function_signatures),
        claimed: Some(&claimed),
        ..DecodeCtx::new(&bytecode, name_table, &asset.imports, export_names, ue5)
    };

    let stmts = decode_linear(0, &scan_ctx);

    // An `ExecuteUbergraph_<ug_name>(N)` call decodes to
    // `Stmt::Call { func: Expr::Var(ug_name), args: [Expr::Literal("N")] }`.
    let is_ubergraph_call = |stmt: &Stmt| -> Option<usize> {
        let Stmt::Call { func, args, .. } = stmt else {
            return None;
        };
        let Expr::Var(callee) = func else {
            return None;
        };
        if callee != ug_name {
            return None;
        }
        match args.first() {
            Some(Expr::Literal(value)) => value.parse::<usize>().ok(),
            _ => None,
        }
    };

    // A `[persistent]` parameter copy decodes to an assignment whose rhs is
    // wrapped in `Expr::Persistent` (EX_LET_VALUE_ON_PERSISTENT_FRAME).
    let is_persistent_copy = |stmt: &Stmt| -> bool {
        matches!(
            stmt,
            Stmt::Assignment {
                rhs: Expr::Persistent(_),
                ..
            }
        )
    };

    let mut entry_offsets = Vec::new();
    let mut has_ubergraph_call = false;
    let mut only_dispatch_or_persistent = true;
    for stmt in &stmts {
        if let Some(offset) = is_ubergraph_call(stmt) {
            entry_offsets.push(offset);
            has_ubergraph_call = true;
            continue;
        }
        // The trailing return is structural noise; drop it.
        if matches!(stmt, Stmt::Return { .. }) {
            continue;
        }
        if is_persistent_copy(stmt) {
            continue;
        }
        only_dispatch_or_persistent = false;
    }

    Some(UbergraphDispatchScan {
        entry_offsets,
        is_pure_dispatch: has_ubergraph_call && only_dispatch_or_persistent,
    })
}

/// Translate event entries from memory coordinates to disk coordinates
/// using a precomputed mem-to-disk offset map.
///
/// Entry offsets in the bytecode property text don't always land exactly on
/// a recorded opcode boundary, because the literal we read from
/// `ExecuteUbergraph_Name(N)` is the runtime's mem coordinate **before** the
/// runtime applies a few extra adjustments. We tolerate that: if the exact
/// `mem_offset` isn't a key, fall forward to the next boundary within
/// [`ENTRY_FUZZY_TOLERANCE`] bytes.
///
/// Entries that still have no resolution are dropped with a stderr
/// diagnostic so partition validation doesn't fail spuriously.
pub(super) fn translate_entries_to_disk(
    entries: &[EventEntry],
    mem_to_disk: &std::collections::BTreeMap<usize, usize>,
    ug_name: &str,
) -> Vec<EventEntry> {
    /// Maximum forward fuzz when an entry doesn't land on an exact opcode
    /// boundary in mem coordinates.
    const ENTRY_FUZZY_TOLERANCE: usize = 16;

    entries
        .iter()
        .filter_map(|entry| {
            if let Some(&disk_offset) = mem_to_disk.get(&entry.mem_offset) {
                return Some(EventEntry {
                    name: entry.name.clone(),
                    mem_offset: disk_offset,
                    export_index: entry.export_index,
                });
            }

            // Forward fuzzy resolution: pick the smallest mem key strictly
            // greater than the requested offset, within tolerance.
            let upper = entry.mem_offset + ENTRY_FUZZY_TOLERANCE;
            if let Some((&matched_mem, &disk_offset)) =
                mem_to_disk.range(entry.mem_offset..=upper).next()
            {
                eprintln!(
                    "decode: event '{}' fuzzy-resolved 0x{:x} -> 0x{:x} (disk 0x{:x}) in {}",
                    entry.name, entry.mem_offset, matched_mem, disk_offset, ug_name
                );
                return Some(EventEntry {
                    name: entry.name.clone(),
                    mem_offset: disk_offset,
                    export_index: entry.export_index,
                });
            }

            eprintln!(
                "decode: event '{}' mem_offset 0x{:x} has no disk mapping in {}",
                entry.name, entry.mem_offset, ug_name
            );
            None
        })
        .collect()
}

/// Collect event entry offsets for the ubergraph by decoding each
/// non-ubergraph function export's bytecode and recording the
/// `ExecuteUbergraph_<ug_name>(N)` dispatch-call entry offsets.
///
/// The offsets are memory coordinates, matching the runtime's view; the
/// caller translates them to disk coordinates before partitioning.
pub(super) fn collect_event_entries(
    asset: &ParsedAsset,
    export_names: &[String],
    ug_name: &str,
    name_table: &NameTable,
    ue5: i32,
) -> Vec<EventEntry> {
    let mut entries: Vec<EventEntry> = Vec::new();
    let mut seen_offsets = std::collections::BTreeSet::new();

    for (export_idx, (hdr, _props)) in asset.exports.iter().enumerate() {
        let class = class_of(&asset.imports, export_names, hdr);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX) {
            continue;
        }

        let scan = match scan_ubergraph_dispatch(
            asset,
            export_names,
            export_idx + 1,
            &hdr.object_name,
            ug_name,
            name_table,
            ue5,
        ) {
            Some(scan) => scan,
            None => continue,
        };
        for offset in scan.entry_offsets {
            if seen_offsets.insert(offset) {
                entries.push(EventEntry {
                    name: hdr.object_name.clone(),
                    mem_offset: offset,
                    export_index: export_idx + 1,
                });
            }
        }
    }

    entries.sort_by_key(|entry| entry.mem_offset);
    entries
}

/// Build the event-name to K2Node export id map by scanning all
/// event-class K2Nodes in the asset. Recognised event classes match the
/// set used by the cross-event inline classifier
/// (`is_event_entry_class` in `cross_event_inline.rs`).
///
/// Event nodes carry the bound function name on their
/// `CustomFunctionName` property (K2Node_CustomEvent /
/// K2Node_InputAxisEvent / K2Node_ComponentBoundEvent) or
/// `EventReference.MemberName` (K2Node_Event), matching the lookup in
/// `output_summary/edgraph.rs::collect_event_position`.
///
/// `K2Node_InputAction` nodes carry only `InputActionName` (e.g. "Crouch").
/// The compiled function name (`InpActEvt_Crouch_K2Node_InputActionEvent_2`)
/// is derived separately by scanning function exports whose names follow the
/// `InpActEvt_{action}_K2Node_InputActionEvent_{N}` pattern and extracting
/// the action name to match against the `InputActionName` property.
pub(crate) fn build_event_node_index(
    asset: &ParsedAsset,
    export_names: &[String],
) -> BTreeMap<String, usize> {
    use crate::prop_query::find_prop;
    use crate::resolve::short_class;
    use crate::types::PropValue;

    let mut index: BTreeMap<String, usize> = BTreeMap::new();

    // First pass: classes whose CustomFunctionName or EventReference.MemberName
    // directly gives the ubergraph event function name.
    for (zero_based, (hdr, props)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = class_of(&asset.imports, export_names, hdr);
        let class = short_class(&class_full);
        let event_name = match class.as_str() {
            "K2Node_CustomEvent" | "K2Node_InputAxisEvent" | "K2Node_ComponentBoundEvent" => {
                find_prop(props, "CustomFunctionName").and_then(|prop| match &prop.value {
                    PropValue::Name(name) => Some(name.clone()),
                    _ => None,
                })
            }
            "K2Node_Event" => find_prop(props, "EventReference")
                .and_then(|prop| match &prop.value {
                    PropValue::Struct { fields, .. } => find_prop(fields, "MemberName"),
                    _ => None,
                })
                .and_then(|prop| match &prop.value {
                    PropValue::Name(name) => Some(name.clone()),
                    _ => None,
                }),
            _ => None,
        };
        if let Some(name) = event_name {
            index.insert(name, one_based);
        }
    }

    // Second pass: K2Node_InputAction nodes. These nodes carry only
    // `InputActionName` (e.g. "Crouch"), not the full compiled function name.
    // Build an action-name -> node-id lookup, then scan function exports whose
    // names match `InpActEvt_{action}_K2Node_InputActionEvent_{N}` to derive
    // the event key and link it to the EdGraph node.
    let action_node_ids: BTreeMap<String, usize> = asset
        .exports
        .iter()
        .enumerate()
        .filter_map(|(zero_based, (hdr, props))| {
            let class_full = class_of(&asset.imports, export_names, hdr);
            if short_class(&class_full) != "K2Node_InputAction" {
                return None;
            }
            let action_name = find_prop(props, "InputActionName").and_then(|prop| {
                if let PropValue::Name(name) = &prop.value {
                    Some(name.clone())
                } else {
                    None
                }
            })?;
            Some((action_name, zero_based + 1))
        })
        .collect();

    if !action_node_ids.is_empty() {
        for (hdr, _) in &asset.exports {
            let class_full = class_of(&asset.imports, export_names, hdr);
            if !class_full.ends_with(".Function") {
                continue;
            }
            if let Some(action_name) = extract_inp_act_evt_action(&hdr.object_name) {
                if let Some(&node_id) = action_node_ids.get(action_name) {
                    index.insert(hdr.object_name.clone(), node_id);
                }
            }
        }
    }

    index
}

/// Extract the action name from a compiled input-action event function name.
///
/// UE compiles `K2Node_InputAction` nodes into event functions named
/// `InpActEvt_{ActionName}_K2Node_InputActionEvent_{N}` (e.g.
/// `InpActEvt_Crouch_K2Node_InputActionEvent_2`). Returns the `{ActionName}`
/// slice when the name matches this pattern, or `None` otherwise.
fn extract_inp_act_evt_action(function_name: &str) -> Option<&str> {
    const PREFIX: &str = "InpActEvt_";
    const SUFFIX_MARKER: &str = "_K2Node_InputActionEvent_";
    let after_prefix = function_name.strip_prefix(PREFIX)?;
    let marker_pos = after_prefix.rfind(SUFFIX_MARKER)?;
    Some(&after_prefix[..marker_pos])
}

/// Build a 1-based-export-index to short class name map for every
/// K2Node export. Lets the cross-event inline classifier check
/// `K2Node_Knot` passthroughs and event-entry class membership without
/// re-resolving import indices per call.
pub(super) fn build_node_class_names(
    asset: &ParsedAsset,
    export_names: &[String],
) -> std::collections::HashMap<usize, String> {
    use crate::resolve::short_class;
    let mut names = std::collections::HashMap::with_capacity(asset.exports.len());
    for (zero_based, (hdr, _)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = class_of(&asset.imports, export_names, hdr);
        names.insert(one_based, short_class(&class_full));
    }
    names
}

/// Build a 1-based-export-index to macro short name map for every
/// K2Node_MacroInstance export with a resolvable
/// `MacroGraphReference.MacroGraph` reference.
pub(super) fn build_macro_names(
    asset: &ParsedAsset,
    export_names: &[String],
) -> std::collections::HashMap<usize, String> {
    use crate::prop_query::find_prop;
    use crate::resolve::short_class;
    use crate::types::PropValue;

    let mut macro_names = std::collections::HashMap::new();
    for (zero_based, (hdr, props)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = class_of(&asset.imports, export_names, hdr);
        if short_class(&class_full) != K2NODE_MACRO_INSTANCE {
            continue;
        }
        let Some(macro_ref) = find_prop(props, "MacroGraphReference") else {
            continue;
        };
        let PropValue::Struct { fields, .. } = &macro_ref.value else {
            continue;
        };
        let Some(graph) = find_prop(fields, "MacroGraph") else {
            continue;
        };
        let PropValue::Object(graph_idx) = graph.value else {
            continue;
        };
        let resolved = resolve_index(&asset.imports, export_names, graph_idx);
        if let Some(macro_name) = resolved.rsplit(['.', ':']).next() {
            macro_names.insert(one_based, macro_name.to_string());
        }
    }
    macro_names
}

/// Discover tail-JIN displaced-arm ranges in an event's bytecode so
/// `build_event_skeleton` can bound chain pin partitions at arm walls.
///
/// Uses a two-pass approach: a throwaway first-pass skeleton (no arm
/// boundaries) is built so `tail_jin_arm_ranges` can use chain pin
/// partitions to compute authoritative arm extents. The second-pass
/// real skeleton consumes these extents and partitions accordingly.
///
/// Without this pass, chain pin partitions span outside arms and the
/// arm body decode emits empty pin scaffolds (an InpAxisEvt failure
/// mode: gate-set / init-set Stmts attributed to the outer chain
/// instead of the arm).
pub(super) fn prescan_event_tail_jin_arms(
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &std::collections::BTreeMap<usize, usize>,
    ranges: &[Range<usize>],
    graph: Option<&OpcodeGraph>,
) -> Vec<Range<usize>> {
    let owner_start = ranges.iter().map(|range| range.start).min().unwrap_or(0);
    let owner_end = ranges.iter().map(|range| range.end).max().unwrap_or(0);
    if owner_start >= owner_end {
        return Vec::new();
    }
    let probe_skeleton = build_skeleton(
        bytecode,
        ue5,
        name_table,
        mem_to_disk,
        owner_start..owner_end,
        &[],
        graph,
    );
    let probe_ctx = DecodeCtx {
        mem_to_disk: Some(mem_to_disk),
        owned_ranges: Some(ranges),
        skeleton: Some(&probe_skeleton),
        ..DecodeCtx::new(bytecode, name_table, &[], &[], ue5)
    };
    let mut arms: Vec<Range<usize>> = Vec::new();
    for range in ranges {
        let mut cursor = range.start;
        while cursor < range.end {
            if cursor >= bytecode.len() {
                break;
            }
            let opcode = bytecode[cursor];
            if opcode == EX_JUMP_IF_NOT {
                if let Some(arms_info) =
                    super::branch::tail_jin_arm_ranges(cursor, range.end, &probe_ctx)
                {
                    arms.push(arms_info.then_range.0..arms_info.then_range.1);
                    arms.push(arms_info.else_range.0..arms_info.else_range.1);
                    // Compound-DoOnce body regions are claimed at decode
                    // time so the user body decodes inside the THEN arm;
                    // they aren't arm walls for the skeleton (chain BFS
                    // shouldn't fence them off, the body bytes are
                    // contiguous user-code reachable via gate-open jump).
                }
            }
            let length = opcode_length_at(cursor, bytecode, ue5, name_table);
            if length == 0 {
                break;
            }
            cursor += length;
        }
    }
    arms.sort_by_key(|range| range.start);
    arms
}

/// Build a `StructureSkeleton` for one ubergraph event. The owner range
/// spans every disk-byte range owned by the event (the partition emits
/// disjoint ranges when sibling events split a body), so the BFS sees
/// the full scope of any push chain whose pin partitions cross the
/// gaps. Reachability inside `build_skeleton` confines the chain to
/// what the opcode graph actually reaches, so unreachable bytes from a
/// sibling event don't bleed in.
pub(super) fn build_event_skeleton(
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &std::collections::BTreeMap<usize, usize>,
    ranges: &[Range<usize>],
    arm_boundaries: &[Range<usize>],
    graph: Option<&OpcodeGraph>,
) -> StructureSkeleton {
    let owner_start = ranges.iter().map(|range| range.start).min().unwrap_or(0);
    let owner_end = ranges.iter().map(|range| range.end).max().unwrap_or(0);
    if owner_start >= owner_end {
        return StructureSkeleton::default();
    }
    build_skeleton(
        bytecode,
        ue5,
        name_table,
        mem_to_disk,
        owner_start..owner_end,
        arm_boundaries,
        graph,
    )
}

/// True if a function export only dispatches into the ubergraph, i.e. its
/// meaningful bytecode is one or more `ExecuteUbergraph_Name(N)` calls
/// optionally preceded by `[persistent]` parameter copies. Compiled input-
/// event stubs (`InpActEvt_*`, `InpAxisEvt_*`) match this shape and are
/// skipped during standalone function decoding so they don't duplicate the
/// friendly named events the ubergraph partition already emits.
///
/// Decided from the decoder's own walk of the export's raw bytecode, not
/// from any pre-rendered text.
pub(super) fn is_ubergraph_stub(
    asset: &ParsedAsset,
    export_names: &[String],
    export_index: usize,
    name: &str,
    ug_name: &str,
    name_table: &NameTable,
    ue5: i32,
) -> bool {
    scan_ubergraph_dispatch(
        asset,
        export_names,
        export_index,
        name,
        ug_name,
        name_table,
        ue5,
    )
    .map(|scan| scan.is_pure_dispatch)
    .unwrap_or(false)
}
