//! K2Node-pin-augmented event seeding for the partition layer.
//!
//! Additive parallel helper. Builds a map from bytecode disk
//! offset to the set of event names whose EdGraph exec-pin tree reaches the
//! K2Node compiled at that offset. The partition layer logs divergences
//! against this attribution but does not override its tie-break.
//!
//! The shape recognised is `K2Node_CallFunction` matched on
//! `FunctionReference.MemberName` against the short callee name carried by
//! the bytecode's call opcodes (`EX_VirtualFunction`,
//! `EX_LocalVirtualFunction`, `EX_FinalFunction`, `EX_LocalFinalFunction`,
//! `EX_CallMath`). Other K2Node subclasses (variable get/set, macro
//! instance, event nodes themselves) are out of scope.
//!
//! Several call sites in the graph can share one function name (two
//! `K2Node_CallFunction` nodes named "SpawnMenu" wired from different
//! event entries). When the bytecode has only one compiled instance of
//! that function call, every K2Node sharing the name maps to the same
//! disk offset; the attribution at that offset is the union of each
//! reaching-event set.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::binary::NameTable;
use crate::bytecode::decode::walker::{walk_opcode, OpcodeVisitor, WalkCtx};
use crate::bytecode::names::{normalize_lwc_name, strip_guid_suffix};
use crate::bytecode::opcodes::{
    EX_CALL_MATH, EX_FINAL_FUNCTION, EX_LOCAL_FINAL_FUNCTION, EX_LOCAL_VIRTUAL_FUNCTION,
    EX_VIRTUAL_FUNCTION,
};
use crate::bytecode::resolve::resolve_bc_obj;
use crate::prop_query::find_struct_field_str;
use crate::resolve::{class_of, short_class};
use crate::types::ParsedAsset;

/// Disk-offset to event-name-set mapping built from K2Node exec-pin
/// reachability. The keys are bytecode disk offsets (as produced by the
/// partition's `bfs_reachable`). The values are non-empty sets of event
/// names whose entry K2Node reaches a `K2Node_CallFunction` whose
/// `FunctionReference.MemberName` matches the callee compiled at that
/// offset.
///
/// Offsets that do not match any recognised K2Node shape (or whose callee
/// short name does not appear in any `K2Node_CallFunction`) simply have
/// no entry. The partition layer treats missing entries as "no
/// pin-attribution opinion" and keeps its lowest-offset tie-break.
pub struct PinEventAttribution {
    pub attribution: BTreeMap<usize, BTreeSet<String>>,
}

impl PinEventAttribution {
    /// An attribution with no recorded offsets. Used by probe tests that
    /// need to invoke the partition with the pin-attribution parameter
    /// without building a real attribution map.
    pub fn empty() -> Self {
        Self {
            attribution: BTreeMap::new(),
        }
    }
}

/// Build a [`PinEventAttribution`] for one ubergraph's bytecode.
///
/// Inputs:
/// - `asset`: source of K2Node export data (class, `FunctionReference`).
/// - `export_names`: 0-based table of export object names, used by
///   `resolve_index` / `resolve_bc_obj` when resolving the bytecode's
///   call-opcode operands.
/// - `node_to_reaching_events`: per-K2Node set of event names whose
///   entry reaches it via exec-pin BFS. Built once per ubergraph by
///   [`crate::bytecode::decode::cross_event_inline::build_node_to_reaching_events`].
/// - `bytecode`: the ubergraph's raw disk-coordinate byte slice.
/// - `name_table`: name table used by the walker to read FName operands.
/// - `ue5`: UE5 version for the walker's LWC-aware operand sizing.
///
/// The builder walks every K2Node_CallFunction export once to construct a
/// `member_name to [node_id]` index. It then walks the bytecode using a
/// call-site visitor that records `(disk_offset, callee_short_name)` for
/// every call opcode. For each recorded pair, it looks up the matching
/// K2Nodes by short member name and unions their reaching-event sets.
pub fn build_pin_event_attribution(
    asset: &ParsedAsset,
    export_names: &[String],
    node_to_reaching_events: &HashMap<usize, BTreeSet<String>>,
    bytecode: &[u8],
    name_table: &NameTable,
    ue5: i32,
) -> PinEventAttribution {
    let callfunc_by_member = build_callfunc_member_index(asset, export_names);
    let call_sites = collect_call_sites(bytecode, name_table, ue5, asset, export_names);

    let mut attribution: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    let debug = std::env::var_os("BP_INSPECT_PIN_ATTR_DEBUG").is_some();
    for (disk_offset, callee_short) in call_sites {
        let Some(matching_nodes) = callfunc_by_member.get(&callee_short) else {
            if debug {
                eprintln!(
                    "PIN_ATTR_CALLSITE addr=0x{:x} callee='{}' no_callfunc_node",
                    disk_offset, callee_short
                );
            }
            continue;
        };
        let mut union_events: BTreeSet<String> = BTreeSet::new();
        for &node_id in matching_nodes {
            if let Some(events) = node_to_reaching_events.get(&node_id) {
                union_events.extend(events.iter().cloned());
            }
        }
        if debug {
            eprintln!(
                "PIN_ATTR_CALLSITE addr=0x{:x} callee='{}' nodes={:?} events={:?}",
                disk_offset, callee_short, matching_nodes, union_events
            );
        }
        if !union_events.is_empty() {
            attribution
                .entry(disk_offset)
                .or_default()
                .extend(union_events);
        }
    }

    PinEventAttribution { attribution }
}

/// Build short-member-name to list-of-K2Node-export-ids for every
/// `K2Node_CallFunction` export with a resolvable
/// `FunctionReference.MemberName`. Multiple call-function nodes may share
/// a member name (two distinct call sites of the same function in the
/// graph); the index keeps every node so the attribution can union their
/// reaching-event sets when their compiled call instances share an offset.
///
/// `pub(crate)` so the parallel K2Node-byte map builder
/// (`crate::bytecode::k2node_byte_map`) can reuse the same member-name
/// to node-id index without duplicating the K2Node scan.
pub(crate) fn build_callfunc_member_index(
    asset: &ParsedAsset,
    export_names: &[String],
) -> HashMap<String, Vec<usize>> {
    let mut index: HashMap<String, Vec<usize>> = HashMap::new();
    for (zero_based, (hdr, props)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = class_of(&asset.imports, export_names, hdr);
        if short_class(&class_full) != "K2Node_CallFunction" {
            continue;
        }
        let Some(member_name) = find_struct_field_str(props, "FunctionReference", "MemberName")
        else {
            continue;
        };
        index
            .entry(normalise_member_name(&member_name))
            .or_default()
            .push(one_based);
    }
    index
}

/// Normalise a function name to its short form for cross-source matching.
///
/// Both the K2Node `FunctionReference.MemberName` side and the
/// bytecode-callee side run through this so the comparison is symmetric.
/// GUID suffixes appear on compiler-generated names; LWC suffixes appear
/// on UE5 math intrinsics. Neither alters the K2Node-visible identity.
fn normalise_member_name(raw: &str) -> String {
    normalize_lwc_name(strip_guid_suffix(raw))
}

/// Walk the bytecode collecting `(disk_offset, callee_short_name)` for
/// every call opcode. The walker drives an [`CallSiteVisitor`] that
/// resolves the callee name the same way the expression decoder
/// does, so the resulting strings match what
/// [`build_callfunc_member_index`] derives from the K2Node properties.
///
/// `pub(crate)` so the parallel K2Node-byte map builder
/// (`crate::bytecode::k2node_byte_map`) can reuse the same call-site
/// enumeration when attributing call opcodes to K2Node ids.
pub(crate) fn collect_call_sites(
    bytecode: &[u8],
    name_table: &NameTable,
    ue5: i32,
    asset: &ParsedAsset,
    export_names: &[String],
) -> Vec<(usize, String)> {
    let walk_ctx = WalkCtx::new(bytecode, name_table, ue5);
    let mut visitor = CallSiteVisitor {
        imports: &asset.imports,
        export_names,
        recorded: Vec::new(),
    };
    let mut cursor = 0usize;
    while cursor < bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    visitor.recorded
}

/// Visitor that records the disk offset and resolved callee short name of
/// every call opcode the walker visits. All other opcode hooks fall
/// through to the trait defaults (returning unit). The visitor traverses
/// nested expressions transparently because the walker drives the
/// recursion; nested calls inside a `EX_LET_VALUE_*` RHS will still be
/// recorded as separate entries with their own start offsets.
struct CallSiteVisitor<'a> {
    imports: &'a [crate::types::ImportEntry],
    export_names: &'a [String],
    recorded: Vec<(usize, String)>,
}

impl OpcodeVisitor for CallSiteVisitor<'_> {
    type Result = ();

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) -> Self::Result {}

    fn on_virtual_function(
        &mut self,
        opcode: u8,
        function_name: String,
        _args: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(opcode == EX_VIRTUAL_FUNCTION || opcode == EX_LOCAL_VIRTUAL_FUNCTION);
        let normalised = normalise_member_name(&function_name);
        self.recorded.push((start_offset, normalised));
    }

    fn on_final_function(
        &mut self,
        opcode: u8,
        callee_obj_idx: i32,
        _args: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(
            opcode == EX_FINAL_FUNCTION
                || opcode == EX_LOCAL_FINAL_FUNCTION
                || opcode == EX_CALL_MATH
        );
        let raw = resolve_bc_obj(callee_obj_idx, self.imports, self.export_names);
        let normalised = normalise_member_name(&raw);
        self.recorded.push((start_offset, normalised));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_attribution_has_no_entries() {
        let attribution = PinEventAttribution::empty();
        assert!(attribution.attribution.is_empty());
    }
}
