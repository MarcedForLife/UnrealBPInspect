//! K2Node-to-bytes attribution map.
//!
//! Maps each K2Node export id to the bytecode disk-byte ranges that
//! node compiles into, plus the inverse `disk_offset -> [node_id]`
//! map and the per-event partition records. The map is consumed in
//! production: the cross-event-inline classifier reads
//! [`K2NodeByteMap::partitions`] to decide which inlined body a shared
//! bytecode region belongs to, and `DecodeCtx` threads the map so the
//! decode loop can key macro identity on a gate-LET disk offset.
//!
//! Attribution sources:
//!
//! - `K2Node_CallFunction.FunctionReference.MemberName` matched against
//!   bytecode call opcode callees. Reuses the
//!   `pin_attribution::build_callfunc_member_index` /
//!   `collect_call_sites` pipeline.
//! - `K2Node_MacroInstance` with macro short name `DoOnce` or `IsValid`.
//!   Range derived from pin-LinkedTo reachability through the macro's
//!   exec-output pins. Cross-event-shared instances (knot fan-in) get
//!   one partition with multiple ranges.
//! - `K2Node_VariableSet.VariableReference.MemberName` matched against
//!   the last `FieldPath` segment of `EX_LET*` opcodes.
//! - `K2Node_DynamicCast.TargetType` matched against the resolved class
//!   reference operand of `EX_DynamicCast` / `EX_MetaCast` opcodes.
//!
//! The submodules split the implementation by concern: [`offsets`]
//! holds the call / variable-set / dynamic-cast offset indexing,
//! [`partition`] holds macro-instance / sequence / tracepoint /
//! latent-resume / enclosing-scope partition building, and
//! [`scaffold`] holds the per-opcode gate-LET / JIN / JUMP scaffold-byte
//! attribution layered onto FlipFlop / DoOnce instances.
//!
//! Suffix-correlation hypothesis disproved during investigation:
//! `K2Node_MacroInstance_N` object-name suffix is a per-graph
//! disambiguator, `Temp_bool_*_Variable_N` suffix is a class-property
//! allocator counter, the two are unrelated. Binding goes through
//! EdGraph pin reachability.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::decode::cross_event_inline::K2NodeClass;
use crate::bytecode::names::{normalize_lwc_name, strip_guid_suffix, MacroKind};
use crate::types::ParsedAsset;

use offsets::{attribute_calls, attribute_dynamic_casts, attribute_variable_sets};
use partition::{
    attribute_enclosing_scope_fallback, attribute_execution_sequences,
    attribute_latent_resume_blocks, attribute_macro_instances, attribute_tracepoints,
};
use scaffold::attribute_macro_scaffold_bytes;

mod offsets;
mod partition;
mod scaffold;

/// Macro short names whose pin reachability the partition builder
/// honours (`DoOnce` / `IsValid` / `FlipFlop`). FlipFlop is handled by
/// the later macro-scaffold pass; its pin A + pin B exec downstream are
/// walked by the same BFS that DoOnce/IsValid use. Classifies the raw
/// resolved name through [`MacroKind`] so attribution and downstream
/// offset collection agree on the macro set.
pub(super) fn is_recognised_macro(macro_name: &str) -> bool {
    MacroKind::from_name(macro_name).is_recognised()
}

/// Macro short names whose gate-LET / JIN / JUMP scaffold bytes the
/// `attribute_macro_scaffold_bytes` pass attributes to the
/// MacroInstance. Distinct from [`is_recognised_macro`]: that whitelist
/// drives downstream pin-reachability attribution; this one drives the
/// scaffold-byte attribution layered on top.
pub(super) fn has_gate_scaffold(macro_name: &str) -> bool {
    MacroKind::from_name(macro_name).has_gate_scaffold()
}

/// Per-K2Node attribution record.
///
/// `ranges` may contain multiple disjoint disk-coordinate spans when
/// the compiler splits the node across non-contiguous segments (e.g.
/// cross-event shared body anchored at multiple sites). `owner_events`
/// is the set of every event whose pin-BFS reaches the node. A single
/// K2Node compiles into one bytecode footprint regardless of how many
/// events reach it (e.g. one `K2Node_InputAction` services both the
/// Pressed and Released compiled event functions); the set captures
/// every reaching event so multi-side audits resolve cleanly. Empty
/// set means no event-rooted path reached the node.
#[derive(Clone, Debug)]
pub(crate) struct K2NodePartition {
    pub node_id: usize,
    pub ranges: Vec<Range<usize>>,
    pub owner_events: BTreeSet<String>,
    /// The export class. Read by the partition tests; production keys macro
    /// identity off `macro_kind` rather than the class.
    #[allow(dead_code)]
    pub kind: K2NodeClass,
    /// For `K2NodeClass::MacroInstance` only, the classified macro kind
    /// (`MacroKind::DoOnce`, `MacroKind::IsValid`, ...).
    pub macro_kind: Option<MacroKind>,
    /// Ranges attributed via the SESE enclosing-scope fallback pass.
    /// When non-empty, those ranges were not matched
    /// by any direct attribution rule (call, macro, varset, cast,
    /// Sequence) and were assigned by looking up the enclosing region
    /// or the event entry K2Node. Empty when direct attribution
    /// covered every byte of this partition.
    pub via_fallback: Vec<Range<usize>>,
}

impl K2NodePartition {
    /// New partition with empty `ranges` and no fallback attribution;
    /// the common direct-attribution insert shape.
    fn new(
        node_id: usize,
        owner_events: BTreeSet<String>,
        kind: K2NodeClass,
        macro_kind: Option<MacroKind>,
    ) -> Self {
        K2NodePartition {
            node_id,
            ranges: Vec::new(),
            owner_events,
            kind,
            macro_kind,
            via_fallback: Vec::new(),
        }
    }
}

/// Parallel K2Node-byte attribution map.
///
/// `partitions` is keyed by 1-based export id so each K2Node has at
/// most one entry. `byte_to_node[offset]` holds `Vec<usize>` because
/// shared member names can map one call opcode to several
/// K2Node_CallFunction exports. `unassigned` is reserved for the
/// macro-scaffold pass's audit harness and is always empty in this
/// direct-attribution pass.
#[derive(Default)]
pub(crate) struct K2NodeByteMap {
    pub partitions: BTreeMap<usize, K2NodePartition>,
    // Populated by the builder; read only by the attribution tests
    // (asserting single-owner-per-byte and direct-attribution invariants),
    // not yet by the production decode path.
    #[allow(dead_code)]
    pub byte_to_node: BTreeMap<usize, Vec<usize>>,
    // Reserved for the macro-scaffold audit harness; the builder writes it
    // and the tests assert it stays empty in the direct-attribution pass.
    #[allow(dead_code)]
    pub unassigned: Vec<Range<usize>>,
    /// Gate-LET disk offset -> the single MacroInstance node id the
    /// locality pass attributed it to. Each `EX_LET*` that sets a
    /// DoOnce / FlipFlop gate boolean true is owned
    /// by exactly one MacroInstance (single owner per offset). This is
    /// the identity disambiguator the flow-stack attribution model keys
    /// on: the shared PUSH/POP frame cannot distinguish stacked macros,
    /// but the gate-LET offset can. Populated by
    /// `attribute_macro_scaffold_bytes`; empty when no scaffold macros
    /// exist in the asset.
    pub gate_let_owner_by_offset: BTreeMap<usize, usize>,
    /// Gate-LET disk offset -> the gate boolean leaf name
    /// (`Temp_bool_IsClosed_Variable_*` /
    /// `Temp_bool_Has_Been_Initd_Variable_*`) the `EX_LET*` writes.
    /// Companion to `gate_let_owner_by_offset` so a consumer can report
    /// the gate var alongside the owning node without re-walking the
    /// bytecode.
    pub gate_let_var_by_offset: BTreeMap<usize, String>,
    /// Gate-LET disk offset -> whether the `EX_LET_BOOL` writes `true`
    /// (the GATE-SET that opens the DoOnce, identity-bearing) versus
    /// `false` (the INIT-SEED that resets the gate). The scaffold scan
    /// records every gate-prefixed bool write; only the `true` write is
    /// the macro's gate-set. Without this the init-seed and gate-set are
    /// indistinguishable and a body-before-scaffold macro mis-attributes
    /// to its init-seed offset.
    pub gate_let_is_set_by_offset: BTreeMap<usize, bool>,
}

impl K2NodeByteMap {
    /// Empty map for synthetic test contexts that do not exercise the
    /// K2Node-attribution layer. Currently referenced only from tests; kept
    /// as a named constructor alongside the builder entry points.
    #[allow(dead_code)]
    pub fn empty() -> Self {
        Self::default()
    }

    /// Disk offsets of every gate-SET (`EX_LET_BOOL gate = true`) the
    /// locality pass attributed to `node_id`, in ascending offset order.
    /// Init-seeds (`=false`) are excluded: only the gate-set bears macro
    /// identity. When `gate_var` is `Some`, the result is further
    /// restricted to gate-sets writing that boolean leaf.
    ///
    /// `gate_let_owner_by_offset` is a `BTreeMap`, so iteration already
    /// yields ascending offsets; the returned `Vec` inherits that order
    /// without an explicit sort.
    pub(crate) fn node_gate_set_offsets(
        &self,
        node_id: usize,
        gate_var: Option<&str>,
    ) -> Vec<usize> {
        self.gate_let_owner_by_offset
            .iter()
            .filter(|(_, &owner)| owner == node_id)
            .map(|(&offset, _)| offset)
            .filter(|offset| self.gate_let_is_set_by_offset.get(offset).copied() == Some(true))
            .filter(|offset| match gate_var {
                Some(var) => {
                    self.gate_let_var_by_offset.get(offset).map(String::as_str) == Some(var)
                }
                None => true,
            })
            .collect()
    }

    /// The gate variable named by `node_id`'s in-body `=false` init-seed,
    /// when exactly one distinct such variable sits in `body_spans` (the
    /// candidate's member-block disk extents). `None` when no in-body seed
    /// exists or when several distinct seed variables sit in the body (the
    /// locality pass mixed several macros' seeds in, so the var is not
    /// determinable).
    ///
    /// Callers compute `body_spans` from their CFG; this query touches only
    /// the gate-LET maps so the map-walk lives in one place.
    pub(crate) fn in_body_seed_gate_var(
        &self,
        body_spans: &[Range<usize>],
        node_id: usize,
    ) -> Option<String> {
        let mut seed_vars: BTreeSet<String> = BTreeSet::new();
        for (&offset, &owner) in &self.gate_let_owner_by_offset {
            if owner != node_id {
                continue;
            }
            if self.gate_let_is_set_by_offset.get(&offset).copied() != Some(false) {
                continue;
            }
            if !body_spans.iter().any(|span| span.contains(&offset)) {
                continue;
            }
            if let Some(var) = self.gate_let_var_by_offset.get(&offset) {
                seed_vars.insert(var.clone());
            }
        }
        if seed_vars.len() == 1 {
            seed_vars.into_iter().next()
        } else {
            None
        }
    }
}

/// Inputs the builder needs from the surrounding decode loop.
/// Bundled so adding another attribution source later only grows
/// this type, not the builder signature.
pub(crate) struct K2NodeByteMapInputs<'a> {
    pub asset: &'a ParsedAsset,
    pub export_names: &'a [String],
    pub bytecode: &'a [u8],
    pub name_table: &'a NameTable,
    pub ue5: i32,
    pub node_classes: &'a HashMap<usize, K2NodeClass>,
    pub macro_names: &'a HashMap<usize, String>,
    pub node_to_reaching_events: &'a HashMap<usize, BTreeSet<String>>,
    pub event_owned_ranges: &'a BTreeMap<String, Vec<Range<usize>>>,
    /// Memory-to-disk offset map for the ubergraph stream. Needed by
    /// the push-chain skeleton builder when computing per-event
    /// Sequence chain partitions. Empty for synthetic test contexts.
    pub mem_to_disk: &'a BTreeMap<usize, usize>,
    /// Per-event entry disk offsets. Used by the enclosing-scope
    /// fallback to build the per-event CFG + region
    /// tree from which unassigned bytes get attributed.
    pub event_entries: &'a BTreeMap<String, usize>,
    /// Per-event K2Node id (the event entry K2Node, e.g. the
    /// K2Node_InputAction). Used by the fallback pass as the final
    /// attribution target when no enclosing region match is found.
    pub event_node_index: &'a BTreeMap<String, usize>,
    /// Latent-call resume-block ranges keyed by the originating
    /// Delay-call disk offset. Threaded from the partitioner so the
    /// resume-tagging pass attributes each resume
    /// chunk back to the call's K2Node.
    pub resume_blocks: &'a BTreeMap<usize, Range<usize>>,
    /// Shared opcode graph for the ubergraph stream, built once by the
    /// decode orchestrator. The Sequence, latent-resume, and
    /// enclosing-scope attribution passes ride this instance instead of
    /// rebuilding it from `(bytecode, ue5, name_table, mem_to_disk)`.
    pub graph: &'a crate::bytecode::partition::OpcodeGraph,
}

/// The recorded class for `node_id`, defaulting to `Other` when the node
/// has no class entry.
fn node_class(inputs: &K2NodeByteMapInputs<'_>, node_id: usize) -> K2NodeClass {
    inputs
        .node_classes
        .get(&node_id)
        .copied()
        .unwrap_or(K2NodeClass::Other)
}

/// Construct a [`K2NodeByteMap`] for one ubergraph.
pub(crate) fn build_k2node_byte_map(inputs: &K2NodeByteMapInputs<'_>) -> K2NodeByteMap {
    let mut partitions: BTreeMap<usize, K2NodePartition> = BTreeMap::new();
    let mut byte_to_node: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

    attribute_calls(inputs, &mut partitions, &mut byte_to_node);
    attribute_macro_instances(inputs, &mut partitions);
    let (gate_let_owner_by_offset, gate_let_var_by_offset, gate_let_is_set_by_offset) =
        attribute_macro_scaffold_bytes(inputs, &mut partitions, &mut byte_to_node);
    attribute_variable_sets(inputs, &mut partitions, &mut byte_to_node);
    attribute_dynamic_casts(inputs, &mut partitions, &mut byte_to_node);
    attribute_execution_sequences(inputs, &mut partitions, &mut byte_to_node);
    attribute_latent_resume_blocks(inputs, &mut partitions, &mut byte_to_node);
    attribute_tracepoints(inputs, &mut partitions, &mut byte_to_node);
    let unassigned = attribute_enclosing_scope_fallback(inputs, &mut partitions, &mut byte_to_node);
    finalize_single_owner_per_byte(&mut byte_to_node);

    K2NodeByteMap {
        partitions,
        byte_to_node,
        unassigned,
        gate_let_owner_by_offset,
        gate_let_var_by_offset,
        gate_let_is_set_by_offset,
    }
}

/// Collapse `byte_to_node[offset]` to a single owner per byte. The
/// per-pass clamps prevent intra-pass fan-out; cross-pass overlap is
/// possible when (for example) a Sequence push opcode coincides with
/// a CallFunction attribution, or the enclosing-scope fallback paints
/// a byte already claimed by a direct attribution. Dedupes duplicate
/// node ids first; if more than one distinct owner remains, the
/// lowest export id wins. Matches the tiebreak the per-pass clamp
/// uses, so the rule is consistent across the producer.
fn finalize_single_owner_per_byte(byte_to_node: &mut BTreeMap<usize, Vec<usize>>) {
    for owners in byte_to_node.values_mut() {
        if owners.len() <= 1 {
            continue;
        }
        owners.sort_unstable();
        owners.dedup();
        if owners.len() > 1 {
            owners.truncate(1);
        }
    }
}

/// Returns every event whose pin-BFS reaches a K2Node. A K2Node has
/// one bytecode footprint regardless of how many events reach it (e.g.
/// a `K2Node_InputAction` services both Pressed and Released compiled
/// event functions); returning the full set lets the partition own
/// every reaching event so multi-side audits resolve cleanly. Empty
/// set when no event-rooted path reaches the node.
pub(super) fn owner_events_for_node(
    node_id: usize,
    inputs: &K2NodeByteMapInputs<'_>,
) -> BTreeSet<String> {
    inputs
        .node_to_reaching_events
        .get(&node_id)
        .cloned()
        .unwrap_or_default()
}

/// Merge `additional` into `partition.owner_events`. Used when a later
/// attribution pass discovers extra reaching events for a partition
/// that was created by an earlier pass (e.g. tracepoint pass uses the
/// event-entry K2Node fallback whose owner set must include the
/// current event).
pub(super) fn extend_owner_events(
    partition: &mut K2NodePartition,
    additional: impl IntoIterator<Item = String>,
) {
    for event_name in additional {
        partition.owner_events.insert(event_name);
    }
}

/// Normalise a member name to its short form for cross-source matching.
pub(super) fn normalise_member_name(raw: &str) -> String {
    normalize_lwc_name(strip_guid_suffix(raw))
}

/// Filter a candidate K2Node id set down to a single owner whose
/// owning events physically contain `call_offset`. When several
/// K2Nodes share a member name (the kismet helper case, e.g.
/// `Add_FloatFloat` or a user-named duplicate call) the unfiltered
/// set fans every bytecode site out to every K2Node that bears the
/// name. Clamping via `node_to_reaching_events` plus
/// `event_owned_ranges` keeps the K2Node whose event actually covers
/// the bytes.
///
/// Tiebreak when more than one candidate survives the clamp: the
/// lowest export id wins. Deterministic across runs.
///
/// Fallback when ZERO candidates survive event-scope filtering:
/// the lowest-id candidate from the input set is returned. This
/// happens for K2Nodes that compile bytecode but whose
/// `node_to_reaching_events` entry is empty or absent (e.g. callees
/// that the pin-BFS-from-event-entries didn't reach because the
/// candidate lives in a local function body, not the ubergraph). The
/// fallback is logged when `BP_INSPECT_K2NODE_AUDIT` is set so
/// the fire rate stays visible.
pub(super) fn clamp_to_event_scope(
    candidates: &[usize],
    call_offset: usize,
    inputs: &K2NodeByteMapInputs<'_>,
) -> Vec<usize> {
    if candidates.len() <= 1 {
        return candidates.to_vec();
    }
    let mut survivors: Vec<usize> = candidates
        .iter()
        .copied()
        .filter(|node_id| {
            let Some(events) = inputs.node_to_reaching_events.get(node_id) else {
                return false;
            };
            events.iter().any(|event_name| {
                inputs
                    .event_owned_ranges
                    .get(event_name)
                    .is_some_and(|ranges| ranges.iter().any(|range| range.contains(&call_offset)))
            })
        })
        .collect();
    if survivors.is_empty() {
        if std::env::var_os("BP_INSPECT_K2NODE_AUDIT").is_some_and(|val| !val.is_empty()) {
            eprintln!(
                "k2node clamp: zero survivors at 0x{:x} from {} candidates ({:?}); using lowest-id fallback",
                call_offset,
                candidates.len(),
                candidates,
            );
        }
        let lowest = *candidates.iter().min().expect("non-empty");
        return vec![lowest];
    }
    survivors.sort_unstable();
    survivors.truncate(1);
    survivors
}

/// Insert a range into a sorted-by-start list, deduping exact
/// duplicates. Overlap merging is out of scope here (single-byte
/// spans).
pub(super) fn push_range(ranges: &mut Vec<Range<usize>>, new_range: Range<usize>) {
    if ranges.contains(&new_range) {
        return;
    }
    ranges.push(new_range);
    ranges.sort_by_key(|range| range.start);
}

/// Tight span over a sorted offset set. Returns `start..end+1` where
/// `start` is the minimum offset and `end` is the maximum. Single
/// element returns a single-byte span. Empty input returns `None`.
pub(super) fn span_of(offsets: &BTreeSet<usize>) -> Option<Range<usize>> {
    let first = *offsets.iter().next()?;
    let last = *offsets.iter().next_back()?;
    Some(first..last + 1)
}

/// Clamp offset set to the subset that lies within any of `ranges`.
pub(super) fn clamp_offsets_to_ranges(
    offsets: &BTreeSet<usize>,
    ranges: &[Range<usize>],
) -> BTreeSet<usize> {
    offsets
        .iter()
        .copied()
        .filter(|offset| ranges.iter().any(|range| range.contains(offset)))
        .collect()
}

/// True if any range in `ranges` contains `offset`.
pub(super) fn any_range_contains(ranges: &[Range<usize>], offset: usize) -> bool {
    ranges.iter().any(|range| range.contains(&offset))
}

/// Minimum `|offset - endpoint|` across all `start` / `end` boundaries
/// of `ranges`. Empty ranges produce `usize::MAX` so the caller treats
/// them as the worst possible anchor.
pub(super) fn min_distance_to_ranges(offset: usize, ranges: &[Range<usize>]) -> usize {
    let mut best = usize::MAX;
    for range in ranges {
        let to_start = offset.abs_diff(range.start);
        let to_end = offset.abs_diff(range.end);
        let candidate = to_start.min(to_end);
        if candidate < best {
            best = candidate;
        }
    }
    best
}

/// Disk-coordinate span of one opcode starting at `start`. Clamps the
/// upper bound to the bytecode length so a malformed final opcode
/// can't produce an out-of-range span.
pub(super) fn opcode_span(start: usize, inputs: &K2NodeByteMapInputs<'_>) -> Range<usize> {
    let length = crate::bytecode::partition::opcode_length_at(
        start,
        inputs.bytecode,
        inputs.ue5,
        inputs.name_table,
    );
    let end = start
        .saturating_add(length.max(1))
        .min(inputs.bytecode.len());
    start..end
}

/// Asset-loading attribution tests live in a sibling `local_tests`
/// module that is gitignored and only compiled with the
/// `private-fixtures` feature, so the default build never references the
/// local fixtures by name or path. The pure-logic tests below run in the
/// default build.
// Re-exported for the gitignored `local_tests` module, which pulls these
// in through `use super::*`. The relocation moved the imports into the
// submodules, so the parent scope must surface them again for the tests.
#[cfg(all(test, feature = "private-fixtures"))]
use crate::resolve::{resolve_index, short_class};

#[cfg(all(test, feature = "private-fixtures"))]
mod local_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::opcodes::{EX_TRACEPOINT, EX_WIRE_TRACEPOINT};

    #[test]
    fn empty_map_has_no_entries() {
        let map = K2NodeByteMap::empty();
        assert!(map.partitions.is_empty());
        assert!(map.byte_to_node.is_empty());
        assert!(map.unassigned.is_empty());
    }

    #[test]
    fn empty_asset_inputs_produce_empty_map() {
        let asset = ParsedAsset {
            imports: Vec::new(),
            exports: Vec::new(),
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::new(),
        };
        let export_names: Vec<String> = Vec::new();
        let name_table = NameTable::from_names(Vec::new());
        let node_classes: HashMap<usize, K2NodeClass> = HashMap::new();
        let macro_names: HashMap<usize, String> = HashMap::new();
        let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
        let event_owned_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
        let bytecode: Vec<u8> = Vec::new();
        let mem_to_disk: BTreeMap<usize, usize> = BTreeMap::new();
        let event_entries: BTreeMap<String, usize> = BTreeMap::new();
        let event_node_index: BTreeMap<String, usize> = BTreeMap::new();
        let resume_blocks: BTreeMap<usize, Range<usize>> = BTreeMap::new();
        let graph =
            crate::bytecode::partition::build_opcode_graph(&bytecode, 0, &name_table, &mem_to_disk);
        let inputs = K2NodeByteMapInputs {
            asset: &asset,
            export_names: &export_names,
            bytecode: &bytecode,
            name_table: &name_table,
            ue5: 0,
            node_classes: &node_classes,
            macro_names: &macro_names,
            node_to_reaching_events: &node_to_reaching_events,
            event_owned_ranges: &event_owned_ranges,
            mem_to_disk: &mem_to_disk,
            event_entries: &event_entries,
            event_node_index: &event_node_index,
            resume_blocks: &resume_blocks,
            graph: &graph,
        };
        let map = build_k2node_byte_map(&inputs);
        assert!(map.partitions.is_empty());
        assert!(map.byte_to_node.is_empty());
        assert!(map.unassigned.is_empty());
    }

    /// Tracepoint attribution: every tracepoint opcode inside an
    /// event's owned ranges gets attributed to the event's K2Node id.
    /// The synthetic bytecode below contains EX_TRACEPOINT (0x5E) and
    /// EX_WIRE_TRACEPOINT (0x5A) inside the event's range; assert each
    /// shows up in the event K2Node's partition.
    #[test]
    fn tracepoints_attributed_to_event_node() {
        use crate::bytecode::opcodes::EX_RETURN;
        let asset = ParsedAsset {
            imports: Vec::new(),
            exports: Vec::new(),
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::new(),
        };
        let export_names: Vec<String> = Vec::new();
        let name_table = NameTable::from_names(Vec::new());
        let node_classes: HashMap<usize, K2NodeClass> = HashMap::new();
        let macro_names: HashMap<usize, String> = HashMap::new();
        let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
        let mut event_owned_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
        let bytecode: Vec<u8> = vec![EX_WIRE_TRACEPOINT, EX_TRACEPOINT, EX_RETURN, 0];
        let event_range: Range<usize> = 0..bytecode.len();
        event_owned_ranges.insert("MyEvent".to_string(), vec![event_range]);
        let mem_to_disk: BTreeMap<usize, usize> = BTreeMap::new();
        let event_entries: BTreeMap<String, usize> = BTreeMap::new();
        let mut event_node_index: BTreeMap<String, usize> = BTreeMap::new();
        event_node_index.insert("MyEvent".to_string(), 42);
        let resume_blocks: BTreeMap<usize, Range<usize>> = BTreeMap::new();
        let graph =
            crate::bytecode::partition::build_opcode_graph(&bytecode, 0, &name_table, &mem_to_disk);
        let inputs = K2NodeByteMapInputs {
            asset: &asset,
            export_names: &export_names,
            bytecode: &bytecode,
            name_table: &name_table,
            ue5: 0,
            node_classes: &node_classes,
            macro_names: &macro_names,
            node_to_reaching_events: &node_to_reaching_events,
            event_owned_ranges: &event_owned_ranges,
            mem_to_disk: &mem_to_disk,
            event_entries: &event_entries,
            event_node_index: &event_node_index,
            resume_blocks: &resume_blocks,
            graph: &graph,
        };
        let map = build_k2node_byte_map(&inputs);
        let partition = map
            .partitions
            .get(&42)
            .expect("event node partition recorded");
        assert!(
            partition.ranges.iter().any(|range| range.contains(&0)),
            "EX_WIRE_TRACEPOINT at offset 0 must be attributed"
        );
        assert!(
            partition.ranges.iter().any(|range| range.contains(&1)),
            "EX_TRACEPOINT at offset 1 must be attributed"
        );
        assert!(map.byte_to_node.contains_key(&0));
        assert!(map.byte_to_node.contains_key(&1));
    }

    /// Synthetic resume-block test: when `resume_blocks` is empty, no
    /// extra ranges land in any partition; the empty inputs path
    /// produces an empty map. Real-data coverage is exercised by the
    /// audit harness commit.
    #[test]
    fn latent_resume_empty_resume_blocks_no_effect() {
        let asset = ParsedAsset {
            imports: Vec::new(),
            exports: Vec::new(),
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::new(),
        };
        let export_names: Vec<String> = Vec::new();
        let name_table = NameTable::from_names(Vec::new());
        let node_classes: HashMap<usize, K2NodeClass> = HashMap::new();
        let macro_names: HashMap<usize, String> = HashMap::new();
        let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
        let event_owned_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
        let bytecode: Vec<u8> = Vec::new();
        let mem_to_disk: BTreeMap<usize, usize> = BTreeMap::new();
        let event_entries: BTreeMap<String, usize> = BTreeMap::new();
        let event_node_index: BTreeMap<String, usize> = BTreeMap::new();
        let resume_blocks: BTreeMap<usize, Range<usize>> = BTreeMap::new();
        let graph =
            crate::bytecode::partition::build_opcode_graph(&bytecode, 0, &name_table, &mem_to_disk);
        let inputs = K2NodeByteMapInputs {
            asset: &asset,
            export_names: &export_names,
            bytecode: &bytecode,
            name_table: &name_table,
            ue5: 0,
            node_classes: &node_classes,
            macro_names: &macro_names,
            node_to_reaching_events: &node_to_reaching_events,
            event_owned_ranges: &event_owned_ranges,
            mem_to_disk: &mem_to_disk,
            event_entries: &event_entries,
            event_node_index: &event_node_index,
            resume_blocks: &resume_blocks,
            graph: &graph,
        };
        let map = build_k2node_byte_map(&inputs);
        assert!(map.partitions.is_empty());
    }

    /// Fallback transparency: a partition's `via_fallback` is empty
    /// when direct attribution covered every byte, and populated only
    /// when the enclosing-scope pass actually fired. The empty asset
    /// inputs path leaves every partition (none in this case) with an
    /// empty fallback list; the smoke fixture exercises the same
    /// shape on real data.
    #[test]
    fn fallback_empty_on_empty_inputs() {
        let asset = ParsedAsset {
            imports: Vec::new(),
            exports: Vec::new(),
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::new(),
        };
        let export_names: Vec<String> = Vec::new();
        let name_table = NameTable::from_names(Vec::new());
        let node_classes: HashMap<usize, K2NodeClass> = HashMap::new();
        let macro_names: HashMap<usize, String> = HashMap::new();
        let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
        let event_owned_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
        let bytecode: Vec<u8> = Vec::new();
        let mem_to_disk: BTreeMap<usize, usize> = BTreeMap::new();
        let event_entries: BTreeMap<String, usize> = BTreeMap::new();
        let event_node_index: BTreeMap<String, usize> = BTreeMap::new();
        let resume_blocks: BTreeMap<usize, Range<usize>> = BTreeMap::new();
        let graph =
            crate::bytecode::partition::build_opcode_graph(&bytecode, 0, &name_table, &mem_to_disk);
        let inputs = K2NodeByteMapInputs {
            asset: &asset,
            export_names: &export_names,
            bytecode: &bytecode,
            name_table: &name_table,
            ue5: 0,
            node_classes: &node_classes,
            macro_names: &macro_names,
            node_to_reaching_events: &node_to_reaching_events,
            event_owned_ranges: &event_owned_ranges,
            mem_to_disk: &mem_to_disk,
            event_entries: &event_entries,
            event_node_index: &event_node_index,
            resume_blocks: &resume_blocks,
            graph: &graph,
        };
        let map = build_k2node_byte_map(&inputs);
        assert!(map.partitions.is_empty());
        assert!(map.unassigned.is_empty());
    }

    /// FlipFlop is in the recognised-macro whitelist. Guards against
    /// accidental removal from `is_recognised_macro` during follow-on
    /// edits.
    #[test]
    fn flipflop_in_recognised_macro_whitelist() {
        assert!(is_recognised_macro("FlipFlop"));
        assert!(is_recognised_macro("DoOnce"));
        assert!(is_recognised_macro("IsValid"));
        assert!(!is_recognised_macro("ForEachLoop"));
        assert!(!is_recognised_macro(""));
    }

    /// Multi-owner roundtrip: a K2Node reached by two events (the
    /// shape that paired Pressed/Released `K2Node_InputAction` events
    /// share in real fixtures) produces a single partition whose
    /// `owner_events` carries both event names. Single-owner
    /// resolution would drop one side and surface as `k2node_only`
    /// divergence under the audit harness.
    #[test]
    fn multi_owner_input_action_roundtrip() {
        use crate::bytecode::opcodes::EX_RETURN;
        let asset = ParsedAsset {
            imports: Vec::new(),
            exports: Vec::new(),
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::new(),
        };
        let export_names: Vec<String> = Vec::new();
        let name_table = NameTable::from_names(Vec::new());
        let node_classes: HashMap<usize, K2NodeClass> = HashMap::new();
        let macro_names: HashMap<usize, String> = HashMap::new();
        // K2Node_InputAction id 7 is reached by both the Pressed and
        // Released compiled event functions. Mirrors the editor
        // truth in a real fixture's input graph
        // where one input action node services both compiled events.
        let input_action_node_id: usize = 7;
        let pressed_event = "InpActEvt_Crouch_K2Node_InputActionEvent_2".to_string();
        let released_event = "InpActEvt_Crouch_K2Node_InputActionEvent_3".to_string();
        let mut node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
        let mut reaching_set: BTreeSet<String> = BTreeSet::new();
        reaching_set.insert(pressed_event.clone());
        reaching_set.insert(released_event.clone());
        node_to_reaching_events.insert(input_action_node_id, reaching_set);
        let bytecode: Vec<u8> = vec![EX_WIRE_TRACEPOINT, EX_RETURN, 0];
        let mut event_owned_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
        // Both events claim the same byte range; that's the
        // production shape for paired Pressed/Released events that
        // share a single K2Node footprint.
        let event_range: Range<usize> = 0..bytecode.len();
        event_owned_ranges.insert(pressed_event.clone(), vec![event_range.clone()]);
        event_owned_ranges.insert(released_event.clone(), vec![event_range]);
        let mem_to_disk: BTreeMap<usize, usize> = BTreeMap::new();
        let event_entries: BTreeMap<String, usize> = BTreeMap::new();
        let mut event_node_index: BTreeMap<String, usize> = BTreeMap::new();
        event_node_index.insert(pressed_event.clone(), input_action_node_id);
        event_node_index.insert(released_event.clone(), input_action_node_id);
        let resume_blocks: BTreeMap<usize, Range<usize>> = BTreeMap::new();
        let graph =
            crate::bytecode::partition::build_opcode_graph(&bytecode, 0, &name_table, &mem_to_disk);
        let inputs = K2NodeByteMapInputs {
            asset: &asset,
            export_names: &export_names,
            bytecode: &bytecode,
            name_table: &name_table,
            ue5: 0,
            node_classes: &node_classes,
            macro_names: &macro_names,
            node_to_reaching_events: &node_to_reaching_events,
            event_owned_ranges: &event_owned_ranges,
            mem_to_disk: &mem_to_disk,
            event_entries: &event_entries,
            event_node_index: &event_node_index,
            resume_blocks: &resume_blocks,
            graph: &graph,
        };
        let map = build_k2node_byte_map(&inputs);
        let partition = map
            .partitions
            .get(&input_action_node_id)
            .expect("multi-owner partition recorded");
        assert_eq!(
            partition.owner_events.len(),
            2,
            "expected 2 owners (Pressed + Released), got {:?}",
            partition.owner_events,
        );
        assert!(partition.owner_events.contains(&pressed_event));
        assert!(partition.owner_events.contains(&released_event));
    }
}
