//! Per-opcode gate-LET / JIN / JUMP scaffold-byte attribution.
//!
//! Widens each gate-scaffold `K2Node_MacroInstance` (FlipFlop, DoOnce,
//! and similar latch macros) partition to cover the gate-variable
//! assignment, the re-entry JIN, and the JUMP into the gate body.
//! Disambiguates multiple instances of
//! the same macro kind in one event by bytecode locality against a
//! frozen snapshot of pre-scaffold partition ranges.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::decode::cross_event_inline::K2NodeClass;
use crate::bytecode::decode::walker::{walk_opcode, FieldPath, OpcodeVisitor, WalkCtx};
use crate::bytecode::names::MacroKind;
use crate::bytecode::opcodes::{
    EX_FALSE, EX_JUMP, EX_JUMP_IF_NOT, EX_LET, EX_LET_BOOL, EX_LET_DELEGATE,
    EX_LET_MULTICAST_DELEGATE, EX_LET_OBJ, EX_LET_VALUE_ON_PERSISTENT_FRAME, EX_LET_WEAK_OBJ_PTR,
    EX_TRUE,
};
use crate::bytecode::transforms::latch_recognition::{
    DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX, FLIPFLOP_TOGGLE_PREFIX,
};

use super::{
    any_range_contains, extend_owner_events, has_gate_scaffold, min_distance_to_ranges,
    normalise_member_name, opcode_span, owner_events_for_node, push_range, K2NodeByteMapInputs,
    K2NodePartition,
};

/// Attribute per-opcode scaffold bytes (gate-LET, gate-reading JIN,
/// JUMP into the gate body) of every gate-scaffold
/// `K2Node_MacroInstance` (FlipFlop, DoOnce, and similar) to the macro
/// itself.
///
/// `attribute_macro_instances` derives the macro's main span from
/// downstream pin reachability, but the scaffold opcodes the compiler
/// emits around the macro body (gate variable assignment, the JIN that
/// guards re-entry, the JUMP into the gate-body region) live outside
/// that span and were otherwise claimed by downstream node attribution
/// (or unclaimed when the macro's downstream is itself a macro). This
/// pass widens attribution so the cross-body Latch wrap can pull a
/// macro's full footprint from `K2NodePartition.ranges`.
///
/// Per-opcode `Range { start, end }` spans (not a single widened span)
/// are added; multiple non-contiguous ranges in `partition.ranges` are
/// the documented shape for split-body macros.
///
/// Disambiguation across multiple instances of the same macro kind in
/// one event scope uses **bytecode locality**. The
/// gate-variable suffix (`Temp_bool_*_Variable_<N>`) buckets every
/// scaffold opcode that names the same gate together; for each bucket
/// the partition whose pre-scaffold ranges sit closest to the bucket's
/// gate-LET offsets wins, and every scaffold opcode in that bucket is
/// attributed only to that one candidate. JIN sites use the cond-leaf
/// suffix; JUMP sites inherit the owner of the gate-LET they target.
/// The locality math runs against a frozen snapshot of partition
/// ranges taken before any scaffold attribution lands so per-LET
/// decisions don't drift mid-pass.
///
/// Returns `(let_owner_by_offset, let_var_by_offset, let_is_set_by_offset)`:
/// every gate-LET offset attributed to its single owning MacroInstance
/// node id, the gate boolean leaf name written at that offset, and
/// whether that write sets the gate `true` (GATE-SET) or `false`
/// (INIT-SEED). The caller persists these on [`K2NodeByteMap`] so the
/// flow-stack attribution model can key macro identity on the gate-LET
/// offset (the shared frame cannot distinguish stacked macros, the
/// gate-LET offset can) and tell the identity-bearing gate-set apart
/// from the reset seed.
pub(super) fn attribute_macro_scaffold_bytes(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) -> (
    BTreeMap<usize, usize>,
    BTreeMap<usize, String>,
    BTreeMap<usize, bool>,
) {
    let scaffold_macros = collect_scaffold_macro_instances(inputs);
    if scaffold_macros.is_empty() {
        return (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    }
    let scan = scan_scaffold_opcodes(inputs);
    let event_to_macros = index_macros_by_owning_event(&scaffold_macros, inputs);
    let anchor_ranges = snapshot_candidate_anchor_ranges(&scaffold_macros, partitions);
    let let_var_by_offset: BTreeMap<usize, String> = scan
        .gate_lets
        .iter()
        .map(|gate_let| (gate_let.offset, gate_let.leaf.clone()))
        .collect();
    let let_is_set_by_offset: BTreeMap<usize, bool> = scan
        .gate_lets
        .iter()
        .map(|gate_let| (gate_let.offset, gate_let.is_set))
        .collect();
    let mut let_owner_by_offset: BTreeMap<usize, usize> = BTreeMap::new();

    for (event_name, owned_ranges) in inputs.event_owned_ranges.iter() {
        let Some(macros_for_event) = event_to_macros.get(event_name) else {
            continue;
        };
        let macros_for_event: Vec<usize> = macros_for_event.iter().copied().collect();
        let event_lets = collect_event_gate_lets(&scan.gate_lets, owned_ranges);
        let buckets = bucket_gate_lets_by_suffix(&event_lets);
        for bucket_lets in buckets.values() {
            let owner = resolve_bucket_owner(bucket_lets, &macros_for_event, &anchor_ranges);
            for gate_let in bucket_lets {
                let span = opcode_span(gate_let.offset, inputs);
                attribute_scaffold_span(
                    span,
                    std::slice::from_ref(&owner),
                    partitions,
                    byte_to_node,
                    inputs,
                );
                let_owner_by_offset.insert(gate_let.offset, owner);
            }
        }
        for (jin_offset, target, cond_leaf) in &scan.jins {
            let Some(cond_leaf) = cond_leaf.as_deref() else {
                continue;
            };
            if !starts_with_gate_prefix(cond_leaf) {
                continue;
            }
            if !any_range_contains(owned_ranges, *jin_offset) {
                continue;
            }
            // JIN/JUMP targets are CodeSkip offsets in memory space;
            // owned_ranges are disk coordinates. Translate before the
            // containment check, else the gate-check JIN never matches.
            let Some(&target_disk) = inputs.mem_to_disk.get(&(*target as usize)) else {
                continue;
            };
            if !any_range_contains(owned_ranges, target_disk) {
                continue;
            }
            let owner = resolve_single_offset_owner(
                *jin_offset,
                cond_leaf,
                &macros_for_event,
                &anchor_ranges,
            );
            let span = opcode_span(*jin_offset, inputs);
            attribute_scaffold_span(
                span,
                std::slice::from_ref(&owner),
                partitions,
                byte_to_node,
                inputs,
            );
        }
        for (jump_offset, target) in &scan.jumps {
            if !any_range_contains(owned_ranges, *jump_offset) {
                continue;
            }
            let Some(&target_offset) = inputs.mem_to_disk.get(&(*target as usize)) else {
                continue;
            };
            if !let_var_by_offset.contains_key(&target_offset) {
                continue;
            }
            // Inherit owner from the gate-LET this JUMP targets. The
            // LET was disambiguated above. Falls back to multi-node
            // fan-out when the target lies in a different event scope
            // (no entry in `let_owner_by_offset` yet).
            let owner = match let_owner_by_offset.get(&target_offset) {
                Some(&node_id) => node_id,
                None => {
                    let span = opcode_span(*jump_offset, inputs);
                    attribute_scaffold_span(
                        span,
                        &macros_for_event,
                        partitions,
                        byte_to_node,
                        inputs,
                    );
                    continue;
                }
            };
            let span = opcode_span(*jump_offset, inputs);
            attribute_scaffold_span(
                span,
                std::slice::from_ref(&owner),
                partitions,
                byte_to_node,
                inputs,
            );
        }
    }
    (let_owner_by_offset, let_var_by_offset, let_is_set_by_offset)
}

/// Snapshot the pre-scaffold ranges for every candidate macro id.
/// Locality math reads from this frozen view so per-LET decisions
/// don't drift as the per-event loop appends scaffold spans onto the
/// live partition map. Candidates with no pre-scaffold ranges yet
/// (e.g. their downstream is itself a macro and `attribute_calls`
/// found nothing) get an empty list; `resolve_bucket_owner` treats
/// them as max-distance.
fn snapshot_candidate_anchor_ranges(
    scaffold_macros: &[(usize, String)],
    partitions: &BTreeMap<usize, K2NodePartition>,
) -> BTreeMap<usize, Vec<Range<usize>>> {
    let mut out: BTreeMap<usize, Vec<Range<usize>>> = BTreeMap::new();
    for (node_id, _macro_kind) in scaffold_macros {
        let ranges = partitions
            .get(node_id)
            .map(|partition| partition.ranges.clone())
            .unwrap_or_default();
        out.insert(*node_id, ranges);
    }
    out
}

/// Return the gate-LET sites that fall inside any of `owned_ranges`.
/// The per-event loop calls this once per event so the suffix bucketer
/// sees the same input twice if the same offset is claimed by
/// overlapping ranges; the resulting attribution is idempotent
/// (extending a single owner's range list with the same span twice is
/// deduped by `push_range`).
fn collect_event_gate_lets(gate_lets: &[GateLet], owned_ranges: &[Range<usize>]) -> Vec<GateLet> {
    gate_lets
        .iter()
        .filter(|gate_let| any_range_contains(owned_ranges, gate_let.offset))
        .cloned()
        .collect()
}

/// Group gate-LETs by the integer suffix of their leaf name. An empty
/// suffix (leaf ends without `_<digits>`) is bucketed as `0`; this
/// covers compiler emission paths that omit the property-allocator
/// counter when only one gate of its kind exists in the class. The
/// inner `Vec` is left in source order so deterministic ties later
/// favour the first-seen LET offset.
fn bucket_gate_lets_by_suffix(event_lets: &[GateLet]) -> BTreeMap<u32, Vec<GateLet>> {
    let mut buckets: BTreeMap<u32, Vec<GateLet>> = BTreeMap::new();
    for gate_let in event_lets {
        let suffix = parse_trailing_suffix_int(&gate_let.leaf);
        buckets.entry(suffix).or_default().push(gate_let.clone());
    }
    buckets
}

/// Parse the trailing `_<digits>` integer from a gate-variable leaf
/// name. Returns `0` when no trailing integer is present, matching the
/// "empty suffix" bucket. Examples: `Temp_bool_IsClosed_Variable_3`
/// returns `3`; `Temp_bool_Variable` returns `0`.
fn parse_trailing_suffix_int(leaf: &str) -> u32 {
    let bytes = leaf.as_bytes();
    let mut tail_start = bytes.len();
    while tail_start > 0 && bytes[tail_start - 1].is_ascii_digit() {
        tail_start -= 1;
    }
    if tail_start == bytes.len() {
        return 0;
    }
    if tail_start == 0 || bytes[tail_start - 1] != b'_' {
        return 0;
    }
    leaf[tail_start..].parse::<u32>().unwrap_or(0)
}

/// Pick the single candidate that wins a (event, suffix) bucket. The
/// rule: for each candidate, take the smallest per-LET min-distance
/// across the bucket; the candidate with the smallest aggregate wins.
/// Ties broken by lowest node-id (deterministic). Candidates with no
/// anchor ranges contribute `usize::MAX`, so a candidate with any
/// pre-scaffold anchor always beats a candidate with none.
fn resolve_bucket_owner(
    bucket_lets: &[GateLet],
    candidates: &[usize],
    anchor_ranges: &BTreeMap<usize, Vec<Range<usize>>>,
) -> usize {
    debug_assert!(!candidates.is_empty());
    debug_assert!(!bucket_lets.is_empty());
    if candidates.len() == 1 {
        return candidates[0];
    }
    let mut best: Option<(usize, usize)> = None;
    for &candidate in candidates {
        let ranges = anchor_ranges
            .get(&candidate)
            .map(|list| list.as_slice())
            .unwrap_or(&[]);
        let candidate_distance = bucket_lets
            .iter()
            .map(|gate_let| min_distance_to_ranges(gate_let.offset, ranges))
            .min()
            .unwrap_or(usize::MAX);
        best = match best {
            None => Some((candidate_distance, candidate)),
            Some((current_distance, current_node))
                if candidate_distance < current_distance
                    || (candidate_distance == current_distance && candidate < current_node) =>
            {
                Some((candidate_distance, candidate))
            }
            other => other,
        };
    }
    let Some((winning_distance, winning_node)) = best else {
        debug_assert!(false, "candidates non-empty but best stayed None");
        return candidates[0];
    };
    debug_assert!(
        winning_distance < usize::MAX
            || candidates.iter().all(|node| {
                anchor_ranges
                    .get(node)
                    .map(|ranges| ranges.is_empty())
                    .unwrap_or(true)
            }),
        "locality resolved to max-distance owner with some candidate having anchors"
    );
    winning_node
}

/// Same disambiguation as [`resolve_bucket_owner`] but for a single
/// scaffold offset (JIN sites). Bucket-of-one shares the bucket rule
/// so the suffix grouping invariant holds even for JIN, which has its
/// own gate-leaf source.
fn resolve_single_offset_owner(
    offset: usize,
    cond_leaf: &str,
    candidates: &[usize],
    anchor_ranges: &BTreeMap<usize, Vec<Range<usize>>>,
) -> usize {
    let normalised = normalise_member_name(cond_leaf);
    // JIN sites carry no bool RHS; `is_set` is irrelevant to the
    // locality math, only the offset/leaf drive bucket ownership.
    let bucket = [GateLet {
        offset,
        leaf: normalised,
        is_set: false,
    }];
    resolve_bucket_owner(&bucket, candidates, anchor_ranges)
}

/// MacroInstance ids whose `macro_kind` matches the gate-scaffold
/// family. Paired with the resolved kind string for downstream
/// indexing.
fn collect_scaffold_macro_instances(inputs: &K2NodeByteMapInputs<'_>) -> Vec<(usize, String)> {
    let mut out: Vec<(usize, String)> = Vec::new();
    for (&node_id, class) in inputs.node_classes {
        if !matches!(class, K2NodeClass::MacroInstance) {
            continue;
        }
        let Some(macro_name) = inputs.macro_names.get(&node_id) else {
            continue;
        };
        if has_gate_scaffold(macro_name) {
            out.push((node_id, macro_name.clone()));
        }
    }
    out
}

/// Group scaffold-macro instances by every event in their
/// `node_to_reaching_events` set. Lookups in the per-event scan stage
/// then return all candidate MacroInstance ids in one map probe.
fn index_macros_by_owning_event(
    scaffold_macros: &[(usize, String)],
    inputs: &K2NodeByteMapInputs<'_>,
) -> BTreeMap<String, BTreeSet<usize>> {
    // Each node id appears at most once per event (distinct `node_classes`
    // keys), so the BTreeSet only orders the ids, it doesn't drop any. The
    // ordered set keeps the per-event id list independent of map iteration.
    let mut out: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (node_id, _macro_kind) in scaffold_macros {
        let Some(events) = inputs.node_to_reaching_events.get(node_id) else {
            continue;
        };
        for event_name in events {
            out.entry(event_name.clone()).or_default().insert(*node_id);
        }
    }
    out
}

/// Walk the bytecode once, recording every opcode the scaffold
/// attribution cares about: gate-LET targets, gate-reading JIN sites,
/// and unconditional JUMP sites with their targets. The visitor keeps
/// the data in a single struct so the per-event scan can iterate each
/// list without re-walking.
fn scan_scaffold_opcodes(inputs: &K2NodeByteMapInputs<'_>) -> ScaffoldOpcodeScan {
    let walk_ctx = WalkCtx::new(inputs.bytecode, inputs.name_table, inputs.ue5);
    let mut visitor = ScaffoldOpcodeVisitor::default();
    let mut cursor = 0usize;
    while cursor < inputs.bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    ScaffoldOpcodeScan {
        gate_lets: visitor.gate_lets,
        jins: visitor.jins,
        jumps: visitor.jumps,
    }
}

/// One gate-boolean `EX_LET*` write found by the scaffold scan.
/// `is_set` is `true` when the RHS literal is `EX_TRUE` (the GATE-SET
/// that opens a DoOnce, the identity-bearing write) and `false` when
/// the RHS is `EX_FALSE` (the INIT-SEED that resets the gate). Writes
/// whose RHS is neither bare literal default to `false`; the
/// attribution treats them as non-gate-set.
#[derive(Clone)]
struct GateLet {
    offset: usize,
    leaf: String,
    is_set: bool,
}

/// Collected scaffold-relevant opcode sites. `gate_lets` are the
/// gate-boolean `EX_LET*` writes whose target leaf starts with one of
/// the gate-prefix constants. `jins` are `(start_offset, target,
/// Some(cond_leaf))` when the JIN's condition is a single variable
/// read, else the third tuple element is `None`. `jumps` are
/// `(start_offset, target)`.
struct ScaffoldOpcodeScan {
    gate_lets: Vec<GateLet>,
    jins: Vec<(usize, u32, Option<String>)>,
    jumps: Vec<(usize, u32)>,
}

/// Sentinel `Self::Result` values the visitor emits for the bare bool
/// literals `EX_TRUE` / `EX_FALSE`, so the gate-LET handlers can read
/// the RHS bool without a second walk. Chosen as non-leaf-name strings
/// (a normalised member leaf never equals these) so they cannot
/// collide with a variable-read result.
const BOOL_TRUE_SENTINEL: &str = "\u{1}true";
const BOOL_FALSE_SENTINEL: &str = "\u{1}false";

/// Visitor that records gate-LET, JIN, and JUMP sites for scaffold
/// attribution. Returns `Some(leaf_name)` from variable-read opcodes
/// so the JIN-condition callback can identify single-variable reads
/// without a second walk pass, and a bool sentinel from `EX_TRUE` /
/// `EX_FALSE` so the gate-LET handlers can capture the RHS value.
#[derive(Default)]
struct ScaffoldOpcodeVisitor {
    gate_lets: Vec<GateLet>,
    jins: Vec<(usize, u32, Option<String>)>,
    jumps: Vec<(usize, u32)>,
}

impl ScaffoldOpcodeVisitor {
    /// Record `start_offset` as a gate-LET when `leaf` is gate-prefixed.
    /// `rhs` is the walked RHS result; it carries the bool sentinel for
    /// a bare `EX_TRUE` / `EX_FALSE` literal, anything else is treated
    /// as a non-gate-set write (`is_set = false`).
    fn record_let_if_gate(&mut self, start_offset: usize, leaf: &str, rhs: Option<&str>) {
        if starts_with_gate_prefix(leaf) {
            self.gate_lets.push(GateLet {
                offset: start_offset,
                leaf: normalise_member_name(leaf),
                is_set: rhs == Some(BOOL_TRUE_SENTINEL),
            });
        }
    }
}

impl OpcodeVisitor for ScaffoldOpcodeVisitor {
    type Result = Option<String>;

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) -> Self::Result {
        None
    }

    fn on_zero_operand(&mut self, opcode: u8, _start_offset: usize) -> Self::Result {
        match opcode {
            EX_TRUE => Some(BOOL_TRUE_SENTINEL.to_string()),
            EX_FALSE => Some(BOOL_FALSE_SENTINEL.to_string()),
            _ => None,
        }
    }

    fn on_field_path_var(
        &mut self,
        _opcode: u8,
        path: FieldPath,
        _start_offset: usize,
    ) -> Self::Result {
        if path.is_null() || path.display.is_empty() {
            return None;
        }
        let leaf = path.display.rsplit("::").next().unwrap_or(&path.display);
        Some(normalise_member_name(leaf))
    }

    fn on_let_with_path(
        &mut self,
        opcode: u8,
        path: FieldPath,
        _lhs: Self::Result,
        rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(
            opcode == EX_LET || opcode == EX_LET_MULTICAST_DELEGATE || opcode == EX_LET_DELEGATE
        );
        if path.is_null() || path.display.is_empty() {
            return None;
        }
        let leaf = path.display.rsplit("::").next().unwrap_or(&path.display);
        self.record_let_if_gate(start_offset, leaf, rhs.as_deref());
        None
    }

    fn on_let_no_path(
        &mut self,
        opcode: u8,
        lhs: Self::Result,
        rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(
            opcode == EX_LET_BOOL || opcode == EX_LET_OBJ || opcode == EX_LET_WEAK_OBJ_PTR
        );
        if let Some(leaf) = lhs.as_deref() {
            self.record_let_if_gate(start_offset, leaf, rhs.as_deref());
        }
        None
    }

    fn on_let_value_on_persistent_frame(
        &mut self,
        path: FieldPath,
        value: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = EX_LET_VALUE_ON_PERSISTENT_FRAME;
        if path.is_null() || path.display.is_empty() {
            return None;
        }
        let leaf = path.display.rsplit("::").next().unwrap_or(&path.display);
        self.record_let_if_gate(start_offset, leaf, value.as_deref());
        None
    }

    fn on_jump_if_not(
        &mut self,
        target: u32,
        condition: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        self.jins.push((start_offset, target, condition));
        None
    }

    fn on_jump(&mut self, opcode: u8, target: u32, start_offset: usize) -> Self::Result {
        debug_assert!(opcode == EX_JUMP);
        let _ = EX_JUMP_IF_NOT;
        self.jumps.push((start_offset, target));
        None
    }
}

/// True if `name` begins with any of the DoOnce / FlipFlop scaffold
/// variable prefixes (`Temp_bool_IsClosed_Variable`,
/// `Temp_bool_Has_Been_Initd_Variable`, or `Temp_bool_Variable`).
fn starts_with_gate_prefix(name: &str) -> bool {
    name.starts_with(DOONCE_GATE_PREFIX)
        || name.starts_with(DOONCE_INIT_PREFIX)
        || name.starts_with(FLIPFLOP_TOGGLE_PREFIX)
}

/// Append `span` to every macro instance in `macro_ids`'s partition
/// and mirror the start offset into `byte_to_node`. Creates the
/// partition entry when missing, matching the insert path used by the
/// other attribution passes.
fn attribute_scaffold_span(
    span: Range<usize>,
    macro_ids: &[usize],
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
    inputs: &K2NodeByteMapInputs<'_>,
) {
    for &node_id in macro_ids {
        let owners = owner_events_for_node(node_id, inputs);
        let macro_kind = inputs
            .macro_names
            .get(&node_id)
            .map(|name| MacroKind::from_name(name));
        let partition = partitions.entry(node_id).or_insert_with(|| {
            K2NodePartition::new(
                node_id,
                owners.clone(),
                K2NodeClass::MacroInstance,
                macro_kind,
            )
        });
        extend_owner_events(partition, owners);
        push_range(&mut partition.ranges, span.clone());
        let entry = byte_to_node.entry(span.start).or_default();
        if !entry.contains(&node_id) {
            entry.push(node_id);
        }
    }
}
