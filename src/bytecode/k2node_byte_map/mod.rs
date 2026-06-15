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
use crate::types::{NodePinData, ParsedAsset};

use offsets::{
    attribute_calls, attribute_dynamic_casts, attribute_function_results, attribute_variable_sets,
};
use partition::{
    attribute_enclosing_scope_fallback, attribute_execution_sequences,
    attribute_latent_resume_blocks, attribute_macro_instances, attribute_tracepoints,
};
use scaffold::attribute_macro_scaffold_bytes;

mod carry;
mod offsets;
mod partition;
mod scaffold;

pub(crate) use carry::ByteMaps;

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
    /// Which graph this map covers. Member-name indices are asset-wide, so
    /// ambiguous matches are restricted to graph-local candidates before
    /// event-scope clamping (see [`resolve_member_group`]).
    pub scope: GraphScope<'a>,
}

/// Identifies the graph a byte map is built for, the basis for restricting
/// ambiguous member-name matches to nodes that live on that graph.
#[derive(Clone, Copy)]
pub(crate) enum GraphScope<'a> {
    /// The ubergraph stream. Local nodes are those the event-entry pin BFS
    /// reaches (`node_to_reaching_events`) plus the event entry nodes
    /// themselves; standalone-function-graph nodes are never reached.
    Ubergraph,
    /// One standalone function graph, named by its page. Local nodes are
    /// those whose enclosing EdGraph export carries this name.
    FunctionPage(&'a str),
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

/// Which attribution view a byte map is built for. The two views differ
/// only in the same-name group bijection (see [`resolve_member_group`]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum AttributionMode {
    /// Decoder view: per-site lowest-id attribution only. The decode loop
    /// threads this. Frozen with respect to comment work, so comment
    /// attribution changes can never alter decoded structure (the
    /// cross-event-inline classifier and macro_region read these
    /// partitions).
    Conservative,
    /// Comment view: the conservative baseline plus the same-name group
    /// bijection. Consumed only by summary comment placement.
    CommentRefined,
}

/// Construct the COMMENT-view [`K2NodeByteMap`] for one graph (group
/// bijection applied). This is the map carried out to summary comment
/// placement; nothing in the decode path reads it.
pub(crate) fn build_k2node_byte_map(inputs: &K2NodeByteMapInputs<'_>) -> K2NodeByteMap {
    build_k2node_byte_map_with_mode(inputs, AttributionMode::CommentRefined)
}

/// Construct the DECODER-view [`K2NodeByteMap`] for one graph
/// (conservative per-site attribution, no comment-only group bijection).
/// The decode loop threads this so that comment-precision work, which
/// rides the [`CommentRefined`](AttributionMode::CommentRefined) view,
/// cannot regress decoded structure.
pub(crate) fn build_k2node_byte_map_conservative(
    inputs: &K2NodeByteMapInputs<'_>,
) -> K2NodeByteMap {
    build_k2node_byte_map_with_mode(inputs, AttributionMode::Conservative)
}

fn build_k2node_byte_map_with_mode(
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
) -> K2NodeByteMap {
    let mut partitions: BTreeMap<usize, K2NodePartition> = BTreeMap::new();
    let mut byte_to_node: BTreeMap<usize, Vec<usize>> = BTreeMap::new();

    attribute_calls(inputs, mode, &mut partitions, &mut byte_to_node);
    attribute_macro_instances(inputs, &mut partitions);
    let (gate_let_owner_by_offset, gate_let_var_by_offset, gate_let_is_set_by_offset) =
        attribute_macro_scaffold_bytes(inputs, &mut partitions, &mut byte_to_node);
    attribute_variable_sets(inputs, mode, &mut partitions, &mut byte_to_node);
    attribute_dynamic_casts(inputs, mode, &mut partitions, &mut byte_to_node);
    attribute_function_results(inputs, &mut partitions, &mut byte_to_node);
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

/// Resolve every same-member site offset to its owning K2Node id.
///
/// When several K2Nodes share a member name (the kismet helper case,
/// e.g. `Add_FloatFloat`, or N user calls to the same function) the
/// unfiltered member index fans every bytecode site out to every node
/// that bears the name, including nodes on other graph pages. This
/// collapses each site to a single owner.
///
/// Per-site resolution stages (the conservative baseline, preserved
/// exactly for sites the group bijection does not claim):
///
/// 1. Restrict to graph-local candidates per [`GraphScope`] (member
///    indices are asset-wide; without this a function map's call sites
///    could attribute to a same-named node on another page). An
///    all-foreign set attributes nothing.
/// 2. Keep the local candidates whose reaching event covers the offset
///    (`node_to_reaching_events` plus `event_owned_ranges`).
/// 3. Lowest export id among the survivors wins. Zero survivors falls
///    back to the lowest-id local candidate (function maps, latent
///    resume chunks); logged under `BP_INSPECT_K2NODE_AUDIT`.
///
/// Group bijection (the starvation fix): when N same-name nodes all
/// reach one event and exactly N sites of that member sit in the
/// event's owned ranges, the per-site lowest-id tiebreak hands every
/// site to one node and starves the rest. Instead, order the N nodes by
/// exec-traversal rank (the compiler emits bytecode in exec-flow order,
/// so the k-th node in exec order compiles to the k-th site in disk
/// order) and zip k-th node to k-th site. Gated on a unique covering
/// event and a total exec order; any group that fails a gate falls
/// through to the per-site baseline, never worse than before.
pub(super) fn resolve_member_group(
    candidates: &[usize],
    offsets: &[usize],
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
) -> Vec<(usize, usize)> {
    // Single-candidate (no scoping needed) and trivially-scoped cases
    // match the historical per-site clamp exactly.
    if candidates.len() <= 1 {
        return match candidates.first() {
            Some(&only) => offsets.iter().map(|&offset| (offset, only)).collect(),
            None => Vec::new(),
        };
    }
    let scoped = graph_local_candidates(candidates, inputs);
    if scoped.is_empty() {
        // Every candidate is foreign to this graph (e.g. a macro-internal
        // call whose only same-named K2Nodes live on other pages).
        return Vec::new();
    }
    if scoped.len() == 1 {
        let only = scoped[0];
        return offsets.iter().map(|&offset| (offset, only)).collect();
    }
    let per_site: Vec<(usize, Vec<usize>)> = offsets
        .iter()
        .map(|&offset| (offset, event_survivors(&scoped, offset, inputs)))
        .collect();
    // The group bijection is the comment-only refinement; the decoder
    // view keeps the per-site lowest-id baseline so its partitions stay
    // frozen.
    let bijection = match mode {
        AttributionMode::CommentRefined => build_group_bijection(&per_site, inputs),
        AttributionMode::Conservative => BTreeMap::new(),
    };
    let lowest_local = *scoped.iter().min().expect("non-empty");
    per_site
        .iter()
        .map(|(offset, survivors)| {
            if let Some(&node_id) = bijection.get(offset) {
                (*offset, node_id)
            } else if let Some(&lowest) = survivors.iter().min() {
                (*offset, lowest)
            } else {
                audit_zero_survivors(*offset, &scoped);
                (*offset, lowest_local)
            }
        })
        .collect()
}

/// Graph-local candidates whose reaching event physically covers
/// `call_offset` (stage 2 of the per-site clamp). Order preserves the
/// input candidate order so the lowest-id tiebreak stays deterministic.
///
/// On a [`FunctionPage`](GraphScope::FunctionPage) scope there are no
/// events: a standalone function owns its entire byte stream, so the
/// `event_owned_ranges` / `node_to_reaching_events` filter would starve
/// every site to zero survivors. Every graph-local candidate covers every
/// in-function offset, so the whole scoped set survives and the existing
/// chain-gated bijection can run on function-internal same-name groups.
fn event_survivors(
    scoped: &[usize],
    call_offset: usize,
    inputs: &K2NodeByteMapInputs<'_>,
) -> Vec<usize> {
    if matches!(inputs.scope, GraphScope::FunctionPage(_)) {
        return scoped.to_vec();
    }
    scoped
        .iter()
        .copied()
        .filter(|node_id| {
            inputs
                .node_to_reaching_events
                .get(node_id)
                .is_some_and(|events| {
                    events.iter().any(|event_name| {
                        inputs
                            .event_owned_ranges
                            .get(event_name)
                            .is_some_and(|ranges| {
                                ranges.iter().any(|range| range.contains(&call_offset))
                            })
                    })
                })
        })
        .collect()
}

/// Log a zero-survivor lowest-id fallback when `BP_INSPECT_K2NODE_AUDIT`
/// is set, so the fire rate stays visible during investigation.
fn audit_zero_survivors(call_offset: usize, scoped: &[usize]) {
    if std::env::var_os("BP_INSPECT_K2NODE_AUDIT").is_some_and(|val| !val.is_empty()) {
        eprintln!(
            "k2node clamp: zero survivors at 0x{:x} from {} local candidates ({:?}); using lowest-id fallback",
            call_offset,
            scoped.len(),
            scoped,
        );
    }
}

/// Map qualifying same-name same-reach starvation groups to a 1:1
/// exec-order-to-disk-order assignment. Returns `offset -> node_id` only
/// for sites inside a qualifying group; all other sites are left for the
/// per-site baseline in [`resolve_member_group`].
///
/// A group is the set of sites sharing one survivor set of size >= 2
/// (the same N nodes reach all of them). It qualifies when the site
/// count equals the node count, the nodes share a unique covering event,
/// and that event yields a total exec order over the nodes.
fn build_group_bijection(
    per_site: &[(usize, Vec<usize>)],
    inputs: &K2NodeByteMapInputs<'_>,
) -> BTreeMap<usize, usize> {
    let mut groups: BTreeMap<Vec<usize>, Vec<usize>> = BTreeMap::new();
    for (offset, survivors) in per_site {
        if survivors.len() >= 2 {
            let mut nodes = survivors.clone();
            nodes.sort_unstable();
            groups.entry(nodes).or_default().push(*offset);
        }
    }
    let mut bijection = BTreeMap::new();
    for (nodes, mut group_offsets) in groups {
        if group_offsets.len() != nodes.len() {
            continue;
        }
        let Some(entry) = unique_group_event_entry(&nodes, &group_offsets, inputs) else {
            continue;
        };
        let Some(ordered) = exec_ordered_nodes(&nodes, entry, inputs) else {
            continue;
        };
        // Only reassign when the group's nodes lie on one linear exec
        // path; sibling-branch groups stay at the per-site baseline. See
        // `nodes_form_exec_chain` for why that bound is a correctness
        // limit (branch order is a non-derivable compiler tiebreak), not
        // a deferred improvement.
        if !nodes_form_exec_chain(&ordered, inputs) {
            continue;
        }
        group_offsets.sort_unstable();
        for (&offset, &node_id) in group_offsets.iter().zip(ordered.iter()) {
            bijection.insert(offset, node_id);
        }
    }
    bijection
}

/// The entry K2Node to root the exec walk at. On the ubergraph this is
/// the single reaching event whose owned ranges cover every site offset
/// (`None`, fall back, when no such event is unique). On a function page
/// there are no events, so the function's own `K2Node_FunctionEntry` is
/// the root; the whole function range already covers every site, so no
/// per-site coverage check is needed.
fn unique_group_event_entry(
    nodes: &[usize],
    offsets: &[usize],
    inputs: &K2NodeByteMapInputs<'_>,
) -> Option<usize> {
    if let GraphScope::FunctionPage(page) = inputs.scope {
        return function_entry_node(page, inputs);
    }
    let mut common: Option<BTreeSet<String>> = None;
    for node_id in nodes {
        let events = inputs.node_to_reaching_events.get(node_id)?;
        common = Some(match common {
            None => events.clone(),
            Some(prev) => prev.intersection(events).cloned().collect(),
        });
    }
    let common = common?;
    let mut covering = common.iter().filter(|event_name| {
        inputs
            .event_owned_ranges
            .get(*event_name)
            .is_some_and(|ranges| {
                offsets
                    .iter()
                    .all(|offset| ranges.iter().any(|range| range.contains(offset)))
            })
    });
    let event_name = covering.next()?;
    if covering.next().is_some() {
        return None;
    }
    inputs.event_node_index.get(event_name).copied()
}

/// The group's nodes ordered by exec-traversal rank from `entry`, or
/// `None` (no total order, fall back) when any node is unreached by the
/// exec walk (e.g. a pure node fed only through data pins).
fn exec_ordered_nodes(
    nodes: &[usize],
    entry: usize,
    inputs: &K2NodeByteMapInputs<'_>,
) -> Option<Vec<usize>> {
    let ranks = exec_visit_ranks(entry, inputs);
    let mut ranked: Vec<(usize, usize)> = Vec::with_capacity(nodes.len());
    for &node_id in nodes {
        ranked.push((*ranks.get(&node_id)?, node_id));
    }
    ranked.sort_unstable();
    Some(ranked.into_iter().map(|(_, node_id)| node_id).collect())
}

/// True when `ordered` (nodes in exec-rank order) lie on a single linear
/// exec path: each node is forward-reachable from its predecessor along
/// exec-output pins. Knots are walked transparently. A chain guarantees
/// the compiler emits the nodes contiguously in this order, so exec rank
/// equals on-disk order.
///
/// This gate is what bounds the group bijection to chains and leaves
/// branch-sibling same-name groups at the per-site lowest-id baseline.
/// The bound is a correctness limit, not a TODO. The compiler emits
/// bytecode in `CreateExecutionSchedule` order (a Kahn topological sort
/// with a `RemoveAtSwap` worklist tiebreak). On one exec chain the
/// data-dependency edges pin the nodes' relative order, so exec rank
/// recovers on-disk order. Two arms of a branch carry no dependency edge
/// between them, so their relative on-disk order is decided by the
/// worklist tiebreak, which is not graph-derivable. The only oracle that
/// records the true node-to-offset mapping, `FBlueprintDebugData`, is
/// transient and never serialized, so reassigning branch siblings would
/// be a guess. A wrong anchor is worse than the lowest-id drop (it
/// attaches a comment to the wrong node), so branch siblings stay at
/// baseline.
fn nodes_form_exec_chain(ordered: &[usize], inputs: &K2NodeByteMapInputs<'_>) -> bool {
    ordered
        .windows(2)
        .all(|pair| exec_forward_reachable(pair[0], pair[1], inputs))
}

/// Node ids targeted by `node_pins`' exec-output pins, in on-disk
/// (`linked_to`) order. The exec-graph traversal primitive shared by the
/// rank walk and the reachability walk.
fn exec_output_targets(node_pins: &NodePinData) -> impl Iterator<Item = usize> + '_ {
    node_pins
        .pins
        .iter()
        .filter(|pin| pin.is_exec_output())
        .flat_map(|pin| pin.linked_to.iter().map(|link| link.node))
}

/// True when `target` is reachable from `from` (exclusive) by following
/// exec-output pins.
fn exec_forward_reachable(from: usize, target: usize, inputs: &K2NodeByteMapInputs<'_>) -> bool {
    let pin_data = &inputs.asset.pin_data;
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<usize> = vec![from];
    visited.insert(from);
    while let Some(node_id) = stack.pop() {
        let Some(node_pins) = pin_data.get(&node_id) else {
            continue;
        };
        for child in exec_output_targets(node_pins) {
            if child == target {
                return true;
            }
            if visited.insert(child) {
                stack.push(child);
            }
        }
    }
    false
}

/// First-visit pre-order DFS rank of every node reachable from `entry`
/// along exec-output pins, following `linked_to` in on-disk order. Knot
/// routing nodes are traversed transparently (they fall between the
/// real nodes without changing their relative order). The compiler emits
/// bytecode in this exec-flow order, so rank order matches on-disk order
/// within a single execution path.
fn exec_visit_ranks(entry: usize, inputs: &K2NodeByteMapInputs<'_>) -> HashMap<usize, usize> {
    let pin_data = &inputs.asset.pin_data;
    let mut ranks: HashMap<usize, usize> = HashMap::new();
    let mut stack: Vec<usize> = vec![entry];
    let mut next_rank = 0usize;
    while let Some(node_id) = stack.pop() {
        if ranks.contains_key(&node_id) {
            continue;
        }
        ranks.insert(node_id, next_rank);
        next_rank += 1;
        let Some(node_pins) = pin_data.get(&node_id) else {
            continue;
        };
        let children: Vec<usize> = exec_output_targets(node_pins).collect();
        // Push reversed so the first exec link is popped (visited) first.
        for &child in children.iter().rev() {
            stack.push(child);
        }
    }
    ranks
}

/// The `K2Node_FunctionEntry` node id on `page`, the exec root for a
/// standalone function's group bijection. `None` when the page has zero
/// or several entry nodes (no single exec root to walk from). Resolves
/// the class through the import/export tables like the function-result
/// attribution pass does.
fn function_entry_node(page: &str, inputs: &K2NodeByteMapInputs<'_>) -> Option<usize> {
    let mut entries =
        inputs
            .asset
            .exports
            .iter()
            .enumerate()
            .filter_map(|(zero_based, (hdr, _))| {
                let one_based = zero_based + 1;
                let class = crate::resolve::short_class(&crate::resolve::resolve_index(
                    &inputs.asset.imports,
                    inputs.export_names,
                    hdr.class_index,
                ));
                (class == "K2Node_FunctionEntry"
                    && crate::resolve::enclosing_graph_name(
                        inputs.asset,
                        inputs.export_names,
                        one_based,
                    )
                    .as_deref()
                        == Some(page))
                .then_some(one_based)
            });
    let entry = entries.next()?;
    if entries.next().is_some() {
        return None;
    }
    Some(entry)
}

/// The subset of `candidates` living on the graph this map covers (see
/// [`GraphScope`]).
fn graph_local_candidates(candidates: &[usize], inputs: &K2NodeByteMapInputs<'_>) -> Vec<usize> {
    candidates
        .iter()
        .copied()
        .filter(|&node_id| match inputs.scope {
            GraphScope::Ubergraph => {
                inputs.node_to_reaching_events.contains_key(&node_id)
                    || inputs
                        .event_node_index
                        .values()
                        .any(|&entry| entry == node_id)
            }
            GraphScope::FunctionPage(page) => {
                crate::resolve::enclosing_graph_name(inputs.asset, inputs.export_names, node_id)
                    .as_deref()
                    == Some(page)
            }
        })
        .collect()
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

/// Asset-loading attribution tests live in a gitignored `local_tests.rs`
/// sidecar, compiled only with the `private-fixtures` feature, so the
/// default build never references the local fixtures by name or path. The
/// pure-logic tests below run in the default build.
// Re-exported for the gitignored `local_tests` body, which pulls these
// in through `use super::*`. The relocation moved the imports into the
// submodules, so the parent scope must surface them again for the tests.
#[cfg(all(test, feature = "private-fixtures"))]
use crate::resolve::{resolve_index, short_class};

// The body is `include!`d rather than declared as a file module so
// `cargo fmt` never tries to resolve the absent sidecar: rustfmt walks
// path-based `mod` declarations even when they are cfg-gated out, but it
// does not follow `include!`.
#[cfg(all(test, feature = "private-fixtures"))]
mod local_tests {
    include!("local_tests.rs");
}

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
            scope: GraphScope::Ubergraph,
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
            scope: GraphScope::Ubergraph,
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
            scope: GraphScope::Ubergraph,
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
            scope: GraphScope::Ubergraph,
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
            scope: GraphScope::Ubergraph,
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
