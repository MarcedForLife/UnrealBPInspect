//! Cross-event jump inline policy decider.
//!
//! When a jump target lands inside another event's owned bytecode region
//! (rather than on an event-entry boundary), `decode_jump` currently
//! drops the jump silently. The grip-shape Blueprint pattern relies on
//! this case: a single `K2Node_MacroInstance(DoOnce)` is wired from two
//! event entries via a `K2Node_Knot` fan-in, and the compiler emits a
//! cross-event jump trampoline from one event into the other event's
//! body region. The author wrote a shared body in one place, so the
//! correct rendering is to inline that shared body at the source pin.
//!
//! This module provides the pure decision function that overrides
//! `decode_jump`'s drop behaviour for the shared-body case.
//!
//! The disambiguating signal for shared-body inlining is target-side:
//! "does the target K2Node have fan-in from multiple event entries, and
//! is the current event one of them?" (see [`is_shared_body_anchor`]).
//! Resolving WHICH K2Node a trampoline target maps to is the one place
//! the current event matters: the owning event's first DoOnce is the
//! shared body when the owning event reaches it first, but
//! when the owning event has an earlier private gate the resolution
//! falls back to the current event's first DoOnce (the reversed-ownership
//! shape, see [`classify_for_decode_jump`]).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::ops::Range;

use crate::bytecode::names::{MacroKind, K2NODE_EXECUTION_SEQUENCE};
use crate::types::{NodePinData, PIN_DIRECTION_INPUT, PIN_DIRECTION_OUTPUT, PIN_TYPE_EXEC};

/// Coarse classification of a K2Node export class for the few checks the
/// cross-event inline classifier needs. `Other` covers everything not
/// otherwise enumerated. Built once per ubergraph from the resolved
/// short class name; keeps the per-jump comparisons typed instead of
/// re-checking string literals.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum K2NodeClass {
    /// Routing-only node, transparently walked through during exec
    /// passthrough.
    Knot,
    /// Macro instance (the macro identity comes from the separate
    /// `macro_names` table since one class covers many macros).
    MacroInstance,
    /// Other recognised class kinds that aren't currently special-cased
    /// individually.
    Other,
}

/// Map a short class name to a [`K2NodeClass`]. Unknown classes (event
/// entries are now keyed by `event_node_index` rather than re-checked
/// here) fall through to `Other`.
pub(crate) fn parse_k2node_class(class: &str) -> K2NodeClass {
    match class {
        "K2Node_Knot" => K2NodeClass::Knot,
        "K2Node_MacroInstance" => K2NodeClass::MacroInstance,
        _ => K2NodeClass::Other,
    }
}

/// Bundle of asset-derived state the cross-event inline classifier needs
/// at decode time. Built once per ubergraph decode and stored on
/// [`super::ctx::DecodeCtx`] as a single optional reference so the
/// existing context construction call sites only grow by one field.
///
/// `current_event_name` is rebound per-event by [`super::mod`]; the rest
/// is shared across every event in a single ubergraph.
pub(crate) struct CrossEventInlineCtx<'a> {
    /// Name of the event currently being decoded. Used for the
    /// shared-body membership check, the current event must be one of
    /// the events whose entry reaches the target K2Node for `Inline` to
    /// fire.
    pub(crate) current_event_name: &'a str,
    /// All ubergraph events' owned disk-coordinate ranges, keyed by
    /// event name. Used by `bytecode_to_node_resolver` to find which
    /// event owns a target disk offset that landed outside the current
    /// event's `owned_ranges`.
    pub(crate) event_owned_ranges: &'a BTreeMap<String, Vec<Range<usize>>>,
    /// 1-based K2Node export id for each event entry, keyed by event
    /// name. Populated for K2Node_CustomEvent / K2Node_Event /
    /// K2Node_InputAxisEvent / K2Node_ComponentBoundEvent nodes.
    pub(crate) event_node_index: &'a BTreeMap<String, usize>,
    /// For each K2Node, the set of event names whose entry node reaches
    /// it via the exec graph (with knot passthrough). Pre-built once per
    /// ubergraph from a single forward BFS per event entry, so per-jump
    /// classification becomes O(reaching_events.len()) instead of
    /// performing a fresh BFS per event-entry node every time.
    pub(crate) node_to_reaching_events: &'a HashMap<usize, BTreeSet<String>>,
    /// EdGraph pin connection data per K2Node export, keyed by 1-based
    /// export index. Walked forward from each event-entry's exec-output
    /// pins to detect which events reach a target K2Node, and walked
    /// upstream by `target_has_knot_fan_in` for the shared-body
    /// signature. Always populated; the cei is only constructed when
    /// pin_data is present.
    pub(crate) pin_data: &'a HashMap<usize, NodePinData>,
    /// 1-based export index to coarse [`K2NodeClass`]. Used to identify
    /// knot passthroughs and macro-instance dispatch without
    /// re-comparing class strings per call.
    pub(crate) node_classes: &'a HashMap<usize, K2NodeClass>,
    /// 1-based export index to macro short name for K2Node_MacroInstance
    /// nodes (e.g. `DoOnce`, `IsValid`). Empty / absent for nodes that
    /// aren't macro instances. Used by `bytecode_to_node` to pick out
    /// the first DoOnce reachable from an event entry.
    pub(crate) macro_names: &'a HashMap<usize, String>,
    /// Disk anchors currently being inlined. `decode_inlined_shared_body`
    /// inserts the anchor before recursing and removes it after, so a
    /// nested cross-event jump inside the same shared body can detect
    /// cycle re-entry and decline (returning `Drop`-equivalent behaviour
    /// from the caller). Also enables idempotence when the same shared
    /// body is reachable via multiple intra-body jumps.
    pub(crate) active_inline_anchors: RefCell<BTreeSet<usize>>,
    /// Per-event dedup record. Each entry is a `resolved_entry_disk`
    /// identifying an inlined emission already produced during the
    /// current event's decode. The grip-shape compiler emits multiple
    /// cross-event trampolines into the same target K2Node from one
    /// source event when several wires from that event fan into the same
    /// downstream node; each trampoline lands at a different intra-body
    /// offset but they all expand back to the same K2Node entry (the
    /// chain head or owning event range start). Keying on the resolved
    /// entry disk collapses these into one render. The set lives for the
    /// duration of one event's decode and is cleared (or constructed
    /// fresh) before the next event begins, so the source-event identity
    /// is implicit in the set's lifetime.
    pub(crate) inlined_targets: RefCell<BTreeSet<usize>>,
    /// Gate-LET locality map (`K2NodeByteMap`). `None` when the byte map
    /// was not built (synthetic test contexts).
    pub(crate) k2node_byte_map: Option<&'a crate::bytecode::k2node_byte_map::K2NodeByteMap>,
}

impl CrossEventInlineCtx<'_> {
    /// True when an inlined emission has already been produced for
    /// `resolved_entry_disk` during the current event's decode.
    pub(crate) fn already_inlined_target(&self, resolved_entry_disk: usize) -> bool {
        self.inlined_targets.borrow().contains(&resolved_entry_disk)
    }

    /// Record that an inlined emission has been produced for
    /// `resolved_entry_disk`. Returns `true` if the entry was newly
    /// inserted, `false` when it was already present.
    pub(crate) fn record_inlined_target(&self, resolved_entry_disk: usize) -> bool {
        self.inlined_targets
            .borrow_mut()
            .insert(resolved_entry_disk)
    }
}

/// Outcome of classifying a cross-event jump.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CrossEventDisposition {
    /// The shared-body case. The target K2Node is reachable from two or
    /// more event entries (via K2Node_Knot passthroughs), and the
    /// current event is one of them. The decoder should co-own the
    /// target region under `OwnerId::SharedBody { target_node,
    /// anchor_disk }` and recurse into it.
    Inline {
        target_node: usize,
        anchor_disk: usize,
    },
    /// The target memory offset is exactly an event-entry boundary.
    /// Equivalent to the existing `Stmt::EventCall` path.
    Schedule { event_name: String },
    /// No shared-body relationship and no event-entry match. Caller
    /// should keep the existing drop behaviour.
    Drop,
}

/// True when `node` is a compiler-shared body anchor for
/// `current_event_name`: the canonical shared-body signature the
/// cross-event inline classifier fires on.
///
/// Two conditions:
/// - **Knot fan-in** (gated on `require_knot_fan_in`). The node has
///   fan-in via a `K2Node_Knot` immediate upstream (2 or more distinct
///   sources). The legacy live path requires this; the shared-body
///   signature is precisely a knot fan-in immediately upstream of the
///   target's exec input. The generalized parallel helper passes
///   `false` here: the real share signal is membership plus the existence
///   of a cross-event jump (the trampoline), and the knot guard is
///   belt-and-suspenders against a false positive that node identity plus
///   a real trampoline already rule out (the knot requirement is
///   over-strict).
/// - **Membership** (always required). The node's reaching-events set has
///   2 or more events and includes `current_event_name`, so the current
///   event is one of the bodies the shared region serves. This is the
///   load-bearing over-fire guard and is enforced in both paths.
fn is_shared_body_anchor(
    node: usize,
    current_event_name: &str,
    pin_data: &HashMap<usize, NodePinData>,
    is_knot: &impl Fn(usize) -> bool,
    node_to_reaching_events: &HashMap<usize, BTreeSet<String>>,
    require_knot_fan_in: bool,
) -> bool {
    if require_knot_fan_in && !target_has_knot_fan_in(node, pin_data, is_knot) {
        return false;
    }
    let reaching_events = events_reaching_target(node, node_to_reaching_events);
    reaching_events.len() >= 2 && reaching_events.contains(current_event_name)
}

/// True when at least one of `target_node`'s exec-input pins resolves
/// (through any chain of knot passthroughs) to a `K2Node_Knot` node
/// that has 2 or more distinct upstream wire endpoints. This is the
/// fan-in signature for compiler-shared bodies: the editor wires
/// multiple event sources into a single knot and the compiler emits
/// one bytecode region for the downstream node.
///
/// The check inspects each exec-input pin's `LinkedTo` entries, walks
/// upstream through any number of intermediate knots, and counts
/// distinct (node, pin_id) pairs at the first non-knot frontier or
/// the immediate knot's input fan-in (whichever comes first). A
/// single-source upstream chain returns false even when intermediate
/// knots are present, since one source can't constitute a fan-in.
fn target_has_knot_fan_in(
    target_node: usize,
    pin_data: &HashMap<usize, NodePinData>,
    is_knot: &impl Fn(usize) -> bool,
) -> bool {
    let Some(target_pins) = pin_data.get(&target_node) else {
        return false;
    };
    for pin in &target_pins.pins {
        if pin.pin_type != PIN_TYPE_EXEC || pin.direction != PIN_DIRECTION_INPUT {
            continue;
        }
        for link in &pin.linked_to {
            if !is_knot(link.node) {
                continue;
            }
            if knot_input_fan_in_count(link.node, pin_data, is_knot) >= 2 {
                return true;
            }
        }
    }
    false
}

/// Per-edge instruction emitted by [`bfs_exec_links`] visitors.
enum Visit<T> {
    /// Don't enqueue this neighbour, keep walking from already-queued
    /// nodes.
    Skip,
    /// Enqueue this neighbour so its exec pins get walked next.
    Enqueue,
    /// Halt the walk and return this value.
    Found(T),
}

/// Breadth-first walk of the K2Node exec graph.
///
/// Starts at `seed`, follows every link on every exec pin matching
/// `direction`, and invokes `visit(downstream_node, link_pin_id)` for
/// each edge. The visitor decides per-edge whether to recurse into the
/// neighbour (`Visit::Enqueue`), record-and-stop at the leaf
/// (`Visit::Skip`), or halt the entire walk (`Visit::Found(value)`).
/// Newly-enqueued neighbours go through a per-walk visited set so each
/// node is enqueued at most once.
///
/// Knot passthrough rules (which node classes to recurse into) are
/// therefore decided per-call-site.
///
/// `seed` is marked visited up-front and never re-enqueued.
fn bfs_exec_links<T>(
    seed: usize,
    direction: u8,
    pin_data: &HashMap<usize, NodePinData>,
    mut visit: impl FnMut(usize, [u8; 16]) -> Visit<T>,
) -> Option<T> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    visited.insert(seed);
    queue.push_back(seed);
    while let Some(current) = queue.pop_front() {
        let Some(node_pins) = pin_data.get(&current) else {
            continue;
        };
        for pin in &node_pins.pins {
            if pin.pin_type != PIN_TYPE_EXEC || pin.direction != direction {
                continue;
            }
            for link in &pin.linked_to {
                match visit(link.node, link.pin_id) {
                    Visit::Skip => {}
                    Visit::Enqueue => {
                        if visited.insert(link.node) {
                            queue.push_back(link.node);
                        }
                    }
                    Visit::Found(value) => return Some(value),
                }
            }
        }
    }
    None
}

/// Count distinct upstream wire endpoints feeding `knot_node`'s input
/// pin (transitively through any chain of upstream knots). Non-knot
/// neighbours are leaf-collected without recursion, knots recurse.
fn knot_input_fan_in_count(
    knot_node: usize,
    pin_data: &HashMap<usize, NodePinData>,
    is_knot: &impl Fn(usize) -> bool,
) -> usize {
    let mut sources: BTreeSet<(usize, [u8; 16])> = BTreeSet::new();
    bfs_exec_links::<()>(knot_node, PIN_DIRECTION_INPUT, pin_data, |node, pin_id| {
        if is_knot(node) {
            Visit::Enqueue
        } else {
            sources.insert((node, pin_id));
            Visit::Skip
        }
    });
    sources.len()
}

/// Collect the names of every event whose entry node reaches
/// `target_node` along the exec graph (with `K2Node_Knot` passthroughs).
///
/// The pre-built `node_to_reaching_events` map is filled once per
/// ubergraph by `build_node_to_reaching_events`. A target node missing
/// from the map has zero reaching events, returned as the empty set.
fn events_reaching_target(
    target_node: usize,
    node_to_reaching_events: &HashMap<usize, BTreeSet<String>>,
) -> BTreeSet<String> {
    node_to_reaching_events
        .get(&target_node)
        .cloned()
        .unwrap_or_default()
}

/// Build the reverse "for each node, set of events whose entry reaches
/// it" map by running a single forward `walk_exec_through_knots` per
/// event-entry K2Node and inserting the entry's event name under each
/// reached node.
pub(crate) fn build_node_to_reaching_events(
    event_node_index: &BTreeMap<String, usize>,
    pin_data: &HashMap<usize, NodePinData>,
    is_knot: impl Fn(usize) -> bool,
) -> HashMap<usize, BTreeSet<String>> {
    let mut reaching: HashMap<usize, BTreeSet<String>> = HashMap::new();
    for (event_name, &entry_node) in event_node_index {
        let reached = walk_exec_through_knots(entry_node, pin_data, &is_knot);
        for reached_node in reached {
            reaching
                .entry(reached_node)
                .or_default()
                .insert(event_name.clone());
        }
    }
    reaching
}

/// Walk forward from `start_node` along every exec-output pin's
/// `LinkedTo` edges, returning the set of non-knot K2Nodes
/// transitively reachable. Knot nodes (`K2Node_Knot`) are walked
/// through transparently and not included in the result.
///
/// A Knot is a graph-only routing node, the compiler erases it at
/// codegen so the bytecode jump bypasses any number of intermediate
/// knots. The classifier mirrors that behaviour by treating knots as
/// transparent.
///
/// The walk traverses every reachable non-knot node so a target node
/// sitting deeper in the graph (past Branch / Sequence / other
/// dispatchers) still appears in the reached set. The disambiguating
/// signal for shared-body classification is that the target is a
/// `K2Node_MacroInstance` resolving to `DoOnce` (filtered upstream by
/// `bytecode_to_node`), which constrains false positives to two
/// events that genuinely share the same DoOnce instance.
pub(crate) fn walk_exec_through_knots(
    start_node: usize,
    pin_data: &HashMap<usize, NodePinData>,
    is_knot: &impl Fn(usize) -> bool,
) -> BTreeSet<usize> {
    let mut reached: BTreeSet<usize> = BTreeSet::new();
    bfs_exec_links::<()>(
        start_node,
        PIN_DIRECTION_OUTPUT,
        pin_data,
        |node, _pin_id| {
            if !is_knot(node) {
                reached.insert(node);
            }
            Visit::Enqueue
        },
    );
    reached
}

/// Maximum gap (bytes) between two of a node's footprint ranges that the
/// clustering still merges. A DoOnce's gate-check, user-call body, and
/// gate-SET sit within one contiguous-ish run separated only by small
/// sub-expression gaps; a genuinely separate occurrence of the same node
/// (a second compiled copy) is hundreds of bytes away. `0x80` merges the
/// former and splits the latter for the BP_DecoderTest Release DoOnce.
const FOOTPRINT_CLUSTER_GAP: usize = 0x80;

/// Resolve the inline body range for an EMBEDDED shared DoOnce, the case
/// where the shared body is a sub-range of a larger owning event rather
/// than the owning event's whole (tight) range.
///
/// Returns `Some(range)` only when:
/// - the event owning `target_disk` reaches a DIFFERENT first DoOnce than
///   `target_node` (so the owning range does NOT tightly bound the body;
///   when they match it is the tight-body shape and the existing
///   `owning_range` resolution is correct, this returns `None`), and
/// - `target_node` has a `k2node_byte_map` footprint (the shared body's
///   gate+call bytes).
///
/// The returned range is the footprint cluster nearest `target_disk`,
/// which decodes to the bare guarded call the caller folds into
/// `DoOnce(){}`. Used both to gate the classifier's current-event fallback
/// (rejecting
/// unrelated out-of-range jumps from a multi-jump trampoline event) and
/// to bound the body decode in `decode_inlined_shared_body`.
pub(crate) fn embedded_inline_range(
    target_node: usize,
    target_disk: usize,
    cei: &CrossEventInlineCtx<'_>,
) -> Option<Range<usize>> {
    if !is_embedded_shared_target(target_node, target_disk, cei) {
        return None;
    }
    let part = cei.k2node_byte_map?.partitions.get(&target_node)?;
    footprint_cluster_for(target_disk, &part.ranges)
}

/// True when `target_disk` is a cross-event jump into a shared DoOnce that
/// is EMBEDDED inside a larger owning event, the event owning `target_disk`
/// reaches a DIFFERENT first DoOnce than `target_node`. When they match,
/// the owning event's range tightly bounds the shared body (the tight-body
/// shape) and the existing owning-range resolution is correct.
///
/// Distinguishes the two embedded body layouts BP_DecoderTest exhibits:
/// the LEFT event's shared body sits at `target_node`'s footprint cluster
/// (`embedded_inline_range` returns it, decoded flat then wrapped), while
/// the RIGHT event's body is a contiguous self-recognising copy starting
/// at `target_disk` itself (`embedded_inline_range` returns `None` because
/// the footprint is elsewhere, the caller bounds from `target_disk`).
pub(crate) fn is_embedded_shared_target(
    target_node: usize,
    target_disk: usize,
    cei: &CrossEventInlineCtx<'_>,
) -> bool {
    let Some(owning_event) = owning_event_for_disk(target_disk, cei.event_owned_ranges) else {
        return false;
    };
    let Some(&owning_entry) = cei.event_node_index.get(owning_event) else {
        return false;
    };
    first_doonce_macro_downstream(owning_entry, cei.pin_data, cei) != Some(target_node)
}

/// The contiguous footprint cluster nearest `target_disk`, or `None` when
/// `ranges` is empty.
///
/// Sorts `ranges` and merges those separated by at most
/// `FOOTPRINT_CLUSTER_GAP` into clusters (a node compiled into two
/// separate copies yields two clusters, each a full DoOnce gate+call
/// run). Returns the cluster whose span is closest to `target_disk`:
/// the cluster containing it, else the one minimising the gap to it.
/// The trampoline target can sit inside the body's gate prologue (LEFT,
/// just before the cluster) or in a distant dispatch region (RIGHT, the
/// shared body is reached indirectly), so proximity is a tiebreak, not a
/// gate, the editor graph already established this node is the shared
/// DoOnce the current event triggers.
fn footprint_cluster_for(target_disk: usize, ranges: &[Range<usize>]) -> Option<Range<usize>> {
    if ranges.is_empty() {
        return None;
    }
    let mut sorted: Vec<Range<usize>> = ranges.to_vec();
    sorted.sort_by_key(|range| range.start);
    let mut clusters: Vec<Range<usize>> = Vec::new();
    let mut cluster_start = sorted[0].start;
    let mut cluster_end = sorted[0].end;
    for range in &sorted[1..] {
        if range.start.saturating_sub(cluster_end) <= FOOTPRINT_CLUSTER_GAP {
            cluster_end = cluster_end.max(range.end);
        } else {
            clusters.push(cluster_start..cluster_end);
            cluster_start = range.start;
            cluster_end = range.end;
        }
    }
    clusters.push(cluster_start..cluster_end);
    clusters.into_iter().min_by_key(|cluster| {
        // distance from target_disk to the cluster's [start, end) interval
        if target_disk < cluster.start {
            cluster.start - target_disk
        } else {
            target_disk.saturating_sub(cluster.end)
        }
    })
}

/// Find the event whose owned disk ranges contain `target_disk`.
/// Returns the event name from `event_owned_ranges`, or `None` if no
/// event covers the offset (genuine orphan disk position).
fn owning_event_for_disk(
    target_disk: usize,
    event_owned_ranges: &BTreeMap<String, Vec<Range<usize>>>,
) -> Option<&str> {
    for (event_name, ranges) in event_owned_ranges {
        for range in ranges {
            if target_disk >= range.start && target_disk < range.end {
                return Some(event_name.as_str());
            }
        }
    }
    None
}

/// BFS from `entry_node` through exec-output pins (with knot
/// passthrough) returning the FIRST reachable K2Node whose
/// `node_to_reaching_events` set has 2 or more events AND includes
/// `current_event_name`, regardless of the node's `K2NodeClass`.
///
/// This is the shape-agnostic generalization of
/// [`first_doonce_macro_downstream`]: where that resolver only accepts a
/// DoOnce MacroInstance, this accepts any convergence node (a shared
/// plain call, Sequence, FlipFlop, or DoOnce) as long as it is genuinely
/// shared by the current event and at least one other. The DoOnce case is
/// a strict subset, so this subsumes it.
///
/// Returns `None` when no node downstream of `entry_node` is a multi-event
/// convergence including the current event. Used by the general
/// cross-event inline parallel helper only.
fn first_convergence_node_downstream(
    entry_node: usize,
    current_event_name: &str,
    pin_data: &HashMap<usize, NodePinData>,
    node_to_reaching_events: &HashMap<usize, BTreeSet<String>>,
) -> Option<usize> {
    bfs_exec_links::<usize>(
        entry_node,
        PIN_DIRECTION_OUTPUT,
        pin_data,
        |node, _pin_id| {
            let reaching = events_reaching_target(node, node_to_reaching_events);
            if reaching.len() >= 2 && reaching.contains(current_event_name) {
                Visit::Found(node)
            } else {
                Visit::Enqueue
            }
        },
    )
}

/// Classify a decode-time forward jump as intra-event or a cross-event
/// inline landing, returning the resolved disposition.
///
/// Resolution axes:
/// - convergence-node target detection via
///   [`first_convergence_node_downstream`] (not DoOnce-only), and
/// - the intra-event short-circuit, the
///   owning-event-then-current-event resolution preference, and the
///   `embedded_inline_range` gate on the current-event fallback.
///
/// The load-bearing membership check (`reaching_events.len() >= 2 &&
/// contains(current)`) is the over-fire guard.
pub(crate) fn classify_for_decode_jump(
    target_mem: usize,
    target_disk: usize,
    event_entries: &BTreeMap<usize, String>,
    cei: &CrossEventInlineCtx<'_>,
) -> CrossEventDisposition {
    if let Some(owning) = owning_event_for_disk(target_disk, cei.event_owned_ranges) {
        if owning == cei.current_event_name {
            return CrossEventDisposition::Drop;
        }
    }
    let is_knot = |node_id: usize| -> bool {
        matches!(cei.node_classes.get(&node_id), Some(K2NodeClass::Knot))
    };
    let bytecode_to_node = |disk: usize| -> Option<usize> {
        let owning_candidate = owning_event_for_disk(disk, cei.event_owned_ranges)
            .and_then(|owning_event| cei.event_node_index.get(owning_event))
            .and_then(|&entry_node| {
                first_convergence_node_downstream(
                    entry_node,
                    cei.current_event_name,
                    cei.pin_data,
                    cei.node_to_reaching_events,
                )
            });
        if let Some(node) = owning_candidate {
            if is_shared_body_anchor(
                node,
                cei.current_event_name,
                cei.pin_data,
                &is_knot,
                cei.node_to_reaching_events,
                false,
            ) {
                return Some(node);
            }
        }
        let current_candidate =
            cei.event_node_index
                .get(cei.current_event_name)
                .and_then(|&entry_node| {
                    first_convergence_node_downstream(
                        entry_node,
                        cei.current_event_name,
                        cei.pin_data,
                        cei.node_to_reaching_events,
                    )
                });
        if let Some(node) = current_candidate {
            if embedded_inline_range(node, disk, cei).is_some() {
                return Some(node);
            }
        }
        owning_candidate
    };
    classify_cross_event_jump(
        target_mem,
        target_disk,
        cei.current_event_name,
        cei.pin_data,
        event_entries,
        bytecode_to_node,
        is_knot,
        cei.node_to_reaching_events,
    )
}

/// Classify a cross-event jump for inline / schedule / drop disposition
/// with the shared-body anchor check running WITHOUT the knot fan-in
/// gate (`require_knot_fan_in = false`).
#[allow(clippy::too_many_arguments)]
fn classify_cross_event_jump(
    target_mem: usize,
    target_disk: usize,
    current_event_name: &str,
    pin_data: &HashMap<usize, NodePinData>,
    event_entries: &BTreeMap<usize, String>,
    bytecode_to_node: impl Fn(usize) -> Option<usize>,
    is_knot: impl Fn(usize) -> bool,
    node_to_reaching_events: &HashMap<usize, BTreeSet<String>>,
) -> CrossEventDisposition {
    if let Some(name) = event_entries.get(&target_mem) {
        return CrossEventDisposition::Schedule {
            event_name: name.clone(),
        };
    }

    let Some(target_node) = bytecode_to_node(target_disk) else {
        return CrossEventDisposition::Drop;
    };

    if !is_shared_body_anchor(
        target_node,
        current_event_name,
        pin_data,
        &is_knot,
        node_to_reaching_events,
        false,
    ) {
        return CrossEventDisposition::Drop;
    }

    CrossEventDisposition::Inline {
        target_node,
        anchor_disk: target_disk,
    }
}

/// BFS from `entry_node` through exec-output pins (with knot
/// passthrough) returning the first reachable K2Node whose macro name
/// equals "DoOnce". Returns `None` if no DoOnce sits downstream.
fn first_doonce_macro_downstream(
    entry_node: usize,
    pin_data: &HashMap<usize, NodePinData>,
    cei: &CrossEventInlineCtx<'_>,
) -> Option<usize> {
    bfs_exec_links::<usize>(
        entry_node,
        PIN_DIRECTION_OUTPUT,
        pin_data,
        |node, _pin_id| {
            let is_doonce = matches!(
                cei.node_classes.get(&node),
                Some(K2NodeClass::MacroInstance)
            ) && cei
                .macro_names
                .get(&node)
                .is_some_and(|macro_name| MacroKind::from_name(macro_name) == MacroKind::DoOnce);
            if is_doonce {
                Visit::Found(node)
            } else {
                Visit::Enqueue
            }
        },
    )
}

/// Resolve the bytecode disk range for a target K2Node's logical entry,
/// expanding the trampoline-target offset back to the K2Node's true
/// scaffold start.
///
/// Cross-event trampolines land at the K2Node body region's interior
/// (typically the user-call subtree of a DoOnce macro), past the gate /
/// init scaffold the standalone event's recogniser folds into the
/// `Stmt::Latch`. Without expansion the inline decode sees only the
/// suffix and the recogniser splits the scaffold across two passes,
/// producing nested Latch wrappers. Anchoring back at the K2Node's true
/// entry brings the inline decode in line with the standalone event's
/// scaffold view.
///
/// Resolution preference order:
/// 1. The push chain in `skeleton.push_chains` whose pin partitions
///    contain `target_disk` (innermost wins for nested chains). The
///    chain head is the K2Node's logical entry.
/// 2. The contiguous owned range of the standalone event that contains
///    `target_disk`. This is the fallback when no chain wraps the
///    target, e.g. a standalone event whose body is a single macro
///    instance. The standalone event's range start is the K2Node's
///    logical entry by construction.
///
/// Edge cases:
/// - Multiple disjoint chains contain `target_disk`: pick the innermost
///   (largest head <= target_disk).
/// - Resolved range straddles a different event's owned range: STOP
///   condition 2 from the design doc; return `None` so the caller falls
///   back to legacy behaviour.
pub(crate) fn k2node_bytecode_range(
    _target_node: usize,
    target_disk: usize,
    skeleton: &crate::bytecode::structure::StructureSkeleton,
    event_owned_ranges: &BTreeMap<String, Vec<Range<usize>>>,
) -> Option<Range<usize>> {
    let owning_event = owning_event_for_disk(target_disk, event_owned_ranges)?;
    let owning_ranges = event_owned_ranges.get(owning_event)?;
    let owning_range = owning_ranges
        .iter()
        .find(|range| target_disk >= range.start && target_disk < range.end)?;

    let mut best_head: Option<usize> = None;
    for (&head_disk, chain) in skeleton.push_chains.iter() {
        if head_disk > target_disk {
            continue;
        }
        let contains = chain.head <= target_disk
            && chain
                .pin_partitions
                .iter()
                .any(|segments| segments.iter().any(|seg| target_disk < seg.end));
        if contains {
            best_head = Some(head_disk);
        }
    }

    // Fallback: no chain wraps the target. Use the owning event's
    // contiguous range start as the K2Node entry. Standalone events
    // with a single macro body (no Sequence push chain) take this path.
    let entry = best_head.unwrap_or(owning_range.start);
    let resolved = entry..owning_range.end;
    if resolved.start >= resolved.end {
        return None;
    }

    // STOP-and-report case 2: resolved range overlaps a different
    // event's owned ranges. Return None so the caller can decide whether
    // to fall back or skip; do not silently absorb sibling-event bytes.
    for (event_name, ranges) in event_owned_ranges {
        if event_name == owning_event {
            continue;
        }
        for other in ranges {
            let overlaps = resolved.start < other.end && other.start < resolved.end;
            if overlaps {
                return None;
            }
        }
    }

    Some(resolved)
}

/// Re-wrap a non-owner event's flat body into a `Stmt::Sequence` when its
/// graph identity is a per-event `K2Node_ExecutionSequence` whose then-0
/// became a cross-event jump (divergent-tail boundary).
///
/// Shape: `Conv_DivergentTail_{A,B}` are paired CustomEvents, each driving
/// its OWN N-pin Sequence node. Their then-0 pins converge on one shared
/// downstream node; their then-1 pins diverge to per-event content. The
/// owner (`_A`) keeps an `EX_PUSH_EXECUTION_FLOW` chain so the Sequence
/// recogniser builds `Stmt::Sequence`. The non-owner (`_B`) had its then-0
/// compiled to a direct cross-event jump (no push chain), so the shared
/// then-0 body inlines as a flat top-level statement and then-1 falls
/// through as a sibling, decoding flat instead of as a Sequence.
///
/// The owner's bytecode-driven Sequence is the source of truth that the
/// shape IS a Sequence; the non-owner reconstructs the same shape from
/// graph identity by wrapping its already-correct flat statements (one per
/// pin) into a `Stmt::Sequence`. Mutates `body` in place; a no-op when the
/// shape does not match.
///
/// Discriminators (all required), each excluding the four single-target
/// `Conv_*_B` shapes that already render correctly:
/// - the event entry drives a node with `>= 2` exec-output pins (a
///   Sequence); the single-shared-target cases drive a 1-pin call/macro;
/// - `body` is a flat list of exactly that pin count, with no top-level
///   `Stmt::Sequence` (the already-correct shared-Sequence case is one
///   `Stmt::Sequence`, so its length is 1, not the pin count);
/// - at least one statement offset lies OUTSIDE the event's owned ranges
///   (the inlined shared then-0) AND at least one lies INSIDE (the event's
///   own divergent tail). This mixed-origin body is the divergent-tail
///   signature; a wholly-shared or wholly-own body does not match.
pub(crate) fn wrap_divergent_tail_sequence(
    body: &mut Vec<crate::bytecode::stmt::Stmt>,
    event_name: &str,
    owned_ranges: &[Range<usize>],
    cei: &CrossEventInlineCtx,
    node_class_names: &HashMap<usize, String>,
    pin_data: &HashMap<usize, NodePinData>,
) {
    use crate::bytecode::stmt::Stmt;

    let Some(&entry_node) = cei.event_node_index.get(event_name) else {
        return;
    };
    let Some(entry_pins) = pin_data.get(&entry_node) else {
        return;
    };

    // The single node the entry's exec-output pins drive. A CustomEvent has
    // one "then" pin; require it to lead to exactly one node so the
    // Sequence identity is unambiguous.
    let driven_node = {
        let mut targets: BTreeSet<usize> = BTreeSet::new();
        for pin in &entry_pins.pins {
            if pin.is_exec_output() {
                for link in &pin.linked_to {
                    targets.insert(link.node);
                }
            }
        }
        if targets.len() != 1 {
            return;
        }
        *targets.iter().next().unwrap()
    };
    if node_class_names.get(&driven_node).map(String::as_str) != Some(K2NODE_EXECUTION_SEQUENCE) {
        return;
    }
    let Some(seq_pins) = pin_data.get(&driven_node) else {
        return;
    };
    let pin_count = seq_pins
        .pins
        .iter()
        .filter(|pin| pin.is_exec_output())
        .count();
    if pin_count < 2 || body.len() != pin_count {
        return;
    }
    if body
        .iter()
        .any(|stmt| matches!(stmt, Stmt::Sequence { .. }))
    {
        return;
    }

    let in_owned = |offset: usize| {
        owned_ranges
            .iter()
            .any(|range| offset >= range.start && offset < range.end)
    };
    let mut saw_inlined = false;
    let mut saw_own = false;
    for stmt in body.iter() {
        if in_owned(stmt.offset()) {
            saw_own = true;
        } else {
            saw_inlined = true;
        }
    }
    if !(saw_inlined && saw_own) {
        return;
    }

    let offset = body[0].offset();
    let pins: Vec<Vec<Stmt>> = body.drain(..).map(|stmt| vec![stmt]).collect();
    body.push(Stmt::Sequence { pins, offset });
}
