//! Tests for `decode/cross_event_inline.rs`. Extracted from the production
//! module so the cross-event classifier stays focused on its data flow;
//! the synthetic pin/node fixtures that exercise each branch live here.

use super::cross_event_inline::*;
use crate::types::NodePinData;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Range;

const TARGET: usize = 300;

const SOURCE_EVENT_NAME: &str = "RightHandGripReleased";
const OTHER_EVENT_NAME: &str = "LeftHandGripReleased";

/// Construct a `Vec<Range<usize>>` containing a single range. Used
/// to bypass clippy's `single_range_in_vec_init` lint, which fires
/// on `vec![start..end]` and `Vec::from([start..end])` literals
/// because they look like attempts to construct a Vec of integers
/// in the range.
fn single_range(range: Range<usize>) -> Vec<Range<usize>> {
    std::iter::once(range).collect()
}

/// Build an empty `CrossEventInlineCtx` parameterised by name. Used
/// by dedup tests that don't need pin topology, so `pin_data` is the
/// caller-supplied empty map.
fn dedup_ctx<'a>(
    current_event_name: &'a str,
    event_owned_ranges: &'a BTreeMap<String, Vec<Range<usize>>>,
    event_node_index: &'a BTreeMap<String, usize>,
    pin_data: &'a HashMap<usize, NodePinData>,
    node_classes: &'a HashMap<usize, K2NodeClass>,
    macro_names: &'a HashMap<usize, String>,
    node_to_reaching_events: &'a HashMap<usize, BTreeSet<String>>,
) -> CrossEventInlineCtx<'a> {
    CrossEventInlineCtx {
        current_event_name,
        event_owned_ranges,
        event_node_index,
        node_to_reaching_events,
        pin_data,
        node_classes,
        macro_names,
        active_inline_anchors: RefCell::new(BTreeSet::new()),
        inlined_targets: RefCell::new(BTreeSet::new()),
        k2node_byte_map: None,
    }
}

#[test]
fn record_then_already_inlined_for_same_pair() {
    let ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    let node_index: BTreeMap<String, usize> = BTreeMap::new();
    let classes: HashMap<usize, K2NodeClass> = HashMap::new();
    let macros: HashMap<usize, String> = HashMap::new();
    let pin_data: HashMap<usize, NodePinData> = HashMap::new();
    let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
    let cei = dedup_ctx(
        SOURCE_EVENT_NAME,
        &ranges,
        &node_index,
        &pin_data,
        &classes,
        &macros,
        &node_to_reaching_events,
    );
    let entry = 0x123;
    assert!(!cei.already_inlined_target(entry));
    assert!(cei.record_inlined_target(entry));
    assert!(cei.already_inlined_target(entry));
    // Re-recording the same pair returns false.
    assert!(!cei.record_inlined_target(entry));
}

#[test]
fn record_distinct_entries_do_not_collide() {
    let ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    let node_index: BTreeMap<String, usize> = BTreeMap::new();
    let classes: HashMap<usize, K2NodeClass> = HashMap::new();
    let macros: HashMap<usize, String> = HashMap::new();
    let pin_data: HashMap<usize, NodePinData> = HashMap::new();
    let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
    let cei = dedup_ctx(
        SOURCE_EVENT_NAME,
        &ranges,
        &node_index,
        &pin_data,
        &classes,
        &macros,
        &node_to_reaching_events,
    );
    cei.record_inlined_target(0x100);
    cei.record_inlined_target(0x200);
    assert!(cei.already_inlined_target(0x100));
    assert!(cei.already_inlined_target(0x200));
    assert!(!cei.already_inlined_target(0x300));
}

#[test]
fn dedup_clears_between_events() {
    let ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    let node_index: BTreeMap<String, usize> = BTreeMap::new();
    let classes: HashMap<usize, K2NodeClass> = HashMap::new();
    let macros: HashMap<usize, String> = HashMap::new();
    let pin_data: HashMap<usize, NodePinData> = HashMap::new();
    let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
    let cei = dedup_ctx(
        SOURCE_EVENT_NAME,
        &ranges,
        &node_index,
        &pin_data,
        &classes,
        &macros,
        &node_to_reaching_events,
    );
    cei.record_inlined_target(0x123);
    assert!(cei.already_inlined_target(0x123));
    cei.inlined_targets.borrow_mut().clear();
    assert!(!cei.already_inlined_target(0x123));
}

#[test]
fn dedup_resets_between_events_via_clear() {
    // The set is per-event lifetime: source-event identity isn't in
    // the key, so the orchestrator clears (or builds a fresh ctx)
    // before each event so the same resolved-entry disk can
    // re-render under a sibling source event.
    let ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    let node_index: BTreeMap<String, usize> = BTreeMap::new();
    let classes: HashMap<usize, K2NodeClass> = HashMap::new();
    let macros: HashMap<usize, String> = HashMap::new();
    let pin_data: HashMap<usize, NodePinData> = HashMap::new();
    let node_to_reaching_events: HashMap<usize, BTreeSet<String>> = HashMap::new();
    let entry = 0x123;
    let cei = dedup_ctx(
        SOURCE_EVENT_NAME,
        &ranges,
        &node_index,
        &pin_data,
        &classes,
        &macros,
        &node_to_reaching_events,
    );
    cei.record_inlined_target(entry);
    assert!(cei.already_inlined_target(entry));
    cei.inlined_targets.borrow_mut().clear();
    assert!(!cei.already_inlined_target(entry));
}

/// Build a single-chain skeleton over `[head_disk..end)` whose pin
/// partition covers the whole range. Sufficient to exercise
/// `k2node_bytecode_range`'s "chain contains target_disk" path.
fn one_chain_skeleton(
    head_disk: usize,
    end: usize,
) -> crate::bytecode::structure::StructureSkeleton {
    use crate::bytecode::structure::{PushChainNode, StructureSkeleton};
    let mut chains = BTreeMap::new();
    chains.insert(
        head_disk,
        PushChainNode {
            head: head_disk,
            after_chain: head_disk + 1,
            push_targets: vec![head_disk + 1],
            pin_partitions: vec![single_range(head_disk + 1..end)],
            parent_chain: None,
        },
    );
    StructureSkeleton {
        push_chains: chains,
    }
}

#[test]
fn k2node_range_picks_chain_head_when_chain_contains_target() {
    // Owning event covers [0x100..0x200). One chain rooted at 0x110
    // whose pin partition covers [0x111..0x200). Target disk 0x180
    // sits inside the partition. Resolved entry is the chain head.
    let mut owned: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    owned.insert(SOURCE_EVENT_NAME.to_string(), single_range(0x100..0x200));
    let skeleton = one_chain_skeleton(0x110, 0x200);
    let range = k2node_bytecode_range(TARGET, 0x180, &skeleton, &owned).expect("resolved");
    assert_eq!(range, 0x110..0x200);
}

#[test]
fn k2node_range_falls_back_to_owning_range_start_without_chain() {
    // Owning event covers [0x100..0x200). Empty skeleton (standalone
    // event with a single macro body). Target disk 0x180 has no
    // chain to expand from; resolver picks the owning range start.
    let mut owned: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    owned.insert(SOURCE_EVENT_NAME.to_string(), single_range(0x100..0x200));
    let skeleton = crate::bytecode::structure::StructureSkeleton::default();
    let range = k2node_bytecode_range(TARGET, 0x180, &skeleton, &owned).expect("resolved");
    assert_eq!(range, 0x100..0x200);
}

#[test]
fn k2node_range_returns_none_when_no_event_owns_target() {
    // Target disk 0x500 sits outside every event's owned range.
    let mut owned: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    owned.insert(SOURCE_EVENT_NAME.to_string(), single_range(0x100..0x200));
    let skeleton = crate::bytecode::structure::StructureSkeleton::default();
    let range = k2node_bytecode_range(TARGET, 0x500, &skeleton, &owned);
    assert!(range.is_none());
}

#[test]
fn k2node_range_returns_none_when_resolved_overlaps_other_event() {
    // Owning event A covers [0x100..0x200). A second event B owns
    // [0x150..0x180) (would only happen if the resolver picked a
    // chain head before B's range start, expanding A's body to
    // overlap B). Sanity guard: return None.
    use crate::bytecode::structure::{PushChainNode, StructureSkeleton};
    let mut owned: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    owned.insert(SOURCE_EVENT_NAME.to_string(), single_range(0x100..0x200));
    owned.insert(OTHER_EVENT_NAME.to_string(), single_range(0x150..0x180));
    // A chain whose head sits before B but whose partition reaches
    // past B's start, so resolved range overlaps B.
    let mut chains = BTreeMap::new();
    chains.insert(
        0x110,
        PushChainNode {
            head: 0x110,
            after_chain: 0x111,
            push_targets: vec![0x111],
            pin_partitions: vec![single_range(0x111..0x200)],
            parent_chain: None,
        },
    );
    let skeleton = StructureSkeleton {
        push_chains: chains,
    };
    // target_disk 0x190 sits inside A's range past B; resolver
    // would expand to [0x110..0x200) which overlaps B's [0x150..0x180).
    let range = k2node_bytecode_range(TARGET, 0x190, &skeleton, &owned);
    assert!(
        range.is_none(),
        "expected None for overlap, got {:?}",
        range
    );
}
