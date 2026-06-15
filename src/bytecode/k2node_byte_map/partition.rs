//! Macro-instance, sequence, tracepoint, latent-resume, and
//! enclosing-scope partition building.
//!
//! Derives each `K2Node_MacroInstance` span from downstream pin
//! reachability, attributes `K2Node_ExecutionSequence` push-chain
//! footprints, tags tracepoint and latent-resume opcodes, and runs the
//! SESE enclosing-scope fallback for bytes no direct rule claimed.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::decode::cross_event_inline::K2NodeClass;
use crate::bytecode::names::MacroKind;
use crate::bytecode::names::K2NODE_EXECUTION_SEQUENCE;
use crate::bytecode::opcodes::{
    EX_INSTRUMENTATION_EVENT, EX_PUSH_EXECUTION_FLOW, EX_TRACEPOINT, EX_WIRE_TRACEPOINT,
};
use crate::resolve::{resolve_index, short_class};
use crate::types::{NodePinData, PIN_DIRECTION_OUTPUT, PIN_TYPE_EXEC};

use super::offsets::{build_offsets_by_callfunc_node, build_offsets_by_varset_node};
use super::{
    clamp_offsets_to_ranges, extend_owner_events, is_recognised_macro, node_class,
    owner_events_for_node, push_range, span_of, K2NodeByteMapInputs, K2NodePartition,
};

/// Attribute disk bytes to `K2Node_MacroInstance` exports whose macro
/// short name is `DoOnce` or `IsValid`. Each macro instance has its
/// range derived from the disk offsets of downstream callable K2Nodes
/// reachable through the macro's exec-output pins.
pub(super) fn attribute_macro_instances(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
) {
    let downstream_calls = collect_downstream_call_offsets(inputs);
    for (&node_id, class) in inputs.node_classes {
        if !matches!(class, K2NodeClass::MacroInstance) {
            continue;
        }
        let Some(macro_name) = inputs.macro_names.get(&node_id) else {
            continue;
        };
        if !is_recognised_macro(macro_name) {
            continue;
        }
        let owners = owner_events_for_node(node_id, inputs);
        let Some(offsets) = downstream_calls.get(&node_id) else {
            // No downstream callable for this macro instance. Record
            // a zero-range partition when at least one event reaches
            // the node so it remains visible to the macro-scaffold pass's
            // audit harness; skip otherwise to keep empty entries from
            // polluting the audit surface.
            if !owners.is_empty() {
                partitions.entry(node_id).or_insert_with(|| {
                    K2NodePartition::new(
                        node_id,
                        owners.clone(),
                        K2NodeClass::MacroInstance,
                        Some(MacroKind::from_name(macro_name)),
                    )
                });
            }
            continue;
        };
        // Compute the macro's anchor range per owning event. A single
        // MacroInstance shared across events (knot fan-in) emits ONE
        // partition with one range per reaching-event anchor.
        let reaching = inputs
            .node_to_reaching_events
            .get(&node_id)
            .cloned()
            .unwrap_or_default();
        let mut ranges: Vec<Range<usize>> = Vec::new();
        if reaching.is_empty() {
            // No event reaches the macro. Fall back to the bare span
            // of downstream call offsets without owner clamping.
            if let Some(span) = span_of(offsets) {
                push_range(&mut ranges, span);
            }
        } else {
            for event_name in &reaching {
                let Some(event_ranges) = inputs.event_owned_ranges.get(event_name) else {
                    continue;
                };
                let clamped = clamp_offsets_to_ranges(offsets, event_ranges);
                if let Some(span) = span_of(&clamped) {
                    push_range(&mut ranges, span);
                }
            }
        }
        let partition = partitions
            .entry(node_id)
            .or_insert_with(|| K2NodePartition {
                node_id,
                ranges,
                owner_events: owners.clone(),
                kind: K2NodeClass::MacroInstance,
                macro_kind: Some(MacroKind::from_name(macro_name)),
                via_fallback: Vec::new(),
            });
        extend_owner_events(partition, owners);
    }
}

/// Attribute every `K2Node_ExecutionSequence` to its push-chain
/// footprint. For each event with at least one Sequence node we
/// build the per-event `StructureSkeleton` and walk its push chains;
/// each chain is matched back to the K2Node_ExecutionSequence whose
/// ordered exec output pins target the same downstream node ids the
/// chain's `push_targets` resolve to. The Sequence partition covers
/// the chain head, every `EX_PUSH_EXECUTION_FLOW` opcode in the
/// chain, and each pin body range.
pub(super) fn attribute_execution_sequences(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let sequence_nodes = collect_execution_sequence_nodes(inputs);
    if sequence_nodes.is_empty() {
        return;
    }
    let offsets_by_callfunc_node = build_offsets_by_callfunc_node(inputs);
    let offsets_by_varset_node = build_offsets_by_varset_node(inputs);
    let target_to_node_offsets = |target_node: usize| -> BTreeSet<usize> {
        let mut offsets = BTreeSet::new();
        if let Some(items) = offsets_by_callfunc_node.get(&target_node) {
            offsets.extend(items.iter().copied());
        }
        if let Some(items) = offsets_by_varset_node.get(&target_node) {
            offsets.extend(items.iter().copied());
        }
        offsets
    };

    for (event_name, event_ranges) in inputs.event_owned_ranges.iter() {
        let owner_range = union_range(event_ranges);
        let Some(owner_range) = owner_range else {
            continue;
        };
        let skeleton = crate::bytecode::structure::build_skeleton(
            inputs.bytecode,
            inputs.ue5,
            inputs.name_table,
            inputs.mem_to_disk,
            owner_range,
            &[],
            Some(inputs.graph),
        );
        if skeleton.push_chains.is_empty() {
            continue;
        }
        for (&_head_disk, chain) in skeleton.push_chains.iter() {
            let Some(sequence_node) = match_chain_to_sequence(
                chain,
                &sequence_nodes,
                &inputs.asset.pin_data,
                &target_to_node_offsets,
            ) else {
                continue;
            };
            apply_sequence_partition(
                sequence_node,
                chain,
                inputs,
                event_name,
                inputs.bytecode,
                partitions,
                byte_to_node,
            );
        }
    }
}

/// Tag each latent-call resume block with the K2Node id of the
/// originating Delay call. The Delay call site has already been
/// attributed to a `K2Node_CallFunction` by `attribute_calls`, so
/// we look up the call offset (the resume_blocks key) in
/// `byte_to_node` and copy the attribution onto every opcode in the
/// resume range. Resume blocks not preceded by an attributed call
/// (e.g. cooked-asset patterns we don't yet support) are skipped.
pub(super) fn attribute_latent_resume_blocks(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    if inputs.resume_blocks.is_empty() {
        return;
    }
    let graph = inputs.graph;
    for (&call_offset, resume_range) in inputs.resume_blocks.iter() {
        let Some(call_nodes) = byte_to_node.get(&call_offset).cloned() else {
            continue;
        };
        for node_id in call_nodes {
            let owners = owner_events_for_node(node_id, inputs);
            let partition = partitions.entry(node_id).or_insert_with(|| {
                K2NodePartition::new(
                    node_id,
                    owners.clone(),
                    node_class(inputs, node_id),
                    inputs
                        .macro_names
                        .get(&node_id)
                        .map(|name| MacroKind::from_name(name)),
                )
            });
            extend_owner_events(partition, owners);
            push_range(&mut partition.ranges, resume_range.clone());
            // `Range::contains` is start-inclusive / end-exclusive, exactly
            // the bound `.range(start..end)` walks, so the range query
            // visits the same boundaries in the same ascending order while
            // skipping the boundaries outside the resume range.
            for &opcode_offset in graph.boundaries.range(resume_range.start..resume_range.end) {
                byte_to_node.entry(opcode_offset).or_default().push(node_id);
            }
        }
    }
}

/// Attribute every tracepoint opcode (EX_TRACEPOINT,
/// EX_WIRE_TRACEPOINT, EX_INSTRUMENTATION_EVENT) inside an event's
/// owned ranges to the event's entry K2Node id. Tracepoints are
/// instrumentation, not a Blueprint-modelled construct, so they
/// belong to whichever event scope contains them. Achieves 100%
/// coverage for this opcode class when `event_node_index` resolves.
pub(super) fn attribute_tracepoints(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    for (event_name, event_ranges) in inputs.event_owned_ranges.iter() {
        let Some(&event_node) = inputs.event_node_index.get(event_name) else {
            continue;
        };
        for range in event_ranges {
            let mut cursor = range.start;
            while cursor < range.end && cursor < inputs.bytecode.len() {
                let opcode = inputs.bytecode[cursor];
                if matches!(
                    opcode,
                    EX_TRACEPOINT | EX_WIRE_TRACEPOINT | EX_INSTRUMENTATION_EVENT
                ) {
                    attribute_tracepoint_at(
                        event_node,
                        cursor,
                        opcode,
                        event_name,
                        inputs,
                        partitions,
                        byte_to_node,
                    );
                }
                let step = crate::bytecode::partition::opcode_length_at(
                    cursor,
                    inputs.bytecode,
                    inputs.ue5,
                    inputs.name_table,
                );
                if step == 0 {
                    break;
                }
                cursor += step;
            }
        }
    }
}

/// Enclosing-scope fallback. For each event with bytes not yet
/// attributed by the direct rules (calls, macros, varsets, casts,
/// sequences), build a per-event CFG + SESE region tree, locate each
/// unassigned byte's enclosing region, look up the region's entry
/// block's first opcode in `byte_to_node` to inherit attribution, and
/// fall back to the event entry K2Node when no region match exists.
/// Returns the bytes that remain unassigned after the fallback pass
/// (typically empty when an event entry K2Node is registered).
pub(super) fn attribute_enclosing_scope_fallback(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) -> Vec<Range<usize>> {
    let graph = inputs.graph;
    let mut remaining_unassigned: Vec<Range<usize>> = Vec::new();
    for (event_name, event_ranges) in inputs.event_owned_ranges.iter() {
        let unassigned = collect_unassigned_event_opcodes(graph, event_ranges, byte_to_node);
        if unassigned.is_empty() {
            continue;
        }
        let Some(&entry_disk) = inputs.event_entries.get(event_name) else {
            continue;
        };
        let (cfg, region_tree, _region_byte_ranges) = build_fallback_event_cfg_and_region_tree(
            entry_disk,
            event_ranges,
            graph,
            inputs.bytecode,
            inputs.ue5,
            inputs.name_table,
            inputs.mem_to_disk,
        );
        let event_node = inputs.event_node_index.get(event_name).copied();
        for unassigned_offset in unassigned {
            let inherited_node =
                resolve_via_region_entry(unassigned_offset, &cfg, &region_tree, byte_to_node);
            let resolved_node = inherited_node.or(event_node);
            let Some(target_node) = resolved_node else {
                remaining_unassigned.push(unassigned_offset..unassigned_offset + 1);
                continue;
            };
            attribute_fallback_byte(
                target_node,
                unassigned_offset,
                event_name,
                inputs,
                partitions,
                byte_to_node,
            );
        }
    }
    remaining_unassigned
}

/// For each recognised `K2Node_MacroInstance`, BFS the exec-output
/// pins (with knot passthrough) and collect the disk offsets of every
/// downstream `K2Node_CallFunction` or `K2Node_VariableSet` whose
/// short name matches a corresponding opcode in the bytecode.
///
/// Variable-set inclusion covers FlipFlop's pin A and pin B, which
/// typically link to a `K2Node_VariableSet` downstream rather than a
/// call.
fn collect_downstream_call_offsets(
    inputs: &K2NodeByteMapInputs<'_>,
) -> HashMap<usize, BTreeSet<usize>> {
    let mut by_node: HashMap<usize, BTreeSet<usize>> = HashMap::new();
    let offsets_by_callfunc_node = build_offsets_by_callfunc_node(inputs);
    let offsets_by_varset_node = build_offsets_by_varset_node(inputs);
    for (&node_id, class) in inputs.node_classes {
        if !matches!(class, K2NodeClass::MacroInstance) {
            continue;
        }
        let Some(macro_name) = inputs.macro_names.get(&node_id) else {
            continue;
        };
        if !is_recognised_macro(macro_name) {
            continue;
        }
        let reached = bfs_downstream_nodes(node_id, &inputs.asset.pin_data, inputs.node_classes);
        let mut offsets = BTreeSet::new();
        for reached_node in reached {
            if let Some(call_offsets) = offsets_by_callfunc_node.get(&reached_node) {
                offsets.extend(call_offsets.iter().copied());
            }
            if let Some(set_offsets) = offsets_by_varset_node.get(&reached_node) {
                offsets.extend(set_offsets.iter().copied());
            }
        }
        if !offsets.is_empty() {
            by_node.insert(node_id, offsets);
        }
    }
    by_node
}

/// Forward BFS through exec-output pins from `seed`, walking through
/// `K2Node_Knot` nodes transparently. Returns every reached node id
/// including the seed.
fn bfs_downstream_nodes(
    seed: usize,
    pin_data: &HashMap<usize, NodePinData>,
    node_classes: &HashMap<usize, K2NodeClass>,
) -> BTreeSet<usize> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    visited.insert(seed);
    queue.push_back(seed);
    while let Some(current) = queue.pop_front() {
        let Some(pins) = pin_data.get(&current) else {
            continue;
        };
        for pin in &pins.pins {
            if pin.pin_type != PIN_TYPE_EXEC || pin.direction != PIN_DIRECTION_OUTPUT {
                continue;
            }
            for link in &pin.linked_to {
                if visited.insert(link.node) {
                    // Recurse through knots transparently; stop at
                    // every other node class (the node itself is the
                    // attribution leaf).
                    if matches!(node_classes.get(&link.node), Some(K2NodeClass::Knot)) {
                        queue.push_back(link.node);
                    }
                }
            }
        }
    }
    visited.remove(&seed);
    visited
}

/// Collect every `K2Node_ExecutionSequence` export id paired with the
/// ordered list of target node ids reached through its exec output
/// pins (one entry per output pin).
fn collect_execution_sequence_nodes(inputs: &K2NodeByteMapInputs<'_>) -> Vec<(usize, Vec<usize>)> {
    let mut result: Vec<(usize, Vec<usize>)> = Vec::new();
    for (zero_based, (hdr, _)) in inputs.asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = resolve_index(&inputs.asset.imports, inputs.export_names, hdr.class_index);
        if short_class(&class_full) != K2NODE_EXECUTION_SEQUENCE {
            continue;
        }
        let Some(pins) = inputs.asset.pin_data.get(&one_based) else {
            continue;
        };
        let mut targets: Vec<usize> = Vec::new();
        for pin in &pins.pins {
            if !pin.is_exec_output() {
                continue;
            }
            if let Some(first_link) = pin.linked_to.first() {
                targets.push(first_link.node);
            }
        }
        if !targets.is_empty() {
            result.push((one_based, targets));
        }
    }
    result
}

/// Match a push chain back to its source `K2Node_ExecutionSequence`.
/// A chain matches when the i-th `push_targets[i]` offset belongs to
/// the i-th downstream-node id recorded on the sequence's pins. The
/// match accepts a chain whose target offsets are a prefix of the
/// sequence's pin targets (compiler-omitted trailing empty pins).
fn match_chain_to_sequence<F>(
    chain: &crate::bytecode::structure::PushChainNode,
    sequence_nodes: &[(usize, Vec<usize>)],
    pin_data: &HashMap<usize, NodePinData>,
    target_to_node_offsets: &F,
) -> Option<usize>
where
    F: Fn(usize) -> BTreeSet<usize>,
{
    for (sequence_node_id, pin_targets) in sequence_nodes {
        if pin_targets.len() < chain.push_targets.len() {
            continue;
        }
        let mut all_match = true;
        for (chain_idx, &chain_target_offset) in chain.push_targets.iter().enumerate() {
            let pin_target_node = pin_targets[chain_idx];
            let resolved_target =
                resolve_through_knots(pin_target_node, pin_data, &mut BTreeSet::new());
            let offsets = target_to_node_offsets(resolved_target);
            if !offsets.iter().any(|&offset| offset == chain_target_offset) {
                all_match = false;
                break;
            }
        }
        if all_match {
            return Some(*sequence_node_id);
        }
    }
    None
}

/// Follow a `K2Node_Knot` exec chain transparently to its first
/// non-knot target. Stops at the first non-knot node or when the
/// knot's exec-output pin has no links.
fn resolve_through_knots(
    start_node: usize,
    pin_data: &HashMap<usize, NodePinData>,
    visited: &mut BTreeSet<usize>,
) -> usize {
    if !visited.insert(start_node) {
        return start_node;
    }
    let Some(pins) = pin_data.get(&start_node) else {
        return start_node;
    };
    // Heuristic: assume the start_node IS the next concrete target.
    // Real downstream of a knot is the linked_to on its exec-output
    // pin. Walk one hop only when this is a knot we recognise by
    // matching pin shape (no class info available here without a
    // node_classes map).
    for pin in &pins.pins {
        if pin.is_exec_output() {
            if let Some(first_link) = pin.linked_to.first() {
                // Only recurse when this looks like a knot
                // passthrough (one input + one output exec pin).
                let is_knot_shape = pins
                    .pins
                    .iter()
                    .filter(|other| other.pin_type == PIN_TYPE_EXEC)
                    .count()
                    == 2;
                if is_knot_shape {
                    return resolve_through_knots(first_link.node, pin_data, visited);
                }
            }
        }
    }
    start_node
}

/// Record the Sequence node's partition: chain head, every push
/// opcode in the chain run, and each pin body range. The partition
/// holds one range per push-opcode site plus one range per pin body.
fn apply_sequence_partition(
    sequence_node: usize,
    chain: &crate::bytecode::structure::PushChainNode,
    inputs: &K2NodeByteMapInputs<'_>,
    event_name: &str,
    bytecode: &[u8],
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let mut owners = owner_events_for_node(sequence_node, inputs);
    if owners.is_empty() {
        owners.insert(event_name.to_string());
    }
    let kind = node_class(inputs, sequence_node);
    let partition = partitions
        .entry(sequence_node)
        .or_insert_with(|| K2NodePartition::new(sequence_node, owners.clone(), kind, None));
    extend_owner_events(partition, owners);
    let mut cursor = chain.head;
    while cursor < chain.after_chain && cursor < bytecode.len() {
        if bytecode.get(cursor) == Some(&EX_PUSH_EXECUTION_FLOW) {
            let push_end =
                (cursor + crate::bytecode::structure::PUSH_INSTR_BYTES).min(bytecode.len());
            push_range(&mut partition.ranges, cursor..push_end);
            byte_to_node.entry(cursor).or_default().push(sequence_node);
        }
        let step = crate::bytecode::partition::opcode_length_at(
            cursor,
            bytecode,
            inputs.ue5,
            inputs.name_table,
        );
        if step == 0 {
            break;
        }
        cursor += step;
    }
    // Pin body ranges: union of partition segments per pin.
    for pin_segments in &chain.pin_partitions {
        for segment in pin_segments {
            if segment.start < segment.end {
                push_range(&mut partition.ranges, segment.clone());
            }
        }
    }
}

/// Union of disjoint ranges into one `start..max_end` span. Used to
/// derive a per-event owner range for the push-chain skeleton; chains
/// that fall in cross-event gaps are excluded by the skeleton's own
/// reachability filter.
fn union_range(ranges: &[Range<usize>]) -> Option<Range<usize>> {
    let first = ranges.iter().min_by_key(|range| range.start)?;
    let last = ranges.iter().max_by_key(|range| range.end)?;
    Some(first.start..last.end)
}

/// Record one tracepoint opcode's full extent onto the event's
/// partition. EX_TRACEPOINT and EX_WIRE_TRACEPOINT are single-byte
/// opcodes; EX_INSTRUMENTATION_EVENT carries operands whose length
/// the opcode-length helper computes.
fn attribute_tracepoint_at(
    event_node: usize,
    offset: usize,
    opcode: u8,
    event_name: &str,
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let length = crate::bytecode::partition::opcode_length_at(
        offset,
        inputs.bytecode,
        inputs.ue5,
        inputs.name_table,
    );
    let span_end = (offset + length.max(1)).min(inputs.bytecode.len());
    let mut owners = owner_events_for_node(event_node, inputs);
    owners.insert(event_name.to_string());
    let kind = node_class(inputs, event_node);
    let macro_kind = inputs
        .macro_names
        .get(&event_node)
        .map(|name| MacroKind::from_name(name));
    let partition = partitions
        .entry(event_node)
        .or_insert_with(|| K2NodePartition::new(event_node, owners.clone(), kind, macro_kind));
    extend_owner_events(partition, owners);
    push_range(&mut partition.ranges, offset..span_end);
    byte_to_node.entry(offset).or_default().push(event_node);
    let _ = opcode;
}

/// Enumerate every opcode boundary inside the event's owned ranges
/// whose offset isn't yet in `byte_to_node`.
fn collect_unassigned_event_opcodes(
    graph: &crate::bytecode::partition::OpcodeGraph,
    event_ranges: &[Range<usize>],
    byte_to_node: &BTreeMap<usize, Vec<usize>>,
) -> Vec<usize> {
    // One bounded `.range(start..end)` query per owned range instead of a
    // full boundary scan filtered by `Range::contains`. `Range::contains`
    // is start-inclusive / end-exclusive, exactly what `.range(start..end)`
    // walks. Collecting through a `BTreeSet` keeps the result ascending and
    // deduplicated, matching the single-pass scan even if two owned ranges
    // were to overlap.
    let mut unassigned: BTreeSet<usize> = BTreeSet::new();
    for range in event_ranges {
        for &offset in graph.boundaries.range(range.start..range.end) {
            if !byte_to_node.contains_key(&offset) {
                unassigned.insert(offset);
            }
        }
    }
    unassigned.into_iter().collect()
}

/// Build the per-event CFG and SESE region tree for the fallback
/// pass. Mirrors `decode::mod::build_event_cfg_and_region_tree` minus
/// the region-byte-range bundle (the fallback only needs the tree).
fn build_fallback_event_cfg_and_region_tree(
    entry: usize,
    event_ranges: &[Range<usize>],
    graph: &crate::bytecode::partition::OpcodeGraph,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> (
    crate::bytecode::cfg::ControlFlowGraph,
    crate::bytecode::cfg::region::RegionTree,
    (),
) {
    use crate::bytecode::cfg::build::build_cfg;
    use crate::bytecode::cfg::dom::{compute_dominators, compute_postdominators};
    use crate::bytecode::cfg::region::{build_region_tree_with_linear_merges, RegionContext};
    let cfg = build_cfg(graph, entry, event_ranges);
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
    (cfg, region_tree, ())
}

/// Look up the K2Node id inherited from the enclosing SESE region's
/// entry block. Returns the first `byte_to_node` hit at any opcode
/// inside the region's entry block, or `None` when no such block has
/// a recorded attribution.
fn resolve_via_region_entry(
    unassigned_offset: usize,
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    region_tree: &crate::bytecode::cfg::region::RegionTree,
    byte_to_node: &BTreeMap<usize, Vec<usize>>,
) -> Option<usize> {
    let containing_block = cfg
        .blocks
        .iter()
        .find(|block| {
            !block.opcodes.is_empty()
                && unassigned_offset >= block.start
                && unassigned_offset < block.end
        })
        .map(|block| block.id)?;
    let region_id = region_tree
        .block_to_region
        .get(&containing_block)
        .copied()?;
    let entry_block_id = region_tree.regions[region_id].entry;
    let entry_block = cfg.blocks.get(entry_block_id)?;
    for &opcode_offset in &entry_block.opcodes {
        if let Some(nodes) = byte_to_node.get(&opcode_offset) {
            if let Some(&first_node) = nodes.first() {
                return Some(first_node);
            }
        }
    }
    None
}

/// Attribute a single unassigned byte to `target_node` and record the
/// span in the partition's `via_fallback` list. Creates the partition
/// entry when missing, mirroring the direct-attribution insert path.
fn attribute_fallback_byte(
    target_node: usize,
    offset: usize,
    event_name: &str,
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let mut owners = owner_events_for_node(target_node, inputs);
    owners.insert(event_name.to_string());
    let kind = node_class(inputs, target_node);
    let macro_kind = inputs
        .macro_names
        .get(&target_node)
        .map(|name| MacroKind::from_name(name));
    let partition = partitions
        .entry(target_node)
        .or_insert_with(|| K2NodePartition::new(target_node, owners.clone(), kind, macro_kind));
    extend_owner_events(partition, owners);
    let single_byte = offset..offset + 1;
    push_range(&mut partition.ranges, single_byte.clone());
    push_range(&mut partition.via_fallback, single_byte);
    byte_to_node.entry(offset).or_default().push(target_node);
}
