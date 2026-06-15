//! Test-only probes reproducing slices of [`super::orchestrate::decode_asset`]
//! so CFG and K2Node-byte-map tests see the same address space the real
//! decoder uses.

use std::collections::BTreeMap;
use std::ops::Range;

use crate::bytecode::partition::{build_opcode_graph_with_resume, EventEntry};
use crate::types::ParsedAsset;

use super::header::{lookup_export_bytecode, read_version_and_name_table};
use super::mem_disk::build_mem_to_disk_map;
#[cfg(all(test, feature = "private-fixtures"))]
use super::ubergraph_scan::{build_event_node_index, build_macro_names, build_node_class_names};
use super::ubergraph_scan::{collect_event_entries, translate_entries_to_disk};
use crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX;

/// Partition output for a single ubergraph, exposed for the CFG
/// probe (`bytecode::cfg::tests`).
///
/// Bundles every value a downstream CFG-builder needs: the raw bytecode
/// bytes, the disk-coordinate `OpcodeGraph`, the per-event byte ranges,
/// and the disk-coordinate event entry addresses (paired with event
/// names). Probe-only; not consumed by the normal decode pipeline.
pub struct UbergraphProbeData {
    #[allow(dead_code)]
    pub bytecode: Vec<u8>,
    pub graph: crate::bytecode::partition::OpcodeGraph,
    pub event_ranges: BTreeMap<String, Vec<Range<usize>>>,
    pub disk_entries: Vec<EventEntry>,
    pub ue5: i32,
    pub name_table: crate::binary::NameTable,
    pub mem_to_disk: BTreeMap<usize, usize>,
}

/// Reproduce the ubergraph-partition slice of `decode_asset` for tests.
/// Returns `None` if the asset has no ubergraph export, no bytecode, or
/// partition fails. Mirrors the production code path so a probe sees
/// the same address space the real decoder uses.
pub fn probe_ubergraph_partition(
    asset: &ParsedAsset,
    asset_data: &[u8],
) -> Option<UbergraphProbeData> {
    let (ue5, name_table) = read_version_and_name_table(asset_data)?;

    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let (ug_idx, (ug_hdr, _)) = asset
        .exports
        .iter()
        .enumerate()
        .find(|(_, (hdr, _))| hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX))?;
    let ug_name = ug_hdr.object_name.clone();
    let ug_export_index = ug_idx + 1;

    let bytecode = lookup_export_bytecode(asset, ug_export_index, &ug_name)?;
    let entries = collect_event_entries(asset, &export_names, &ug_name, &name_table, ue5);

    let (mem_to_disk, _err) = build_mem_to_disk_map(&bytecode, &name_table, ue5);
    let disk_entries = translate_entries_to_disk(&entries, &mem_to_disk, &ug_name);
    if disk_entries.is_empty() {
        return None;
    }

    let (graph, latent_resumes) =
        build_opcode_graph_with_resume(&bytecode, ue5, &name_table, &mem_to_disk);

    let event_ranges = crate::bytecode::partition::partition_ubergraph_with_translation(
        &bytecode,
        &disk_entries,
        &name_table,
        ue5,
        &graph,
        &latent_resumes,
        None,
    )
    .ok()?
    .event_ranges;

    Some(UbergraphProbeData {
        bytecode,
        graph,
        event_ranges,
        disk_entries,
        ue5,
        name_table,
        mem_to_disk,
    })
}

/// Test-only return: K2NodeByteMap paired with the event-name to
/// owned-range map the audit harness consumes. Gated behind
/// `private-fixtures` because its only callers are the asset-loading
/// tests in the gitignored `k2node_byte_map::local_tests` module.
#[cfg(all(test, feature = "private-fixtures"))]
pub(crate) type K2NodeByteMapForTest = (
    crate::bytecode::k2node_byte_map::K2NodeByteMap,
    BTreeMap<String, Vec<Range<usize>>>,
);

/// Test-only helper that reproduces the production K2NodeByteMap build
/// for a single ubergraph asset. Returns `None` when the asset has no
/// ubergraph export or partitioning fails. The returned event-name to
/// owned-range map mirrors `event_ranges` so call-site tests can assert
/// against the same data the audit harness consumes.
#[cfg(all(test, feature = "private-fixtures"))]
pub(crate) fn build_k2node_byte_map_for_test(
    asset: &ParsedAsset,
    asset_data: &[u8],
) -> Option<K2NodeByteMapForTest> {
    let (ue5, name_table) = read_version_and_name_table(asset_data)?;
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();
    let (ug_idx, (ug_hdr, _)) = asset
        .exports
        .iter()
        .enumerate()
        .find(|(_, (hdr, _))| hdr.object_name.starts_with(EXECUTE_UBERGRAPH_PREFIX))?;
    let ug_name = ug_hdr.object_name.clone();
    let bytecode = lookup_export_bytecode(asset, ug_idx + 1, &ug_name)?;
    let entries = collect_event_entries(asset, &export_names, &ug_name, &name_table, ue5);
    let (mem_to_disk, _err) = build_mem_to_disk_map(&bytecode, &name_table, ue5);
    let translated_entries = translate_entries_to_disk(&entries, &mem_to_disk, &ug_name);
    if translated_entries.is_empty() {
        return None;
    }
    let event_node_index = build_event_node_index(asset, &export_names);
    let node_class_names = build_node_class_names(asset, &export_names);
    let node_classes: std::collections::HashMap<usize, super::cross_event_inline::K2NodeClass> =
        node_class_names
            .iter()
            .map(|(&node_id, class)| {
                (
                    node_id,
                    super::cross_event_inline::parse_k2node_class(class),
                )
            })
            .collect();
    let macro_names = build_macro_names(asset, &export_names);
    let node_to_reaching_events = super::cross_event_inline::build_node_to_reaching_events(
        &event_node_index,
        &asset.pin_data,
        |node_id| {
            matches!(
                node_classes.get(&node_id),
                Some(super::cross_event_inline::K2NodeClass::Knot)
            )
        },
    );
    let (graph, latent_resumes) =
        build_opcode_graph_with_resume(&bytecode, ue5, &name_table, &mem_to_disk);
    let partition_output = crate::bytecode::partition::partition_ubergraph_with_translation(
        &bytecode,
        &translated_entries,
        &name_table,
        ue5,
        &graph,
        &latent_resumes,
        None,
    )
    .ok()?;
    let event_ranges = partition_output.event_ranges;
    let resume_blocks = partition_output.resume_blocks;
    let event_entry_disks: BTreeMap<String, usize> = translated_entries
        .iter()
        .map(|entry| (entry.name.clone(), entry.mem_offset))
        .collect();
    let inputs = crate::bytecode::k2node_byte_map::K2NodeByteMapInputs {
        asset,
        export_names: &export_names,
        bytecode: &bytecode,
        name_table: &name_table,
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
    };
    let map = crate::bytecode::k2node_byte_map::build_k2node_byte_map(&inputs);
    Some((map, event_ranges))
}
