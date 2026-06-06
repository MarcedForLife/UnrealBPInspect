//! CFG validation probes.
//!
//! These tests are gated behind `#[ignore]` so the regular `cargo test`
//! run skips them; CI is free to invoke them via `--include-ignored`.
//! Each probe iterates every baseline fixture, builds a CFG per event
//! from that asset's ubergraph, and writes a per-event report to
//! `/tmp/cfg_*.log` (overwritten each run).
//!
//! `cfg_reducibility.log` reports the count of irreducible events and
//! their names. Expectation: 0 (or a small number), confirming the
//! bytecode is reducible enough for the structuring passes.
//!
//! `cfg_reachability.log` cross-checks CFG construction against the
//! partition's BFS by comparing the opcode-address set the CFG reaches
//! against the address set the partition assigned to the event. They
//! should match exactly because the CFG forward-reachability mirrors
//! `bfs_reachable` minus the flow-stack scaffolding (the partition
//! already filtered out unreachable bytes).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::PathBuf;

use crate::bytecode::decode::probe_ubergraph_partition;
use crate::parser::parse_asset;

use super::build::build_cfg;
use super::dom::{compute_dominators, compute_postdominators};
use super::reducibility::is_reducible;
use super::region::{build_region_tree_with, region_kind_label, RegionContext, RegionTree};

/// Absolute path to a baseline fixture, derived from a baseline filename.
///
/// Baseline files follow the pattern `<ue_version>_<fixture_name>.txt`
/// (e.g. `ue_4.27_Helm_BP.txt`). The asset lives at
/// `samples/<ue_version>/<fixture_name>.uasset`.
fn sample_path_for_baseline(baseline_name: &str) -> Option<PathBuf> {
    let stem = baseline_name.strip_suffix(".txt")?;
    let without_ue = stem.strip_prefix("ue_")?;
    let version_end = without_ue.find('_')?;
    let version_number = &without_ue[..version_end];
    let fixture_name = &without_ue[version_end + 1..];
    Some(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("samples")
            .join(format!("ue_{}", version_number))
            .join(format!("{}.uasset", fixture_name)),
    )
}

/// List of baseline filenames; used to derive sample paths. Sorted for
/// deterministic probe output.
fn baseline_names() -> Vec<String> {
    let baseline_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("baseline-snapshots");
    let mut names: Vec<String> = fs::read_dir(&baseline_dir)
        .unwrap_or_else(|err| {
            panic!(
                "Failed to read baseline directory {}: {}",
                baseline_dir.display(),
                err
            )
        })
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let name = entry.file_name().into_string().ok()?;
            if name.ends_with(".txt") {
                Some(name)
            } else {
                None
            }
        })
        .collect();
    names.sort();
    names
}

#[test]
#[ignore]
fn cfg_reducibility_probe() {
    let log_path = "/tmp/cfg_reducibility.log";
    let mut log =
        fs::File::create(log_path).unwrap_or_else(|err| panic!("create {}: {}", log_path, err));

    let mut total_events: usize = 0;
    let mut irreducible: Vec<(String, String)> = Vec::new();
    let mut empty_events: usize = 0;
    let mut fixtures_scanned = 0;

    for baseline_name in baseline_names() {
        let Some(sample_path) = sample_path_for_baseline(&baseline_name) else {
            writeln!(log, "skip: {} (no derived path)", baseline_name).ok();
            continue;
        };
        if !sample_path.exists() {
            writeln!(log, "skip: {} (sample missing)", baseline_name).ok();
            continue;
        }
        fixtures_scanned += 1;

        let asset_bytes = match fs::read(&sample_path) {
            Ok(bytes) => bytes,
            Err(err) => {
                writeln!(log, "read fail: {}: {}", sample_path.display(), err).ok();
                continue;
            }
        };
        let parsed = match parse_asset(&asset_bytes, false) {
            Ok(parsed) => parsed,
            Err(err) => {
                writeln!(log, "parse fail: {}: {}", sample_path.display(), err).ok();
                continue;
            }
        };
        let Some(probe) = probe_ubergraph_partition(&parsed, &asset_bytes) else {
            writeln!(log, "no ubergraph: {}", baseline_name).ok();
            continue;
        };

        writeln!(log, "=== {} ===", baseline_name).ok();
        for entry in &probe.disk_entries {
            let Some(ranges) = probe.event_ranges.get(&entry.name) else {
                continue;
            };
            total_events += 1;
            let cfg = build_cfg(&probe.graph, entry.mem_offset, ranges);
            if cfg.opcode_count() == 0 {
                empty_events += 1;
                writeln!(log, "  empty: {}", entry.name).ok();
                continue;
            }
            let reducible = is_reducible(&cfg);
            if !reducible {
                irreducible.push((baseline_name.clone(), entry.name.clone()));
                writeln!(
                    log,
                    "  IRREDUCIBLE: {} (blocks={}, opcodes={})",
                    entry.name,
                    cfg.blocks.len(),
                    cfg.opcode_count()
                )
                .ok();
            } else {
                writeln!(
                    log,
                    "  ok: {} (blocks={}, opcodes={})",
                    entry.name,
                    cfg.blocks.len(),
                    cfg.opcode_count()
                )
                .ok();
            }
        }
    }

    writeln!(log).ok();
    writeln!(log, "SUMMARY").ok();
    writeln!(log, "  fixtures: {}", fixtures_scanned).ok();
    writeln!(log, "  events: {}", total_events).ok();
    writeln!(log, "  empty events: {}", empty_events).ok();
    writeln!(log, "  irreducible: {}", irreducible.len()).ok();
    for (fixture, name) in &irreducible {
        writeln!(log, "    {}::{}", fixture, name).ok();
    }

    // Print so `cargo test -- --nocapture` (or the test runner log)
    // surfaces the headline numbers without grepping the log file.
    println!(
        "cfg_reducibility_probe: fixtures={} events={} irreducible={} (log: {})",
        fixtures_scanned,
        total_events,
        irreducible.len(),
        log_path,
    );
}

#[test]
#[ignore]
fn cfg_reachability_probe() {
    let log_path = "/tmp/cfg_reachability.log";
    let mut log =
        fs::File::create(log_path).unwrap_or_else(|err| panic!("create {}: {}", log_path, err));

    let mut total_events: usize = 0;
    let mut mismatches: Vec<MismatchEntry> = Vec::new();

    for baseline_name in baseline_names() {
        let Some(sample_path) = sample_path_for_baseline(&baseline_name) else {
            continue;
        };
        if !sample_path.exists() {
            continue;
        }
        let asset_bytes = match fs::read(&sample_path) {
            Ok(bytes) => bytes,
            Err(_) => continue,
        };
        let parsed = match parse_asset(&asset_bytes, false) {
            Ok(parsed) => parsed,
            Err(_) => continue,
        };
        let Some(probe) = probe_ubergraph_partition(&parsed, &asset_bytes) else {
            continue;
        };

        writeln!(log, "=== {} ===", baseline_name).ok();
        for entry in &probe.disk_entries {
            let Some(ranges) = probe.event_ranges.get(&entry.name) else {
                continue;
            };
            total_events += 1;

            // CFG reachability: every opcode address held by every block.
            let cfg = build_cfg(&probe.graph, entry.mem_offset, ranges);
            let cfg_addrs: BTreeSet<usize> = cfg
                .blocks
                .iter()
                .flat_map(|block| block.opcodes.iter().copied())
                .collect();

            // Partition's reachability: every opcode boundary inside the
            // event's owned byte ranges. The partition assigns whole
            // disk byte ranges; the CFG operates on opcode boundaries.
            let partition_addrs: BTreeSet<usize> = ranges
                .iter()
                .flat_map(|range| {
                    probe
                        .graph
                        .boundaries
                        .range(range.start..range.end)
                        .copied()
                })
                .collect();

            let only_cfg: BTreeSet<usize> =
                cfg_addrs.difference(&partition_addrs).copied().collect();
            let only_partition: BTreeSet<usize> =
                partition_addrs.difference(&cfg_addrs).copied().collect();

            if only_cfg.is_empty() && only_partition.is_empty() {
                writeln!(log, "  ok: {} ({} opcodes)", entry.name, cfg_addrs.len()).ok();
            } else {
                writeln!(
                    log,
                    "  MISMATCH: {} cfg-only={} partition-only={}",
                    entry.name,
                    only_cfg.len(),
                    only_partition.len()
                )
                .ok();
                let sample_only_cfg: Vec<String> = only_cfg
                    .iter()
                    .take(8)
                    .map(|addr| format!("0x{:x}", addr))
                    .collect();
                let sample_only_partition: Vec<String> = only_partition
                    .iter()
                    .take(8)
                    .map(|addr| format!("0x{:x}", addr))
                    .collect();
                writeln!(log, "    cfg-only sample: [{}]", sample_only_cfg.join(", ")).ok();
                writeln!(
                    log,
                    "    partition-only sample: [{}]",
                    sample_only_partition.join(", ")
                )
                .ok();
                mismatches.push(MismatchEntry {
                    fixture: baseline_name.clone(),
                    event: entry.name.clone(),
                    cfg_only_count: only_cfg.len(),
                    partition_only_count: only_partition.len(),
                });
            }
        }
    }

    writeln!(log).ok();
    writeln!(log, "SUMMARY").ok();
    writeln!(log, "  events: {}", total_events).ok();
    writeln!(log, "  mismatches: {}", mismatches.len()).ok();
    for entry in &mismatches {
        writeln!(
            log,
            "    {}::{} cfg-only={} partition-only={}",
            entry.fixture, entry.event, entry.cfg_only_count, entry.partition_only_count
        )
        .ok();
    }

    println!(
        "cfg_reachability_probe: events={} mismatches={} (log: {})",
        total_events,
        mismatches.len(),
        log_path
    );
}

struct MismatchEntry {
    fixture: String,
    event: String,
    cfg_only_count: usize,
    partition_only_count: usize,
}

#[test]
#[ignore]
fn cfg_regions_probe() {
    let log_path = "/tmp/cfg_regions.log";
    let mut log =
        fs::File::create(log_path).unwrap_or_else(|err| panic!("create {}: {}", log_path, err));

    let mut total_events: usize = 0;
    let mut clean_events: usize = 0;
    let mut anomalies: Vec<RegionAnomaly> = Vec::new();
    let mut kind_totals: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut total_regions: usize = 0;
    let mut max_depth: usize = 0;
    let mut sample_initialise_sleep: Option<String> = None;

    for baseline_name in baseline_names() {
        let Some(sample_path) = sample_path_for_baseline(&baseline_name) else {
            continue;
        };
        if !sample_path.exists() {
            continue;
        }
        let asset_bytes = match fs::read(&sample_path) {
            Ok(bytes) => bytes,
            Err(_) => continue,
        };
        let parsed = match parse_asset(&asset_bytes, false) {
            Ok(parsed) => parsed,
            Err(_) => continue,
        };
        let Some(probe) = probe_ubergraph_partition(&parsed, &asset_bytes) else {
            continue;
        };

        writeln!(log, "=== {} ===", baseline_name).ok();
        for entry in &probe.disk_entries {
            let Some(ranges) = probe.event_ranges.get(&entry.name) else {
                continue;
            };
            total_events += 1;
            let cfg = build_cfg(&probe.graph, entry.mem_offset, ranges);
            if cfg.opcode_count() == 0 {
                writeln!(log, "  skip (empty cfg): {}", entry.name).ok();
                continue;
            }
            if !is_reducible(&cfg) {
                writeln!(log, "  skip (irreducible cfg): {}", entry.name).ok();
                continue;
            }

            let idom = compute_dominators(&cfg);
            let ipostdom = compute_postdominators(&cfg);
            let region_ctx = RegionContext {
                bytecode: probe.bytecode.as_slice(),
                ue5: probe.ue5,
                name_table: &probe.name_table,
                mem_to_disk: Some(&probe.mem_to_disk),
            };
            let tree =
                build_region_tree_with(&cfg, &idom, &ipostdom, &probe.graph, Some(region_ctx));

            let issues = validate_region_tree(&cfg, &tree);
            for kind_label in collect_kind_labels(&tree) {
                *kind_totals.entry(kind_label).or_insert(0) += 1;
            }
            total_regions += tree.regions.len();
            let depth = tree.max_depth();
            if depth > max_depth {
                max_depth = depth;
            }

            if issues.is_empty() {
                clean_events += 1;
                writeln!(
                    log,
                    "  ok: {} (blocks={} regions={} depth={})",
                    entry.name,
                    cfg.blocks.len(),
                    tree.regions.len(),
                    depth,
                )
                .ok();
            } else {
                writeln!(
                    log,
                    "  ANOMALY: {} (regions={} depth={}) issues={:?}",
                    entry.name,
                    tree.regions.len(),
                    depth,
                    issues,
                )
                .ok();
                anomalies.push(RegionAnomaly {
                    fixture: baseline_name.clone(),
                    event: entry.name.clone(),
                    issues,
                });
            }

            if entry.name.contains("InitialiseSleep") && sample_initialise_sleep.is_none() {
                let mut rendering = format_region_tree(&tree, &baseline_name, entry.name.as_str());
                rendering.push_str(&format_cfg(&cfg));
                sample_initialise_sleep = Some(rendering);
            }
        }
    }

    writeln!(log).ok();
    writeln!(log, "SUMMARY").ok();
    writeln!(log, "  events: {}", total_events).ok();
    writeln!(log, "  clean: {}", clean_events).ok();
    writeln!(log, "  anomalies: {}", anomalies.len()).ok();
    writeln!(log, "  total regions: {}", total_regions).ok();
    writeln!(log, "  max nesting depth: {}", max_depth).ok();
    writeln!(log, "  kind distribution:").ok();
    for (kind, count) in &kind_totals {
        writeln!(log, "    {}: {}", kind, count).ok();
    }
    for anomaly in &anomalies {
        writeln!(
            log,
            "    {}::{}: {:?}",
            anomaly.fixture, anomaly.event, anomaly.issues
        )
        .ok();
    }
    if let Some(rendering) = &sample_initialise_sleep {
        writeln!(log).ok();
        writeln!(log, "SAMPLE InitialiseSleep:").ok();
        writeln!(log, "{}", rendering).ok();
    }

    println!(
        "cfg_regions_probe: events={} clean={} anomalies={} regions={} max_depth={} (log: {})",
        total_events,
        clean_events,
        anomalies.len(),
        total_regions,
        max_depth,
        log_path,
    );
}

#[derive(Debug)]
struct RegionAnomaly {
    fixture: String,
    event: String,
    issues: Vec<String>,
}

/// Validate that `tree` is a well-formed SESE decomposition: every block
/// has exactly one innermost region, every non-root region points at a
/// real parent, and parents/children agree.
fn validate_region_tree(cfg: &super::ControlFlowGraph, tree: &RegionTree) -> Vec<String> {
    let mut issues: Vec<String> = Vec::new();

    let mut assigned: BTreeSet<usize> = BTreeSet::new();
    for block in &cfg.blocks {
        if let Some(region_id) = tree.block_to_region.get(&block.id) {
            if *region_id >= tree.regions.len() {
                issues.push(format!("block {} -> bad region {}", block.id, region_id));
            } else {
                assigned.insert(block.id);
            }
        }
    }
    for block in &cfg.blocks {
        if !assigned.contains(&block.id) {
            issues.push(format!("block {} unassigned", block.id));
        }
    }

    for (region_id, region) in tree.regions.iter().enumerate() {
        if region.id != region_id {
            issues.push(format!("region {} has id {}", region_id, region.id));
        }
        if let Some(parent_id) = region.parent {
            if parent_id >= tree.regions.len() {
                issues.push(format!("region {} parent {} OOB", region_id, parent_id));
                continue;
            }
            if !tree.regions[parent_id].children.contains(&region_id) {
                issues.push(format!(
                    "region {} not in parent {} children",
                    region_id, parent_id
                ));
            }
        } else if region_id != tree.root {
            issues.push(format!("region {} parentless and not root", region_id));
        }
        for &child in &region.children {
            if child >= tree.regions.len() {
                issues.push(format!("region {} child {} OOB", region_id, child));
                continue;
            }
            if tree.regions[child].parent != Some(region_id) {
                issues.push(format!(
                    "region {} child {} disagrees on parent",
                    region_id, child
                ));
            }
        }
    }

    if tree.regions.is_empty() || tree.root >= tree.regions.len() {
        issues.push("root region missing".to_string());
    } else if tree.regions[tree.root].parent.is_some() {
        issues.push("root region has parent".to_string());
    }

    issues
}

fn collect_kind_labels(tree: &RegionTree) -> Vec<&'static str> {
    tree.regions
        .iter()
        .map(|region| region_kind_label(region.kind))
        .collect()
}

fn format_cfg(cfg: &super::ControlFlowGraph) -> String {
    let mut output = String::from("  cfg:\n");
    for block in &cfg.blocks {
        let succs = cfg
            .successors
            .get(&block.id)
            .map(|edges| {
                edges
                    .iter()
                    .map(|target| format!("b{}", target))
                    .collect::<Vec<_>>()
                    .join(",")
            })
            .unwrap_or_default();
        output.push_str(&format!(
            "    b{} [0x{:x}..0x{:x}] -> [{}]\n",
            block.id, block.start, block.end, succs
        ));
    }
    output
}

fn format_region_tree(tree: &RegionTree, fixture: &str, event: &str) -> String {
    fn render(tree: &RegionTree, region_id: usize, indent: usize, out: &mut String) {
        let region = &tree.regions[region_id];
        let kind = region_kind_label(region.kind);
        out.push_str(&" ".repeat(indent * 2));
        out.push_str(&format!(
            "[{}] {} entry=b{} exit=b{}\n",
            region.id, kind, region.entry, region.exit
        ));
        for &child in &region.children {
            render(tree, child, indent + 1, out);
        }
    }

    let mut output = format!("{}::{}\n", fixture, event);
    render(tree, tree.root, 1, &mut output);
    output
}
