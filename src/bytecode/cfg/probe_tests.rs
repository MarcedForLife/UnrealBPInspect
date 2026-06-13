//! CFG validation probes.
//!
//! The diagnostic probes are gated behind `#[ignore]` so the regular
//! `cargo test` run skips them; CI is free to invoke them via
//! `--include-ignored`. The exception is `rc_vs_structure_survey`, the
//! default-run reaching-condition oracle guard. Each probe iterates every
//! baseline fixture, builds a CFG per event from that asset's ubergraph,
//! and writes a per-event report to `/tmp/cfg_*.log` (overwritten each
//! run).
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

use super::build::{build_cfg, build_cfg_flow_reachable};
use super::dom::{compute_dominators, compute_postdominators};
use super::reducibility::is_reducible;
use super::region::{build_region_tree_with, region_kind_label, RegionContext, RegionTree};
use super::BlockId;

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

// Reaching-condition probe: a read-only diagnostic that classifies each
// basic block of a gnarly Blueprint event by its reaching condition (the
// boolean over branch predicates under which control reaches it) and asks
// whether that bucketing implies the same then/else/tail placement the
// current special-case emitters produce. Writes `rc-probe-report.md` to
// the system temp dir.

use super::reaching::{
    classify_bucket, classify_bucket_in_context, collect_genuine_conditionals,
    compute_reaching_conditions, format_cond, Bucket,
};
use super::region::RegionKind;

/// Best-effort mnemonic for a Kismet opcode byte. Covers the opcodes that
/// actually show up in the probed events' terminators and bodies; falls
/// back to a hex label so the report never hides an opcode it lacks a name
/// for. Probe-local on purpose, production output renders statements not
/// raw opcodes.
fn opcode_mnemonic(opcode: u8) -> String {
    use crate::bytecode::opcodes::*;
    let name = match opcode {
        EX_LOCAL_VARIABLE => "LocalVariable",
        EX_INSTANCE_VARIABLE => "InstanceVariable",
        EX_DEFAULT_VARIABLE => "DefaultVariable",
        EX_RETURN => "Return",
        EX_JUMP => "Jump",
        EX_JUMP_IF_NOT => "JumpIfNot",
        EX_ASSERT => "Assert",
        EX_NOTHING => "Nothing",
        EX_LET => "Let",
        EX_CLASS_CONTEXT => "ClassContext",
        EX_LET_BOOL => "LetBool",
        EX_END_FUNCTION_PARMS => "EndFunctionParms",
        EX_SELF => "Self",
        EX_CONTEXT => "Context",
        EX_CONTEXT_FAIL_SILENT => "ContextFailSilent",
        EX_VIRTUAL_FUNCTION => "VirtualFunction",
        EX_FINAL_FUNCTION => "FinalFunction",
        EX_INT_CONST => "IntConst",
        EX_FLOAT_CONST => "FloatConst",
        EX_STRING_CONST => "StringConst",
        EX_OBJECT_CONST => "ObjectConst",
        EX_NAME_CONST => "NameConst",
        EX_TRUE => "True",
        EX_FALSE => "False",
        EX_NO_OBJECT => "NoObject",
        EX_DYNAMIC_CAST => "DynamicCast",
        EX_STRUCT_CONST => "StructConst",
        EX_SET_ARRAY => "SetArray",
        EX_LET_OBJ => "LetObj",
        EX_PUSH_EXECUTION_FLOW => "PushExecutionFlow",
        EX_POP_EXECUTION_FLOW => "PopExecutionFlow",
        EX_COMPUTED_JUMP => "ComputedJump",
        EX_POP_FLOW_IF_NOT => "PopFlowIfNot",
        EX_LOCAL_FINAL_FUNCTION => "LocalFinalFunction",
        EX_LOCAL_VIRTUAL_FUNCTION => "LocalVirtualFunction",
        EX_STRUCT_MEMBER_CONTEXT => "StructMemberContext",
        EX_CALL_MATH => "CallMath",
        EX_LET_VALUE_ON_PERSISTENT_FRAME => "LetValueOnPersistentFrame",
        EX_LET_DELEGATE => "LetDelegate",
        EX_LET_MULTICAST_DELEGATE => "LetMulticastDelegate",
        EX_LOCAL_OUT_VARIABLE => "LocalOutVariable",
        _ => return format!("0x{:02x}", opcode),
    };
    name.to_string()
}

/// (version directory, event-name substrings to match in `disk_entries`).
/// Events are matched by `contains` so mangled headers (Input axes,
/// component-signature events) still resolve. The same target list runs
/// against every version; missing fixtures no-op.
fn rc_probe_targets() -> Vec<&'static str> {
    vec![
        "OnActorReleased",
        "AttemptGrip",
        "Interact",
        "GripOutOfRangeActor",
        "ReleaseGrip",
        "GripLeftAxis",
        "ComponentEndOverlapSignature",
    ]
}

/// One conditional block's reaching-condition analysis, rendered into the
/// report.
fn render_conditional(
    out: &mut String,
    cfg: &super::ControlFlowGraph,
    graph: &crate::bytecode::partition::OpcodeGraph,
    tree: &RegionTree,
    ipostdom: &BTreeMap<usize, usize>,
    conditions: &BTreeMap<usize, super::reaching::Cond>,
    cond_block: usize,
) {
    let block = &cfg.blocks[cond_block];
    let kind = tree
        .block_to_region
        .get(&cond_block)
        .map(|&region_id| region_kind_label(tree.regions[region_id].kind))
        .unwrap_or("?");
    let merge = ipostdom
        .get(&cond_block)
        .map(|&block_id| {
            if block_id == cfg.sink {
                "sink".to_string()
            } else {
                format!("b{} @0x{:x}", block_id, cfg.blocks[block_id].start)
            }
        })
        .unwrap_or_else(|| "?".to_string());

    out.push_str(&format!(
        "  conditional b{} @0x{:x}  region={}  merge={}\n",
        cond_block, block.start, kind, merge
    ));

    // Blocks reachable on a path from `cond_block`, in id order. For each:
    // its reaching condition, the implied bucket relative to this
    // conditional, and the opcode mnemonics it holds.
    for descendant in blocks_reachable_from(cfg, cond_block) {
        if descendant == cond_block {
            continue;
        }
        let Some(rc) = conditions.get(&descendant) else {
            out.push_str(&format!(
                "    b{} -> (no RC: unreachable on DAG)\n",
                descendant
            ));
            continue;
        };
        let bucket = match classify_bucket(cond_block, rc) {
            Bucket::Then => "THEN",
            Bucket::Else => "ELSE",
            Bucket::Tail => "TAIL",
            Bucket::Other => "OTHER",
        };
        let mnemonics: Vec<String> = cfg.blocks[descendant]
            .opcodes
            .iter()
            .filter_map(|addr| graph.opcodes.get(addr).map(|&op| opcode_mnemonic(op)))
            .collect();
        out.push_str(&format!(
            "    b{} @0x{:x}  RC={}  bucket={}  ops=[{}]\n",
            descendant,
            cfg.blocks[descendant].start,
            format_cond(rc),
            bucket,
            mnemonics.join(", "),
        ));
    }
}

/// Blocks reachable from `start` over forward CFG edges (sink excluded),
/// returned in ascending id order for deterministic output.
fn blocks_reachable_from(cfg: &super::ControlFlowGraph, start: usize) -> Vec<usize> {
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(block) = stack.pop() {
        if block == cfg.sink || !seen.insert(block) {
            continue;
        }
        if let Some(successors) = cfg.successors.get(&block) {
            for &next in successors {
                if next != cfg.sink && !seen.contains(&next) {
                    stack.push(next);
                }
            }
        }
    }
    seen.into_iter().collect()
}

#[test]
#[ignore]
fn reaching_condition_probe() {
    // The per-event body. The top heading, legend, and JIN-mapping note are
    // prepended after the scan so the verified mapping can sit up front.
    let mut report = String::new();
    let targets = rc_probe_targets();
    let mut jin_mapping_note: Option<String> = None;

    for baseline_name in baseline_names() {
        if !baseline_name.contains("VRPlayer") {
            continue;
        }
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

        let version = baseline_name
            .strip_prefix("ue_")
            .and_then(|rest| rest.split('_').next())
            .unwrap_or("?");
        report.push_str(&format!("\n## {} ({})\n\n", baseline_name, version));

        // Record which targets resolved to a ubergraph event and which did
        // not. The named function-graph events (OnActorReleased, AttemptGrip,
        // GripOutOfRangeActor, ReleaseGrip) are separate Function exports, not
        // ubergraph entries, so `probe_ubergraph_partition` does not surface
        // them; this section documents that gap honestly.
        let mut matched: Vec<&str> = Vec::new();
        for target in &targets {
            if probe
                .disk_entries
                .iter()
                .any(|entry| entry.name.contains(target))
            {
                matched.push(target);
            }
        }
        let unmatched: Vec<&&str> = targets.iter().filter(|t| !matched.contains(t)).collect();
        report.push_str(&format!(
            "_target coverage: matched {:?}; not in ubergraph {:?}_\n\n",
            matched, unmatched
        ));

        for entry in &probe.disk_entries {
            if !targets.iter().any(|target| entry.name.contains(target)) {
                continue;
            }
            let Some(ranges) = probe.event_ranges.get(&entry.name) else {
                continue;
            };

            report.push_str(&format!("### {}\n\n", entry.name));

            let cfg = build_cfg(&probe.graph, entry.mem_offset, ranges);
            if cfg.opcode_count() == 0 {
                report.push_str("  (empty cfg)\n\n");
                continue;
            }
            if !is_reducible(&cfg) {
                report.push_str("  (irreducible cfg; reaching-condition pass skipped)\n\n");
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

            render_unit(
                &mut report,
                &cfg,
                &probe.graph,
                &tree,
                &ipostdom,
                &baseline_name,
                &entry.name,
                &mut jin_mapping_note,
            );
        }

        render_function_section(
            &mut report,
            &parsed,
            &asset_bytes,
            &baseline_name,
            &mut jin_mapping_note,
        );
    }

    let mapping = jin_mapping_note
        .unwrap_or_else(|| "(no conditional block found to verify mapping)".to_string());
    let mut final_report = String::from("# Reaching-condition probe report\n\n");
    final_report.push_str(
        "Read-only diagnostic. For each genuine conditional block\n\
         (`EX_JUMP_IF_NOT` or `EX_POP_FLOW_IF_NOT`, excluding DoOnce macro\n\
         gates) in a handful of gnarly VRPlayer events and the dropped-else\n\
         target Functions, this\n\
         lists the reaching condition of every block reachable from it and the\n\
         bucket that condition implies.\n\n\
         Legend:\n\
         - `P@b<id>` is the predicate atom \"the condition at block b<id> is TRUE\"\n\
           (the JIN fallthrough edge). `!P@b<id>` is the FALSE / jump-target edge.\n\
         - bucket THEN: RC implies `P@b` (reached only when b is TRUE).\n\
         - bucket ELSE: RC implies `!P@b` (reached only when b is FALSE).\n\
         - bucket TAIL: RC is a tautology (the merge / continuation after b).\n\
         - bucket OTHER: RC references other predicates; b alone does not decide it.\n\
           Buckets are decided by exact truth-table evaluation, not just `simplify`.\n\
         - `region=` is the enclosing `RegionKind` the current classifier assigned.\n\
         - `merge=` is the conditional's immediate post-dominator.\n\
         - `macro-collapse:` lists the conditional blocks suppressed as DoOnce gates\n\
           (atoms removed before the reaching-condition pass), so the collapse\n\
           is auditable. Flow-stack forks (`EX_PushExecutionFlow`) never enter\n\
           the atom set, so they cannot produce phantom predicates.\n\
         Back edges (loops) are excluded from the reaching-condition DAG; a block\n\
         only reachable via a back edge shows `(no RC: unreachable on DAG)`.\n\n",
    );
    final_report.push_str("## JIN edge-mapping verification\n\n");
    final_report.push_str(&mapping);
    final_report.push('\n');
    final_report.push_str(&report);

    let report_path = std::env::temp_dir().join("rc-probe-report.md");
    fs::write(&report_path, &final_report)
        .unwrap_or_else(|err| panic!("write {}: {}", report_path.display(), err));

    println!(
        "reaching_condition_probe: wrote {} ({} bytes)",
        report_path.display(),
        final_report.len()
    );
}

/// Render one CFG's reaching-condition analysis into the report. Shared by
/// the event and function paths: computes the genuine-conditional atom set
/// (JIN minus DoOnce gates), emits the `macro-collapse:` audit line, runs
/// `compute_reaching_conditions`, surfaces any irreducibility / missing
/// blocks, then renders each genuine conditional. Records the JIN
/// edge-mapping note from the first conditional ever seen.
#[allow(clippy::too_many_arguments)]
fn render_unit(
    report: &mut String,
    cfg: &super::ControlFlowGraph,
    graph: &crate::bytecode::partition::OpcodeGraph,
    tree: &RegionTree,
    ipostdom: &BTreeMap<usize, usize>,
    fixture: &str,
    unit_name: &str,
    jin_mapping_note: &mut Option<String>,
) {
    let (conditional_blocks, suppressed_gates) =
        collect_genuine_conditionals(cfg, Some(tree), |addr| graph.opcodes.get(&addr).copied());

    if suppressed_gates.is_empty() {
        report.push_str("  macro-collapse: (none)\n");
    } else {
        let gates: Vec<String> = suppressed_gates
            .iter()
            .map(|block| format!("b{}", block))
            .collect();
        report.push_str(&format!(
            "  macro-collapse: suppressed DoOnce-gate JIN blocks [{}]\n",
            gates.join(", ")
        ));
    }

    // Verify the JIN fallthrough/jump-target mapping on the first genuine
    // branch we ever see and record it once for the report header.
    if jin_mapping_note.is_none() {
        if let Some(&first) = conditional_blocks.iter().next() {
            *jin_mapping_note = Some(describe_jin_mapping(cfg, fixture, unit_name, first));
        }
    }

    let rc = compute_reaching_conditions(cfg, &conditional_blocks);
    if rc.irreducible {
        report.push_str("  (forward DAG still cyclic; reaching conditions not computed)\n\n");
        return;
    }
    if !rc.missing.is_empty() {
        let missing: Vec<String> = rc
            .missing
            .iter()
            .map(|block| format!("b{}", block))
            .collect();
        report.push_str(&format!(
            "  WARNING: reachable blocks without an RC: [{}]\n",
            missing.join(", ")
        ));
    }

    if conditional_blocks.is_empty() {
        report.push_str("  (no genuine conditional blocks)\n\n");
        return;
    }

    for &cond_block in &conditional_blocks {
        render_conditional(
            report,
            cfg,
            graph,
            tree,
            ipostdom,
            &rc.conditions,
            cond_block,
        );
    }
    report.push('\n');
}

/// Build a per-function CFG and region tree from a standalone `.Function`
/// export's raw disk bytecode, mirroring `decode_standalone_function_body`'s
/// recipe (whole-body range, per-function mem-to-disk map, dominators /
/// post-dominators, region tree with bytecode context). Returns `None` when
/// the export carries no bytecode bytes.
#[allow(clippy::type_complexity)]
fn build_function_cfg_and_region_tree(
    bytecode: &[u8],
    ue5: i32,
    name_table: &crate::binary::NameTable,
) -> (
    super::ControlFlowGraph,
    RegionTree,
    BTreeMap<usize, usize>,
    crate::bytecode::partition::OpcodeGraph,
) {
    let (fn_mem_to_disk, _err) =
        crate::bytecode::decode::build_mem_to_disk_map(bytecode, name_table, ue5);
    let fn_graph =
        crate::bytecode::partition::build_opcode_graph(bytecode, ue5, name_table, &fn_mem_to_disk);
    let full = 0..bytecode.len();
    // Flow-aware reachability (simulates the PUSH/POP execution-flow stack)
    // so a Sequence-structured function threads its pin resumes in execution
    // order. The flow-unaware `build_cfg` dead-ends at each pin's POP and
    // surfaces only the pin on a clean static-forward path.
    let cfg = build_cfg_flow_reachable(&fn_graph, 0, std::slice::from_ref(&full));
    let idom = compute_dominators(&cfg);
    let ipostdom = compute_postdominators(&cfg);
    let region_ctx = RegionContext {
        bytecode,
        ue5,
        name_table,
        mem_to_disk: Some(&fn_mem_to_disk),
    };
    let region_tree = build_region_tree_with(&cfg, &idom, &ipostdom, &fn_graph, Some(region_ctx));
    (cfg, region_tree, ipostdom, fn_graph)
}

/// Append the `## FUNCTIONS` section for one fixture: the four dropped-else
/// target functions (matched by name substring) rendered exactly as events
/// are, plus a one-line note for any other `.Function` that holds a genuine
/// conditional. `.Function` exports never surface through
/// `probe_ubergraph_partition` (it is ubergraph-only), so this builds each
/// function's CFG directly from its disk bytecode.
fn render_function_section(
    report: &mut String,
    asset: &crate::types::ParsedAsset,
    asset_data: &[u8],
    fixture: &str,
    jin_mapping_note: &mut Option<String>,
) {
    let Some((ue5, name_table)) = crate::bytecode::decode::read_version_and_name_table(asset_data)
    else {
        return;
    };
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let function_targets = [
        "OnActorReleased",
        "AttemptGrip",
        "GripOutOfRangeActor",
        "ReleaseGrip",
    ];

    report.push_str("### FUNCTIONS\n\n");

    let mut other_with_conditional: Vec<String> = Vec::new();

    for (export_idx, (hdr, _props)) in asset.exports.iter().enumerate() {
        let class = crate::resolve::resolve_index(&asset.imports, &export_names, hdr.class_index);
        if !class.ends_with(".Function") {
            continue;
        }
        if hdr
            .object_name
            .starts_with(crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX)
        {
            continue;
        }
        // `bytecode_by_export` is keyed by 1-based export index (see
        // `lookup_export_bytecode`).
        let Some((bytecode, _mem_size)) = asset.bytecode_by_export.get(&(export_idx + 1)) else {
            continue;
        };
        if bytecode.is_empty() {
            continue;
        }

        let (cfg, tree, ipostdom, fn_graph) =
            build_function_cfg_and_region_tree(bytecode, ue5, &name_table);
        if cfg.opcode_count() == 0 || !is_reducible(&cfg) {
            // Only note a target by name; a non-target irreducible/empty
            // function is not interesting for this report.
            if function_targets
                .iter()
                .any(|target| hdr.object_name.contains(target))
            {
                report.push_str(&format!("#### {}\n\n", hdr.object_name));
                report.push_str("  (empty or irreducible cfg; skipped)\n\n");
            }
            continue;
        }

        let (conditional_blocks, _suppressed) =
            collect_genuine_conditionals(&cfg, Some(&tree), |addr| {
                fn_graph.opcodes.get(&addr).copied()
            });

        let is_target = function_targets
            .iter()
            .any(|target| hdr.object_name.contains(target));

        if is_target {
            report.push_str(&format!("#### {}\n\n", hdr.object_name));
            render_unit(
                report,
                &cfg,
                &fn_graph,
                &tree,
                &ipostdom,
                fixture,
                &hdr.object_name,
                jin_mapping_note,
            );
        } else if !conditional_blocks.is_empty() {
            other_with_conditional.push(format!(
                "{} ({} genuine conditional block(s))",
                hdr.object_name,
                conditional_blocks.len()
            ));
        }
    }

    if other_with_conditional.is_empty() {
        report.push_str("_other `.Function` exports with a genuine conditional: none_\n\n");
    } else {
        report.push_str(&format!(
            "_other `.Function` exports with a genuine conditional: {}_\n\n",
            other_with_conditional.join("; ")
        ));
    }
}

/// Empirically describe which successor of `cond_block` is the JIN
/// fallthrough (cond TRUE) vs the jump target (cond FALSE), using the
/// `start == cond.end` rule. Records the concrete addresses so the report
/// shows the verification on a real branch.
fn describe_jin_mapping(
    cfg: &super::ControlFlowGraph,
    fixture: &str,
    event: &str,
    cond_block: usize,
) -> String {
    let block = &cfg.blocks[cond_block];
    let successors = cfg.successors.get(&cond_block).cloned().unwrap_or_default();
    let real: Vec<usize> = successors
        .into_iter()
        .filter(|&id| id != cfg.sink)
        .collect();
    let mut note = format!(
        "Verified on {}::{}, conditional b{} (terminator JIN at 0x{:x}, block end 0x{:x}).\n",
        fixture,
        event,
        cond_block,
        block.opcodes.last().copied().unwrap_or(block.start),
        block.end,
    );
    for succ in &real {
        let succ_start = cfg.blocks[*succ].start;
        let role = if succ_start == block.end {
            "FALLTHROUGH (cond TRUE, carries P@b)"
        } else {
            "JUMP-TARGET (cond FALSE, carries !P@b)"
        };
        note.push_str(&format!(
            "  b{} starts at 0x{:x} -> {}\n",
            succ, succ_start, role
        ));
    }
    note.push_str(
        "Rule: the successor whose start == the conditional block's end is the\n\
         fallthrough (next sequential opcode after the JIN); the other is the\n\
         jump target.\n",
    );
    note
}

// Full-corpus RC-vs-structure survey, promoted to a default-run
// regression guard: it fails on any disagreement, machine-checking the
// "bytecode determines semantics" contract for conditional structure.
// Where `reaching_condition_probe` dumps RC for a handful of hand-picked
// VRPlayer events, this widens to every event AND standalone function in
// every sample asset present on disk and cross-checks the region-scoped
// RC bucket of each block against the structural arm assignment the
// decoder actually emits.
//
// The structural signal is the decoder's own arm-membership primitive:
// for an IfThenElse / IfThen region whose conditional is `region.entry`,
// the THEN arm is the dominance-bounded forward reachable set from the
// fallthrough successor and the ELSE arm the mirror from the jump-target
// successor (a faithful re-implementation of
// `region_decode::reachable_blocks_in_arm`, which is `pub(super)` and not
// reachable here). The merge / post-merge is TAIL.
//
// The RC signal is `classify_bucket_in_context(region.entry, RC(block),
// RC(region.entry))`: region-scoped so an ancestor predicate fixed inside
// the region (the benign MouseY whole-function artifact) collapses rather
// than leaking.
//
// A disagreement is a block whose RC bucket and structural bucket are both
// concrete (THEN / ELSE / TAIL) and differ. Such a block is one the
// emitter places in an arm that its reaching condition contradicts, the
// shape of a real structuring win.

/// One block where the region-scoped RC bucket contradicts the structural
/// arm assignment.
struct RcStructDisagreement {
    fixture: String,
    unit: String,
    conditional: BlockId,
    cond_addr: usize,
    block: BlockId,
    block_addr: usize,
    region_kind: &'static str,
    rc_bucket: Bucket,
    struct_bucket: Bucket,
    rc: super::reaching::Cond,
}

/// Stable label for a bucket, for the distribution audit line.
fn bucket_name(bucket: Bucket) -> &'static str {
    match bucket {
        Bucket::Then => "THEN",
        Bucket::Else => "ELSE",
        Bucket::Tail => "TAIL",
        Bucket::Other => "OTHER",
    }
}

/// Structural arm bucket of `block` relative to the conditional
/// `region.entry`, mirroring `region_decode::reachable_blocks_in_arm`'s
/// dominance-bounded forward reachability. `then_block` is the JIN
/// fallthrough successor (P@b TRUE), `else_block` the jump-target (FALSE).
/// Returns the bucket the decoder's arm walk would place `block` in:
/// `Then` / `Else` if it falls in exactly one arm's reachable slice,
/// `Tail` if it is the region exit (merge) or a post-merge block, `Other`
/// if it sits in neither arm and is not the merge (a shared convergence
/// the arm walk leaves to a sibling).
fn structural_arm_bucket(
    block: BlockId,
    region: &super::region::Region,
    then_block: BlockId,
    else_block: BlockId,
    cfg: &super::ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
) -> Bucket {
    if block == region.exit {
        return Bucket::Tail;
    }
    let then_set = arm_reachable_set(then_block, else_block, region, cfg, idom);
    let else_set = arm_reachable_set(else_block, then_block, region, cfg, idom);
    let in_then = then_set.contains(&block);
    let in_else = else_set.contains(&block);
    match (in_then, in_else) {
        (true, false) => Bucket::Then,
        (false, true) => Bucket::Else,
        (true, true) => Bucket::Other, // shared by both arm walks (convergence)
        (false, false) => {
            // Not in either arm slice and not the merge endpoint. Either a
            // post-merge continuation (dominated by exit -> Tail) or an
            // unrelated block the arm walk excludes (Other).
            if is_post_merge(block, region.exit, idom) {
                Bucket::Tail
            } else {
                Bucket::Other
            }
        }
    }
}

/// Faithful mirror of `region_decode::reachable_blocks_in_arm` with empty
/// `extra_stops`: forward BFS from `arm_entry`, stopping at the region
/// entry / exit / sibling arm and at any successor not strictly dominated
/// by `arm_entry`.
fn arm_reachable_set(
    arm_entry: BlockId,
    sibling_arm_entry: BlockId,
    region: &super::region::Region,
    cfg: &super::ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
) -> BTreeSet<BlockId> {
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let is_boundary = |block_id: BlockId| -> bool {
        block_id == region.exit || block_id == region.entry || block_id == sibling_arm_entry
    };
    if is_boundary(arm_entry) {
        return visited;
    }
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(arm_entry);
    while let Some(block_id) = queue.pop_front() {
        if !visited.insert(block_id) {
            continue;
        }
        let Some(succs) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &succ in succs {
            if is_boundary(succ) || visited.contains(&succ) {
                continue;
            }
            if succ != arm_entry && !strictly_dominated_by(succ, arm_entry, idom) {
                continue;
            }
            queue.push_back(succ);
        }
    }
    visited
}

/// Mirror of `region_decode::is_strictly_dominated_by`.
fn strictly_dominated_by(
    block: BlockId,
    dominator: BlockId,
    idom: &BTreeMap<BlockId, BlockId>,
) -> bool {
    if block == dominator {
        return false;
    }
    let mut cursor = block;
    while let Some(&parent) = idom.get(&cursor) {
        if parent == dominator {
            return true;
        }
        if parent == cursor {
            return false;
        }
        cursor = parent;
    }
    false
}

/// True if `block` is `exit` itself or strictly dominated by `exit`
/// (a continuation after the merge).
fn is_post_merge(block: BlockId, exit: BlockId, idom: &BTreeMap<BlockId, BlockId>) -> bool {
    block == exit || strictly_dominated_by(block, exit, idom)
}

/// Survey one CFG + region tree: for every genuine conditional that heads
/// an IfThenElse / IfThen region, compare the region-scoped RC bucket of
/// each forward-reachable block against its structural arm bucket.
/// Appends disagreements to `out` and returns
/// `(conditionals_checked, blocks_checked, agreements)`.
#[allow(clippy::too_many_arguments)]
fn survey_unit(
    cfg: &super::ControlFlowGraph,
    graph: &crate::bytecode::partition::OpcodeGraph,
    tree: &RegionTree,
    fixture: &str,
    unit: &str,
    out: &mut Vec<RcStructDisagreement>,
    pair_dist: &mut BTreeMap<(&'static str, &'static str), usize>,
) -> (usize, usize, usize) {
    let (conditional_blocks, _suppressed) =
        collect_genuine_conditionals(cfg, Some(tree), |addr| graph.opcodes.get(&addr).copied());
    if conditional_blocks.is_empty() {
        return (0, 0, 0);
    }
    let rc = compute_reaching_conditions(cfg, &conditional_blocks);
    if rc.irreducible {
        return (0, 0, 0);
    }
    let idom = compute_dominators(cfg);

    let mut conditionals_checked = 0;
    let mut blocks_checked = 0;
    let mut agreements = 0;

    for &cond_block in &conditional_blocks {
        let Some(&region_id) = tree.block_to_region.get(&cond_block) else {
            continue;
        };
        let region = &tree.regions[region_id];
        // Only the two-way branch emitters make an RC-mappable
        // THEN/ELSE/TAIL arm-placement decision. The conditional must head
        // its region (be the region entry) for the arm primitive to apply.
        if region.entry != cond_block
            || !matches!(region.kind, RegionKind::IfThenElse | RegionKind::IfThen)
        {
            continue;
        }
        let succs: Vec<BlockId> = cfg
            .successors
            .get(&cond_block)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|&id| id != cfg.sink)
            .collect();
        if succs.len() != 2 {
            continue;
        }
        // succs[0] is the jump-target (FALSE / else), succs[1] the
        // fallthrough (TRUE / then), matching try_emit_ifthenelse_region.
        let else_block = succs[0];
        let then_block = succs[1];

        let Some(entry_rc) = rc.conditions.get(&cond_block) else {
            continue;
        };
        let context = entry_rc.clone();
        conditionals_checked += 1;

        for descendant in blocks_reachable_from(cfg, cond_block) {
            if descendant == cond_block || descendant == cfg.sink {
                continue;
            }
            let Some(block_rc) = rc.conditions.get(&descendant) else {
                continue;
            };
            let rc_bucket = classify_bucket_in_context(cond_block, block_rc, &context);
            let struct_bucket =
                structural_arm_bucket(descendant, region, then_block, else_block, cfg, &idom);
            blocks_checked += 1;

            let both_concrete = matches!(rc_bucket, Bucket::Then | Bucket::Else | Bucket::Tail)
                && matches!(struct_bucket, Bucket::Then | Bucket::Else | Bucket::Tail);
            // Record the concrete-vs-concrete pair distribution so the
            // "zero disagreements" headline is auditable: a vacuous gate
            // (one side always Other) would show no concrete pairs here.
            if both_concrete {
                *pair_dist
                    .entry((bucket_name(rc_bucket), bucket_name(struct_bucket)))
                    .or_insert(0) += 1;
            }
            if !both_concrete || rc_bucket == struct_bucket {
                agreements += 1;
                continue;
            }
            out.push(RcStructDisagreement {
                fixture: fixture.to_string(),
                unit: unit.to_string(),
                conditional: cond_block,
                cond_addr: cfg.blocks[cond_block].start,
                block: descendant,
                block_addr: cfg.blocks[descendant].start,
                region_kind: region_kind_label(region.kind),
                rc_bucket,
                struct_bucket,
                rc: block_rc.clone(),
            });
        }
    }
    (conditionals_checked, blocks_checked, agreements)
}

/// Every sample asset on disk, as sorted `(label, path)` pairs with labels
/// like `ue_4.27/Helm_BP.uasset`. The guard surveys whatever subset is
/// present: the committed fixtures in CI, the full private corpus locally.
fn survey_sample_paths() -> Vec<(String, PathBuf)> {
    let samples_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("samples");
    let mut paths: Vec<(String, PathBuf)> = Vec::new();
    let Ok(version_dirs) = fs::read_dir(&samples_dir) else {
        return paths;
    };
    for version_entry in version_dirs.flatten() {
        if !version_entry.path().is_dir() {
            continue;
        }
        let Ok(entries) = fs::read_dir(version_entry.path()) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "uasset") {
                let label = format!(
                    "{}/{}",
                    version_entry.file_name().to_string_lossy(),
                    entry.file_name().to_string_lossy()
                );
                paths.push((label, path));
            }
        }
    }
    paths.sort();
    paths
}

#[test]
fn rc_vs_structure_survey() {
    let log_path = std::env::temp_dir().join("rc_vs_structure_survey.log");
    let mut log = fs::File::create(&log_path)
        .unwrap_or_else(|err| panic!("create {}: {}", log_path.display(), err));

    let mut total_conditionals = 0usize;
    let mut total_blocks = 0usize;
    let mut total_agreements = 0usize;
    let mut disagreements: Vec<RcStructDisagreement> = Vec::new();
    let mut pair_dist: BTreeMap<(&'static str, &'static str), usize> = BTreeMap::new();
    let mut fixtures_scanned = 0usize;
    let mut events_scanned = 0usize;
    let mut functions_scanned = 0usize;

    for (fixture_label, sample_path) in survey_sample_paths() {
        let asset_bytes = match fs::read(&sample_path) {
            Ok(bytes) => bytes,
            Err(_) => continue,
        };
        let parsed = match parse_asset(&asset_bytes, false) {
            Ok(parsed) => parsed,
            Err(_) => continue,
        };
        fixtures_scanned += 1;
        writeln!(log, "=== {} ===", fixture_label).ok();

        // Ubergraph events via the partition path.
        if let Some(probe) = probe_ubergraph_partition(&parsed, &asset_bytes) {
            for entry in &probe.disk_entries {
                let Some(ranges) = probe.event_ranges.get(&entry.name) else {
                    continue;
                };
                let cfg = build_cfg(&probe.graph, entry.mem_offset, ranges);
                if cfg.opcode_count() == 0 || !is_reducible(&cfg) {
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
                let (conds, blocks, agree) = survey_unit(
                    &cfg,
                    &probe.graph,
                    &tree,
                    &fixture_label,
                    &entry.name,
                    &mut disagreements,
                    &mut pair_dist,
                );
                total_conditionals += conds;
                total_blocks += blocks;
                total_agreements += agree;
                events_scanned += 1;
            }
        }

        // Standalone `.Function` exports via the flow-aware CFG.
        if let Some((ue5, name_table)) =
            crate::bytecode::decode::read_version_and_name_table(&asset_bytes)
        {
            let export_names: Vec<String> = parsed
                .exports
                .iter()
                .map(|(hdr, _)| hdr.object_name.clone())
                .collect();
            for (export_idx, (hdr, _props)) in parsed.exports.iter().enumerate() {
                let class =
                    crate::resolve::resolve_index(&parsed.imports, &export_names, hdr.class_index);
                if !class.ends_with(".Function") {
                    continue;
                }
                if hdr
                    .object_name
                    .starts_with(crate::bytecode::names::EXECUTE_UBERGRAPH_PREFIX)
                {
                    continue;
                }
                let Some((bytecode, _mem_size)) = parsed.bytecode_by_export.get(&(export_idx + 1))
                else {
                    continue;
                };
                if bytecode.is_empty() {
                    continue;
                }
                let (cfg, tree, _ipostdom, fn_graph) =
                    build_function_cfg_and_region_tree(bytecode, ue5, &name_table);
                if cfg.opcode_count() == 0 || !is_reducible(&cfg) {
                    continue;
                }
                let (conds, blocks, agree) = survey_unit(
                    &cfg,
                    &fn_graph,
                    &tree,
                    &fixture_label,
                    &hdr.object_name,
                    &mut disagreements,
                    &mut pair_dist,
                );
                total_conditionals += conds;
                total_blocks += blocks;
                total_agreements += agree;
                functions_scanned += 1;
            }
        }
    }

    writeln!(log).ok();
    writeln!(log, "SUMMARY").ok();
    writeln!(log, "  fixtures: {}", fixtures_scanned).ok();
    writeln!(log, "  events scanned: {}", events_scanned).ok();
    writeln!(log, "  functions scanned: {}", functions_scanned).ok();
    writeln!(
        log,
        "  IfThen(Else) conditionals checked: {}",
        total_conditionals
    )
    .ok();
    writeln!(log, "  block comparisons: {}", total_blocks).ok();
    writeln!(log, "  agreements: {}", total_agreements).ok();
    writeln!(log, "  disagreements: {}", disagreements.len()).ok();
    writeln!(log).ok();
    writeln!(
        log,
        "CONCRETE PAIR DISTRIBUTION (rc -> struct), audits non-vacuity:"
    )
    .ok();
    let concrete_pairs: usize = pair_dist.values().sum();
    writeln!(
        log,
        "  total concrete-vs-concrete comparisons: {}",
        concrete_pairs
    )
    .ok();
    for ((rc_label, struct_label), count) in &pair_dist {
        writeln!(log, "  rc={} struct={}: {}", rc_label, struct_label, count).ok();
    }
    writeln!(log).ok();
    let disagreement_lines: Vec<String> = disagreements
        .iter()
        .map(|diff| {
            format!(
                "DISAGREE {}::{} cond=b{}@0x{:x} ({}) block=b{}@0x{:x} rc={:?} struct={:?} rc_cond={}",
                diff.fixture,
                diff.unit,
                diff.conditional,
                diff.cond_addr,
                diff.region_kind,
                diff.block,
                diff.block_addr,
                diff.rc_bucket,
                diff.struct_bucket,
                format_cond(&diff.rc),
            )
        })
        .collect();
    for line in &disagreement_lines {
        writeln!(log, "{}", line).ok();
    }

    println!(
        "rc_vs_structure_survey: fixtures={} events={} functions={} conditionals={} comparisons={} agreements={} disagreements={} (log: {})",
        fixtures_scanned,
        events_scanned,
        functions_scanned,
        total_conditionals,
        total_blocks,
        total_agreements,
        disagreements.len(),
        log_path.display(),
    );

    // Non-vacuity: an empty or unparseable corpus must fail loudly rather
    // than green-wash the oracle.
    assert!(
        fixtures_scanned > 0 && total_conditionals > 0 && concrete_pairs > 0,
        "RC oracle surveyed nothing (fixtures={}, conditionals={}, concrete pairs={}); \
         the samples/ corpus or the conditional collection is broken",
        fixtures_scanned,
        total_conditionals,
        concrete_pairs,
    );
    assert!(
        disagreement_lines.is_empty(),
        "reaching-condition oracle disagrees with emitted structure on {} block(s) \
         (full report: {}):\n{}",
        disagreement_lines.len(),
        log_path.display(),
        disagreement_lines.join("\n"),
    );
}
