//! Audit pass comparing K2Node DoOnce macro count to decoded statement
//! count. Env-gated, output unchanged. Tests whether the EdGraph (Unreal
//! Editor node graph) is a reliable identity source for DoOnce macros.
//!
//! Set `BP_GRAPH_CLAIM_AUDIT=1` to activate. Output appended to the
//! divergence log keyed by ubergraph name. Per-event bucketing is
//! deferred: mapping K2Node DoOnces to events requires graph BFS
//! infrastructure not currently threaded through the decoder.

use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;

use crate::bytecode::asset::Event;
use crate::bytecode::names::{MacroKind, K2NODE_MACRO_INSTANCE};
use crate::bytecode::stmt::{LatchKind, Stmt};
use crate::prop_query::find_prop;
use crate::resolve::{resolve_index, short_class};
use crate::types::{ParsedAsset, PropValue};

/// Log path is fixed relative to the project root. Created if absent;
/// appended-to across runs so successive fixture passes accumulate.
const AUDIT_LOG_PATH: &str = "target/v2-graph-claim-divergence.log";

/// Env-gated entry. Returns `Ok(())` immediately when the gate is unset
/// or empty, so the call site stays cheap on the default path. Empty
/// value treated as off so `BP_GRAPH_CLAIM_AUDIT=` round-trips clean.
pub fn run_audit(asset: &ParsedAsset, asset_label: &str, events: &[Event]) -> std::io::Result<()> {
    match std::env::var("BP_GRAPH_CLAIM_AUDIT") {
        Ok(value) if !value.is_empty() => {}
        _ => return Ok(()),
    }

    let graph_count = count_graph_doonce_macros(asset);
    let decoded_count = count_decoded_doonce_latches(events);
    let divergence = graph_count as i64 - decoded_count as i64;

    let log_path = PathBuf::from(AUDIT_LOG_PATH);
    if let Some(parent) = log_path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log_path)?;
    writeln!(file, "=== {} ===", asset_label)?;
    writeln!(file, "graph_doonce_count: {}", graph_count)?;
    writeln!(file, "decoded_doonce_count: {}", decoded_count)?;
    writeln!(file, "divergence: {}", divergence)?;
    Ok(())
}

/// Walk every export, counting `K2Node_MacroInstance` entries whose
/// resolved macro name equals "DoOnce".
fn count_graph_doonce_macros(asset: &ParsedAsset) -> usize {
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let mut count = 0usize;
    for (export_idx_zero, (hdr, props)) in asset.exports.iter().enumerate() {
        let export_index_one_based = export_idx_zero + 1;
        let class_full = resolve_index(&asset.imports, &export_names, hdr.class_index);
        if short_class(&class_full) != K2NODE_MACRO_INSTANCE {
            continue;
        }
        if !asset.pin_data.contains_key(&export_index_one_based) {
            continue;
        }
        if resolve_macro_name(asset, &export_names, props).map(|name| MacroKind::from_name(&name))
            == Some(MacroKind::DoOnce)
        {
            count += 1;
        }
    }
    count
}

/// Resolve the macro name for a `K2Node_MacroInstance` from its
/// `MacroGraphReference.MacroGraph` object property. Returns `None` when
/// the reference is missing or unresolvable. Resolves the name locally so
/// the audit stays intentionally inert and self-contained.
fn resolve_macro_name(
    asset: &ParsedAsset,
    export_names: &[String],
    props: &[crate::types::Property],
) -> Option<String> {
    let macro_ref = find_prop(props, "MacroGraphReference")?;
    let PropValue::Struct { fields, .. } = &macro_ref.value else {
        return None;
    };
    let graph = find_prop(fields, "MacroGraph")?;
    let PropValue::Object(graph_index) = graph.value else {
        return None;
    };
    let resolved_full = resolve_index(&asset.imports, export_names, graph_index);
    // Resolved path looks like `...StandardMacros:DoOnce` or
    // `...StandardMacros.DoOnce`; the trailing component is the macro name.
    resolved_full.rsplit(['.', ':']).next().map(str::to_string)
}

/// Count every `Stmt::Latch::DoOnce` reachable in the decoded event tree,
/// recursing into Branch/Sequence/Loop/Switch/Latch bodies.
fn count_decoded_doonce_latches(events: &[Event]) -> usize {
    let mut total = 0usize;
    for event in events {
        for stmt in &event.body {
            count_doonce_in_stmt(stmt, &mut total);
        }
    }
    total
}

fn count_doonce_in_stmt(stmt: &Stmt, total: &mut usize) {
    match stmt {
        Stmt::Latch {
            kind, init, body, ..
        } => {
            if matches!(kind, LatchKind::DoOnce { .. }) {
                *total += 1;
            }
            for child in init {
                count_doonce_in_stmt(child, total);
            }
            for child in body {
                count_doonce_in_stmt(child, total);
            }
        }
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            for child in then_body {
                count_doonce_in_stmt(child, total);
            }
            for child in else_body {
                count_doonce_in_stmt(child, total);
            }
        }
        Stmt::Sequence { pins, .. } => {
            for pin in pins {
                for child in pin {
                    count_doonce_in_stmt(child, total);
                }
            }
        }
        Stmt::Loop {
            body, completion, ..
        } => {
            for child in body {
                count_doonce_in_stmt(child, total);
            }
            if let Some(completion_body) = completion {
                for child in completion_body {
                    count_doonce_in_stmt(child, total);
                }
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for case in cases {
                for child in &case.body {
                    count_doonce_in_stmt(child, total);
                }
            }
            if let Some(default_body) = default {
                for child in default_body {
                    count_doonce_in_stmt(child, total);
                }
            }
        }
        Stmt::Assignment { .. }
        | Stmt::Call { .. }
        | Stmt::Return { .. }
        | Stmt::Break { .. }
        | Stmt::EventCall { .. }
        | Stmt::Unknown { .. } => {}
    }
}
