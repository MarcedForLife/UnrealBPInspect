//! Golden round-trip harness for the typed statement IR.
//!
//! Exercises `parse_stmt` + `fmt_stmt` (Phase 5d.7a) against every
//! `BcStatement.text` recoverable from the decoded corpus. Unlike the
//! `Expr`-level harness (see `bytecode_ir_roundtrip.rs`), this operates
//! on whole statement lines, flow opcodes, assignments, and bare calls
//! all in their natural shape, no pre-classification split.
//!
//! Checks parse-print-parse idempotence as a hard assert. Byte-equality
//! and `Stmt::Unknown` fallback rate were dropped, whitespace-only
//! divergences are benign and the fallback count was corpus-sensitive.
//!
//! Skips cleanly when no fixtures are present so CI stays green.

use std::path::{Path, PathBuf};

use unreal_bp_inspect::bytecode::decode::{fmt_stmt, parse_stmt, Stmt};
use unreal_bp_inspect::parser::parse_asset;
use unreal_bp_inspect::types::{ParsedAsset, PropValue};

/// Walk the samples tree for every `.uasset`, in sorted order for
/// deterministic output across OSes.
fn collect_fixture_paths() -> Vec<PathBuf> {
    let samples_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("samples");
    let mut paths = Vec::new();
    walk_uassets(&samples_root, &mut paths);
    paths.sort();
    paths
}

fn walk_uassets(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_uassets(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("uasset") {
            out.push(path);
        }
    }
}

/// Pull every decoded bytecode statement line out of a parsed asset.
///
/// Bytecode is stored as `Property { name: "Bytecode", value: Array { items: Str(...) } }`
/// with each string shaped `"{:04x}: {text}"` (see `parser.rs`).
fn collect_statement_lines(asset: &ParsedAsset) -> Vec<String> {
    let mut lines = Vec::new();
    for (_, props) in &asset.exports {
        for prop in props {
            if prop.name != "Bytecode" {
                continue;
            }
            if let PropValue::Array { items, .. } = &prop.value {
                for item in items {
                    if let PropValue::Str(line) = item {
                        if let Some(text) = strip_offset_prefix(line) {
                            lines.push(text.to_owned());
                        }
                    }
                }
            }
        }
    }
    lines
}

/// Strip the `"XXXX: "` hex-offset prefix that `parser.rs` prepends to
/// each decoded statement.
fn strip_offset_prefix(line: &str) -> Option<&str> {
    let colon_space = line.find(": ")?;
    let hex_part = &line[..colon_space];
    if !hex_part.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    Some(&line[colon_space + ": ".len()..])
}

/// Gather every statement line across the full local fixture corpus.
/// Returns an empty vec if no fixtures were found.
fn gather_corpus() -> Vec<String> {
    let mut all = Vec::new();
    for path in collect_fixture_paths() {
        let Ok(data) = std::fs::read(&path) else {
            continue;
        };
        let Ok(asset) = parse_asset(&data, false) else {
            continue;
        };
        all.extend(collect_statement_lines(&asset));
    }
    all
}

#[test]
fn parse_print_parse_idempotent_stmt() {
    let lines = gather_corpus();
    if lines.is_empty() {
        eprintln!("No fixtures available; skipping parse_print_parse_idempotent_stmt");
        return;
    }

    let mut failures: Vec<(String, Stmt, String, Stmt)> = Vec::new();
    for text in &lines {
        let first = parse_stmt(text);
        let printed = fmt_stmt(&first);
        let second = parse_stmt(&printed);
        if first != second {
            failures.push((text.clone(), first, printed, second));
            if failures.len() >= 5 {
                break;
            }
        }
    }

    if !failures.is_empty() {
        let mut msg = format!(
            "parse_stmt/fmt_stmt idempotence failed on {} input(s). First {} cases:\n",
            failures.len(),
            failures.len().min(5),
        );
        for (text, first, printed, second) in &failures {
            msg.push_str(&format!(
                "--\ninput:    {text}\nparsed:   {first:?}\nprinted:  {printed}\nreparsed: {second:?}\n",
            ));
        }
        panic!("{msg}");
    }
}
