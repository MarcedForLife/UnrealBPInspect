//! Golden round-trip harness for the typed expression IR.
//!
//! Walks every `.uasset` under `samples/`, runs `parse_stmt` on each
//! stored bytecode line, then harvests the typed [`Expr`] children of
//! the resulting [`Stmt`] tree. Each harvested expression is checked
//! for parse-print-parse idempotence via `fmt_expr` -> `parse_expr`.
//!
//! Consuming `parse_stmt` rather than re-classifying the raw line text
//! keeps this runner downstream of the statement IR instead of
//! maintaining a parallel surface-level classifier.
//!
//! Skips cleanly when no fixtures are present so CI stays green.

use std::path::{Path, PathBuf};

use unreal_bp_inspect::bytecode::decode::{fmt_expr, parse_expr, parse_stmt, Expr, Stmt};
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

/// Push every top-level [`Expr`] child reachable from `stmt` into `out`.
/// Descends through [`Stmt::WithTrailer`] but does not recurse into
/// nested `Expr` trees, the parse/fmt roundtrip check itself walks
/// sub-expressions by reparsing the printed form.
fn collect_stmt_exprs<'a>(stmt: &'a Stmt, out: &mut Vec<&'a Expr>) {
    match stmt {
        Stmt::Assignment { lhs, rhs } | Stmt::CompoundAssign { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        Stmt::Call { expr } | Stmt::JumpComputed { expr } => out.push(expr),
        Stmt::PopFlowIfNot { cond }
        | Stmt::ContinueIfNot { cond }
        | Stmt::IfJump { cond, .. }
        | Stmt::IfOpen { cond } => out.push(cond),
        Stmt::WithTrailer { inner, .. } => collect_stmt_exprs(inner, out),
        Stmt::PopFlow
        | Stmt::PushFlow { .. }
        | Stmt::Jump { .. }
        | Stmt::ReturnNop
        | Stmt::BareReturn
        | Stmt::Comment(_)
        | Stmt::BlockClose
        | Stmt::Break
        | Stmt::Else
        | Stmt::Unknown(_) => {}
    }
}

#[test]
fn parse_print_parse_idempotent_expr() {
    let lines = gather_corpus();
    if lines.is_empty() {
        eprintln!("No fixtures available; skipping parse_print_parse_idempotent_expr");
        return;
    }

    let mut failures: Vec<(String, Expr, Expr)> = Vec::new();
    for line in &lines {
        let stmt = parse_stmt(line);
        let mut exprs = Vec::new();
        collect_stmt_exprs(&stmt, &mut exprs);
        for expr in exprs {
            let printed = fmt_expr(expr);
            let reparsed = parse_expr(&printed);
            if *expr != reparsed {
                failures.push((printed, expr.clone(), reparsed));
                if failures.len() >= 5 {
                    break;
                }
            }
        }
        if failures.len() >= 5 {
            break;
        }
    }

    if !failures.is_empty() {
        let mut msg = format!(
            "parse_expr/fmt_expr idempotence failed on {} expression(s). First {} cases:\n",
            failures.len(),
            failures.len().min(5),
        );
        for (printed, original, reparsed) in &failures {
            msg.push_str(&format!(
                "--\nprinted:  {printed}\noriginal: {original:?}\nreparsed: {reparsed:?}\n",
            ));
        }
        panic!("{msg}");
    }
}
