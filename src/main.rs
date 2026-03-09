use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use std::path::{Path, PathBuf};

use unreal_bp_inspect::output_diff::format_diff;
use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::format_summary;
use unreal_bp_inspect::output_text::format_text;
use unreal_bp_inspect::parser::parse_asset;
use unreal_bp_inspect::update::run_update;

#[derive(ClapParser)]
#[command(
    name = "bp-inspect",
    about = "Extract Blueprint graph data from .uasset files",
    version
)]
struct Cli {
    /// Paths to .uasset files or directories (recursive)
    #[arg(required_unless_present = "update", num_args = 1..)]
    paths: Vec<PathBuf>,

    /// Update bp-inspect to the latest version (or specify a version, e.g. --update v0.2.0)
    #[arg(long, num_args = 0..=1, default_missing_value = "latest")]
    update: Option<String>,

    /// Output as JSON
    #[arg(long)]
    json: bool,

    /// Full import/export/property dump
    #[arg(long)]
    dump: bool,

    /// Filter exports by name (substring match, comma-separated)
    #[arg(long, short)]
    filter: Option<String>,

    /// Compare two .uasset files (requires exactly 2 paths)
    #[arg(long)]
    diff: bool,

    /// Number of context lines in diff output (default: 3)
    #[arg(long, default_value = "3")]
    context: usize,

    /// Debug: dump raw table data
    #[arg(long)]
    debug: bool,
}

enum OutputMode {
    Summary,
    Dump,
    Json,
}

fn collect_uasset_paths(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut result = Vec::new();
    for path in paths {
        if path.is_dir() {
            collect_from_dir(path, &mut result);
        } else {
            result.push(path.clone());
        }
    }
    result.sort();
    result
}

fn collect_from_dir(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Warning: cannot read directory {}: {}", dir.display(), e);
            return;
        }
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_from_dir(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "uasset") {
            out.push(path);
        }
    }
}

fn process_file(path: &Path, mode: &OutputMode, filters: &[String], debug: bool) -> Result<String> {
    let data = std::fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
    let asset =
        parse_asset(&data, debug).with_context(|| format!("failed to parse {}", path.display()))?;
    Ok(match mode {
        OutputMode::Summary => format_summary(&asset, filters),
        OutputMode::Dump => format_text(&asset, filters),
        OutputMode::Json => serde_json::to_string_pretty(&to_json(&asset, filters)).unwrap(),
    })
}

fn main() {
    let cli = Cli::parse();

    if let Some(version) = cli.update {
        let target = if version == "latest" {
            None
        } else {
            Some(version)
        };
        if let Err(e) = run_update(target.as_deref()) {
            eprintln!("Update failed: {:#}", e);
            std::process::exit(1);
        }
        return;
    }

    let mode = if cli.json {
        OutputMode::Json
    } else if cli.dump {
        OutputMode::Dump
    } else {
        OutputMode::Summary
    };

    let filters: Vec<String> = cli
        .filter
        .map(|f| f.split(',').map(|s| s.trim().to_lowercase()).collect())
        .unwrap_or_default();

    let files = collect_uasset_paths(&cli.paths);
    if files.is_empty() {
        eprintln!("No .uasset files found");
        std::process::exit(1);
    }

    if cli.diff {
        if files.len() != 2 {
            eprintln!("--diff requires exactly 2 .uasset files");
            std::process::exit(2);
        }
        let before = match std::fs::read(&files[0]) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("failed to read {}: {}", files[0].display(), e);
                std::process::exit(2);
            }
        };
        let after = match std::fs::read(&files[1]) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("failed to read {}: {}", files[1].display(), e);
                std::process::exit(2);
            }
        };
        let label_a = files[0].display().to_string();
        let label_b = files[1].display().to_string();
        match format_diff(&before, &after, &label_a, &label_b, &filters, cli.context) {
            Ok((output, has_changes)) => {
                if has_changes {
                    print!("{}", output);
                    std::process::exit(1);
                }
            }
            Err(e) => {
                eprintln!("{:#}", e);
                std::process::exit(2);
            }
        }
        return;
    }

    let single = files.len() == 1;

    if matches!(mode, OutputMode::Json) && !single {
        // Multi-file JSON: collect into array
        let mut results = Vec::new();
        let mut failures = 0;
        for path in &files {
            match process_file(path, &mode, &filters, cli.debug) {
                Ok(json_str) => {
                    let mut val: serde_json::Value =
                        serde_json::from_str(&json_str).expect("internal JSON error");
                    val["file"] = serde_json::json!(path.display().to_string());
                    results.push(val);
                }
                Err(e) => {
                    eprintln!("Warning: {:#}", e);
                    failures += 1;
                }
            }
        }
        if results.is_empty() {
            std::process::exit(1);
        }
        println!(
            "{}",
            serde_json::to_string_pretty(&results).expect("internal JSON error")
        );
        if failures > 0 {
            eprintln!("{} of {} files failed", failures, failures + results.len());
        }
    } else {
        // Single file or multi-file text modes
        let mut successes = 0;
        let mut failures = 0;
        for path in &files {
            match process_file(path, &mode, &filters, cli.debug) {
                Ok(output) => {
                    if !single {
                        println!("=== {} ===\n", path.display());
                    }
                    print!("{}", output);
                    successes += 1;
                }
                Err(e) => {
                    if single {
                        eprintln!("{:#}", e);
                        std::process::exit(1);
                    }
                    eprintln!("Warning: {:#}", e);
                    failures += 1;
                }
            }
        }
        if successes == 0 {
            std::process::exit(1);
        }
        if failures > 0 {
            eprintln!("{} of {} files failed", failures, failures + successes);
        }
    }
}
