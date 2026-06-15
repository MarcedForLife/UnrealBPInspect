use anyhow::{bail, Context, Result};
use clap::Parser as ClapParser;
use std::path::{Path, PathBuf};

use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::bytecode::dump_bridge::inject_v2_bytecode_props;
use unreal_bp_inspect::bytecode::emit::emit_summary_with_asset;
use unreal_bp_inspect::output_diff::diff_summary_texts;
use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::filter_summary;
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
    #[arg(long, short)]
    json: bool,

    /// Full import/export/property dump
    #[arg(long)]
    dump: bool,

    /// Filter output by substring (comma-separated, case-insensitive)
    #[arg(long, short)]
    filter: Option<String>,

    /// Compare two .uasset files (requires exactly 2 paths)
    #[arg(long, short)]
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
    let mut asset =
        parse_asset(&data, debug).with_context(|| format!("failed to parse {}", path.display()))?;
    Ok(match mode {
        // Summary routes through the decoder + emitter. Dump and JSON are
        // parse-level table/property renderers; the override bridge below
        // re-sources their per-function bytecode from the decoder so they
        // stay consistent with the summary mode.
        OutputMode::Summary => {
            let decoded = decode_asset(&asset, &data);
            filter_summary(&emit_summary_with_asset(&decoded, &asset), filters)
        }
        OutputMode::Dump => {
            let decoded = decode_asset(&asset, &data);
            inject_v2_bytecode_props(&mut asset, &decoded);
            format_text(&asset, filters)
        }
        OutputMode::Json => {
            let decoded = decode_asset(&asset, &data);
            inject_v2_bytecode_props(&mut asset, &decoded);
            serde_json::to_string_pretty(&to_json(&asset, filters))
                .context("serializing asset to JSON")?
        }
    })
}

fn run(cli: Cli) -> Result<bool> {
    if let Some(version) = cli.update {
        let target = if version == "latest" {
            None
        } else {
            Some(version)
        };
        run_update(target.as_deref())?;
        return Ok(true);
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
        bail!("No .uasset files found");
    }

    if cli.diff {
        return run_diff(&files, &filters, cli.context);
    }

    let single = files.len() == 1;
    if matches!(mode, OutputMode::Json) && !single {
        run_batch_json(&files, &mode, &filters, cli.debug)
    } else {
        run_batch_text(&files, &mode, &filters, cli.debug, single)
    }
}

fn run_diff(files: &[PathBuf], filters: &[String], context: usize) -> Result<bool> {
    if files.len() != 2 {
        bail!("--diff requires exactly 2 .uasset files");
    }
    let before = std::fs::read(&files[0])
        .with_context(|| format!("failed to read {}", files[0].display()))?;
    let after = std::fs::read(&files[1])
        .with_context(|| format!("failed to read {}", files[1].display()))?;
    let before_asset = parse_asset(&before, false)
        .with_context(|| format!("failed to parse {}", files[0].display()))?;
    let after_asset = parse_asset(&after, false)
        .with_context(|| format!("failed to parse {}", files[1].display()))?;
    let before_text = filter_summary(
        &emit_summary_with_asset(&decode_asset(&before_asset, &before), &before_asset),
        filters,
    );
    let after_text = filter_summary(
        &emit_summary_with_asset(&decode_asset(&after_asset, &after), &after_asset),
        filters,
    );
    let label_a = files[0].display().to_string();
    let label_b = files[1].display().to_string();
    let (output, has_changes) =
        diff_summary_texts(&before_text, &after_text, &label_a, &label_b, context);
    if has_changes {
        print!("{}", output);
        return Ok(false);
    }
    Ok(true)
}

/// Print the per-batch "N of M files failed" notice to stderr when some files
/// failed but at least one succeeded. `successes` is the count that produced
/// output, so `successes + failures` is the total file count.
fn report_batch_failures(failures: usize, successes: usize) {
    if failures > 0 {
        eprintln!("{} of {} files failed", failures, failures + successes);
    }
}

fn run_batch_json(
    files: &[PathBuf],
    mode: &OutputMode,
    filters: &[String],
    debug: bool,
) -> Result<bool> {
    let mut results = Vec::new();
    let mut failures = 0;
    for path in files {
        match process_file(path, mode, filters, debug) {
            Ok(json_str) => {
                let mut val: serde_json::Value = serde_json::from_str(&json_str)
                    .context("re-parsing per-file JSON output for batch aggregation")?;
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
        bail!("all files failed to parse");
    }
    let serialized = serde_json::to_string_pretty(&results)
        .context("serializing aggregated batch JSON results")?;
    println!("{}", serialized);
    report_batch_failures(failures, results.len());
    Ok(true)
}

fn run_batch_text(
    files: &[PathBuf],
    mode: &OutputMode,
    filters: &[String],
    debug: bool,
    single: bool,
) -> Result<bool> {
    let mut successes = 0;
    let mut failures = 0;
    for path in files {
        match process_file(path, mode, filters, debug) {
            Ok(output) => {
                if !single {
                    println!("=== {} ===\n", path.display());
                }
                print!("{}", output);
                successes += 1;
            }
            Err(e) => {
                if single {
                    return Err(e);
                }
                eprintln!("Warning: {:#}", e);
                failures += 1;
            }
        }
    }
    if successes == 0 {
        bail!("all files failed to parse");
    }
    report_batch_failures(failures, successes);
    Ok(true)
}

fn main() {
    let cli = Cli::parse();
    match run(cli) {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(e) => {
            eprintln!("{:#}", e);
            std::process::exit(1);
        }
    }
}
