use clap::Parser as ClapParser;
use std::path::PathBuf;

use unreal_bp_inspect::output_json::to_json;
use unreal_bp_inspect::output_summary::print_summary;
use unreal_bp_inspect::output_text::print_text;
use unreal_bp_inspect::parser::parse_asset;

#[derive(ClapParser)]
#[command(
    name = "bp-inspect",
    about = "Extract Blueprint graph data from .uasset files",
    version
)]
struct Cli {
    /// Path to the .uasset file
    path: PathBuf,

    /// Output as JSON
    #[arg(long)]
    json: bool,

    /// Full import/export/property dump
    #[arg(long)]
    dump: bool,

    /// Filter exports by name (substring match, comma-separated)
    #[arg(long, short)]
    filter: Option<String>,

    /// Debug: dump raw table data
    #[arg(long)]
    debug: bool,
}

fn main() {
    let cli = Cli::parse();

    let data = std::fs::read(&cli.path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {}", cli.path.display(), e);
        std::process::exit(1);
    });

    let asset = match parse_asset(&data, cli.debug) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("Failed to parse {}: {}", cli.path.display(), e);
            std::process::exit(1);
        }
    };

    let filters: Vec<String> = cli
        .filter
        .map(|f| f.split(',').map(|s| s.trim().to_lowercase()).collect())
        .unwrap_or_default();

    if cli.json {
        println!(
            "{}",
            serde_json::to_string_pretty(&to_json(&asset, &filters)).unwrap()
        );
    } else if cli.dump {
        print_text(&asset, &filters);
    } else {
        print_summary(&asset, &filters);
    }
}
