mod common;

use common::helpers::baseline_dir;
use common::samples_dir;
use similar::TextDiff;
use std::path::PathBuf;

/// Map a baseline filename to its sample asset path. Baselines are named
/// `<ue_version>_<fixture>.txt` (e.g. `ue_4.27_Helm_BP.txt`); the version
/// prefix itself contains an underscore, so split right after the `ue_`
/// prefix: `ue_4.27_Helm_BP` -> version `ue_4.27`, fixture `Helm_BP` ->
/// `samples/ue_4.27/Helm_BP.uasset`.
fn sample_path_for_baseline(baseline_name: &str) -> Option<PathBuf> {
    let stem = baseline_name.strip_suffix(".txt")?;
    let without_ue = stem.strip_prefix("ue_")?;
    let version_end = without_ue.find('_')?;
    let version_number = &without_ue[..version_end];
    let fixture_name = &without_ue[version_end + 1..];
    Some(
        samples_dir()
            .join(format!("ue_{version_number}"))
            .join(format!("{fixture_name}.uasset")),
    )
}

/// Assert each baseline in `tests/baseline-snapshots/` matches the current v2
/// emit output for its sample. Baselines whose sample isn't checked in locally
/// are skipped (CI only ships the small committed fixtures; private-fixture
/// baselines are local-only developer signals per CLAUDE.md). Set
/// `UPDATE_SNAPSHOTS=1` to refresh baselines after an intentional emit change.
#[test]
fn v2_baseline_assert() {
    let baseline_dir = baseline_dir();

    let mut baseline_files: Vec<_> = std::fs::read_dir(&baseline_dir)
        .unwrap_or_else(|err| {
            panic!(
                "Failed to read baseline directory {}: {}",
                baseline_dir.display(),
                err
            )
        })
        .filter_map(|entry| {
            let name = entry.ok()?.file_name().into_string().ok()?;
            name.ends_with(".txt").then_some(name)
        })
        .collect();
    baseline_files.sort();

    assert!(
        !baseline_files.is_empty(),
        "No baseline files found in {}",
        baseline_dir.display()
    );

    for baseline_name in &baseline_files {
        let Some(sample_path) = sample_path_for_baseline(baseline_name) else {
            eprintln!("skip: {} (could not derive sample path)", baseline_name);
            continue;
        };
        if !sample_path.exists() {
            eprintln!(
                "skip: {} (source not found: {})",
                baseline_name,
                sample_path.display()
            );
            continue;
        }

        let baseline_path = baseline_dir.join(baseline_name);
        let baseline_text = std::fs::read_to_string(&baseline_path).unwrap_or_else(|err| {
            panic!(
                "Failed to read baseline {}: {}",
                baseline_path.display(),
                err
            )
        });
        let asset_bytes = std::fs::read(&sample_path).unwrap_or_else(|err| {
            panic!("Failed to read sample {}: {}", sample_path.display(), err)
        });
        let emitted = common::decoded_summary(&asset_bytes);

        if std::env::var("UPDATE_SNAPSHOTS").is_ok() {
            std::fs::write(&baseline_path, &emitted).unwrap_or_else(|err| {
                panic!(
                    "Failed to write baseline {}: {}",
                    baseline_path.display(),
                    err
                )
            });
            println!("updated: {}", baseline_name);
            continue;
        }

        if emitted != baseline_text {
            let diff = TextDiff::from_lines(&baseline_text, &emitted);
            let first_diff_hint = diff
                .iter_all_changes()
                .enumerate()
                .find(|(_, change)| change.tag() != similar::ChangeTag::Equal)
                .map(|(line_num, change)| {
                    format!(
                        "first diff at line {}: {:?} {}",
                        line_num,
                        change.tag(),
                        change
                    )
                })
                .unwrap_or_else(|| "no diff hint available".into());
            panic!(
                "v2 emit diverged from baseline {}.\n{}\nRun with UPDATE_SNAPSHOTS=1 to refresh if intentional.",
                baseline_name, first_diff_hint
            );
        }
    }
}
