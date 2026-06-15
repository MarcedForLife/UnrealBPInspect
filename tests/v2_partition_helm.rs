//! Real-fixture partition tests.
//!
//! The unit tests in `src/bytecode/partition.rs` only exercise the partitioner
//! against synthetic byte streams. These run it on real `.uasset` fixtures, so
//! drift between synthetic and real input shapes (operand sizes, opcode
//! coverage, memory-vs-disk coordinate mismatches) surfaces here.
//!
//! Helm is the only committed fixture. Private fixtures present locally are
//! picked up by the `#[ignore]`d discovery test.

#[path = "common/helpers.rs"]
mod helpers;

use helpers::{baseline_dir, discover_uassets, samples_dir};
use std::path::Path;

use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::parser::parse_asset;

/// Decode an asset and return its event names. A failed partition leaves
/// `events` empty even when the fixture has an ubergraph with entries.
fn decoded_event_names(asset_path: &Path) -> Vec<String> {
    let asset_bytes = std::fs::read(asset_path)
        .unwrap_or_else(|err| panic!("read {}: {}", asset_path.display(), err));
    let parsed = parse_asset(&asset_bytes, false)
        .unwrap_or_else(|err| panic!("parse {}: {}", asset_path.display(), err));
    decode_asset(&parsed, &asset_bytes)
        .events
        .iter()
        .map(|event| event.name.clone())
        .collect()
}

/// Event names the v1 baseline lists in its `Functions:` block. V1 emits events
/// and ordinary functions together, tagging events `[Event...]`; we pick lines
/// carrying that tag and take the leading identifier. This is the closest stable
/// proxy for the event-name list without re-running the full v1 emit pipeline.
fn baseline_event_names(baseline_path: &Path) -> Vec<String> {
    let text = std::fs::read_to_string(baseline_path)
        .unwrap_or_else(|err| panic!("read baseline {}: {}", baseline_path.display(), err));
    text.lines()
        .filter(|line| line.contains("[Event"))
        .filter_map(|line| {
            let trimmed = line.trim_start();
            trimmed.find('(').map(|open| trimmed[..open].to_string())
        })
        .collect()
}

#[test]
fn helm_4_27_decodes_standalone_functions() {
    // Helm 4.27 has no ubergraph events; its only event (UserConstructionScript)
    // lives in a standalone export. This guards the standalone-function decode
    // path: a regression in the ubergraph branch must not abort the decode or
    // drop these functions.
    let asset_path = samples_dir().join("ue_4.27").join("Helm_BP.uasset");
    assert!(
        asset_path.exists(),
        "missing committed fixture: {} (Helm_BP must remain committed)",
        asset_path.display()
    );

    let asset_bytes = std::fs::read(&asset_path).unwrap();
    let parsed = parse_asset(&asset_bytes, false).unwrap();
    let decoded = decode_asset(&parsed, &asset_bytes);

    // UserConstructionScript may land in either bucket depending on how the
    // standalone event is classified, so check the union.
    let mut names: Vec<&str> = decoded.functions.iter().map(|f| f.name.as_str()).collect();
    names.extend(decoded.events.iter().map(|e| e.name.as_str()));
    for expected in ["GetSteeringAngle", "UserConstructionScript"] {
        assert!(
            names.contains(&expected),
            "4.27 Helm decode missing standalone function '{expected}': got {names:?}"
        );
    }
}

#[test]
fn helm_5_3_partition_succeeds_with_event_match() {
    // Helm 5.3 has an ubergraph with events. Canary that the mem-to-disk
    // converter plus the partition graph resolve all entry offsets and jump
    // targets, so every event the v1 baseline lists survives the v2 decode.
    let asset_path = samples_dir().join("ue_5.3").join("Helm_BP.uasset");
    if !asset_path.exists() {
        eprintln!(
            "skipping: committed fixture missing at {}",
            asset_path.display()
        );
        return;
    }

    let baseline_events = baseline_event_names(&baseline_dir().join("ue_5.3_Helm_BP.txt"));
    let decoded_events = decoded_event_names(&asset_path);

    assert!(
        !decoded_events.is_empty(),
        "Helm 5.3 partition produced no events (partition probably failed)"
    );
    for name in &baseline_events {
        assert!(
            decoded_events.iter().any(|d| d == name),
            "decoded events missing '{}': got {:?}",
            name,
            decoded_events
        );
    }
}

/// Generic check for any non-Helm fixtures present locally. These are gitignored
/// and absent in CI, so the test no-ops there. Locally, each discovered fixture
/// is partitioned and required to produce at least one event.
#[test]
#[ignore = "private fixtures gitignored; run locally with -- --ignored when present"]
fn private_fixtures_partition_succeeds() {
    let fixtures = discover_uassets(&["Helm_BP"]);
    if fixtures.is_empty() {
        eprintln!("no private fixtures present; nothing to check");
        return;
    }
    for (version, name, path) in fixtures {
        assert!(
            !decoded_event_names(&path).is_empty(),
            "{}/{} partition produced no events (partition probably failed)",
            version,
            name
        );
    }
}
