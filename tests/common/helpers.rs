//! Shared filesystem helpers for the test suite.
//!
//! Reachable via `mod common;` (re-exported through `common::mod`) or
//! directly via `#[path = "common/helpers.rs"] mod helpers;` for binaries
//! that don't want to pull in the full common module tree (e.g. to avoid
//! the pattern-DSL unit tests being recompiled into every test binary).

#![allow(dead_code)]

use std::path::PathBuf;

/// Absolute path to the `samples/` directory under the crate root. Holds
/// every committed and gitignored `.uasset` fixture used by tests.
pub fn samples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("samples")
}

/// Absolute path to the committed `tests/baseline-snapshots/` directory.
pub fn baseline_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("baseline-snapshots")
}

/// Discover every `<ue_version>/<fixture>.uasset` present locally,
/// excluding fixtures whose stem matches any entry in `exclude`. Sorted
/// `(version, stem)` order for deterministic iteration.
pub fn discover_uassets(exclude: &[&str]) -> Vec<(String, String, PathBuf)> {
    let mut fixtures = Vec::new();
    let samples = samples_dir();
    let Ok(version_iter) = std::fs::read_dir(&samples) else {
        return fixtures;
    };
    for version_entry in version_iter.flatten() {
        if !version_entry
            .file_type()
            .map(|t| t.is_dir())
            .unwrap_or(false)
        {
            continue;
        }
        let version = version_entry.file_name().to_string_lossy().into_owned();
        let Ok(asset_iter) = std::fs::read_dir(version_entry.path()) else {
            continue;
        };
        for asset_entry in asset_iter.flatten() {
            let path = asset_entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("uasset") {
                continue;
            }
            let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
                continue;
            };
            if exclude.contains(&stem) {
                continue;
            }
            fixtures.push((version.clone(), stem.to_string(), path));
        }
    }
    fixtures.sort_by(|a, b| (a.0.as_str(), a.1.as_str()).cmp(&(b.0.as_str(), b.1.as_str())));
    fixtures
}
