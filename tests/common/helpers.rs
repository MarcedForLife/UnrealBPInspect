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
