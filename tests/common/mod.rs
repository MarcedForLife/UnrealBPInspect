#![allow(dead_code)]

use std::path::PathBuf;

pub fn load_fixture(name: &str) -> Vec<u8> {
    let path = fixture_path(name);
    std::fs::read(&path).unwrap_or_else(|e| panic!("Failed to read fixture {}: {}", path.display(), e))
}

pub fn fixture_exists(name: &str) -> bool {
    fixture_path(name).exists()
}

pub fn assert_snapshot(name: &str, actual: &str) {
    let path = snapshot_path(name);

    if std::env::var("UPDATE_SNAPSHOTS").is_ok() {
        std::fs::write(&path, actual).unwrap_or_else(|e| panic!("Failed to write snapshot {}: {}", path.display(), e));
        return;
    }

    let expected = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(_) => {
            let new_path = path.with_extension("txt.new");
            std::fs::write(&new_path, actual).unwrap();
            panic!(
                "Snapshot {} does not exist. Actual output written to {}.\nRun with UPDATE_SNAPSHOTS=1 to create it.",
                path.display(),
                new_path.display()
            );
        }
    };

    if actual != expected {
        let new_path = path.with_extension("txt.new");
        std::fs::write(&new_path, actual).unwrap();

        // Find first differing line
        let actual_lines: Vec<&str> = actual.lines().collect();
        let expected_lines: Vec<&str> = expected.lines().collect();
        let mut diff_line = 0;
        for (i, (a, e)) in actual_lines.iter().zip(expected_lines.iter()).enumerate() {
            if a != e {
                diff_line = i + 1;
                break;
            }
        }
        if diff_line == 0 {
            diff_line = actual_lines.len().min(expected_lines.len()) + 1;
        }

        panic!(
            "Snapshot mismatch for {}.\nFirst difference at line {}.\nExpected ({} lines) vs actual ({} lines).\nActual output written to {}.\nRun with UPDATE_SNAPSHOTS=1 to update.",
            path.display(),
            diff_line,
            expected_lines.len(),
            actual_lines.len(),
            new_path.display()
        );
    }
}

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("samples").join(name)
}

fn snapshot_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests").join("snapshots").join(format!("{}.txt", name))
}
