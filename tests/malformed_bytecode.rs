//! Corrupted bytecode must end in a diagnostic, not a hang.
//!
//! Each patch changes one byte of an `FFieldPath` operand in a
//! BP_DecoderTest function, which misaligns every opcode after it. The
//! misread stream forms a jump cycle through an `EX_PUSH_EXECUTION_FLOW`
//! with no matching pop, which once kept the flow-stack search running
//! until it was killed. A new or widened opcode in an unverified engine
//! version misaligns a stream the same way.

mod common;

use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const FIXTURE: &str = "ue_4.27/BP_DecoderTest.uasset";
const TIME_LIMIT: Duration = Duration::from_secs(60);

/// One corrupted operand: the bytes around it as compiled, and the same
/// bytes with the field path count changed.
struct Corruption {
    function: &'static str,
    compiled: &'static [u8],
    corrupted: &'static [u8],
}

const CORRUPTIONS: [Corruption; 2] = [
    Corruption {
        function: "Loop_ForEachInt",
        compiled:
            b"\x00\x00\x00\x58\x00\x00\x00\x16\x5e\x5a\x07\x26\x01\x00\x00\x00\x01\x00\x00\x00",
        corrupted:
            b"\x00\x00\x00\x58\x00\x00\x00\x16\x5e\x5a\x07\x26\x01\x00\x00\x00\xea\x00\x00\x00",
    },
    Corruption {
        function: "Loop_ForEachItemName",
        compiled: b"\x59\x00\x00\x00\x1d\x01\x00\x00\x00\x16\x5e\x0f\x01\x00\x00\x00",
        corrupted: b"\x59\x00\x00\x00\x1d\x01\x00\x00\x00\x16\x5e\x0f\x12\x00\x00\x00",
    },
];

fn corrupted_fixture(corruption: &Corruption) -> Vec<u8> {
    let bytes = common::load_fixture(FIXTURE);
    let positions: Vec<usize> = bytes
        .windows(corruption.compiled.len())
        .enumerate()
        .filter(|(_, window)| *window == corruption.compiled)
        .map(|(position, _)| position)
        .collect();
    let [position] = positions[..] else {
        panic!(
            "{} pattern found {} times",
            corruption.function,
            positions.len()
        );
    };
    let mut patched = bytes;
    patched[position..position + corruption.corrupted.len()].copy_from_slice(corruption.corrupted);
    patched
}

struct Finished {
    code: Option<i32>,
    stdout: String,
    stderr: String,
}

/// Run the CLI and kill it if it outlives `TIME_LIMIT`, so a regression
/// fails instead of stalling the test run.
fn run_within_limit(flags: &[&str], paths: &[&Path]) -> Finished {
    let mut child = Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .args(flags)
        .args(paths)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = child.stdout.take().unwrap();
    let mut stderr = child.stderr.take().unwrap();
    let stdout = std::thread::spawn(move || {
        let mut text = String::new();
        stdout.read_to_string(&mut text).unwrap();
        text
    });
    let stderr = std::thread::spawn(move || {
        let mut text = String::new();
        stderr.read_to_string(&mut text).unwrap();
        text
    });
    let deadline = Instant::now() + TIME_LIMIT;
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("bp-inspect {flags:?} did not finish within {TIME_LIMIT:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    Finished {
        code: status.code(),
        stdout: stdout.join().unwrap(),
        stderr: stderr.join().unwrap(),
    }
}

#[test]
fn corrupted_operands_are_reported_as_incomplete() {
    let directory = tempfile::tempdir().unwrap();
    for corruption in &CORRUPTIONS {
        let path = directory
            .path()
            .join(format!("{}.uasset", corruption.function));
        std::fs::write(&path, corrupted_fixture(corruption)).unwrap();

        let inspect = run_within_limit(&[], &[&path]);
        assert_eq!(inspect.code, Some(2), "{}", inspect.stderr);
        assert!(
            inspect
                .stderr
                .contains(&format!("function {}:", corruption.function)),
            "{}",
            inspect.stderr
        );
        // The rest of the asset still renders.
        assert!(
            inspect.stdout.contains("Latent_OneDelay():"),
            "{}",
            inspect.stdout
        );

        let textconv = run_within_limit(&["--textconv"], &[&path]);
        assert_eq!(textconv.code, Some(0), "{}", textconv.stderr);
        assert!(
            textconv.stdout.starts_with("Incomplete result:\n"),
            "{}",
            textconv.stdout
        );
        assert!(
            textconv.stdout.contains(corruption.function),
            "{}",
            textconv.stdout
        );
    }
}

#[test]
fn corrupted_asset_cannot_be_compared() {
    let directory = tempfile::tempdir().unwrap();
    let corrupted = directory.path().join("corrupted.uasset");
    std::fs::write(&corrupted, corrupted_fixture(&CORRUPTIONS[0])).unwrap();
    let original = common::samples_dir().join(FIXTURE);

    let compare = run_within_limit(&["--diff"], &[&original, &corrupted]);
    assert_eq!(compare.code, Some(2), "{}", compare.stderr);
    assert!(
        compare.stderr.contains("cannot reliably compare"),
        "{}",
        compare.stderr
    );
}
