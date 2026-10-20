//! Latent call continuations through partition, decode and every output mode.
//!
//! BP_DecoderTest's `Latent_OneDelay` and `Latent_TwoDelays` events are
//! editor-compiled Delay chains. Renaming the `Delay` FName in place turns
//! them into calls to a latent function the decoder has never seen, with the
//! compiler's real linkage operands left intact. Patching a linkage operand
//! produces resume targets the decoder must refuse.

mod common;

use std::path::Path;
use std::process::{Command, Output};

use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::parser::parse_asset;

const FIXTURE: &str = "ue_4.27/BP_DecoderTest.uasset";
/// Name-table entry for `Delay`: length including the terminator, then text.
const DELAY_NAME: &[u8] = b"\x06\x00\x00\x00Delay\x00";
const PAUSE_NAME: &[u8] = b"\x06\x00\x00\x00Pause\x00";
/// `EX_SKIP_OFFSET_CONST` carrying `Latent_OneDelay`'s linkage.
const ONE_DELAY_LINKAGE: &[u8] = b"\x5b\x55\x00\x00\x00";

/// Replace each of the `count` occurrences of `needle` in place.
fn replace_exactly(bytes: &[u8], needle: &[u8], replacement: &[u8], count: usize) -> Vec<u8> {
    assert_eq!(needle.len(), replacement.len());
    let positions: Vec<usize> = bytes
        .windows(needle.len())
        .enumerate()
        .filter(|(_, window)| *window == needle)
        .map(|(position, _)| position)
        .collect();
    assert_eq!(positions.len(), count, "occurrences of {needle:?}");
    let mut patched = bytes.to_vec();
    for position in positions {
        patched[position..position + needle.len()].copy_from_slice(replacement);
    }
    patched
}

fn replace_once(bytes: &[u8], needle: &[u8], replacement: &[u8]) -> Vec<u8> {
    replace_exactly(bytes, needle, replacement, 1)
}

fn renamed_fixture() -> Vec<u8> {
    replace_once(&common::load_fixture(FIXTURE), DELAY_NAME, PAUSE_NAME)
}

fn with_one_delay_linkage(target: u32) -> Vec<u8> {
    let mut linkage = vec![0x5b];
    linkage.extend_from_slice(&target.to_le_bytes());
    replace_once(&common::load_fixture(FIXTURE), ONE_DELAY_LINKAGE, &linkage)
}

fn print_line(text: &str) -> String {
    format!(
        "PrintString(self, \"{text}\", true, true, MakeLinearColor(0.0000, 0.6600, 1.0000, \
         1.0000), 2.0000)"
    )
}

fn run_cli(args: &[&Path], flags: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_bp-inspect"))
        .args(flags)
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn unfamiliar_latent_function_keeps_its_continuations() {
    let original = common::decoded_summary(&common::load_fixture(FIXTURE));
    let renamed = common::decoded_summary(&renamed_fixture());
    assert_eq!(renamed, original.replace("Delay(self", "Pause(self"));
    assert!(!renamed.contains("MakeLatentActionInfo"));

    let one_delay = [
        print_line("Before"),
        "Pause(self, 0.5000)".into(),
        print_line("After"),
    ];
    let two_delays = [
        print_line("A"),
        "Pause(self, 0.1000)".into(),
        print_line("B"),
        "Pause(self, 0.2000)".into(),
        print_line("C"),
    ];
    for expected in [&one_delay[..], &two_delays[..]] {
        let block = expected
            .iter()
            .map(|line| format!("    {line}\n"))
            .collect::<String>();
        assert!(renamed.contains(&block), "missing in order:\n{block}");
    }

    let parsed = parse_asset(&renamed_fixture(), false).unwrap();
    assert!(decode_asset(&parsed).diagnostics.is_empty());
}

#[test]
fn unfamiliar_latent_continuations_reach_dump_and_json() {
    let bytes = renamed_fixture();
    let dump = common::decoded_text(&bytes);
    let json = common::decoded_json(&bytes);
    for text in ["After", "B", "C"] {
        let line = print_line(text);
        assert!(dump.contains(&line), "dump is missing {line}");
        let escaped = serde_json::to_string(&line).unwrap();
        assert!(
            json.contains(escaped.trim_matches('"')),
            "JSON is missing {line}"
        );
    }
    for output in [dump, json] {
        assert!(!output.contains("MakeLatentActionInfo(skip_offset"));
    }
}

#[test]
fn diff_shows_a_change_after_an_unfamiliar_latent_call() {
    let directory = tempfile::tempdir().unwrap();
    let before = directory.path().join("before.uasset");
    let after = directory.path().join("after.uasset");
    std::fs::write(&before, renamed_fixture()).unwrap();
    // The bytecode string constant and the editor pin default both change.
    std::fs::write(
        &after,
        replace_exactly(&renamed_fixture(), b"After\x00", b"Later\x00", 2),
    )
    .unwrap();
    let result = run_cli(&[&before, &after], &["--diff"]);
    assert_eq!(result.status.code(), Some(1));
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(stdout.contains(&format!("-    {}", print_line("After"))));
    assert!(stdout.contains(&format!("+    {}", print_line("Later"))));
}

/// The summary line after `Latent_OneDelay`'s Delay call.
fn line_after_one_delay(summary: &str) -> &str {
    let call = summary.find("    Delay(self, 0.5000)\n").unwrap();
    summary[call..].lines().nth(1).unwrap()
}

#[test]
fn malformed_resume_target_is_reported_and_marked() {
    // 0x5c falls inside an opcode.
    let bytes = with_one_delay_linkage(0x5c);
    let parsed = parse_asset(&bytes, false).unwrap();
    let diagnostics = decode_asset(&parsed).diagnostics;
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert!(diagnostics[0]
        .reason
        .contains("resume target 0x5c is not an opcode boundary"));

    let summary = common::decoded_summary(&bytes);
    assert_eq!(
        line_after_one_delay(&summary),
        "    // UNKNOWN at 0x5c: latent continuation not decoded, resume target 0x5c is not an \
         opcode boundary [0 bytes]"
    );
    assert!(!summary.contains(&print_line("After")));
}

#[test]
fn resume_target_in_event_code_is_marked_without_failing() {
    // A loop back to an earlier node resumes onto code an event already
    // shows. 0x10 lands in Conv_DirectDoOnce_A's code.
    let bytes = with_one_delay_linkage(0x10);
    let parsed = parse_asset(&bytes, false).unwrap();
    assert!(decode_asset(&parsed).diagnostics.is_empty());
    let summary = common::decoded_summary(&bytes);
    let marker = line_after_one_delay(&summary);
    assert!(
        marker.starts_with("    // UNKNOWN at ")
            && marker
                .contains("latent continuation resumes in code shown in event Conv_DirectDoOnce_A"),
        "{marker}"
    );

    let directory = tempfile::tempdir().unwrap();
    let shared = directory.path().join("shared.uasset");
    std::fs::write(&shared, &bytes).unwrap();
    assert_eq!(run_cli(&[&shared], &[]).status.code(), Some(0));
}

#[test]
fn rejected_resume_target_fails_inspection_and_comparison() {
    let directory = tempfile::tempdir().unwrap();
    let rejected = directory.path().join("rejected.uasset");
    let original = common::samples_dir().join(FIXTURE);
    std::fs::write(&rejected, with_one_delay_linkage(0x5c)).unwrap();

    let inspect = run_cli(&[&rejected], &[]);
    assert_eq!(inspect.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&inspect.stderr).contains("latent continuation"));
    assert!(String::from_utf8_lossy(&inspect.stdout).contains("latent continuation not decoded"));

    let compare = run_cli(&[&rejected, &original], &["--diff"]);
    assert_eq!(compare.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&compare.stderr).contains("cannot reliably compare"));
}
