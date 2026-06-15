//! Trackers for the v2 decoder behaviours surfaced by the committed
//! `BP_DecoderTest` synthetic fixture.
//!
//! These assert the DESIRED output. Each maps to a numbered finding in
//! `docs/v2-cfg-structuring-plan.md` ("BP_DecoderTest fixture findings").
//! When a fix lands, its tracker flips to green and the `v2_baseline`
//! snapshot for `ue_4.27_BP_DecoderTest.txt` is refreshed in the same change.
//! The "EXPECTED-FAIL" wording inside some assert messages is the diagnostic
//! shown only on regression; the suite is fully green.
//!
//! Run just these with:
//!   cargo test --release --test decodertest_known_bugs

use std::path::PathBuf;
use std::sync::OnceLock;
use unreal_bp_inspect::bytecode::decode::decode_asset;
use unreal_bp_inspect::bytecode::emit::emit_summary_with_asset;
use unreal_bp_inspect::parser::parse_asset;

/// v2 summary of the committed BP_DecoderTest fixture. Cached: the fixture is
/// deterministic, so it decodes once for the whole test binary.
fn decoder_test_emit() -> &'static str {
    static EMIT: OnceLock<String> = OnceLock::new();
    EMIT.get_or_init(|| {
        let asset_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("samples/ue_4.27/BP_DecoderTest.uasset");
        let bytes = std::fs::read(&asset_path)
            .unwrap_or_else(|err| panic!("read {}: {}", asset_path.display(), err));
        let parsed = parse_asset(&bytes, false)
            .unwrap_or_else(|err| panic!("parse {}: {:?}", asset_path.display(), err));
        let decoded = decode_asset(&parsed, &bytes);
        emit_summary_with_asset(&decoded, &parsed)
    })
}

/// Return the body lines of a function or event by name: everything after the
/// `  <name>(...)` header up to the next top-level header (a line indented
/// exactly two spaces whose first character is a letter). `// called by:`
/// comment lines (indent two spaces, then `/`) are not treated as headers.
fn function_body(emit: &str, name: &str) -> String {
    let lines: Vec<&str> = emit.lines().collect();
    let header_idx = lines.iter().position(|line| {
        line.starts_with("  ")
            && !line.starts_with("   ")
            && line.trim_start().starts_with(name)
            && line.contains('(')
    });
    let start = match header_idx {
        Some(index) => index + 1,
        None => panic!("function/event `{}` not found in emit", name),
    };
    let mut body = Vec::new();
    for line in &lines[start..] {
        let is_header = line.starts_with("  ")
            && !line.starts_with("   ")
            && line
                .chars()
                .nth(2)
                .is_some_and(|ch| ch.is_ascii_alphabetic());
        if is_header {
            break;
        }
        body.push(*line);
    }
    body.join("\n")
}

/// Finding 1: identically-wired mirror events decode asymmetrically.
/// `OnRightAxis` prepends a spurious `ResetDoOnce(Release)` inside the
/// `DoOnce(Attempt)` THEN body that `OnLeftAxis` does not. Both should have
/// exactly one (the post-`Attempt` re-arm), matching the editor graph.
#[test]
fn finding1_onrightaxis_no_duplicate_release_reset() {
    let emit = decoder_test_emit();
    let left = function_body(emit, "OnLeftAxis")
        .matches("ResetDoOnce(Release)")
        .count();
    let right = function_body(emit, "OnRightAxis")
        .matches("ResetDoOnce(Release)")
        .count();
    assert_eq!(
        left, 1,
        "sanity: OnLeftAxis should have exactly one ResetDoOnce(Release)"
    );
    assert_eq!(
        right, left,
        "EXPECTED-FAIL (finding 1): OnRightAxis has {} ResetDoOnce(Release), \
         should mirror OnLeftAxis ({}). The convergence/duplication pass is \
         duplicating the shared Release-gate reset for the right event.",
        right, left
    );
}

/// Finding 2: the dedicated released events fire the shared `DoOnce(Release)`
/// via fan-in. They must render the `DoOnce(Release) { Release(bIsLeft) }`
/// path they trigger, not an empty body and not the wrong content. The
/// assertion checks the full shape, the tracker is otherwise fooled by a
/// non-empty-but-wrong body.
#[test]
fn finding2_released_events_show_release_doonce() {
    let emit = decoder_test_emit();
    for (event, call) in [
        ("OnLeftReleased", "Release(true)"),
        ("OnRightReleased", "Release(false)"),
    ] {
        let body = function_body(emit, event);
        assert!(
            body.contains("DoOnce(Release)") && body.contains(call),
            "finding 2: {}() should render `DoOnce(Release) {{ {} }}` (the shared \
             Release path it drives via fan-in), got:\n{}",
            event,
            call,
            body
        );
    }
}

/// Finding 3: a plain two-pin Sequence emits a third, unlabeled `PrintString`
/// duplicating pin 0's content. `Seq_TwoPin` should have exactly two calls.
#[test]
fn finding3_seq_twopin_no_trailing_duplicate() {
    let emit = decoder_test_emit();
    let calls = function_body(emit, "Seq_TwoPin")
        .matches("PrintString(")
        .count();
    assert_eq!(
        calls, 2,
        "EXPECTED-FAIL (finding 3): Seq_TwoPin emits {} PrintString calls, should \
         be 2 (then0 -> A, then1 -> B). A trailing copy of pin 0's call is being \
         duplicated after the sequence.",
        calls
    );
}

/// Finding 4 (RESOLVED): a 4-pin Sequence with pin 2 disconnected preserves
/// faithful editor pin numbering. The disconnected pin emits an explicit
/// `// sequence [2] (empty):` header with no body, and the wired pin 3 stays
/// `// sequence [3]:`. Faithful numbering comes from emit-time EdGraph
/// then-pin correlation (no IR change); see `emit_sequence` in
/// `bytecode/emit/summary.rs`.
#[test]
fn finding4_seq_withemptypin_faithful_numbering() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Seq_WithEmptyPin");
    assert!(
        body.contains("// sequence [2] (empty):"),
        "Seq_WithEmptyPin should render the disconnected pin 2 as an empty slot \
         `// sequence [2] (empty):`.\nbody:\n{}",
        body
    );
    assert!(
        body.contains("// sequence [3]:"),
        "Seq_WithEmptyPin should keep the disconnected pin 2's slot so the wired \
         pin 3 stays `// sequence [3]:`.\nbody:\n{}",
        body
    );
}

/// Cross-event convergence: each `Conv_*` scenario is a pair of CustomEvents
/// (`_A`/`_B`) whose exec outputs both wire into one shared node. The compiler
/// emits that body once under the partition owner (`_A`) and reaches it from
/// `_B` via a cross-event jump, so the decoder must inline the shared body under
/// BOTH; the non-owner `_B` is the case that used to render empty (general
/// inliner in `decode/cross_event_inline.rs`). Divergent-tail is a separate
/// boundary, tracked below.
#[test]
fn conv_shared_body_inlined_under_non_owner() {
    let emit = decoder_test_emit();
    // (non-owner event, substrings the inlined shared body must contain)
    let cases: &[(&str, &[&str])] = &[
        ("Conv_DirectDoOnce_B", &["DoOnce(", "\"Conv direct\""]),
        ("Conv_SharedCall_B", &["\"Shared call\""]),
        ("Conv_SharedSequence_B", &["\"Seq 0\"", "\"Seq 1\""]),
        (
            "Conv_SharedFlipFlop_B",
            &["FlipFlop(", "\"Flip\"", "\"Flop\""],
        ),
    ];
    for (event, required) in cases {
        let body = function_body(emit, event);
        for needle in *required {
            assert!(
                body.contains(needle),
                "cross-event inline: {event} should inline the shared body it converges \
                 on (missing `{needle}`); the non-owner event renders empty.\nbody:\n{body}"
            );
        }
    }
}

/// Divergent-downstream boundary (RESOLVED): `Conv_DivergentTail_{A,B}` are
/// per-event Sequences whose then-0 converges on a shared `Print("Shared mid")`
/// and whose then-1 diverges. The non-owner `_B` must render the shared then-0
/// plus its OWN then-1 (`Shared mid`, `B tail`), wrapped in the same two-pin
/// Sequence as the owner, and must NOT bleed the owner's `A tail`. No bytecode
/// push chain exists for `_B`, so that wrapper is graph-identity synthesis.
#[test]
fn conv_divergenttail_b_renders_shared_then_own_tail() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Conv_DivergentTail_B");
    assert!(
        body.contains("\"Shared mid\"")
            && body.contains("\"B tail\"")
            && !body.contains("\"A tail\""),
        "divergent-tail boundary: Conv_DivergentTail_B should render the \
         shared then-0 `Print(\"Shared mid\")` and its OWN then-1 `Print(\"B tail\")`, and must \
         NOT bleed the owner's `Print(\"A tail\")`.\nbody:\n{}",
        body
    );
    // The non-owner must mirror the owner's two-pin Sequence rendering: the
    // shared then-0 and own then-1 are wrapped in a synthesized `Stmt::Sequence`
    // (no bytecode push chain exists for the non-owner, so this is graph-identity
    // synthesis). Locks in the wrapper, not just the content.
    assert!(
        body.contains("// sequence [0]:") && body.contains("// sequence [1]:"),
        "divergent-tail boundary: Conv_DivergentTail_B should wrap its shared then-0 and own \
         then-1 in a two-pin Sequence (`// sequence [0]:` / `// sequence [1]:`) to match the \
         owner `Conv_DivergentTail_A`.\nbody:\n{}",
        body
    );
}

/// Finding G1: a plain single-body loop's body bytes are re-decoded by the
/// function-root disk-order sweep and surface as spurious sibling statements
/// after the loop (`try_decode_loop` only claimed body bytes for nested/
/// dual-role dispatched loops). `Loop_ForEachInt`/`Loop_ForEachItemName` leak a
/// trailing `$Array_Get_Item = <array>[0]` plus its Print; `Loop_ForSimple`
/// leaks a third `PrintString` (body + Done + spurious); `Loop_While` leaks a
/// second copy of its sole increment after `// completed:`.
#[test]
fn g1_no_trailing_loop_body_redecode() {
    let emit = decoder_test_emit();

    let foreach_int = function_body(emit, "Loop_ForEachInt");
    assert!(
        !foreach_int.contains("self.IntArray[0]"),
        "EXPECTED-FAIL (finding G1): Loop_ForEachInt re-decodes its loop body \
         and leaks a trailing `$Array_Get_Item = self.IntArray[0]` after the \
         `for`.\nbody:\n{}",
        foreach_int
    );

    let foreach_name = function_body(emit, "Loop_ForEachItemName");
    assert!(
        !foreach_name.contains("GrabbedActors[0]"),
        "EXPECTED-FAIL (finding G1): Loop_ForEachItemName re-decodes its loop \
         body and leaks a trailing `$Array_Get_Item = GrabbedActors[0]` after \
         the `for`.\nbody:\n{}",
        foreach_name
    );

    let for_simple = function_body(emit, "Loop_ForSimple");
    let for_simple_prints = for_simple.matches("PrintString(").count();
    assert_eq!(
        for_simple_prints, 2,
        "EXPECTED-FAIL (finding G1): Loop_ForSimple has {} PrintString calls, \
         should be 2 (body + Done). The loop body re-decode leaks a third copy \
         of the body Print after `// completed:`.\nbody:\n{}",
        for_simple_prints, for_simple
    );

    let loop_while = function_body(emit, "Loop_While");
    let loop_while_increments = loop_while
        .matches("LoopCounter = (LoopCounter + 1)")
        .count();
    assert_eq!(
        loop_while_increments, 1,
        "EXPECTED-FAIL (finding G1): Loop_While has {} `LoopCounter = (LoopCounter + 1)` \
         lines, should be 1 (the body increment only). The loop body re-decode \
         leaks a second copy after `// completed:`.\nbody:\n{}",
        loop_while_increments, loop_while
    );
}

/// Finding G2: a ForEach-promoted loop leaks its canonical head condition
/// (`$Less_IntInt = (0 < Array_Length(array))`) as a sibling line before the
/// `for (item in array)`. For a real for-loop that line is the head cond; for
/// a ForEach (`*cond = None`) it has no editor-graph counterpart and must be
/// dropped. Only the `$BooleanAND` form of `Loop_ForEachWithBreak` (an `And`,
/// finding G3) is excluded. The inner loop of `Loop_ForEachNested` leaks the
/// same line (the outer index-`for` is the G4 documented limit and stays).
#[test]
fn g2_foreach_no_leading_bound_expr() {
    let emit = decoder_test_emit();
    for name in [
        "Loop_ForEachInt",
        "Loop_ForEachItemName",
        "Loop_ForEachNested",
    ] {
        let body = function_body(emit, name);
        assert!(
            !body.contains("$Less_IntInt"),
            "EXPECTED-FAIL (finding G2): {}() leaks the loop's canonical head \
             condition `$Less_IntInt = (0 < Array_Length(...))` as a sibling \
             before the ForEach `for`; it has no editor-graph counterpart and \
             should be dropped.\nbody:\n{}",
            name,
            body
        );
    }
}

/// Finding G5: `Loop_While` is a counter-driven WHILE loop whose body is just
/// the counter increment (`LoopCounter = LoopCounter + 1`). The refiner
/// misclassifies it as a ForC, hoisting that sole statement into the for-header
/// increment slot and EMPTYING the body. A counter loop with no other body IS a
/// while, the editor shows no separate increment node. It must render as
/// `while (LoopCounter < 5) { LoopCounter = (LoopCounter + 1) }`, not an
/// empty-body `for`.
///
/// The trailing duplicate increment after `// completed:` is the separate
/// finding G1 (loop-body re-decode), covered by
/// `g1_no_trailing_loop_body_redecode`; this tracker is scoped to the
/// while/ForC classification only.
#[test]
fn g5_loop_while_not_emptied_forc() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_While");
    assert!(
        body.contains("while (") && !body.contains("for ("),
        "EXPECTED-FAIL (finding G5): Loop_While should render as a `while` loop, \
         not be misclassified as an empty-body `for`.\nbody:\n{}",
        body
    );
    // The increment is the loop body, not a hoisted for-header slot: it must
    // appear inside the while body (which must therefore be non-empty).
    assert!(
        body.contains("LoopCounter = (LoopCounter + 1)"),
        "EXPECTED-FAIL (finding G5): Loop_While's body should contain the counter \
         increment `LoopCounter = (LoopCounter + 1)`; the ForC misclassification \
         drains it into the for-header and empties the body.\nbody:\n{}",
        body
    );
}

/// Finding G4: `Loop_ForEachNested`'s OUTER loop iterates `self.OverlappingActors`
/// but never reads the element, so the Blueprint compiler emits no array-element
/// fetch. The refiner sees `counter < Array_Length(self.OverlappingActors)` plus a
/// matching increment but no fetch, so it falls back to an index-`for`
/// (`for (i = 0 to Array_Length(self.OverlappingActors) - 1)`). The editor renders
/// it as `for (OverlappingActor in self.OverlappingActors)`; the unused item is
/// promoted to a ForEach with a synthesized name.
#[test]
fn g4_nested_outer_foreach() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_ForEachNested");
    assert!(
        body.contains("for (OverlappingActor in self.OverlappingActors)"),
        "EXPECTED-FAIL (finding G4): Loop_ForEachNested's outer loop should render \
         as `for (OverlappingActor in self.OverlappingActors)` (unused-item \
         ForEach), not an index-`for`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("for (i = 0 to"),
        "EXPECTED-FAIL (finding G4): Loop_ForEachNested's outer loop should not \
         render as an index-`for`.\nbody:\n{}",
        body
    );
}

/// Return the substring of `body` that sits inside the first loop construct: the
/// indented block opened by the first line containing `for (` or `while (`,
/// up to (but not including) the loop's `// completed:` marker or the first
/// line dedented back to the loop-header indent. Used by the G3 trackers to
/// assert the break/else live INSIDE the loop rather than ejected after it.
fn first_loop_inner(body: &str) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let header_idx = lines
        .iter()
        .position(|line| line.contains("for (") || line.contains("while ("))
        .unwrap_or_else(|| panic!("no loop header in body:\n{}", body));
    let header_indent = lines[header_idx].len() - lines[header_idx].trim_start().len();
    let mut inner = Vec::new();
    for line in &lines[header_idx + 1..] {
        if line.trim().is_empty() {
            inner.push(*line);
            continue;
        }
        let indent = line.len() - line.trim_start().len();
        // The loop body is strictly more indented than the header; the
        // closing `}` sits at the header indent and ends the block.
        if indent <= header_indent {
            break;
        }
        inner.push(*line);
    }
    inner.join("\n")
}

/// Finding G3 (ForEach): `Loop_ForEachWithBreak` is a `for (item in array)`
/// whose body is a break if/else (`if (item > 5) { break } else { Print(...) }`).
/// The displaced break-body has TWO `EX_POP_EXECUTION_FLOW` (one per arm) but
/// `scan_for_displaced_terminator` stops at the FIRST, truncating the if/else:
/// the true-arm break is dropped (empty `if`), and the false-arm Print is ejected
/// past the loop as a `if (!(...))` post-loop guard. The break and the false-arm
/// Print must both live INSIDE the loop, with no post-loop guard.
///
/// Scoped to break/else recovery; the loop shape (`for`-vs-`while`) is the
/// separate ForLoopWithBreak classification gap and is out of scope here.
#[test]
fn g3_foreach_with_break_recovers_break_else() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_ForEachWithBreak");
    let inner = first_loop_inner(&body);

    assert!(
        inner.contains("break"),
        "EXPECTED-FAIL (finding G3): Loop_ForEachWithBreak's loop body should \
         contain a `break` (the true-arm of the `if (item > 5)` break-test); the \
         displaced two-pop truncation drops it, leaving an empty `if`.\nbody:\n{}",
        body
    );
    assert!(
        inner.contains("PrintString("),
        "EXPECTED-FAIL (finding G3): Loop_ForEachWithBreak's false-arm \
         `PrintString(...)` should render INSIDE the loop as the else; the \
         truncation ejects it past the loop.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("if (!("),
        "EXPECTED-FAIL (finding G3): Loop_ForEachWithBreak should have NO post-loop \
         `if (!(...))` guard; the false-arm Print belongs inside the loop, not \
         ejected after it.\nbody:\n{}",
        body
    );
    // The break-flag head-cond scaffolding leak (`$BooleanAND = (Not_PreBool(false)
    // && (counter < Array_Length(...)))`) is asserted separately by
    // `g7_foreach_with_break_drops_head_cond_leak`; G3 covers only break/else
    // recovery.
}

/// Finding G7: `Loop_ForEachWithBreak` leaks the break-flag-ANDed head cond
/// (`$BooleanAND = (Not_PreBool(false) && (0 < Array_Length(self.IntArray)))`)
/// as a dead sibling before the `for`. It is the ForEach-with-break macro's
/// trampoline bound check, scaffolding with no editor-graph counterpart, and
/// the loop already renders its own `for (item in array)` bound. Extends the
/// G2 `is_foreach_bound_expr_leak` drop to the `$BooleanAND` And-wrapped form
/// (via `match_foreach_cond` peeling the break-flag negation), with a transitive
/// `$`-temp sweep so the chain the leak fed doesn't surface.
#[test]
fn g7_foreach_with_break_drops_head_cond_leak() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_ForEachWithBreak");

    assert!(
        !body.contains("$BooleanAND"),
        "EXPECTED-FAIL (finding G7): Loop_ForEachWithBreak should NOT leak the \
         `$BooleanAND` break-flag head cond before the loop; it is dead scaffolding \
         and the `for (item in ...)` already carries the bound.\nbody:\n{}",
        body
    );
    // Guard against the assertion passing on a regressed/empty body: the G3
    // for-loop + break must still be present.
    assert!(
        body.contains("for (item in self.IntArray)") && body.contains("break"),
        "G7 guard: Loop_ForEachWithBreak must still render the G3 \
         `for (item in self.IntArray)` with a `break`.\nbody:\n{}",
        body
    );
}

/// Finding G3 (ForC/While): `Loop_ForWithBreak`'s body is a break if/else
/// (`if (Temp_int_Variable == 5) { break } else { Print(IntToString(...)) }`).
/// Same two-pop truncation as the ForEach case: the break is dropped and the
/// false-arm Print is ejected as a post-loop `if (!(...))` guard. Recover the
/// break and false-arm inside the loop, with no post-loop guard.
///
/// The `while`-vs-`for (i=0 to 9)` rendering is the separate ForLoopWithBreak
/// classification gap, now resolved by finding G8
/// (`g8_for_with_break_renders_for`): the loop renders `for (Temp_int_Variable
/// = 0 to 9)` rather than the `while` v1 still emits.
#[test]
fn g3_for_with_break_recovers_break_else() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_ForWithBreak");
    let inner = first_loop_inner(&body);

    assert!(
        inner.contains("break"),
        "EXPECTED-FAIL (finding G3): Loop_ForWithBreak's loop body should contain \
         a `break` (the true-arm of the `if (Temp_int_Variable == 5)` break-test); \
         the displaced two-pop truncation drops it.\nbody:\n{}",
        body
    );
    assert!(
        inner.contains("IntToString(Temp_int_Variable)"),
        "EXPECTED-FAIL (finding G3): Loop_ForWithBreak's false-arm \
         `PrintString(IntToString(Temp_int_Variable))` should render INSIDE the \
         loop as the else; the truncation ejects it past the loop.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("if (!("),
        "EXPECTED-FAIL (finding G3): Loop_ForWithBreak should have NO post-loop \
         `if (!(...))` guard; the false-arm Print belongs inside the loop.\nbody:\n{}",
        body
    );
}

/// Finding G8: `Loop_ForWithBreak` (ForLoopWithBreak macro, First=0 Last=9) must
/// render `for (Temp_int_Variable = 0 to 9)`, not the `while` v1 emits. The macro
/// compiles to a while with head cond `(!break_flag && counter <= 9)` and the
/// increment buried in a trailing `if (!break_flag) { ++ }` guard; `refine_loops`
/// recognizes this, recovers the increment, promotes to ForC, and drops the dead
/// break-flag scaffolding. (G3 covers the break/else body.)
#[test]
fn g8_for_with_break_renders_for() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Loop_ForWithBreak");
    let inner = first_loop_inner(&body);

    assert!(
        body.contains("for (Temp_int_Variable = 0 to 9)"),
        "finding G8: Loop_ForWithBreak should render `for (Temp_int_Variable = 0 \
         to 9)`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("while ("),
        "finding G8: Loop_ForWithBreak should have NO `while (` header; the \
         ForLoopWithBreak must promote to a `for`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("if (Not_PreBool("),
        "finding G8: Loop_ForWithBreak should have NO empty break-flag \
         increment-if (`if (Not_PreBool(...)) {{ }}`); the increment is folded \
         into the for-step.\nbody:\n{}",
        body
    );
    // G3 break + false-arm Print must still live INSIDE the loop.
    assert!(
        inner.contains("break"),
        "G8 guard: Loop_ForWithBreak's loop body must still contain the G3 \
         `break`.\nbody:\n{}",
        body
    );
    assert!(
        inner.contains("IntToString(Temp_int_Variable)"),
        "G8 guard: Loop_ForWithBreak's loop body must still contain the G3 \
         false-arm `PrintString(IntToString(Temp_int_Variable))`.\nbody:\n{}",
        body
    );
}

/// Finding L1: `Latch_DoOnceInForEach` is a ForEach over `IntArray` whose loop
/// body is a `DoOnce` wrapping a `Print` of the array element. The DoOnce gate
/// inside the body defeats loop refinement: the ForEach is never recognized, so
/// v2 falls back to a raw counter `while` with an EMPTY body, leaks the loop
/// counter init/increment as siblings, and hoists `DoOnce(...) { Print(...) }`
/// OUT of the loop with a hardcoded `self.IntArray[0]` element fetch. It must
/// render `for (item in self.IntArray) { DoOnce(...) { Print(IntToString(item)) } }`.
#[test]
fn l1_latch_doonce_in_foreach_keeps_loop() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Latch_DoOnceInForEach");

    assert!(
        body.contains("for (item in self.IntArray)"),
        "EXPECTED-FAIL (finding L1): Latch_DoOnceInForEach should render \
         `for (item in self.IntArray)`; the in-body DoOnce defeats ForEach \
         refinement and it falls back to a raw counter `while`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("while ("),
        "EXPECTED-FAIL (finding L1): Latch_DoOnceInForEach should have NO `while (` \
         header; the ForEach must be recognized despite the in-body DoOnce.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("self.IntArray[0]"),
        "EXPECTED-FAIL (finding L1): Latch_DoOnceInForEach hoists the loop body out \
         of the loop with a hardcoded `self.IntArray[0]` fetch; the element read \
         belongs inside the loop as `IntToString(item)`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("Temp_int_Loop_Counter_Variable"),
        "EXPECTED-FAIL (finding L1): Latch_DoOnceInForEach leaks the ForEach \
         scaffolding counter (`Temp_int_Loop_Counter_Variable` init/increment) as \
         siblings; a recognized ForEach carries its own bound.\nbody:\n{}",
        body
    );
    // The DoOnce body must survive INSIDE the loop, not just be dropped.
    let inner = first_loop_inner(&body);
    assert!(
        inner.contains("DoOnce(") && inner.contains("IntToString(item)"),
        "EXPECTED-FAIL (finding L1): Latch_DoOnceInForEach's loop body should keep \
         its `DoOnce(...) {{ Print(IntToString(item)) }}` INSIDE the loop.\nbody:\n{}",
        body
    );
}

/// Finding L2: `Latch_DoOnce` is a SINGLE DoOnce wrapping `Print("Once")`, reset
/// later in the same body, followed by `Print("Reset done")`. v2 mis-resolves
/// the reset's gate name to the downstream `PrintString` call
/// (`ResetDoOnce(PrintString)`) and synthesizes a SPURIOUS second
/// `DoOnce(PrintString) { Print("Reset done") }`. There is only one DoOnce node:
/// the reset must name the same gate as the wrapping DoOnce, and `"Reset done"`
/// must not be wrapped in a phantom second latch.
#[test]
fn l2_latch_doonce_single_gate_no_phantom() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "Latch_DoOnce");

    // Sanity: the body content must survive.
    assert!(
        body.contains("\"Once\"") && body.contains("\"Reset done\""),
        "L2 guard: Latch_DoOnce must still render both `Print(\"Once\")` and \
         `Print(\"Reset done\")`.\nbody:\n{}",
        body
    );
    assert!(
        !body.contains("(PrintString)"),
        "EXPECTED-FAIL (finding L2): Latch_DoOnce names a latch gate `PrintString` \
         (`ResetDoOnce(PrintString)` / `DoOnce(PrintString)`); the gate should be \
         the DoOnce node, never the downstream call.\nbody:\n{}",
        body
    );
    // Exactly one DoOnce gate opens a block; the reset is the only `ResetDoOnce`.
    // `matches("DoOnce(")` counts both `DoOnce(` and the suffix of `ResetDoOnce(`,
    // so subtracting the reset count yields the real wrapping-DoOnce count.
    let doonce_blocks = body.matches("DoOnce(").count() - body.matches("ResetDoOnce(").count();
    assert_eq!(
        doonce_blocks, 1,
        "EXPECTED-FAIL (finding L2): Latch_DoOnce should open exactly ONE DoOnce \
         block (got {}); the second `DoOnce(PrintString)` wrapping \"Reset done\" \
         is a phantom latch and must not be synthesized.\nbody:\n{}",
        doonce_blocks, body
    );
}

/// Finding L3: `OnLeftAxis`'s else branch must emit exactly ONE
/// `ResetDoOnce(Attempt)` (then `DoOnce(Release) { Release(true) }`), matching the
/// editor graph and the mirror `OnRightAxis`. The re-wired explicit Sequence in
/// the else re-triggers the B3b sibling-arm duplicate-decode: v2 emits
/// `ResetDoOnce(Attempt)` TWICE. Scoped to the duplicate (the unambiguous spec
/// violation); the then-arm ordering and the call-graph attribution drop are
/// tracked in the investigation, not pinned here. SENSITIVE: shares machinery
/// with the GripLeft/GripRight real fixtures — guard the 9-fixture gate on fix.
#[test]
fn l3_onleftaxis_else_single_attempt_reset() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "OnLeftAxis");
    let resets = body.matches("ResetDoOnce(Attempt)").count();
    assert_eq!(
        resets, 1,
        "EXPECTED-FAIL (finding L3): OnLeftAxis emits {} `ResetDoOnce(Attempt)` in \
         its else; should be exactly 1. The re-wired else Sequence re-triggers the \
         B3b sibling-arm duplicate-decode.\nbody:\n{}",
        resets, body
    );
}

/// Finding L4: `OnLeftAxis` calls `Attempt(true)` and `Release(true)` in its
/// body but is absent from the call graph (and from `Attempt`/`Release`'s
/// `// called by:` attributions). The re-export's new OnLeftAxis structure (else
/// Sequence + within-event Knot fan-in from OnLeftReleased) trips the call-graph
/// builder's ownership traversal; the pre-ingest baseline listed it. It must
/// reappear as `OnLeftAxis → Attempt, Release` with OnLeftAxis back in both
/// callees' `called by:` lines.
#[test]
fn l4_onleftaxis_in_call_graph() {
    let emit = decoder_test_emit();
    let has_onleftaxis_edge = emit.lines().any(|line| {
        let trimmed = line.trim_start();
        trimmed.starts_with("OnLeftAxis ")
            && line.contains('→')
            && line.contains("Attempt")
            && line.contains("Release")
    });
    assert!(
        has_onleftaxis_edge,
        "EXPECTED-FAIL (finding L4): OnLeftAxis is missing from the call graph; it \
         calls Attempt(true) and Release(true) and must be listed \
         `OnLeftAxis → Attempt, Release`.\n{}",
        emit
    );
    // Guard against a degenerate call graph passing the edge check: the mirror
    // OnRightAxis edge must remain, and both callees must name OnLeftAxis.
    assert!(
        emit.contains("OnRightAxis →"),
        "L4 guard: the call graph must still list the mirror OnRightAxis edge.\n{}",
        emit
    );
    // Both callees (Attempt and Release) must name OnLeftAxis in their
    // `// called by:` line, so at least two such lines mention it.
    let called_by_left = emit
        .lines()
        .filter(|line| {
            line.trim_start().starts_with("// called by:") && line.contains("OnLeftAxis")
        })
        .count();
    assert!(
        called_by_left >= 2,
        "EXPECTED-FAIL (finding L4): only {} `// called by:` line(s) name OnLeftAxis; \
         both Attempt and Release should attribute the call to OnLeftAxis.\n{}",
        called_by_left,
        emit
    );
}

/// Finding L5: `OnLeftAxis`'s then-arm (the `DoOnce(Attempt)` block) must order
/// `Attempt(true)` BEFORE the post-Attempt `ResetDoOnce(Release)` re-arm,
/// matching the editor graph and the mirror `OnRightAxis` (`Attempt(false)` then
/// `ResetDoOnce(Release)`). The two events are mirrors and must render the
/// then-arm identically; the within-event Knot fan-in scrambles OnLeftAxis's
/// statement order so v2 emits the reset first (`ResetDoOnce(Release)` then
/// `Attempt(true)`).
#[test]
fn l5_onleftaxis_thenarm_attempt_before_release_reset() {
    let emit = decoder_test_emit();
    let body = function_body(emit, "OnLeftAxis");
    let (attempt_pos, reset_pos) = match (
        body.find("Attempt(true)"),
        body.find("ResetDoOnce(Release)"),
    ) {
        (Some(attempt), Some(reset)) => (attempt, reset),
        _ => panic!(
            "L5 guard: OnLeftAxis must contain both `Attempt(true)` and \
             `ResetDoOnce(Release)` in its then-arm.\nbody:\n{}",
            body
        ),
    };
    assert!(
        attempt_pos < reset_pos,
        "EXPECTED-FAIL (finding L5): OnLeftAxis's then-arm emits \
         `ResetDoOnce(Release)` before `Attempt(true)`; the editor order is \
         `Attempt(true)` then the post-Attempt `ResetDoOnce(Release)` re-arm \
         (matching the mirror OnRightAxis).\nbody:\n{}",
        body
    );
    // Sanity: the mirror OnRightAxis already renders the correct order, guarding
    // against a fix that reverses both events instead of just OnLeftAxis.
    let right = function_body(emit, "OnRightAxis");
    let right_ordered = match (
        right.find("Attempt(false)"),
        right.find("ResetDoOnce(Release)"),
    ) {
        (Some(attempt), Some(reset)) => attempt < reset,
        _ => false,
    };
    assert!(
        right_ordered,
        "L5 sanity: OnRightAxis should order `Attempt(false)` before its \
         `ResetDoOnce(Release)`.\nbody:\n{}",
        right
    );
}
