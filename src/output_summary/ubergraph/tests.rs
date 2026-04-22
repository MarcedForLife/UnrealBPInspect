use crate::bytecode::pipeline::resolve_cross_segment_jumps;
use crate::bytecode::transforms::strip_orphaned_blocks;
use crate::bytecode::BcStatement;

use super::linearize::collapse_jump_chains;

fn stmt(offset: usize, text: &str) -> BcStatement {
    BcStatement::new(offset, text.to_string())
}

#[test]
fn cross_segment_jump_past_end_not_rewritten() {
    // jump 0x2000 is past max offset (120) -> find_target_idx_or_end resolves
    // this as jump-to-end, so resolve_cross_segment_jumps leaves it alone
    let mut stmts = vec![
        stmt(100, "some_call()"),
        stmt(110, "jump 0x2000"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[1].text, "jump 0x2000"); // unchanged, past-end is resolvable
                                              // Sentinel still appended
    assert_eq!(stmts.last().unwrap().text, "return nop");
    assert_eq!(stmts.last().unwrap().mem_offset, 121);
}

#[test]
fn unresolvable_jump_rewritten() {
    // jump 0x50 (=80) is before the segment start and >4 bytes from any
    // statement -> find_target_idx would return None -> rewritten to sentinel
    let mut stmts = vec![
        stmt(100, "some_call()"),
        stmt(110, "jump 0x50"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[1].text, "jump 0x79"); // rewritten to sentinel (121)
}

#[test]
fn unresolvable_conditional_jump_rewritten() {
    // if !(cond) jump 0x50, target not resolvable -> rewritten
    let mut stmts = vec![
        stmt(100, "if !(IsValid(X)) jump 0x50"),
        stmt(110, "DoThing()"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[0].text, "if !(IsValid(X)) jump 0x79");
}

#[test]
fn local_jump_preserved() {
    // jump 0x78 (=120) is within the segment -> preserved
    let mut stmts = vec![
        stmt(100, "some_call()"),
        stmt(110, "jump 0x78"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[1].text, "jump 0x78"); // unchanged
}

#[test]
fn local_fuzzy_jump_preserved() {
    // jump 0x75 (=117) is within +/-4 of offset 120 -> preserved as local
    let mut stmts = vec![
        stmt(100, "some_call()"),
        stmt(110, "jump 0x75"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[1].text, "jump 0x75"); // unchanged, fuzzy match
}

#[test]
fn fuzzy_jump_beyond_4_bytes_rewritten() {
    // jump 0x73 (=115) is 5 bytes from offset 120, outside +/-4 window
    // and >4 from offset 110 too -> unresolvable -> rewritten
    let mut stmts = vec![
        stmt(100, "some_call()"),
        stmt(110, "jump 0x73"),
        stmt(120, "return nop"),
    ];
    resolve_cross_segment_jumps(&mut stmts);
    assert_eq!(stmts[1].text, "jump 0x79"); // rewritten, outside +/-4
}

#[test]
fn strip_orphaned_empty_if() {
    let mut lines = vec![
        "if (cond) {".to_string(),
        "}".to_string(),
        "DoThing()".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(lines, vec!["DoThing()"]);
}

#[test]
fn strip_orphaned_empty_if_else() {
    // An `if (cond) { } else { body }` pattern with an empty then-branch
    // should become `if (!cond) { body }`, preserving the guard rather
    // than unconditionally emitting the else body.
    let mut lines = vec![
        "if (cond) {".to_string(),
        "} else {".to_string(),
        "    DoThing()".to_string(),
        "}".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(
        lines,
        vec![
            "if (!cond) {".to_string(),
            "    DoThing()".to_string(),
            "}".to_string(),
        ]
    );
}

#[test]
fn strip_orphaned_else_empty() {
    let mut lines = vec![
        "    DoThing()".to_string(),
        "} else {".to_string(),
        "}".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(lines, vec!["    DoThing()"]);
}

#[test]
fn strip_goto_label_at_end() {
    // goto L_01fa where label is at end of output (convergence to end).
    // The trailing `}` is balanced (closes the if-block) and preserved.
    let mut lines = vec![
        "if (cast(X)) {".to_string(),
        "    iface(X).CanConsume(Y)".to_string(),
        "    L_01fa:".to_string(),
        "}".to_string(),
        "goto L_01fa".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(
        lines,
        vec![
            "if (cast(X)) {".to_string(),
            "    iface(X).CanConsume(Y)".to_string(),
            "}".to_string(),
        ]
    );
}

#[test]
fn strip_backward_goto_to_start() {
    // backward goto to label at start of segment (Sequence artifact)
    let mut lines = vec![
        "L_0c3e:".to_string(),
        "AttemptGrip(true)".to_string(),
        "goto L_0c3e".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(lines, vec!["AttemptGrip(true)"]);
}

#[test]
fn strip_goto_fall_through() {
    // goto immediately before its label with only } between (fall-through)
    // The } is structural (closes an if-block) and stays
    let mut lines = vec![
        "DoThing()".to_string(),
        "goto L_0100".to_string(),
        "}".to_string(),
        "L_0100:".to_string(),
        "DoOther()".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(
        lines,
        vec![
            "DoThing()".to_string(),
            "}".to_string(),
            "DoOther()".to_string(),
        ]
    );
}

#[test]
fn preserve_multi_ref_goto() {
    // Labels with 2+ gotos are preserved (handled by extract_convergence)
    let mut lines = vec![
        "goto L_0100".to_string(),
        "L_0100:".to_string(),
        "DoThing()".to_string(),
        "goto L_0100".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert!(lines.iter().any(|l| l.contains("L_0100")));
}

#[test]
fn strip_bare_temp_expression() {
    let mut lines = vec![
        "$InputActionEvent_Key_4".to_string(),
        "self.EnableDebugHandRotation = true".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert_eq!(lines, vec!["self.EnableDebugHandRotation = true"]);
}

#[test]
fn strip_bare_boolean_literal() {
    let mut lines = vec!["false".to_string()];
    strip_orphaned_blocks(&mut lines);
    assert!(lines.is_empty());
}

#[test]
fn keep_indented_bare_expression() {
    // Inside a block, bare expressions should be preserved
    let mut lines = vec![
        "if (cond) {".to_string(),
        "    $SomeVar".to_string(),
        "}".to_string(),
    ];
    strip_orphaned_blocks(&mut lines);
    assert!(lines.iter().any(|l| l.contains("$SomeVar")));
}

#[test]
fn collapse_preserves_non_trampoline_backward_jump() {
    // Backward jump that the chain-walk cannot collapse (target is a real
    // statement, not another bare jump) must survive collapse_jump_chains.
    // The predecessor is a plain call (not a flow terminator) and nothing
    // else references the jump's offset, so the only thing keeping it alive
    // is the elided_offsets invariant: offsets absent from that set are
    // never stripped.
    let mut stmts = vec![
        stmt(0x10, "loop_body_call()"),
        stmt(0x20, "another_call()"),
        stmt(0x30, "jump 0x10"),
        stmt(0x40, "tail_call()"),
    ];
    collapse_jump_chains(&mut stmts);
    let has_backward_jump = stmts.iter().any(|s| s.text.trim() == "jump 0x10");
    assert!(
        has_backward_jump,
        "backward jump not in elided_offsets must survive collapse_jump_chains; got {:?}",
        stmts.iter().map(|s| s.text.clone()).collect::<Vec<_>>()
    );
}
