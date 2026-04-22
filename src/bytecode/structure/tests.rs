use super::super::decode::BcStatement;
use super::build::build_region_tree;
use super::postprocess::{convert_gotos_to_breaks, strip_dead_backward_gotos};
use super::region::{IfBlock, RegionKind};
use super::{apply_indentation, negate_cond, structure_bytecode};
use std::collections::{HashMap, HashSet};

#[test]
fn negate_simple_not() {
    assert_eq!(negate_cond("!X"), "X");
}

#[test]
fn negate_parenthesized_not() {
    assert_eq!(negate_cond("!(A && B)"), "A && B");
}

#[test]
fn negate_simple_var() {
    assert_eq!(negate_cond("X"), "!X");
}

#[test]
fn negate_compound() {
    assert_eq!(negate_cond("A && B"), "!(A && B)");
}

#[test]
fn negate_self_member() {
    assert_eq!(negate_cond("!self.GrippingActor"), "self.GrippingActor");
}

#[test]
fn strip_dead_goto_removes_post_latch_trampoline() {
    // Pattern produced by UberGraph linearization when a DoOnce body
    // sits at a lower offset than the gate check. The backward goto
    // to the DoOnce header is dead after the body has already run.
    let mut lines = vec![
        "if (cond) {".to_string(),
        "    stuff()".to_string(),
        "}".to_string(),
        "L_0050:".to_string(),
        "DoOnce(Foo) {".to_string(),
        "    call()".to_string(),
        "}".to_string(),
        "goto L_0050".to_string(),
        "return".to_string(),
    ];
    strip_dead_backward_gotos(&mut lines);
    // Both the label and the goto are gone; the latch body stays.
    assert!(!lines.iter().any(|l| l.trim() == "L_0050:"));
    assert!(!lines.iter().any(|l| l.trim() == "goto L_0050"));
    assert!(lines.iter().any(|l| l.trim() == "DoOnce(Foo) {"));
}

#[test]
fn strip_dead_goto_keeps_loop_backward_jumps() {
    // Plain backward gotos that form real loops must survive; this
    // pass is limited to post-latch trampolines.
    let mut lines = vec![
        "L_0020:".to_string(),
        "i = i + 1".to_string(),
        "if (i < 10) {".to_string(),
        "    continue()".to_string(),
        "}".to_string(),
        "goto L_0020".to_string(),
    ];
    let before = lines.clone();
    strip_dead_backward_gotos(&mut lines);
    assert_eq!(lines, before);
}

#[test]
fn strip_dead_goto_ignores_forward_gotos() {
    // Forward gotos are handled by `extract_convergence`.
    let mut lines = vec![
        "goto L_0050".to_string(),
        "other_stuff()".to_string(),
        "L_0050:".to_string(),
        "DoOnce(Foo) {".to_string(),
        "    call()".to_string(),
        "}".to_string(),
    ];
    let before = lines.clone();
    strip_dead_backward_gotos(&mut lines);
    assert_eq!(lines, before);
}

fn make_stmt(offset: usize, text: &str) -> BcStatement {
    BcStatement::new(offset, text.to_string())
}

#[test]
fn simple_if_block() {
    // if !(cond) jump 0x30 -> negated to "if (cond) {"
    // body
    // return nop
    let stmts = vec![
        make_stmt(0x10, "if !(Cond) jump 0x30"),
        make_stmt(0x20, "DoSomething()"),
        make_stmt(0x30, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    assert!(result.iter().any(|l| l.contains("if (Cond) {")));
    assert!(result.iter().any(|l| l.contains("DoSomething()")));
}

#[test]
fn simple_if_else() {
    // if !(cond) jump 0x30
    // TrueBranch()
    // jump 0x40          (unconditional jump to end)
    // FalseBranch()
    // return nop
    let stmts = vec![
        make_stmt(0x10, "if !(Cond) jump 0x30"),
        make_stmt(0x20, "TrueBranch()"),
        make_stmt(0x28, "jump 0x40"),
        make_stmt(0x30, "FalseBranch()"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("if (Cond) {"));
    assert!(text.contains("TrueBranch()"));
    assert!(text.contains("} else {"));
    assert!(text.contains("FalseBranch()"));
}

#[test]
fn if_else_with_return_terminated_true_body() {
    // if !(cond) jump 0x30
    // TrueBranch()
    // return nop          (true body returns instead of jumping)
    // FalseBranch()       (at jump target)
    // return nop
    let stmts = vec![
        make_stmt(0x10, "if !(Cond) jump 0x30"),
        make_stmt(0x20, "TrueBranch()"),
        make_stmt(0x28, "return nop"),
        make_stmt(0x30, "FalseBranch()"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("if (Cond) {"), "missing if: {}", text);
    assert!(text.contains("TrueBranch()"), "missing true: {}", text);
    assert!(text.contains("} else {"), "missing else: {}", text);
    assert!(text.contains("FalseBranch()"), "missing false: {}", text);
}

#[test]
fn nested_if_blocks() {
    // if !(A) jump 0x50
    //   if !(B) jump 0x40
    //     InnerBody()
    //   OuterAfterInner()
    // return nop
    let stmts = vec![
        make_stmt(0x10, "if !(A) jump 0x50"),
        make_stmt(0x18, "if !(B) jump 0x40"),
        make_stmt(0x20, "InnerBody()"),
        make_stmt(0x40, "OuterAfterInner()"),
        make_stmt(0x50, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("if (A) {"));
    assert!(text.contains("if (B) {"));
    assert!(text.contains("InnerBody()"));
    assert!(text.contains("OuterAfterInner()"));
}

#[test]
fn overlapping_blocks_demoted_to_guard() {
    // Two if-blocks that partially overlap should not crash.
    // The overlapping one becomes a guard.
    let stmts = vec![
        make_stmt(0x10, "if !(A) jump 0x40"),
        make_stmt(0x18, "if !(B) jump 0x50"),
        make_stmt(0x20, "Body()"),
        make_stmt(0x40, "AfterA()"),
        make_stmt(0x50, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    // Should not panic and should produce output
    assert!(!result.is_empty());
}

#[test]
fn if_else_if_chain() {
    // if !(A) jump 0x30
    // TrueA()
    // jump 0x50
    // if !(B) jump 0x50
    // TrueB()
    // return nop
    let stmts = vec![
        make_stmt(0x10, "if !(A) jump 0x30"),
        make_stmt(0x20, "TrueA()"),
        make_stmt(0x28, "jump 0x50"),
        make_stmt(0x30, "if !(B) jump 0x50"),
        make_stmt(0x40, "TrueB()"),
        make_stmt(0x50, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("if (A) {"));
    assert!(text.contains("} else if (B) {"));
    assert!(text.contains("TrueB()"));
}

#[test]
fn region_tree_simple_if() {
    let mut skip = HashSet::new();
    let blocks = vec![IfBlock {
        if_idx: 0,
        cond: "X".to_string(),
        target_idx: 3,
        jump_idx: None,
        end_idx: None,
        else_close_idx: None,
    }];
    let tree = build_region_tree(5, &blocks, &mut skip);
    assert_eq!(tree.children.len(), 1);
    assert!(matches!(tree.children[0].kind, RegionKind::IfThen(_)));
    assert_eq!(tree.children[0].start, 1);
    assert_eq!(tree.children[0].end, 3);
    assert!(skip.contains(&0));
}

#[test]
fn region_tree_if_else() {
    let mut skip = HashSet::new();
    let blocks = vec![IfBlock {
        if_idx: 0,
        cond: "X".to_string(),
        target_idx: 3,
        jump_idx: Some(2),
        end_idx: Some(5),
        else_close_idx: None,
    }];
    let tree = build_region_tree(6, &blocks, &mut skip);
    assert_eq!(tree.children.len(), 2);
    assert!(matches!(tree.children[0].kind, RegionKind::IfThen(_)));
    assert!(matches!(tree.children[1].kind, RegionKind::Else));
    assert_eq!(tree.children[0].start, 1);
    assert_eq!(tree.children[0].end, 3); // includes jump_idx (skipped during emit)
    assert_eq!(tree.children[1].start, 3);
    assert_eq!(tree.children[1].end, 5);
    assert!(skip.contains(&0));
    assert!(skip.contains(&2));
}

#[test]
fn region_tree_nested() {
    let mut skip = HashSet::new();
    // Outer: if at 0, target 5
    // Inner: if at 1, target 3
    let blocks = vec![
        IfBlock {
            if_idx: 0,
            cond: "A".to_string(),
            target_idx: 5,
            jump_idx: None,
            end_idx: None,
            else_close_idx: None,
        },
        IfBlock {
            if_idx: 1,
            cond: "B".to_string(),
            target_idx: 3,
            jump_idx: None,
            end_idx: None,
            else_close_idx: None,
        },
    ];
    let tree = build_region_tree(6, &blocks, &mut skip);
    assert_eq!(tree.children.len(), 1); // outer IfThen
    assert_eq!(tree.children[0].children.len(), 1); // inner IfThen
}

#[test]
fn if_then_else_followed_by_if_then() {
    // Pattern from OnActorGripped: if/else followed by a second if (no else).
    // structure_bytecode produces flat output; verify brace structure.
    let stmts = vec![
        make_stmt(0x10, "if !(LeftHand) jump 0x30"),
        make_stmt(0x20, "self.Left = GrippedActor"),
        make_stmt(0x28, "jump 0x40"),
        make_stmt(0x30, "self.Right = GrippedActor"),
        make_stmt(0x40, "if !(GrippedActor.IsClimbable) jump 0x60"),
        make_stmt(0x50, "UpdateClimbing(LeftHand)"),
        make_stmt(0x60, "OnGripped(GrippedActor)"),
        make_stmt(0x70, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(
        text.contains("if (LeftHand) {"),
        "missing first if:\n{}",
        text
    );
    assert!(
        text.contains("if (GrippedActor.IsClimbable) {"),
        "missing second if:\n{}",
        text
    );
    // apply_indentation produces correct indent when called at the pipeline end
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    let itext = indented.join("\n");
    assert!(
        itext.contains("    UpdateClimbing(LeftHand)"),
        "IsClimbable body not indented after apply_indentation:\n{}",
        itext
    );
}

#[test]
fn while_loop_body_indented() {
    let stmts = vec![
        make_stmt(0x10, "while (Cond) {"),
        make_stmt(0x20, "Body()"),
        make_stmt(0x30, "}"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    assert!(
        result.iter().any(|l| l == "while (Cond) {"),
        "missing while"
    );
    assert!(result.iter().any(|l| l == "Body()"), "missing body");
    // Verify indentation works
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    assert!(
        indented.iter().any(|l| l == "    Body()"),
        "body not indented:\n{}",
        indented.join("\n")
    );
}

#[test]
fn if_inside_while_indented() {
    let stmts = vec![
        make_stmt(0x10, "while (LoopCond) {"),
        make_stmt(0x18, "if !(X) jump 0x30"),
        make_stmt(0x20, "IfBody()"),
        make_stmt(0x30, "AfterIf()"),
        make_stmt(0x38, "}"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    // Flat output has correct braces
    assert!(result.iter().any(|l| l == "while (LoopCond) {"));
    assert!(result.iter().any(|l| l == "if (X) {"));
    // After indentation: double-nested
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    let itext = indented.join("\n");
    assert!(
        itext.contains("        IfBody()"),
        "if body not double-indented:\n{}",
        itext
    );
    assert!(
        itext.contains("    AfterIf()"),
        "after-if not single-indented:\n{}",
        itext
    );
}

#[test]
fn nested_while_loops() {
    let stmts = vec![
        make_stmt(0x10, "while (Outer) {"),
        make_stmt(0x18, "while (Inner) {"),
        make_stmt(0x20, "Body()"),
        make_stmt(0x28, "}"),
        make_stmt(0x30, "}"),
        make_stmt(0x38, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    let text = indented.join("\n");
    assert!(
        text.contains("        Body()"),
        "body not double-indented:\n{}",
        text
    );
    assert!(
        text.contains("    while (Inner) {"),
        "inner while not indented:\n{}",
        text
    );
}

#[test]
fn apply_indentation_else_if_chain() {
    let mut lines = vec![
        "if (A) {".to_string(),
        "BodyA()".to_string(),
        "} else if (B) {".to_string(),
        "BodyB()".to_string(),
        "} else {".to_string(),
        "BodyC()".to_string(),
        "}".to_string(),
    ];
    apply_indentation(&mut lines);
    assert_eq!(lines[0], "if (A) {");
    assert_eq!(lines[1], "    BodyA()");
    assert_eq!(lines[2], "} else if (B) {");
    assert_eq!(lines[3], "    BodyB()");
    assert_eq!(lines[4], "} else {");
    assert_eq!(lines[5], "    BodyC()");
    assert_eq!(lines[6], "}");
}

#[test]
fn apply_indentation_depth_zero_no_prefix() {
    let mut lines = vec!["TopLevel()".to_string(), "return".to_string()];
    apply_indentation(&mut lines);
    assert_eq!(lines[0], "TopLevel()");
    assert_eq!(lines[1], "return");
}

#[test]
fn rewrite_gotos_detects_loop_via_braces() {
    // goto inside a while loop should become break
    let mut output = vec![
        "while (Cond) {".to_string(),
        "if (X) {".to_string(),
        "goto L_0050".to_string(),
        "}".to_string(),
        "}".to_string(),
        "L_0050:".to_string(),
    ];
    convert_gotos_to_breaks(&mut output);
    assert!(
        output.iter().any(|l| l == "break"),
        "goto not converted to break:\n{}",
        output.join("\n")
    );
}

#[test]
fn rewrite_gotos_outside_loop_removes() {
    // goto outside any loop should be removed
    let mut output = vec![
        "if (X) {".to_string(),
        "goto L_0050".to_string(),
        "}".to_string(),
        "L_0050:".to_string(),
    ];
    convert_gotos_to_breaks(&mut output);
    assert!(
        !output.iter().any(|l| l.contains("goto")),
        "goto not removed:\n{}",
        output.join("\n")
    );
}

#[test]
fn guard_wraps_remaining_scope() {
    // pop_flow_if_not(X) should wrap all subsequent code in if (X) { ... }
    let stmts = vec![
        make_stmt(0x10, "pop_flow_if_not(IsValid)"),
        make_stmt(0x20, "DoA()"),
        make_stmt(0x30, "DoB()"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(
        text.contains("if (IsValid) {"),
        "missing wrapping if:\n{}",
        text
    );
    assert!(text.contains("DoA()"), "missing body A:\n{}", text);
    assert!(text.contains("DoB()"), "missing body B:\n{}", text);
}

#[test]
fn consecutive_guards_nest() {
    // Two consecutive guards should produce nested if blocks
    let stmts = vec![
        make_stmt(0x10, "pop_flow_if_not(A)"),
        make_stmt(0x20, "pop_flow_if_not(B)"),
        make_stmt(0x30, "Body()"),
        make_stmt(0x40, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    let text = indented.join("\n");
    assert!(text.contains("if (A) {"), "missing outer if:\n{}", text);
    assert!(
        text.contains("    if (B) {"),
        "missing nested if:\n{}",
        text
    );
    assert!(
        text.contains("        Body()"),
        "body not double-indented:\n{}",
        text
    );
}

#[test]
fn guard_wraps_child_if_block() {
    // Guard followed by an if/else block: the guard should wrap both
    let stmts = vec![
        make_stmt(0x10, "pop_flow_if_not(Valid)"),
        make_stmt(0x20, "if !(X) jump 0x40"),
        make_stmt(0x30, "TrueBranch()"),
        make_stmt(0x40, "FalseBranch()"),
        make_stmt(0x50, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let mut indented = result.clone();
    apply_indentation(&mut indented);
    let text = indented.join("\n");
    assert!(text.contains("if (Valid) {"), "missing guard if:\n{}", text);
    assert!(
        text.contains("    if (X) {"),
        "child if not inside guard:\n{}",
        text
    );
}

#[test]
fn guard_at_end_of_scope_suppressed() {
    // Guard as the very last statement (nothing after it to wrap)
    // should be suppressed rather than appearing as raw bytecode
    let stmts = vec![
        make_stmt(0x10, "if !(Outer) jump 0x30"),
        make_stmt(0x18, "DoWork()"),
        make_stmt(0x20, "pop_flow_if_not(Cond)"),
        make_stmt(0x30, "return nop"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("DoWork()"), "missing body:\n{}", text);
    assert!(
        !text.contains("pop_flow_if_not"),
        "raw guard leaked:\n{}",
        text
    );
}

#[test]
fn pop_flow_terminates_true_branch_with_else() {
    // Pattern: if !(cond) jump TARGET; true_body; pop_flow; TARGET: false_body; pop_flow
    let stmts = vec![
        make_stmt(0x10, "if !($IsValid) jump 0x40"),
        make_stmt(0x20, "SpawnSound()"),
        make_stmt(0x30, "pop_flow"),
        make_stmt(0x40, "PrintString(\"no sound\")"),
        make_stmt(0x50, "pop_flow"),
        make_stmt(0x60, "AfterBlock()"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(text.contains("} else {"), "missing else:\n{}", text);
    assert!(
        text.contains("SpawnSound()"),
        "missing true body:\n{}",
        text
    );
    assert!(
        text.contains("PrintString(\"no sound\")"),
        "missing false body:\n{}",
        text
    );
}

#[test]
fn nested_push_pop_not_treated_as_else_terminator() {
    // push_flow/pop_flow pair inside true body is balanced, not an exit
    let stmts = vec![
        make_stmt(0x10, "if !(Cond) jump 0x60"),
        make_stmt(0x20, "push_flow 0x40"),
        make_stmt(0x28, "DoWork()"),
        make_stmt(0x30, "pop_flow"),
        make_stmt(0x40, "AfterPush()"),
        make_stmt(0x50, "pop_flow"),
        make_stmt(0x60, "FalseBody()"),
    ];
    let result = structure_bytecode(&stmts, &HashMap::new());
    let text = result.join("\n");
    assert!(
        text.contains("AfterPush()"),
        "push/pop body lost:\n{}",
        text
    );
}
