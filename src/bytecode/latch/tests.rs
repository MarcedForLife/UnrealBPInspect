use super::super::decode::BcStatement;
use super::doonce::detect_init_blocks;
use super::flipflop::detect_flipflop_toggle;
use super::transform_latch_patterns;

fn stmt(offset: usize, text: &str) -> BcStatement {
    BcStatement::new(offset, text.to_string())
}

#[test]
fn detect_init_block_start_open() {
    let stmts = vec![
        stmt(0x00e4, "Temp_bool_Has_Been_Initd_Variable = true"),
        stmt(0x00f0, "pop_flow_if_not(false)"),
        stmt(0x0104, "Temp_bool_IsClosed_Variable_2 = true"),
        stmt(0x0110, "pop_flow"),
        stmt(0x0113, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0xf1"),
        stmt(0x0122, "pop_flow"),
    ];
    let blocks = detect_init_blocks(&stmts);
    assert_eq!(blocks.len(), 1);
    assert_eq!(blocks[0].init_var, "Temp_bool_Has_Been_Initd_Variable");
    assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable_2");
}

#[test]
fn detect_init_block_start_closed() {
    let stmts = vec![
        stmt(0x0289, "Temp_bool_Has_Been_Initd_Variable_1 = true"),
        stmt(0x0297, "pop_flow_if_not(true)"),
        stmt(0x029b, "Temp_bool_IsClosed_Variable = true"),
        stmt(0x02a7, "pop_flow"),
        stmt(
            0x02aa,
            "if !(Temp_bool_Has_Been_Initd_Variable_1) jump 0x288",
        ),
        stmt(0x02b9, "pop_flow"),
    ];
    let blocks = detect_init_blocks(&stmts);
    assert_eq!(blocks.len(), 1);
    assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable");
}

#[test]
fn detect_init_block_forward_layout() {
    // Layout B: init body AFTER the if-check (forward jump)
    let stmts = vec![
        stmt(
            0x0b0e,
            "if !(Temp_bool_Has_Been_Initd_Variable_5) jump 0xb1e",
        ),
        stmt(0x0b1d, "pop_flow"),
        stmt(0x0b1f, "Temp_bool_Has_Been_Initd_Variable_5 = true"),
        stmt(0x0b2d, "pop_flow_if_not(false)"),
        stmt(0x0b31, "Temp_bool_IsClosed_Variable_5 = true"),
        stmt(0x0b3d, "pop_flow"),
    ];
    let blocks = detect_init_blocks(&stmts);
    assert_eq!(blocks.len(), 1, "Should detect forward-layout init block");
    assert_eq!(blocks[0].init_var, "Temp_bool_Has_Been_Initd_Variable_5");
    assert_eq!(blocks[0].gate_var, "Temp_bool_IsClosed_Variable_5");
}

#[test]
fn gate_resets_found() {
    let stmts = [
        stmt(0x063d, "Temp_bool_IsClosed_Variable_2 = false"),
        stmt(0x0649, "jump 0xe3"),
    ];
    let reset_pattern = format!("{} = false", "Temp_bool_IsClosed_Variable_2");
    let resets: Vec<usize> = stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| s.text.trim() == reset_pattern)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(resets.len(), 1);
    assert_eq!(resets[0], 0);
}

#[test]
fn detect_flipflop_toggle_pattern() {
    let stmts = vec![
        stmt(0x05ed, "$Not_PreBool = !Temp_bool_Variable"),
        stmt(0x060b, "Temp_bool_Variable = $Not_PreBool"),
        stmt(0x061f, "jump 0x5ce"),
        stmt(0x05d0, "if !(Temp_bool_Variable) jump 0x5e6"),
    ];
    let toggles = detect_flipflop_toggle(&stmts);
    assert_eq!(toggles.len(), 1);
    assert_eq!(toggles[0].0, "Temp_bool_Variable");
}

#[test]
fn simple_doonce_transform() {
    let mut stmts = vec![
        // Init block
        stmt(0x10, "Temp_bool_Has_Been_Initd_Variable = true"),
        stmt(0x20, "pop_flow_if_not(false)"),
        stmt(0x30, "Temp_bool_IsClosed_Variable = true"),
        stmt(0x40, "pop_flow"),
        // Init check
        stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0x11"),
        stmt(0x60, "pop_flow"),
        // Gate check
        stmt(0x70, "if !(Temp_bool_IsClosed_Variable) jump 0x90"),
        stmt(0x80, "pop_flow"),
        // Gate close (before body)
        stmt(0x84, "Temp_bool_IsClosed_Variable = true"),
        // Body
        stmt(0x85, "MyFunction(42)"),
        // Body end
        stmt(0x90, "pop_flow"),
    ];
    transform_latch_patterns(&mut stmts, None);

    let texts: Vec<&str> = stmts.iter().map(|s| s.text.trim()).collect();
    assert!(
        texts.contains(&"DoOnce(MyFunction) {"),
        "Expected DoOnce header, got: {:?}",
        texts
    );
    assert!(
        texts.contains(&"MyFunction(42)"),
        "Expected body preserved, got: {:?}",
        texts
    );
    assert!(
        !texts.iter().any(|t| t.contains("Has_Been_Initd")),
        "Init statements should be removed, got: {:?}",
        texts
    );
    assert!(
        !texts.iter().any(|t| t.contains("IsClosed")),
        "Gate close should be removed, got: {:?}",
        texts
    );
    // Body-end pop_flow replaced directly with `}`
    assert!(
        texts.contains(&"}"),
        "Body-end should be closing brace, got: {:?}",
        texts
    );
    assert!(
        !texts.contains(&"pop_flow"),
        "No pop_flow should remain, got: {:?}",
        texts
    );
}

#[test]
fn interleaved_doonce_bodies_kept_separate() {
    // Two DoOnce instances whose bodies sit next to each other at low
    // offsets, with both gate checks at higher offsets jumping backward.
    // This mirrors the UberGraph InputAxis_GripLeftAxis layout where each
    // branch of an outer if-else contains its own DoOnce and UE emits the
    // bodies interleaved before the gate scaffolding.
    //
    // Each gate's body_path walk must stop at body-end and not pull in
    // the adjacent gate's body. When the walk tangles, statements get
    // relocated under the wrong DoOnce header, duplicating bodies and
    // destroying the outer if-else boundary.
    let mut stmts = vec![
        // Init block A
        stmt(0x00, "Temp_bool_Has_Been_Initd_Variable_A = true"),
        stmt(0x04, "pop_flow_if_not(false)"),
        stmt(0x08, "Temp_bool_IsClosed_Variable_A = true"),
        stmt(0x0c, "pop_flow"),
        // Init block B
        stmt(0x10, "Temp_bool_Has_Been_Initd_Variable_B = true"),
        stmt(0x14, "pop_flow_if_not(false)"),
        stmt(0x18, "Temp_bool_IsClosed_Variable_B = true"),
        stmt(0x1c, "pop_flow"),
        // Interleaved bodies: action-A, action-B, pop-A, pop-B
        stmt(0x20, "ActionA()"),
        stmt(0x24, "ActionB()"),
        stmt(0x28, "pop_flow"),
        stmt(0x2c, "pop_flow"),
        // Gate A scaffolding with backward jump to body-A
        stmt(0x30, "if !(Temp_bool_Has_Been_Initd_Variable_A) jump 0x1"),
        stmt(0x34, "pop_flow"),
        stmt(0x38, "if !(Temp_bool_IsClosed_Variable_A) jump 0x50"),
        stmt(0x3c, "pop_flow"),
        stmt(0x40, "Temp_bool_IsClosed_Variable_A = true"),
        stmt(0x44, "jump 0x20"),
        // Gate B scaffolding with backward jump to body-B
        stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable_B) jump 0x11"),
        stmt(0x54, "pop_flow"),
        stmt(0x58, "if !(Temp_bool_IsClosed_Variable_B) jump 0x70"),
        stmt(0x5c, "pop_flow"),
        stmt(0x60, "Temp_bool_IsClosed_Variable_B = true"),
        stmt(0x64, "jump 0x24"),
        stmt(0x70, "pop_flow"),
    ];
    transform_latch_patterns(&mut stmts, None);

    let texts: Vec<String> = stmts.iter().map(|s| s.text.trim().to_string()).collect();

    assert!(
        texts.iter().any(|t| t == "DoOnce(ActionA) {"),
        "Missing DoOnce(ActionA) header, got: {:?}",
        texts
    );
    assert!(
        texts.iter().any(|t| t == "DoOnce(ActionB) {"),
        "Missing DoOnce(ActionB) header, got: {:?}",
        texts
    );

    let action_a_count = texts.iter().filter(|t| t.as_str() == "ActionA()").count();
    let action_b_count = texts.iter().filter(|t| t.as_str() == "ActionB()").count();
    assert_eq!(
        action_a_count, 1,
        "ActionA() appears {} times, expected 1. Output: {:?}",
        action_a_count, texts
    );
    assert_eq!(
        action_b_count, 1,
        "ActionB() appears {} times, expected 1. Output: {:?}",
        action_b_count, texts
    );
}

#[test]
fn doonce_reset_transformed() {
    let mut stmts = vec![
        // Init block
        stmt(0x10, "Temp_bool_Has_Been_Initd_Variable = true"),
        stmt(0x20, "pop_flow_if_not(false)"),
        stmt(0x30, "Temp_bool_IsClosed_Variable = true"),
        stmt(0x40, "pop_flow"),
        stmt(0x50, "if !(Temp_bool_Has_Been_Initd_Variable) jump 0x11"),
        stmt(0x60, "pop_flow"),
        // Gate check
        stmt(0x70, "if !(Temp_bool_IsClosed_Variable) jump 0x90"),
        stmt(0x80, "pop_flow"),
        stmt(0x84, "Temp_bool_IsClosed_Variable = true"),
        stmt(0x85, "DoSomething()"),
        stmt(0x90, "pop_flow"),
        // Reset somewhere else
        stmt(0xA0, "Temp_bool_IsClosed_Variable = false"),
    ];
    transform_latch_patterns(&mut stmts, None);

    let texts: Vec<&str> = stmts.iter().map(|s| s.text.trim()).collect();
    assert!(
        texts.contains(&"ResetDoOnce(DoSomething)"),
        "Expected ResetDoOnce, got: {:?}",
        texts
    );
}
