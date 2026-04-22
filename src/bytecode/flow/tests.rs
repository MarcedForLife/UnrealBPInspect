// Inline tests: these test private flow pattern parsers (parse_push_flow, parse_jump, etc.)
// that aren't accessible from tests/.

use super::parsers::{
    parse_if_jump, parse_jump, parse_jump_computed, parse_pop_flow_if_not, parse_push_flow,
};

#[test]
fn push_flow_valid() {
    assert_eq!(parse_push_flow("push_flow 0x1A2B"), Some(0x1A2B));
}

#[test]
fn push_flow_invalid() {
    assert_eq!(parse_push_flow("something else"), None);
}

#[test]
fn jump_valid() {
    assert_eq!(parse_jump("jump 0xFF"), Some(0xFF));
}

#[test]
fn jump_invalid() {
    assert_eq!(parse_jump("not a jump"), None);
}

#[test]
fn if_jump_valid() {
    assert_eq!(
        parse_if_jump("if !(cond) jump 0x100"),
        Some(("cond", 0x100))
    );
}

#[test]
fn if_jump_invalid() {
    assert_eq!(parse_if_jump("if (cond) jump 0x100"), None);
}

#[test]
fn pop_flow_if_not_valid() {
    assert_eq!(parse_pop_flow_if_not("pop_flow_if_not(cond)"), Some("cond"));
}

#[test]
fn pop_flow_if_not_invalid() {
    assert_eq!(parse_pop_flow_if_not("something else"), None);
}

#[test]
fn jump_computed_true() {
    assert!(parse_jump_computed("jump_computed(expr)"));
}

#[test]
fn jump_computed_false() {
    assert!(!parse_jump_computed("jump 0x100"));
}
