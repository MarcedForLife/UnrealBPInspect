//! Statement-text parsers (push/pop/jump/if-jump/etc.) and push/pop balance helpers.

use super::super::decode::BcStatement;
use super::super::POP_FLOW;

/// Parse "push_flow 0xHEX" -> target offset.
pub fn parse_push_flow(text: &str) -> Option<usize> {
    text.strip_prefix("push_flow 0x")
        .and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "jump 0xHEX" -> target offset.
pub fn parse_jump(text: &str) -> Option<usize> {
    text.strip_prefix("jump 0x")
        .and_then(|h| usize::from_str_radix(h, 16).ok())
}

/// Parse "if !(COND) jump 0xHEX" -> (condition, target offset).
pub fn parse_if_jump(text: &str) -> Option<(&str, usize)> {
    if !text.starts_with("if !(") {
        return None;
    }
    let jump_pos = text.rfind(") jump 0x")?;
    let cond = &text[5..jump_pos];
    let target = usize::from_str_radix(&text[jump_pos + 9..], 16).ok()?;
    Some((cond, target))
}

/// Parse "pop_flow_if_not(COND)" -> condition string.
pub fn parse_pop_flow_if_not(text: &str) -> Option<&str> {
    let inner = text.strip_prefix("pop_flow_if_not(")?;
    let cond = inner.strip_suffix(')')?;
    Some(cond)
}

/// Net push_flow/pop_flow depth change across `stmts[start..end)`. 0 when balanced.
pub fn flow_depth(stmts: &[BcStatement], start: usize, end: usize) -> i32 {
    let mut balance: i32 = 0;
    for stmt in &stmts[start..end] {
        if parse_push_flow(&stmt.text).is_some() {
            balance += 1;
        } else if stmt.text == POP_FLOW {
            balance -= 1;
        }
    }
    balance
}

/// Find the first `pop_flow` at nesting depth 0 in `stmts[start..end)`.
pub fn find_first_unmatched_pop(stmts: &[BcStatement], start: usize, end: usize) -> Option<usize> {
    let mut depth: i32 = 0;
    for (idx, stmt) in stmts.iter().enumerate().take(end).skip(start) {
        if parse_push_flow(&stmt.text).is_some() {
            depth += 1;
        } else if stmt.text == POP_FLOW {
            if depth > 0 {
                depth -= 1;
            } else {
                return Some(idx);
            }
        }
    }
    None
}

/// Find the last `pop_flow` at nesting depth 0 in `stmts[start..end)`.
pub fn find_last_unmatched_pop(stmts: &[BcStatement], start: usize, end: usize) -> Option<usize> {
    let mut depth: i32 = 0;
    let mut last: Option<usize> = None;
    for (idx, stmt) in stmts.iter().enumerate().take(end).skip(start) {
        if parse_push_flow(&stmt.text).is_some() {
            depth += 1;
        } else if stmt.text == POP_FLOW {
            if depth > 0 {
                depth -= 1;
            } else {
                last = Some(idx);
            }
        }
    }
    last
}

/// Parse "continue_if_not(COND)". Synthetic marker for pop_flow_if_not inside
/// ForEach bodies (pop means "skip to next iteration", not "break").
pub fn parse_continue_if_not(text: &str) -> Option<&str> {
    let inner = text.strip_prefix("continue_if_not(")?;
    let cond = inner.strip_suffix(')')?;
    Some(cond)
}

/// Parse "jump_computed(EXPR)" -> true if it's a computed jump.
pub fn parse_jump_computed(text: &str) -> bool {
    text.starts_with("jump_computed(")
}
