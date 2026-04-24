//! Push/pop balance helpers over pre-classified `BcStatement`s.

use super::super::decode::{BcStatement, StmtKind};

/// Net push_flow/pop_flow depth change across `stmts[start..end)`. 0 when balanced.
pub fn flow_depth(stmts: &[BcStatement], start: usize, end: usize) -> i32 {
    let mut balance: i32 = 0;
    for stmt in &stmts[start..end] {
        if stmt.push_flow_target().is_some() {
            balance += 1;
        } else if stmt.kind == StmtKind::PopFlow {
            balance -= 1;
        }
    }
    balance
}

/// Find the first `pop_flow` at nesting depth 0 in `stmts[start..end)`.
pub fn find_first_unmatched_pop(stmts: &[BcStatement], start: usize, end: usize) -> Option<usize> {
    let mut depth: i32 = 0;
    for (idx, stmt) in stmts.iter().enumerate().take(end).skip(start) {
        if stmt.push_flow_target().is_some() {
            depth += 1;
        } else if stmt.kind == StmtKind::PopFlow {
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
        if stmt.push_flow_target().is_some() {
            depth += 1;
        } else if stmt.kind == StmtKind::PopFlow {
            if depth > 0 {
                depth -= 1;
            } else {
                last = Some(idx);
            }
        }
    }
    last
}
