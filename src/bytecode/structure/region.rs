use super::super::decode::BcStatement;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub(super) enum RegionKind {
    Root,
    IfThen(String),
    Else,
    ElseIf(String),
    Loop(String),
}

#[derive(Debug, Clone)]
pub(super) struct Region {
    pub(super) kind: RegionKind,
    /// Statement-index range `[start, end)`.
    pub(super) start: usize,
    pub(super) end: usize,
    /// Non-overlapping children contained in `[start, end)`.
    pub(super) children: Vec<Region>,
}

impl Region {
    pub(super) fn new(kind: RegionKind, start: usize, end: usize) -> Self {
        Region {
            kind,
            start,
            end,
            children: Vec::new(),
        }
    }
}

pub(super) struct IfBlock {
    /// Index of the `if !(cond) jump` statement.
    pub(super) if_idx: usize,
    pub(super) cond: String,
    /// Where the false branch starts.
    pub(super) target_idx: usize,
    /// Unconditional jump at the end of the true branch. `None` if no else.
    pub(super) jump_idx: Option<usize>,
    /// Where both branches converge.
    pub(super) end_idx: Option<usize>,
    /// First statement after the else's early-exit jump, used to stop the
    /// else from engulfing subsequent code in nested patterns.
    pub(super) else_close_idx: Option<usize>,
}

/// Block kind used to disambiguate `pop_flow` as `break` vs `return`.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum BlockType {
    If,
    Loop,
}

pub(super) fn in_loop(stack: &[BlockType]) -> bool {
    stack.iter().rev().any(|b| *b == BlockType::Loop)
}

/// Shared context for `emit_stmts_range` / `emit_region_tree`.
pub(super) struct EmitCtx<'a> {
    pub(super) stmts: &'a [BcStatement],
    pub(super) skip: &'a HashSet<usize>,
    pub(super) label_targets: &'a HashMap<usize, String>,
    pub(super) pending_labels: &'a HashMap<usize, String>,
    pub(super) label_at: &'a HashMap<usize, &'a String>,
    pub(super) is_ubergraph: bool,
    pub(super) find_target_idx_or_end: &'a dyn Fn(usize) -> Option<usize>,
}

/// Move `parent`'s children that fall within `new_region` into `new_region`.
pub(super) fn adopt_children(parent: &mut Region, mut new_region: Region) -> Region {
    let mut adopted = Vec::new();
    let mut kept = Vec::new();
    for child in parent.children.drain(..) {
        if child.start >= new_region.start && child.end <= new_region.end {
            adopted.push(child);
        } else {
            kept.push(child);
        }
    }
    parent.children = kept;
    new_region.children.extend(adopted);
    new_region
        .children
        .sort_by_key(|c| (c.start, std::cmp::Reverse(c.end)));
    new_region
}

/// Insert a child region maintaining sorted order by `start`.
pub(super) fn insert_child_sorted(parent: &mut Region, child: Region) {
    let pos = parent.children.partition_point(|c| c.start < child.start);
    parent.children.insert(pos, child);
}
