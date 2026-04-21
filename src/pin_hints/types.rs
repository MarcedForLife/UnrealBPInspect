//! Core data types for pin-aware branch hints.

use std::collections::{BTreeMap, BTreeSet};

/// Which side of a `K2Node_IfThenElse` a pin connects to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchSide {
    Then,
    Else,
}

/// Callees observed on each side of a single Branch node.
#[derive(Debug, Clone)]
pub struct BranchInfo {
    /// 1-based export index of the `K2Node_IfThenElse` node.
    pub branch_export_idx: usize,
    /// Callee function names reachable through the Then-pin subgraph.
    pub then_callees: BTreeSet<String>,
    /// Callee function names reachable through the Else-pin subgraph.
    pub else_callees: BTreeSet<String>,
}

impl BranchInfo {
    /// Callees reachable via Then but not via Else. Disambiguates which
    /// side owns each callee when the downstream flow converges at common
    /// nodes, which causes `then_callees` and `else_callees` to overlap.
    pub fn then_only_callees(&self) -> BTreeSet<String> {
        self.then_callees
            .difference(&self.else_callees)
            .cloned()
            .collect()
    }

    /// Callees reachable via Else but not via Then.
    pub fn else_only_callees(&self) -> BTreeSet<String> {
        self.else_callees
            .difference(&self.then_callees)
            .cloned()
            .collect()
    }
}

/// Branch hints grouped by containing event or function identifier.
#[derive(Debug, Clone, Default)]
pub struct BranchHints {
    /// Keyed by event stub name (e.g. `CustomFunctionName` for input events)
    /// or, for regular functions, by the enclosing Function export's
    /// `object_name`.
    pub by_function: BTreeMap<String, Vec<BranchInfo>>,
}
