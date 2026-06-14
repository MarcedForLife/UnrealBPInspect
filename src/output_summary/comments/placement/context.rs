//! Per-asset lookups the classifier consults, plus the node/entry helpers that
//! read pin geometry to find a box's execution boundary.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::stmt::Stmt;
use crate::types::{EdGraphPin, ParsedAsset};

use super::super::CommentModel;

/// Per-asset lookups the classifier consults, built once.
pub(super) struct ClassifyContext<'a> {
    pub(super) decoded: &'a DecodedAsset,
    /// `event_node_export_index -> event_name`, for the EventWrapping check.
    pub(super) event_node_to_name: BTreeMap<usize, String>,
    /// `export_index -> (x, y)` node geometry, for entry ordering.
    node_positions: BTreeMap<usize, (i32, i32)>,
    /// Identifiable-node count per graph page, the coverage-rule denominator.
    page_node_totals: BTreeMap<String, usize>,
    /// Pin data is read here to find a box's execution entry point.
    pub(super) parsed: &'a ParsedAsset,
}

impl<'a> ClassifyContext<'a> {
    pub(super) fn new(
        decoded: &'a DecodedAsset,
        parsed: &'a ParsedAsset,
        export_names: &[String],
        model: &CommentModel,
    ) -> Self {
        let event_node_to_name = build_event_node_to_name(parsed, export_names);
        let mut node_positions: BTreeMap<usize, (i32, i32)> = BTreeMap::new();
        let mut page_node_totals: BTreeMap<String, usize> = BTreeMap::new();
        for node in &model.nodes {
            node_positions
                .entry(node.export_index)
                .or_insert((node.x, node.y));
            if let Some(page) = &node.graph_page {
                *page_node_totals.entry(page.clone()).or_insert(0) += 1;
            }
        }
        ClassifyContext {
            decoded,
            event_node_to_name,
            node_positions,
            page_node_totals,
            parsed,
        }
    }

    /// `(x, y)` of `node` from the model geometry, defaulting to `(0, 0)`.
    pub(super) fn node_position(&self, node: usize) -> (i32, i32) {
        self.node_positions.get(&node).copied().unwrap_or((0, 0))
    }

    /// Number of identifiable nodes on `page`, the coverage-rule denominator.
    pub(super) fn page_node_total(&self, page: &str) -> usize {
        self.page_node_totals.get(page).copied().unwrap_or(0)
    }

    /// Body slice for `block`, searching events first then functions.
    pub(super) fn body_for_block(&self, block: &str) -> Option<&[Stmt]> {
        if let Some(event) = self.decoded.events.iter().find(|event| event.name == block) {
            return Some(&event.body);
        }
        self.decoded
            .functions
            .iter()
            .find(|func| func.name == block)
            .map(|func| func.body.as_slice())
    }

    /// Byte map covering `block`: the ubergraph map for an event page, the
    /// function's own map for a standalone-function page. `None` when no map
    /// covers the block (then inline placements cannot anchor and are dropped).
    pub(super) fn byte_map_for_block(
        &self,
        block: &str,
    ) -> Option<&crate::bytecode::k2node_byte_map::K2NodeByteMap> {
        if self.decoded.events.iter().any(|event| event.name == block) {
            return self.decoded.byte_maps.ubergraph.as_ref();
        }
        self.decoded.byte_maps.functions.get(block)
    }
}

/// The box's execution entry points: contained nodes whose input exec pin
/// links to a node outside the contained set. Ordered by `(y, x)` then export
/// index, top-to-bottom as drawn in the editor.
pub(super) fn sorted_exec_entries(contained: &[usize], context: &ClassifyContext) -> Vec<usize> {
    let contained_set: BTreeSet<usize> = contained.iter().copied().collect();
    let mut entries: Vec<(i32, i32, usize)> = contained
        .iter()
        .copied()
        .filter(|&node| node_has_external_exec_input(node, &contained_set, context.parsed))
        .map(|node| {
            let (x, y) = context.node_position(node);
            (y, x, node)
        })
        .collect();
    entries.sort_unstable();
    entries.into_iter().map(|(_, _, node)| node).collect()
}

/// The top-left execution entry point of the box, if any.
pub(super) fn exec_entry_point(contained: &[usize], context: &ClassifyContext) -> Option<usize> {
    sorted_exec_entries(contained, context).into_iter().next()
}

/// Whether `node` is an execution-root: it drives exec flow (has at least one
/// exec-output pin) and is itself a source (no exec-input pin carries an
/// incoming link). This is the structural shape of a graph's entry, the
/// `K2Node_FunctionEntry` of a function page or the event-entry node of an
/// event page, without needing the node's class. A box that spans a whole
/// graph contains such a root; a dense box that merely crosses the coverage
/// threshold without reaching the root does not.
fn node_is_exec_root(node: usize, parsed: &ParsedAsset) -> bool {
    let Some(pin_data) = parsed.pin_data.get(&node) else {
        return false;
    };
    let drives_exec = pin_data.pins.iter().any(EdGraphPin::is_exec_output);
    let has_incoming_exec = pin_data
        .pins
        .iter()
        .filter(|pin| pin.is_exec_input())
        .any(|pin| !pin.linked_to.is_empty());
    drives_exec && !has_incoming_exec
}

/// Whether the box covers the page's execution-entry: at least one contained
/// node is an exec-root (see [`node_is_exec_root`]). The structural half of the
/// function-level promotion rule, paired with the coverage threshold.
pub(super) fn box_contains_exec_root(contained: &[usize], parsed: &ParsedAsset) -> bool {
    contained
        .iter()
        .any(|&node| node_is_exec_root(node, parsed))
}

/// Whether `node`'s input exec pin is wired from a node outside `contained`.
pub(super) fn node_has_external_exec_input(
    node: usize,
    contained: &BTreeSet<usize>,
    parsed: &ParsedAsset,
) -> bool {
    let Some(pin_data) = parsed.pin_data.get(&node) else {
        return false;
    };
    pin_data
        .pins
        .iter()
        .filter(|pin| pin.is_exec_input())
        .flat_map(|pin| pin.linked_to.iter())
        .any(|link| !contained.contains(&link.node))
}

/// Map each event-entry node export index to its event name, by inverting the
/// canonical decode-side derivation (`decode::build_event_node_index`), which
/// also covers `K2Node_InputAction` nodes (their event names follow the
/// `InpActEvt_{action}_...` function-export pattern, not a node property).
///
/// A single node can serve several compiled events (one InputAction node
/// backs both the Pressed and Released functions); name-ascending iteration
/// keeps the lexicographically first, matching the EventWrapping
/// first-contained-event tie-break.
fn build_event_node_to_name(
    parsed: &ParsedAsset,
    export_names: &[String],
) -> BTreeMap<usize, String> {
    let mut map = BTreeMap::new();
    for (name, node) in crate::bytecode::decode::build_event_node_index(parsed, export_names) {
        map.entry(node).or_insert(name);
    }
    map
}
