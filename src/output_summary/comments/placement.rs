//! Classify each comment box into a placement and resolve its anchor.
//!
//! Placement is decided structurally from the extracted [`CommentModel`] and
//! the decoded asset, rather than by string-matching rendered output. The
//! classifier runs each box through a first-match cascade:
//!
//! 1. `BubbleOwned`   - a bubble comment annotating the node it sits on.
//! 2. `EventWrapping` - a box that contains an event-entry node, rendered
//!    above that event's header.
//! 3. `FunctionLevel` - a box covering more than [`COVERAGE_THRESHOLD_PERCENT`]
//!    of the identifiable nodes on its graph page, promoted to a description
//!    under the block header.
//! 4. `InlineAtEntry` - a box anchored to the statement produced by its
//!    top-left contained execution node.
//! 5. Exec follow-through - when no entry point anchors (the entry is a Knot
//!    reroute or a Branch with no attributable bytes), walk exec-output links
//!    deeper into the contained set and anchor at the box's first anchorable
//!    own statement.
//! 6. Pin-follow      - when no contained node resolves directly (a bubble
//!    on a pure node, a box of pure expression nodes, or exec nodes with no
//!    byte attribution), follow data-output pin links outward and anchor to
//!    the nearest consuming statement.
//! 7. `Fallback`      - no usable anchor; dropped (and counted).
//!
//! Inline and bubble placements anchor through the byte map: contained node
//! (or the bubble's owner) -> disk byte range -> covering statement -> the
//! statement's disk offset, which the emitter keys annotations by. Event and
//! function-level placements need no byte map; they key by block name and
//! attach at the block header.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::stmt::Stmt;
use crate::types::{EdGraphPin, ParsedAsset};

use super::render::render_comment_lines;
use super::{CommentBox, CommentModel};

/// A box covering more than this percentage of a graph page's identifiable
/// nodes is promoted to a function-level description rather than anchored
/// inline. The comparison is strictly greater-than.
const COVERAGE_THRESHOLD_PERCENT: usize = 80;

/// Indent applied to an event-wrapping comment, sitting directly above the
/// `EventName():` header. One summary indent level (two spaces).
const EVENT_WRAP_INDENT: &str = "  ";

/// Indent applied to a function-level description, sitting directly below the
/// block signature at body indent (two summary levels, four spaces).
const FUNCTION_LEVEL_INDENT: &str = "    ";

/// Maximum breadth-first depth when following data-output pin links to find a
/// consuming statement. Real chains run through Knot reroute nodes and nested
/// pure-math nodes; the deepest anchor observed across the fixture corpus sits
/// at depth 5.
const PIN_FOLLOW_MAX_DEPTH: usize = 8;

/// Where a placed comment attaches and how the emitter keys it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PlacementClass {
    /// Above the `EventName():` header of `block` (the owning event).
    EventWrapping,
    /// Below the block signature, as a whole-graph description.
    FunctionLevel,
    /// Above the statement at disk offset `statement_offset` in `block`'s body.
    /// Covers both the spatial inline-entry case and bubble ownership; both
    /// resolve to a covering statement through the byte map.
    InlineAtStatement { statement_offset: usize },
}

/// One classified, rendered comment ready to interleave at emit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacedComment {
    /// Block (function or event) name the comment belongs to.
    pub block: String,
    pub class: PlacementClass,
    /// Pre-rendered marker lines (already indented for the placement class).
    pub lines: Vec<String>,
    /// Box top-left, kept for the stable multi-comment tie-break.
    pub box_x: i32,
    pub box_y: i32,
    /// Box text, the final tie-break key.
    pub text: String,
}

/// The full set of placed comments for one asset, plus the count of boxes that
/// classified as inline/bubble but could not anchor (no byte map, or no
/// covering statement). The drop count is reported, never silently swallowed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PlacementPlan {
    pub placed: Vec<PlacedComment>,
    /// Boxes that wanted a statement anchor but found none.
    pub unanchored: usize,
}

impl PlacementPlan {
    /// Count placed comments of a given class (test/inspection helper).
    pub fn count_class(&self, class: &PlacementClass) -> usize {
        self.placed
            .iter()
            .filter(|placed| std::mem::discriminant(&placed.class) == std::mem::discriminant(class))
            .count()
    }
}

/// Build the placement plan for `decoded`/`parsed` from `model`.
///
/// `export_names` is the parallel object-name vector (the same one the emit
/// prefix pass builds). The returned plan lists every comment that resolved
/// to a placement, deterministically ordered.
pub(crate) fn build_placement_plan(
    decoded: &DecodedAsset,
    parsed: &ParsedAsset,
    export_names: &[String],
    model: &CommentModel,
) -> PlacementPlan {
    let context = ClassifyContext::new(decoded, parsed, export_names, model);
    let mut plan = PlacementPlan::default();

    // Event-wrapping suppression is page-global: a box over more than the
    // group-size cap of event nodes is a layout divider, dropped outright.
    for comment in &model.boxes {
        match classify(comment, model, &context) {
            Some(Classification::Placed(placed)) => plan.placed.push(*placed),
            Some(Classification::Unanchored) => plan.unanchored += 1,
            None => {}
        }
    }

    sort_placed(&mut plan.placed);
    plan
}

/// Classification outcome for one box before it joins the plan.
enum Classification {
    Placed(Box<PlacedComment>),
    /// Inline/bubble box with no resolvable statement anchor.
    Unanchored,
}

impl Classification {
    /// Cascade combinator: keep a resolved `Placed` outcome, otherwise
    /// evaluate the next strategy. Lets a fallback chain read as an ordered
    /// list of anchoring attempts instead of repeated
    /// match-on-`Unanchored`.
    fn or_else(self, next: impl FnOnce() -> Classification) -> Classification {
        match self {
            Classification::Unanchored => next(),
            resolved => resolved,
        }
    }
}

/// Per-asset lookups the classifier consults, built once.
struct ClassifyContext<'a> {
    decoded: &'a DecodedAsset,
    /// `event_node_export_index -> event_name`, for the EventWrapping check.
    event_node_to_name: BTreeMap<usize, String>,
    /// `export_index -> (x, y)` node geometry, for entry ordering.
    node_positions: BTreeMap<usize, (i32, i32)>,
    /// Identifiable-node count per graph page, the coverage-rule denominator.
    page_node_totals: BTreeMap<String, usize>,
    /// Pin data is read here to find a box's execution entry point.
    parsed: &'a ParsedAsset,
}

impl<'a> ClassifyContext<'a> {
    fn new(
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
    fn node_position(&self, node: usize) -> (i32, i32) {
        self.node_positions.get(&node).copied().unwrap_or((0, 0))
    }

    /// Number of identifiable nodes on `page`, the coverage-rule denominator.
    fn page_node_total(&self, page: &str) -> usize {
        self.page_node_totals.get(page).copied().unwrap_or(0)
    }

    /// Body slice for `block`, searching events first then functions.
    fn body_for_block(&self, block: &str) -> Option<&[Stmt]> {
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
    fn byte_map_for_block(
        &self,
        block: &str,
    ) -> Option<&crate::bytecode::k2node_byte_map::K2NodeByteMap> {
        if self.decoded.events.iter().any(|event| event.name == block) {
            return self.decoded.byte_maps.ubergraph.as_ref();
        }
        self.decoded.byte_maps.functions.get(block)
    }
}

/// Classify one box. Returns `None` for a box with no graph page (cannot be
/// placed at all).
fn classify(
    comment: &CommentBox,
    model: &CommentModel,
    context: &ClassifyContext,
) -> Option<Classification> {
    let page = comment.graph_page.clone()?;

    // Bubble comments own one node; anchor to the owner's statement, to the
    // owner's nearest data consumer when the owner compiled to no bytes of
    // its own (a bubble on a pure node), or to the nearest downstream exec
    // statement when the owner has no data outputs either (a bubble on a
    // Branch or Knot).
    if comment.is_bubble {
        let owner = comment.owner_export?;
        return Some(
            anchor_to_node(comment, &page, owner, context)
                .or_else(|| anchor_via_pin_follow(comment, &page, &[owner], context))
                .or_else(|| anchor_via_exec_follow_outward(comment, &page, owner, context)),
        );
    }

    let contained = model.contained_nodes(comment);
    if contained.is_empty() {
        // A box with no contained nodes has nothing to annotate.
        return None;
    }

    // EventWrapping: the box contains one or more event-entry nodes. A box
    // spanning many events is a canvas region label ("Latches and delays"
    // over a cluster of events); a linear summary can't bracket the group,
    // so it anchors to the first contained event in render order and renders
    // as a plain `// "text"` marker like any other event-wrapping comment.
    let event_nodes: Vec<&String> = contained
        .iter()
        .filter_map(|node| context.event_node_to_name.get(node))
        .collect();
    if !event_nodes.is_empty() {
        // First contained event in export order wins (contained is sorted),
        // a deterministic stand-in for the box's first contained event.
        let event_name = event_nodes
            .iter()
            .min()
            .copied()
            .cloned()
            .expect("event_nodes is non-empty");
        let lines = render_comment_lines(&comment.text, EVENT_WRAP_INDENT);
        return Some(Classification::Placed(Box::new(PlacedComment {
            block: event_name,
            class: PlacementClass::EventWrapping,
            lines,
            box_x: comment.x,
            box_y: comment.y,
            text: comment.text.clone(),
        })));
    }

    // FunctionLevel: the box covers more than the coverage threshold of the
    // page's identifiable nodes.
    let page_total = context.page_node_total(&page);
    if page_total > 0 && contained.len() * 100 / page_total > COVERAGE_THRESHOLD_PERCENT {
        let lines = render_comment_lines(&comment.text, FUNCTION_LEVEL_INDENT);
        return Some(Classification::Placed(Box::new(PlacedComment {
            block: page.clone(),
            class: PlacementClass::FunctionLevel,
            lines,
            box_x: comment.x,
            box_y: comment.y,
            text: comment.text.clone(),
        })));
    }

    // InlineAtEntry: anchor to the top-left execution entry point of the box.
    let Some(entry) = exec_entry_point(&contained, context) else {
        // No exec boundary crossing: a box of pure expression nodes, or a
        // self-contained exec block. Pure expressions render inside their
        // consuming statement, so follow the data pins out before giving up.
        return Some(anchor_via_pin_follow(comment, &page, &contained, context));
    };
    // The geometric entry is the top-left exec node, but it may be a pure node
    // or a node whose member name didn't survive byte attribution. When it
    // does not resolve, fall back to the first contained exec node that does,
    // in deterministic (y, x, export) order, then to exec follow-through,
    // then to pin-following.
    match anchor_to_node(comment, &page, entry, context) {
        placed @ Classification::Placed(_) => Some(placed),
        Classification::Unanchored => {
            let placed = anchor_to_first_resolvable(comment, &page, &contained, entry, context)
                .or_else(|| anchor_via_exec_follow(comment, &page, &contained, context))
                .unwrap_or_else(|| anchor_via_pin_follow(comment, &page, &contained, context));
            Some(placed)
        }
    }
}

/// After the box's exec entry points fail to anchor, walk exec-output pin
/// links from them deeper into the contained set, breadth-first, trying each
/// reached contained node as an anchor. Returns `None` when nothing inside
/// the box anchors.
///
/// This reaches a box's real content when its entry compiles to no
/// attributable bytes of its own: a Knot reroute on the box boundary, or an
/// IfThenElse whose JumpIfNot carries no member name to match. The first
/// anchorable node in execution order is the box's first own statement.
/// Targets outside the contained set are never tried, so the anchor stays
/// inside the box. Display-only EdGraph read; enumerated in
/// `docs/edgraph-correlation-inventory.md`.
fn anchor_via_exec_follow(
    comment: &CommentBox,
    page: &str,
    contained: &[usize],
    context: &ClassifyContext,
) -> Option<Classification> {
    let contained_set: BTreeSet<usize> = contained.iter().copied().collect();
    // Seed with the entry points (already tried by the direct cascade).
    let mut visited: BTreeSet<usize> = contained
        .iter()
        .copied()
        .filter(|&node| node_has_external_exec_input(node, &contained_set, context.parsed))
        .collect();
    let mut frontier: Vec<usize> = visited.iter().copied().collect();
    while !frontier.is_empty() {
        let mut next: Vec<usize> = Vec::new();
        for &node in &frontier {
            let Some(pin_data) = context.parsed.pin_data.get(&node) else {
                continue;
            };
            for link in pin_data
                .pins
                .iter()
                .filter(|pin| pin.is_exec_output())
                .flat_map(|pin| pin.linked_to.iter())
            {
                if contained_set.contains(&link.node) && visited.insert(link.node) {
                    next.push(link.node);
                }
            }
        }
        next.sort_unstable();
        for &candidate in &next {
            if let placed @ Classification::Placed(_) =
                anchor_to_node(comment, page, candidate, context)
            {
                return Some(placed);
            }
        }
        frontier = next;
    }
    None
}

/// Last-resort anchor: follow data-output pin links outward from `start`,
/// breadth-first, anchoring to the first reached node that resolves to a
/// covering statement.
///
/// This is what places a bubble on a pure node (`VariableGet`, pure
/// `CallFunction`, math operators) or a box containing only pure nodes: a
/// pure node compiles to no bytes of its own, its expression renders inside
/// the consuming statement, so the nearest resolvable consumer is the line
/// the comment annotates (v1 reached the same line by string-matching the
/// rendered expression text). Display-only EdGraph read; enumerated in
/// `docs/edgraph-correlation-inventory.md`.
fn anchor_via_pin_follow(
    comment: &CommentBox,
    page: &str,
    start: &[usize],
    context: &ClassifyContext,
) -> Classification {
    anchor_via_link_follow(comment, page, start, context, EdGraphPin::is_data_output)
}

/// Last-resort bubble anchor: follow exec-output pin links outward from the
/// bubble's owner, breadth-first, anchoring to the first reached node that
/// resolves to a covering statement.
///
/// A bubble on an exec node with no attributable bytes of its own (a Branch
/// whose JumpIfNot carries no member name, a Knot reroute) resolves neither
/// directly nor through data pins; its nearest downstream execution
/// statement is the line the comment annotates. The outward mirror of
/// [`anchor_via_exec_follow`], without the contained-set restriction (a
/// bubble has no box), so the walk is depth-capped like pin-following.
/// Display-only EdGraph read; enumerated in
/// `docs/edgraph-correlation-inventory.md`.
fn anchor_via_exec_follow_outward(
    comment: &CommentBox,
    page: &str,
    owner: usize,
    context: &ClassifyContext,
) -> Classification {
    anchor_via_link_follow(comment, page, &[owner], context, EdGraphPin::is_exec_output)
}

/// Breadth-first walk over `follow_pin`-selected output links from `start`,
/// trying each reached node as an anchor, up to [`PIN_FOLLOW_MAX_DEPTH`].
/// Candidates at one depth are tried in export-index order, so the nearest
/// match wins deterministically.
fn anchor_via_link_follow(
    comment: &CommentBox,
    page: &str,
    start: &[usize],
    context: &ClassifyContext,
    follow_pin: fn(&EdGraphPin) -> bool,
) -> Classification {
    let mut visited: BTreeSet<usize> = start.iter().copied().collect();
    let mut frontier: Vec<usize> = start.to_vec();
    for _ in 0..PIN_FOLLOW_MAX_DEPTH {
        let mut next: Vec<usize> = Vec::new();
        for &node in &frontier {
            let Some(pin_data) = context.parsed.pin_data.get(&node) else {
                continue;
            };
            for link in pin_data
                .pins
                .iter()
                .filter(|pin| follow_pin(pin))
                .flat_map(|pin| pin.linked_to.iter())
            {
                if visited.insert(link.node) {
                    next.push(link.node);
                }
            }
        }
        if next.is_empty() {
            return Classification::Unanchored;
        }
        next.sort_unstable();
        for &candidate in &next {
            if let placed @ Classification::Placed(_) =
                anchor_to_node(comment, page, candidate, context)
            {
                return placed;
            }
        }
        frontier = next;
    }
    Classification::Unanchored
}

/// Try each contained execution entry point after `already_tried`, in the same
/// `(y, x, export)` order [`exec_entry_point`] uses, returning the first that
/// resolves to a covering statement. `None` when none resolve.
fn anchor_to_first_resolvable(
    comment: &CommentBox,
    page: &str,
    contained: &[usize],
    already_tried: usize,
    context: &ClassifyContext,
) -> Option<Classification> {
    for node in sorted_exec_entries(contained, context) {
        if node == already_tried {
            continue;
        }
        if let Classification::Placed(placed) = anchor_to_node(comment, page, node, context) {
            return Some(Classification::Placed(placed));
        }
    }
    None
}

/// Resolve `node` (a contained or owner export) to the statement it produced
/// and build the inline placement. Returns `Unanchored` when no byte map
/// covers the node or no statement covers its range.
///
/// When `page` names a decoded block directly, the anchor resolves inside that
/// block. When it does not (an ubergraph editor page like `EventGraph` or
/// `Input`, which decoded events are not keyed by), the owning event is
/// inferred from the node's byte attribution instead.
fn anchor_to_node(
    comment: &CommentBox,
    page: &str,
    node: usize,
    context: &ClassifyContext,
) -> Classification {
    let Some(body) = context.body_for_block(page) else {
        return anchor_via_owner_event(comment, node, context);
    };
    let Some(byte_map) = context.byte_map_for_block(page) else {
        return Classification::Unanchored;
    };
    let Some(stmt) = byte_map.statement_for_node(node, body) else {
        return Classification::Unanchored;
    };
    Classification::Placed(build_inline_placement(comment, page, stmt.offset()))
}

/// Anchor a box whose `graph_page` is an ubergraph editor page name rather
/// than a decoded block name. The ubergraph partition for `node` carries the
/// events whose pin trees reach it (`owner_events`); try each owning event in
/// sorted order and anchor inside the first decoded body whose statement span
/// contains the node's bytes. The span requirement stops a multi-owner node
/// (shared scaffold) from anchoring to the trailing statement of a sibling
/// event that merely precedes it.
fn anchor_via_owner_event(
    comment: &CommentBox,
    node: usize,
    context: &ClassifyContext,
) -> Classification {
    let Some(ubergraph) = context.decoded.byte_maps.ubergraph.as_ref() else {
        return Classification::Unanchored;
    };
    let Some(partition) = ubergraph.partitions.get(&node) else {
        return Classification::Unanchored;
    };
    let owner_bodies: Vec<(&String, &[Stmt])> = partition
        .owner_events
        .iter()
        .filter_map(|event_name| {
            context
                .decoded
                .events
                .iter()
                .find(|event| &event.name == event_name)
                .map(|event| (event_name, event.body.as_slice()))
        })
        .collect();
    // Latent-resume continuations render interleaved inside the owning
    // event's body, but their statements live in `resume_bodies`, not the
    // event body, so the owner-body search misses nodes that compiled into
    // a resume chunk (everything after a Delay-style call).
    let chunk_bodies: Vec<(&String, &[Stmt])> = context
        .decoded
        .resume_bodies
        .iter()
        .filter_map(|(call_offset, resume_body)| {
            context
                .decoded
                .resume_owner_events
                .get(call_offset)
                .map(|event_name| (event_name, resume_body.as_slice()))
        })
        .collect();
    for (event_name, body) in owner_bodies.iter().chain(&chunk_bodies) {
        if let Some(stmt) = ubergraph.statement_for_node_in_span(node, body) {
            return Classification::Placed(build_inline_placement(
                comment,
                event_name,
                stmt.offset(),
            ));
        }
    }
    // Per-range fallback, only after the strict gate rejected every body so
    // existing anchors never move. Chunks before owner bodies: a near-miss
    // node's true bytes live in its resume chunk, while a collision-merged
    // partition can carry stray range starts inside any owner's span.
    for (event_name, body) in chunk_bodies.iter().chain(&owner_bodies) {
        if let Some(stmt) = ubergraph.statement_for_node_in_span_per_range(node, body) {
            return Classification::Placed(build_inline_placement(
                comment,
                event_name,
                stmt.offset(),
            ));
        }
    }
    Classification::Unanchored
}

/// Package one inline placement at `statement_offset` in `block`.
///
/// Inline placements carry no pre-rendered lines: the emitter renders the
/// text with the anchored statement's actual indent at the point of emission
/// (the IR nesting depth here does not always match the rendered layout).
fn build_inline_placement(
    comment: &CommentBox,
    block: &str,
    statement_offset: usize,
) -> Box<PlacedComment> {
    Box::new(PlacedComment {
        block: block.to_string(),
        class: PlacementClass::InlineAtStatement { statement_offset },
        lines: Vec::new(),
        box_x: comment.x,
        box_y: comment.y,
        text: comment.text.clone(),
    })
}

/// The box's execution entry points: contained nodes whose input exec pin
/// links to a node outside the contained set. Ordered by `(y, x)` then export
/// index, matching v1's top-to-bottom order.
fn sorted_exec_entries(contained: &[usize], context: &ClassifyContext) -> Vec<usize> {
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
fn exec_entry_point(contained: &[usize], context: &ClassifyContext) -> Option<usize> {
    sorted_exec_entries(contained, context).into_iter().next()
}

/// Whether `node`'s input exec pin is wired from a node outside `contained`.
fn node_has_external_exec_input(
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

/// Deterministic order over placed comments.
///
/// Primary key is the block name so a block's comments group together. Within
/// a block the spec's anchor-collision tie-break applies: box `y`, then `x`,
/// then text. Inline placements additionally key on the statement offset
/// first so two anchors in the same block keep statement order.
fn sort_placed(placed: &mut [PlacedComment]) {
    placed.sort_by(|a, b| {
        a.block
            .cmp(&b.block)
            .then_with(|| class_rank(&a.class).cmp(&class_rank(&b.class)))
            .then_with(|| inline_offset(&a.class).cmp(&inline_offset(&b.class)))
            .then_with(|| a.box_y.cmp(&b.box_y))
            .then_with(|| a.box_x.cmp(&b.box_x))
            .then_with(|| a.text.cmp(&b.text))
    });
}

/// Stable rank so event-wrapping sorts before function-level before inline
/// within one block (header annotations precede body annotations).
fn class_rank(class: &PlacementClass) -> u8 {
    match class {
        PlacementClass::EventWrapping => 0,
        PlacementClass::FunctionLevel => 1,
        PlacementClass::InlineAtStatement { .. } => 2,
    }
}

/// Statement offset for inline placements, `0` for header placements (which
/// already sort ahead via `class_rank`).
fn inline_offset(class: &PlacementClass) -> usize {
    match class {
        PlacementClass::InlineAtStatement { statement_offset } => *statement_offset,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::asset::{Event, Function};
    use crate::bytecode::decode::cross_event_inline::K2NodeClass;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::k2node_byte_map::{ByteMaps, K2NodeByteMap, K2NodePartition};
    use crate::output_summary::comments::NodeGeometry;
    use crate::types::{
        EdGraphPin, LinkedPin, NodePinData, PIN_DIRECTION_INPUT, PIN_DIRECTION_OUTPUT,
        PIN_TYPE_EXEC,
    };

    fn call(offset: usize, name: &str) -> Stmt {
        Stmt::Call {
            func: Expr::Var(name.into()),
            args: vec![],
            offset,
        }
    }

    fn box_at(text: &str, x: i32, y: i32, width: i32, height: i32, page: &str) -> CommentBox {
        CommentBox {
            text: text.into(),
            x,
            y,
            width,
            height,
            is_bubble: false,
            owner_export: None,
            graph_page: Some(page.into()),
        }
    }

    fn node_geom(export_index: usize, x: i32, y: i32, page: &str) -> NodeGeometry {
        NodeGeometry {
            export_index,
            x,
            y,
            graph_page: Some(page.into()),
        }
    }

    /// A decoded asset with one event body and no byte map.
    fn decoded_with_event(name: &str, body: Vec<Stmt>) -> DecodedAsset {
        DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: name.into(),
                body,
                export_index: None,
            }],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps: Default::default(),
        }
    }

    fn empty_parsed() -> ParsedAsset {
        ParsedAsset {
            imports: vec![],
            exports: vec![],
            pin_data: Default::default(),
            function_signatures: Default::default(),
            bytecode_by_export: Default::default(),
        }
    }

    /// One exec pin in `direction`, optionally linked to `target`.
    fn exec_pin(direction: u8, target: Option<usize>) -> EdGraphPin {
        EdGraphPin {
            name: "exec".into(),
            pin_type: PIN_TYPE_EXEC.into(),
            direction,
            pin_id: [0; 16],
            linked_to: target
                .map(|node| {
                    vec![LinkedPin {
                        node,
                        pin_id: [0; 16],
                    }]
                })
                .unwrap_or_default(),
        }
    }

    /// Pin data for a pure node: one data-output pin linked to `target`.
    fn pure_node_pins(target: usize) -> NodePinData {
        NodePinData {
            pins: vec![EdGraphPin {
                name: "Out".into(),
                pin_type: "float".into(),
                direction: PIN_DIRECTION_OUTPUT,
                pin_id: [0; 16],
                linked_to: vec![LinkedPin {
                    node: target,
                    pin_id: [0; 16],
                }],
            }],
        }
    }

    /// A decoded asset with one function whose byte map attributes
    /// `attributed_node` to a disk range starting at `disk_start`.
    fn decoded_with_mapped_function(
        name: &str,
        body: Vec<Stmt>,
        attributed_node: usize,
        disk_start: usize,
    ) -> DecodedAsset {
        let mut byte_map = K2NodeByteMap::default();
        byte_map.partitions.insert(
            attributed_node,
            K2NodePartition {
                node_id: attributed_node,
                ranges: std::iter::once(disk_start..disk_start + 4).collect(),
                owner_events: Default::default(),
                kind: K2NodeClass::Other,
                macro_kind: None,
                via_fallback: Vec::new(),
            },
        );
        let mut byte_maps = ByteMaps::default();
        byte_maps.functions.insert(name.into(), byte_map);
        DecodedAsset {
            functions: vec![Function {
                name: name.into(),
                body,
                export_index: None,
            }],
            events: vec![],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps,
        }
    }

    #[test]
    fn function_level_when_box_covers_over_threshold() {
        // Page "MyFunc" has 4 nodes; the box contains all 4 (100% > 80%).
        let model = CommentModel {
            boxes: vec![box_at("whole graph desc", -10, -10, 500, 500, "MyFunc")],
            nodes: vec![
                node_geom(2, 0, 0, "MyFunc"),
                node_geom(3, 10, 10, "MyFunc"),
                node_geom(4, 20, 20, "MyFunc"),
                node_geom(5, 30, 30, "MyFunc"),
            ],
        };
        let decoded = DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps: Default::default(),
        };
        let parsed = empty_parsed();
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.count_class(&PlacementClass::FunctionLevel), 1);
        assert_eq!(plan.placed[0].block, "MyFunc");
        assert_eq!(plan.placed[0].lines, vec!["    // \"whole graph desc\""]);
    }

    #[test]
    fn below_threshold_box_without_anchor_is_unanchored() {
        // Box covers 1 of 4 nodes (25% < 80%); no byte map, no exec entry
        // crossing, so it drops to the unanchored count.
        let model = CommentModel {
            boxes: vec![box_at("inline note", 0, 0, 5, 5, "MyFunc")],
            nodes: vec![
                node_geom(2, 0, 0, "MyFunc"),
                node_geom(3, 100, 100, "MyFunc"),
                node_geom(4, 200, 200, "MyFunc"),
                node_geom(5, 300, 300, "MyFunc"),
            ],
        };
        let decoded = decoded_with_event("MyFunc", vec![call(0, "f")]);
        let parsed = empty_parsed();
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.placed.len(), 0);
        assert_eq!(plan.unanchored, 1);
    }

    #[test]
    fn bubble_on_pure_node_anchors_via_pin_follow() {
        // Node 2 is pure (no byte attribution); its data output feeds node 3,
        // attributed to disk bytes from 20. The bubble anchors to the
        // statement covering those bytes.
        let model = CommentModel {
            boxes: vec![CommentBox {
                text: "pure note".into(),
                x: 0,
                y: 0,
                width: 10,
                height: 10,
                is_bubble: true,
                owner_export: Some(2),
                graph_page: Some("MyFunc".into()),
            }],
            nodes: vec![],
        };
        let decoded =
            decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
        let mut parsed = empty_parsed();
        parsed.pin_data.insert(2, pure_node_pins(3));
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.unanchored, 0);
        assert_eq!(plan.placed.len(), 1);
        assert_eq!(plan.placed[0].block, "MyFunc");
        assert_eq!(
            plan.placed[0].class,
            PlacementClass::InlineAtStatement {
                statement_offset: 20
            }
        );
    }

    #[test]
    fn all_pure_box_anchors_through_knot_chain() {
        // The box contains only pure node 2 (25% of the page, below the
        // coverage threshold, no exec pins). Its output reroutes through pure
        // node 9 before reaching the attributed consumer node 3 at depth 2.
        let model = CommentModel {
            boxes: vec![box_at("pure box", -5, -5, 10, 10, "MyFunc")],
            nodes: vec![
                node_geom(2, 0, 0, "MyFunc"),
                node_geom(3, 100, 100, "MyFunc"),
                node_geom(4, 200, 200, "MyFunc"),
                node_geom(5, 300, 300, "MyFunc"),
            ],
        };
        let decoded =
            decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
        let mut parsed = empty_parsed();
        parsed.pin_data.insert(2, pure_node_pins(9));
        parsed.pin_data.insert(9, pure_node_pins(3));
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.unanchored, 0);
        assert_eq!(plan.placed.len(), 1);
        assert_eq!(
            plan.placed[0].class,
            PlacementClass::InlineAtStatement {
                statement_offset: 20
            }
        );
    }

    #[test]
    fn ubergraph_page_node_anchors_inside_resume_body() {
        // Node 7 compiled into a latent-resume chunk: its bytes (50..51) lie
        // in the resume body of the Delay call at offset 10, which itself
        // sits in event "Ev". The bubble's page is the ubergraph editor page
        // name, so anchoring goes through anchor_via_owner_event; the event
        // body span (10..=10) misses the node, the resume-chain search finds
        // it and keys the placement by the owning event.
        let model = CommentModel {
            boxes: vec![CommentBox {
                text: "after the delay".into(),
                x: 0,
                y: 0,
                width: 10,
                height: 10,
                is_bubble: true,
                owner_export: Some(7),
                graph_page: Some("EventGraph".into()),
            }],
            nodes: vec![],
        };
        let mut byte_map = K2NodeByteMap::default();
        byte_map.partitions.insert(
            7,
            K2NodePartition {
                node_id: 7,
                ranges: std::iter::once(50..51).collect(),
                owner_events: Default::default(),
                kind: K2NodeClass::Other,
                macro_kind: None,
                via_fallback: Vec::new(),
            },
        );
        let decoded = DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "Ev".into(),
                body: vec![call(10, "Delay")],
                export_index: None,
            }],
            resume_bodies: std::iter::once((10usize, vec![call(50, "AfterDelay")])).collect(),
            resume_owner_events: std::iter::once((10usize, "Ev".to_string())).collect(),
            byte_maps: ByteMaps {
                ubergraph: Some(byte_map),
                functions: Default::default(),
            },
        };
        let parsed = empty_parsed();
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.unanchored, 0);
        assert_eq!(plan.placed.len(), 1);
        assert_eq!(plan.placed[0].block, "Ev");
        assert_eq!(
            plan.placed[0].class,
            PlacementClass::InlineAtStatement {
                statement_offset: 50
            }
        );
    }

    #[test]
    fn knot_entry_box_anchors_via_exec_follow() {
        // Node 2 is the box's only exec entry (wired from node 99 outside)
        // but has no byte attribution (a reroute); its exec output leads to
        // contained node 3, which is attributed. The box anchors at node 3's
        // statement instead of dropping.
        let model = CommentModel {
            boxes: vec![box_at("entry is a knot", -5, -5, 120, 120, "MyFunc")],
            nodes: vec![
                node_geom(2, 0, 0, "MyFunc"),
                node_geom(3, 50, 50, "MyFunc"),
                node_geom(4, 500, 500, "MyFunc"),
                node_geom(5, 600, 600, "MyFunc"),
                node_geom(99, -300, 0, "MyFunc"),
            ],
        };
        let decoded =
            decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
        let mut parsed = empty_parsed();
        parsed.pin_data.insert(
            2,
            NodePinData {
                pins: vec![
                    exec_pin(PIN_DIRECTION_INPUT, Some(99)),
                    exec_pin(PIN_DIRECTION_OUTPUT, Some(3)),
                ],
            },
        );
        parsed.pin_data.insert(
            3,
            NodePinData {
                pins: vec![exec_pin(PIN_DIRECTION_INPUT, Some(2))],
            },
        );
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.unanchored, 0);
        assert_eq!(plan.placed.len(), 1);
        assert_eq!(
            plan.placed[0].class,
            PlacementClass::InlineAtStatement {
                statement_offset: 20
            }
        );
    }

    #[test]
    fn pin_follow_dead_end_stays_unanchored() {
        // Node 2's data chain ends at node 9, which has no attribution and no
        // further links; the box drops to the unanchored count.
        let model = CommentModel {
            boxes: vec![box_at("dead end", -5, -5, 10, 10, "MyFunc")],
            nodes: vec![
                node_geom(2, 0, 0, "MyFunc"),
                node_geom(3, 100, 100, "MyFunc"),
                node_geom(4, 200, 200, "MyFunc"),
                node_geom(5, 300, 300, "MyFunc"),
            ],
        };
        let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a")], 3, 20);
        let mut parsed = empty_parsed();
        parsed.pin_data.insert(2, pure_node_pins(9));
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.placed.len(), 0);
        assert_eq!(plan.unanchored, 1);
    }

    #[test]
    fn box_without_contained_nodes_is_dropped_silently() {
        let model = CommentModel {
            boxes: vec![box_at("empty box", 0, 0, 5, 5, "MyFunc")],
            nodes: vec![node_geom(2, 100, 100, "MyFunc")],
        };
        let decoded = decoded_with_event("MyFunc", vec![]);
        let parsed = empty_parsed();
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.placed.len(), 0);
        assert_eq!(plan.unanchored, 0);
    }

    #[test]
    fn placed_comments_sorted_by_block_then_position() {
        // Both boxes cover their page's sole node (100% > 80%), so both
        // promote to function-level; the plan must order them by block name.
        let model = CommentModel {
            boxes: vec![
                box_at("zzz", -10, -10, 500, 500, "BFunc"),
                box_at("aaa", -10, -10, 500, 500, "AFunc"),
            ],
            nodes: vec![node_geom(2, 0, 0, "AFunc"), node_geom(3, 0, 0, "BFunc")],
        };
        let decoded = DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps: Default::default(),
        };
        let parsed = empty_parsed();
        let plan = build_placement_plan(&decoded, &parsed, &[], &model);
        assert_eq!(plan.placed.len(), 2);
        assert_eq!(plan.placed[0].block, "AFunc");
        assert_eq!(plan.placed[1].block, "BFunc");
    }

    /// Whole-pipeline check against the committed BP_DecoderTest fixture: parse,
    /// decode, extract the comment model, build the plan, and assert the class
    /// split holds (every box placed, the expected EventWrapping/function-level
    /// counts, no inline anchors on this asset).
    #[test]
    fn decodertest_class_split() {
        use crate::output_summary::comments::extract::build_comment_model;
        use crate::parser::parse_asset;

        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("samples/ue_4.27/BP_DecoderTest.uasset");
        let bytes = std::fs::read(&path).expect("read DecoderTest fixture");
        let parsed = parse_asset(&bytes, false).expect("parse DecoderTest");
        let decoded = crate::bytecode::decode::decode_asset(&parsed, &bytes);
        let export_names: Vec<String> = parsed
            .exports
            .iter()
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        let model = build_comment_model(&parsed, &export_names);
        let plan = build_placement_plan(&decoded, &parsed, &export_names, &model);

        let event_wrapping = plan.count_class(&PlacementClass::EventWrapping);
        let function_level = plan.count_class(&PlacementClass::FunctionLevel);
        let inline = plan.count_class(&PlacementClass::InlineAtStatement {
            statement_offset: 0,
        });

        // 17 EventWrapping, 18 function-level, 0 inline, every box placed.
        // 14 of the EventWrapping boxes are single/small-group annotations;
        // the other 3 are the multi-event region labels ("Latches and
        // delays" / "Cross-event convergence" / "Complex nested symetrical
        // flow gates with event convergence", spanning 5/10/4 events), which
        // anchor to their first contained event in render order (a linear
        // summary cannot bracket the group).
        assert_eq!(model.boxes.len(), 35, "DecoderTest comment-box count");
        assert_eq!(event_wrapping, 17, "EventWrapping count");
        assert_eq!(function_level, 18, "function-level count");
        assert_eq!(inline, 0, "inline count");
        assert_eq!(plan.unanchored, 0, "unanchored count");
        assert_eq!(plan.placed.len(), 35, "total placed");
    }
}
