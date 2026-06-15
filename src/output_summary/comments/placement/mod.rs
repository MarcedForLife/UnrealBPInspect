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
//!    of the identifiable nodes on its graph page AND containing the page's
//!    execution-root, promoted to a description under the block header.
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
//!
//! The implementation splits by concern: [`context`] holds the per-asset
//! lookups and the node/entry helpers, [`classify`] holds the cascade body,
//! [`anchor`] holds the anchor strategies, and [`ordering`] holds the
//! deterministic placed-comment sort.

use std::cell::Cell;

use crate::bytecode::asset::DecodedAsset;
use crate::types::ParsedAsset;

use super::audit::{maybe_emit_audit, PlacementTrace, Strategy};
use super::CommentModel;

mod anchor;
mod classify;
mod context;
mod ordering;

#[cfg(test)]
mod tests;

use classify::classify;
use context::ClassifyContext;
use ordering::sort_placed;

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
///
/// `trace` is the per-comment placement audit, populated for measurement only
/// (consumed by `BP_INSPECT_COMMENT_AUDIT`, never by STDOUT). It carries no
/// influence on `placed`/`unanchored`; it records how each one was reached.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PlacementPlan {
    pub placed: Vec<PlacedComment>,
    /// Boxes that wanted a statement anchor but found none.
    pub unanchored: usize,
    /// One audit entry per comment box/bubble, in box iteration order.
    pub trace: Vec<PlacementTrace>,
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
        let (outcome, trace) = classify(comment, model, &context);
        match outcome {
            Some(Classification::Placed(placed)) => plan.placed.push(*placed),
            Some(Classification::Unanchored) => plan.unanchored += 1,
            None => {}
        }
        plan.trace.push(trace);
    }

    sort_placed(&mut plan.placed);
    maybe_emit_audit(&plan.trace);
    plan
}

/// Classification outcome for one box before it joins the plan.
pub(super) enum Classification {
    Placed(Box<PlacedComment>),
    /// Inline/bubble box with no resolvable statement anchor.
    Unanchored,
}

impl Classification {
    /// Cascade combinator: keep a resolved `Placed` outcome, otherwise
    /// evaluate the next strategy. Lets a fallback chain read as an ordered
    /// list of anchoring attempts instead of repeated
    /// match-on-`Unanchored`.
    pub(super) fn or_else(self, next: impl FnOnce() -> Classification) -> Classification {
        match self {
            Classification::Unanchored => next(),
            resolved => resolved,
        }
    }
}

/// Audit-only side channel the anchor strategies write into as they run.
///
/// The cascade short-circuits on the first `Placed`, so the helper that
/// produces it records its strategy (and the follow depth it used) here just
/// before returning. Plain interior mutability, no influence on the returned
/// `Classification`; if the env var is unset the recorded values are simply
/// discarded by [`build_placement_plan`].
#[derive(Default)]
pub(super) struct TraceRecorder {
    strategy: Cell<Option<Strategy>>,
    depth: Cell<usize>,
}

impl TraceRecorder {
    /// Tag the strategy that just produced a `Placed`. Last writer before the
    /// cascade short-circuits wins, which is the winning strategy.
    pub(super) fn record(&self, strategy: Strategy) {
        self.strategy.set(Some(strategy));
    }

    /// Note the follow depth a pin-follow / exec-follow walk consumed.
    pub(super) fn record_depth(&self, depth: usize) {
        self.depth.set(depth);
    }

    /// The strategy recorded by the last successful anchor, if any.
    pub(super) fn strategy(&self) -> Option<Strategy> {
        self.strategy.get()
    }

    /// The follow depth recorded by the winning walk.
    pub(super) fn depth(&self) -> usize {
        self.depth.get()
    }
}
