//! Classify each comment box into a placement and resolve its anchor.
//!
//! Placement is decided structurally from the extracted [`CommentModel`] and
//! the decoded asset, rather than by string-matching rendered output. The
//! classifier runs each box through a first-match cascade:
//!
//! 1. `BubbleOwned`   - a bubble comment annotating the node it sits on.
//! 2. `EventWrapping` - a box containing identified event-entry nodes,
//!    attached to every covered event and grouped when several are covered.
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
//! 7. `Unresolved`    - retain the text under its source graph page.
//!
//! Inline and bubble placements resolve graph evidence to exact statement
//! paths. Several proven statements remain separate locations rather than
//! implying that an intervening branch or statement belongs to the comment.
//! Event and function-level locations attach to identified block headers.
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
mod call_attribution;
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
    /// Retained under the source graph because no unique location was found.
    Unresolved,
    /// Below the block signature, as a whole-graph description.
    FunctionLevel,
    /// Above one statement identified by its body path. The offset is retained
    /// for audit output and unique-offset compatibility with older anchors.
    InlineAtStatement {
        statement_offset: usize,
        /// Root body, statement index, then alternating child-body and statement indices.
        /// Root zero is the block body, later roots are its owned resumptions by call offset.
        statement_path: Vec<usize>,
    },
}

/// One exact statement or header annotated by an authored comment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommentLocation {
    pub block: String,
    pub class: PlacementClass,
}

/// One authored comment with every independently proven location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PlacedComment {
    pub locations: Vec<CommentLocation>,
    /// Pre-rendered marker lines (already indented for the placement class).
    pub lines: Vec<String>,
    /// Box top-left, kept for the stable multi-comment tie-break.
    pub box_x: i32,
    pub box_y: i32,
    /// Box text, the final tie-break key.
    pub text: String,
}

/// Every extracted comment has either a resolved placement or an explicitly
/// unresolved entry. `unanchored` counts the latter, including empty boxes
/// and comments without a known graph page.
///
/// `trace` is the per-comment placement audit, populated for measurement only
/// (consumed by `BP_INSPECT_COMMENT_AUDIT`, never by STDOUT). It carries no
/// influence on `placed`/`unanchored`; it records how each one was reached.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PlacementPlan {
    pub placed: Vec<PlacedComment>,
    /// Retained comments without a unique statement or header anchor.
    pub unanchored: usize,
    /// One audit entry per comment box/bubble, in box iteration order.
    pub trace: Vec<PlacementTrace>,
}

impl PlacementPlan {
    /// Count placed comments of a given class (test/inspection helper).
    pub fn count_class(&self, class: &PlacementClass) -> usize {
        self.placed
            .iter()
            .filter(|placed| {
                placed.locations.iter().any(|location| {
                    std::mem::discriminant(&location.class) == std::mem::discriminant(class)
                })
            })
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

    for comment in &model.boxes {
        let (outcome, mut trace) = classify(comment, model, &context);
        match outcome {
            Some(Classification::Placed(mut placed)) => {
                if !resolve_locations(&mut placed.locations, decoded) {
                    if let Classification::Placed(unresolved) = Classification::unresolved(comment)
                    {
                        placed = unresolved;
                    }
                    trace.strategy =
                        Strategy::Dropped(super::audit::DropReason::NoCoveringStatement);
                }
                sort_placed(std::slice::from_mut(placed.as_mut()));
                let unresolved = placed
                    .locations
                    .iter()
                    .any(|location| location.class == PlacementClass::Unresolved);
                plan.unanchored += usize::from(unresolved);
                trace.locations = if unresolved {
                    Vec::new()
                } else {
                    placed.locations.clone()
                };
                plan.placed.push(*placed);
            }
            Some(Classification::Unanchored) | None => {
                plan.unanchored += 1;
                if let Classification::Placed(placed) = Classification::unresolved(comment) {
                    plan.placed.push(*placed);
                }
            }
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
    fn unresolved(comment: &super::CommentBox) -> Self {
        Self::Placed(Box::new(PlacedComment {
            locations: vec![CommentLocation {
                block: comment
                    .graph_page
                    .clone()
                    .unwrap_or_else(|| "<unknown graph>".into()),
                class: PlacementClass::Unresolved,
            }],
            lines: Vec::new(),
            text: comment.text.clone(),
            box_x: comment.x,
            box_y: comment.y,
        }))
    }

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

impl CommentLocation {
    /// Resolve the exact immutable statement used by the summary emitter.
    pub(crate) fn statement<'a>(
        &self,
        decoded: &'a DecodedAsset,
    ) -> Option<&'a crate::bytecode::stmt::Stmt> {
        let PlacementClass::InlineAtStatement {
            statement_path,
            statement_offset,
        } = &self.class
        else {
            return None;
        };
        let (&root, path) = statement_path.split_first()?;
        let (&index, children) = path.split_first()?;
        let bodies = block_bodies(decoded, &self.block);
        let mut statement = bodies.get(root)?.get(index)?;
        let (steps, remainder) = children.as_chunks::<2>();
        for step in steps {
            statement = statement.child_bodies_all().get(step[0])?.get(step[1])?;
        }
        (remainder.is_empty() && statement.offset() == *statement_offset).then_some(statement)
    }
}

fn block_bodies<'a>(
    decoded: &'a DecodedAsset,
    block: &str,
) -> Vec<&'a [crate::bytecode::stmt::Stmt]> {
    let mut bodies = Vec::new();
    let body = decoded
        .events
        .iter()
        .find(|event| event.name == block)
        .map(|event| event.body.as_slice())
        .or_else(|| {
            decoded
                .functions
                .iter()
                .find(|function| function.name == block)
                .map(|function| function.body.as_slice())
        });
    let Some(body) = body else {
        return bodies;
    };
    bodies.push(body);
    for (offset, owner) in &decoded.resume_owner_events {
        if owner == block {
            if let Some(body) = decoded.resume_bodies.get(offset) {
                bodies.push(body.as_slice());
            }
        }
    }
    bodies
}

fn resolve_locations(locations: &mut [CommentLocation], decoded: &DecodedAsset) -> bool {
    for location in locations {
        if let PlacementClass::InlineAtStatement {
            statement_offset,
            statement_path,
        } = &mut location.class
        {
            if statement_path.is_empty() {
                let mut matches = Vec::new();
                for (root, body) in block_bodies(decoded, &location.block)
                    .into_iter()
                    .enumerate()
                {
                    collect_statement_paths(body, *statement_offset, &[root], &mut matches);
                }
                let [path] = matches.as_slice() else {
                    return false;
                };
                *statement_path = path.clone();
            }
            if location.statement(decoded).is_none() {
                return false;
            }
        }
    }
    true
}

fn collect_statement_paths(
    body: &[crate::bytecode::stmt::Stmt],
    offset: usize,
    prefix: &[usize],
    paths: &mut Vec<Vec<usize>>,
) {
    for (index, statement) in body.iter().enumerate() {
        let mut path = prefix.to_vec();
        path.push(index);
        if statement.offset() == offset {
            paths.push(path.clone());
        }
        for (child_index, child) in statement.child_bodies_all().iter().enumerate() {
            let mut child_path = path.clone();
            child_path.push(child_index);
            collect_statement_paths(child, offset, &child_path, paths);
        }
    }
}
