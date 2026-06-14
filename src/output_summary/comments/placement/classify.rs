//! The first-match cascade: route one box through EventWrapping, FunctionLevel,
//! and the inline/bubble anchor strategies, and build the audit trace.

use super::super::audit::{DropReason, PlacementTrace, Strategy};
use super::super::render::render_comment_lines;
use super::super::{CommentBox, CommentModel};
use super::anchor::{
    anchor_to_first_resolvable, anchor_to_node, anchor_via_exec_follow,
    anchor_via_exec_follow_outward, anchor_via_pin_follow,
};
use super::context::{box_contains_exec_root, exec_entry_point, ClassifyContext};
use super::{Classification, PlacedComment, PlacementClass, TraceRecorder};

/// Coverage half of the function-level promotion rule: a box must cover more
/// than this percentage of a graph page's identifiable nodes (strictly
/// greater-than) AND contain the page's exec-root (see
/// [`box_contains_exec_root`]) to promote to a whole-graph description.
///
/// The threshold is data-justified, not fitted. Across the fixture corpus the
/// per-box coverage ratio is bimodal: whole-graph boxes cluster at 1.0 and
/// every other box sits below 0.4, a clean gap with nothing in between, so any
/// cut in `(0.4, 1.0)` selects the same boxes. 80% sits inside that gap. The
/// exec-root requirement is what actually distinguishes the two clusters
/// structurally; the threshold only excludes near-total-but-partial coverage.
const COVERAGE_THRESHOLD_PERCENT: usize = 80;

/// Indent applied to an event-wrapping comment, sitting directly above the
/// `EventName():` header. One summary indent level (two spaces).
const EVENT_WRAP_INDENT: &str = "  ";

/// Indent applied to a function-level description, sitting directly below the
/// block signature at body indent (two summary levels, four spaces).
const FUNCTION_LEVEL_INDENT: &str = "    ";

/// Classify one box, returning both the placement outcome and the audit trace.
/// The outcome is `None` for a box with no graph page (cannot be placed at
/// all); the trace records that as a `NoGraphPage` drop. The trace is
/// side-channel only and never influences the outcome.
pub(super) fn classify(
    comment: &CommentBox,
    model: &CommentModel,
    context: &ClassifyContext,
) -> (Option<Classification>, PlacementTrace) {
    let recorder = TraceRecorder::default();
    let Some(page) = comment.graph_page.clone() else {
        return (None, drop_trace(comment, "<none>", DropReason::NoGraphPage));
    };

    // Bubble comments own one node; anchor to the owner's statement, to the
    // owner's nearest data consumer when the owner compiled to no bytes of
    // its own (a bubble on a pure node), or to the nearest downstream exec
    // statement when the owner has no data outputs either (a bubble on a
    // Branch or Knot).
    if comment.is_bubble {
        let Some(owner) = comment.owner_export else {
            return (
                None,
                drop_trace(comment, &page, DropReason::NoContainedNodes),
            );
        };
        let outcome = anchor_to_node(
            comment,
            &page,
            owner,
            Strategy::BubbleDirect,
            context,
            &recorder,
        )
        .or_else(|| {
            anchor_via_pin_follow(
                comment,
                &page,
                &[owner],
                Strategy::BubblePinFollow,
                context,
                &recorder,
            )
        })
        .or_else(|| anchor_via_exec_follow_outward(comment, &page, owner, context, &recorder));
        let trace = trace_for(comment, &page, None, None, &recorder, &outcome);
        return (Some(outcome), trace);
    }

    let contained = model.contained_nodes(comment);
    if contained.is_empty() {
        // A box with no contained nodes has nothing to annotate.
        return (
            None,
            drop_trace(comment, &page, DropReason::NoContainedNodes),
        );
    }
    let page_total = context.page_node_total(&page);

    // Every box outcome below shares the same coverage/page/recorder trace
    // inputs; only the resolved `outcome` differs.
    let finish_box = |outcome: Classification| {
        let trace = trace_for(
            comment,
            &page,
            Some(contained.len()),
            Some(page_total),
            &recorder,
            &outcome,
        );
        (Some(outcome), trace)
    };

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
            .into_iter()
            .min()
            .cloned()
            .expect("event_nodes is non-empty");
        let lines = render_comment_lines(&comment.text, EVENT_WRAP_INDENT);
        recorder.record(Strategy::EventWrapping);
        let outcome = Classification::Placed(Box::new(PlacedComment {
            block: event_name,
            class: PlacementClass::EventWrapping,
            lines,
            box_x: comment.x,
            box_y: comment.y,
            text: comment.text.clone(),
        }));
        return finish_box(outcome);
    }

    // FunctionLevel: the box covers more than the coverage threshold of the
    // page's identifiable nodes AND reaches the page's execution-entry. The
    // coverage gate alone could misfire on a dense graph where a box that is
    // not whole-graph still crosses the threshold; requiring the box to
    // contain an exec-root confirms it really spans the graph from the entry.
    if page_total > 0
        && contained.len() * 100 / page_total > COVERAGE_THRESHOLD_PERCENT
        && box_contains_exec_root(&contained, context.parsed)
    {
        let lines = render_comment_lines(&comment.text, FUNCTION_LEVEL_INDENT);
        recorder.record(Strategy::FunctionLevel);
        let outcome = Classification::Placed(Box::new(PlacedComment {
            block: page.clone(),
            class: PlacementClass::FunctionLevel,
            lines,
            box_x: comment.x,
            box_y: comment.y,
            text: comment.text.clone(),
        }));
        return finish_box(outcome);
    }

    // InlineAtEntry: anchor to the top-left execution entry point of the box.
    let outcome = match exec_entry_point(&contained, context) {
        // No exec boundary crossing: a box of pure expression nodes, or a
        // self-contained exec block. Pure expressions render inside their
        // consuming statement, so follow the data pins out before giving up.
        None => anchor_via_pin_follow(
            comment,
            &page,
            &contained,
            Strategy::PinFollow,
            context,
            &recorder,
        ),
        // The geometric entry is the top-left exec node, but it may be a pure
        // node or a node whose member name didn't survive byte attribution.
        // When it does not resolve, fall back to the first contained exec node
        // that does, in deterministic (y, x, export) order, then to exec
        // follow-through, then to pin-following.
        Some(entry) => anchor_to_node(
            comment,
            &page,
            entry,
            Strategy::InlineEntry,
            context,
            &recorder,
        )
        .or_else(|| {
            anchor_to_first_resolvable(comment, &page, &contained, entry, context, &recorder)
                .unwrap_or(Classification::Unanchored)
        })
        .or_else(|| anchor_via_exec_follow(comment, &page, &contained, context, &recorder))
        .or_else(|| {
            anchor_via_pin_follow(
                comment,
                &page,
                &contained,
                Strategy::PinFollow,
                context,
                &recorder,
            )
        }),
    };
    finish_box(outcome)
}

/// Build a drop trace for a box that never entered the anchor cascade
/// (page-less, bubble without owner, or no contained nodes).
fn drop_trace(comment: &CommentBox, page: &str, reason: DropReason) -> PlacementTrace {
    PlacementTrace {
        page: page.to_string(),
        snippet: super::super::audit::snippet_of(&comment.text),
        strategy: Strategy::Dropped(reason),
        contained: None,
        page_total: None,
        depth: 0,
        placement: None,
    }
}

/// Assemble the audit trace from the recorded strategy/depth and the final
/// outcome. An `Unanchored` outcome with no recorded strategy means the
/// cascade exhausted every follow without reaching a covering statement
/// (`PinFollowDeadEnd`).
fn trace_for(
    comment: &CommentBox,
    page: &str,
    contained: Option<usize>,
    page_total: Option<usize>,
    recorder: &TraceRecorder,
    outcome: &Classification,
) -> PlacementTrace {
    let (strategy, placement) = match outcome {
        Classification::Placed(placed) => {
            let strategy = recorder
                .strategy()
                .unwrap_or(Strategy::Dropped(DropReason::NoCoveringStatement));
            let offset = match placed.class {
                PlacementClass::InlineAtStatement { statement_offset } => Some(statement_offset),
                _ => None,
            };
            (strategy, Some((placed.block.clone(), offset)))
        }
        Classification::Unanchored => {
            let reason = recorder
                .strategy()
                .and_then(|strategy| match strategy {
                    Strategy::Dropped(reason) => Some(reason),
                    _ => None,
                })
                .unwrap_or(DropReason::PinFollowDeadEnd);
            (Strategy::Dropped(reason), None)
        }
    };
    PlacementTrace {
        page: page.to_string(),
        snippet: super::super::audit::snippet_of(&comment.text),
        strategy,
        contained,
        page_total,
        depth: recorder.depth(),
        placement,
    }
}
