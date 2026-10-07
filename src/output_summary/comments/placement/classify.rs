//! The first-match cascade: route one box through EventWrapping, FunctionLevel,
//! and the inline/bubble anchor strategies, and build the audit trace.

use super::super::audit::{DropReason, PlacementTrace, Strategy};
use super::super::render::render_comment_lines;
use super::super::{CommentBox, CommentModel};
use super::anchor::{
    anchor_to_node, anchor_via_exec_follow, anchor_via_exec_follow_outward, anchor_via_pin_follow,
};
use super::context::{box_contains_exec_root, sorted_exec_entries, ClassifyContext};
use super::{Classification, CommentLocation, PlacedComment, PlacementClass, TraceRecorder};

/// Coverage half of the function-level promotion rule: a box must cover more
/// than this percentage of a graph page's identifiable nodes (strictly
/// greater-than) AND contain the page's exec-root (see
/// [`box_contains_exec_root`]) to promote to a whole-graph description.
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

    // A box can describe several independently identified event headers.
    let event_nodes: Vec<&String> = contained
        .iter()
        .filter_map(|node| context.event_node_to_name.get(node))
        .collect();
    if !event_nodes.is_empty() {
        // A single InputAction node can back several events. Keep every
        // event identity when deciding whether a box has one clear owner.
        let names: Vec<String> = context
            .parsed
            .exports
            .iter()
            .map(|(header, _)| header.object_name.clone())
            .collect();
        let events: Vec<String> =
            crate::bytecode::decode::build_event_node_index(context.parsed, &names)
                .into_iter()
                .filter(|(_, node)| contained.contains(node))
                .map(|(name, _)| name)
                .collect();
        if events.is_empty()
            || events.iter().any(|name| {
                !context
                    .decoded
                    .events
                    .iter()
                    .any(|event| event.name == *name)
            })
        {
            recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
            return finish_box(Classification::unresolved(comment));
        }
        let lines = render_comment_lines(&comment.text, EVENT_WRAP_INDENT);
        recorder.record(Strategy::EventWrapping);
        let outcome = Classification::Placed(Box::new(PlacedComment {
            locations: events
                .into_iter()
                .map(|block| CommentLocation {
                    block,
                    class: PlacementClass::EventWrapping,
                })
                .collect(),
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
        && context.body_for_block(&page).is_some()
    {
        let lines = render_comment_lines(&comment.text, FUNCTION_LEVEL_INDENT);
        recorder.record(Strategy::FunctionLevel);
        let outcome = Classification::Placed(Box::new(PlacedComment {
            locations: vec![CommentLocation {
                block: page.clone(),
                class: PlacementClass::FunctionLevel,
            }],
            lines,
            box_x: comment.x,
            box_y: comment.y,
            text: comment.text.clone(),
        }));
        return finish_box(outcome);
    }

    // Every independent entry must resolve. Keep separate locations instead
    // of pretending that the statements between them belong to the box.
    let entries = sorted_exec_entries(&contained, context);
    if entries.len() > 1 {
        let mut combined: Option<Box<PlacedComment>> = None;
        for entry in &entries {
            let Classification::Placed(placed) = anchor_to_node(
                comment,
                &page,
                *entry,
                Strategy::InlineEntry,
                context,
                &recorder,
            ) else {
                return finish_box(Classification::unresolved(comment));
            };
            if placed
                .locations
                .iter()
                .any(|location| location.class == PlacementClass::Unresolved)
            {
                return finish_box(Classification::unresolved(comment));
            }
            if let Some(combined) = &mut combined {
                combined.locations.extend(placed.locations);
            } else {
                combined = Some(placed);
            }
        }
        if let Some(combined) = combined {
            return finish_box(Classification::Placed(combined));
        }
    }

    // InlineAtEntry: anchor to the top-left execution entry point of the box.
    let outcome = match entries.first().copied() {
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
        // Follow a unique entry through routing nodes when it has no direct
        // statement, then try data consumers if execution evidence runs out.
        Some(entry) => anchor_to_node(
            comment,
            &page,
            entry,
            Strategy::InlineEntry,
            context,
            &recorder,
        )
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
        locations: Vec::new(),
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
    let (strategy, locations) = match outcome {
        Classification::Placed(placed) => {
            let strategy = if placed
                .locations
                .iter()
                .any(|location| location.class == PlacementClass::Unresolved)
            {
                match recorder.strategy() {
                    Some(Strategy::Dropped(reason)) => Strategy::Dropped(reason),
                    _ => Strategy::Dropped(DropReason::NoCoveringStatement),
                }
            } else {
                recorder
                    .strategy()
                    .unwrap_or(Strategy::Dropped(DropReason::NoCoveringStatement))
            };
            let locations = placed
                .locations
                .iter()
                .filter(|location| location.class != PlacementClass::Unresolved)
                .cloned()
                .collect();
            (strategy, locations)
        }
        Classification::Unanchored => {
            let reason = recorder
                .strategy()
                .and_then(|strategy| match strategy {
                    Strategy::Dropped(reason) => Some(reason),
                    _ => None,
                })
                .unwrap_or(DropReason::PinFollowDeadEnd);
            (Strategy::Dropped(reason), Vec::new())
        }
    };
    PlacementTrace {
        page: page.to_string(),
        snippet: super::super::audit::snippet_of(&comment.text),
        strategy,
        contained,
        page_total,
        depth: recorder.depth(),
        locations,
    }
}
