//! The anchor strategies: resolve a contained or owner node to the statement
//! it produced, with breadth-first exec/pin-follow walks for nodes that carry
//! no byte attribution of their own.

use std::collections::BTreeSet;

use crate::bytecode::stmt::Stmt;
use crate::types::EdGraphPin;

use super::super::audit::{DropReason, Strategy};
use super::super::CommentBox;
use super::call_attribution::{
    branch_statement_for_node, call_statements_by_node, contains_statement,
};
use super::context::{node_has_external_exec_input, ClassifyContext};
use super::{Classification, PlacedComment, PlacementClass, TraceRecorder};

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
/// inside the box. Display-only EdGraph read.
pub(super) fn anchor_via_exec_follow(
    comment: &CommentBox,
    page: &str,
    contained: &[usize],
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    let contained_set: BTreeSet<usize> = contained.iter().copied().collect();
    // Seed with the entry points (already tried by the direct cascade).
    // Collect into a BTreeSet first so the walk's `visited` evolution and the
    // first frontier round stay in export-index order.
    let seed: BTreeSet<usize> = contained
        .iter()
        .copied()
        .filter(|&node| node_has_external_exec_input(node, &contained_set, context.parsed))
        .collect();
    let start: Vec<usize> = seed.into_iter().collect();
    anchor_via_link_follow(
        comment,
        page,
        &start,
        Strategy::ExecFollow,
        context,
        recorder,
        LinkWalk {
            follow_pin: EdGraphPin::is_exec_output,
            contained_set: Some(&contained_set),
        },
    )
}

/// Last-resort anchor: follow data-output pin links outward from `start`,
/// breadth-first, anchoring to the first reached node that resolves to a
/// covering statement.
///
/// This is what places a bubble on a pure node (`VariableGet`, pure
/// `CallFunction`, math operators) or a box containing only pure nodes: a
/// pure node compiles to no bytes of its own, its expression renders inside
/// the consuming statement, so the nearest resolvable consumer is the line
/// the comment annotates. Display-only EdGraph read.
pub(super) fn anchor_via_pin_follow(
    comment: &CommentBox,
    page: &str,
    start: &[usize],
    strategy: Strategy,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    anchor_via_link_follow(
        comment,
        page,
        start,
        strategy,
        context,
        recorder,
        LinkWalk {
            follow_pin: EdGraphPin::is_data_output,
            contained_set: None,
        },
    )
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
/// bubble has no box), so the walk is bounded only by graph reachability.
/// Display-only EdGraph read.
pub(super) fn anchor_via_exec_follow_outward(
    comment: &CommentBox,
    page: &str,
    owner: usize,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    anchor_via_link_follow(
        comment,
        page,
        &[owner],
        Strategy::BubbleExecFollow,
        context,
        recorder,
        LinkWalk {
            follow_pin: EdGraphPin::is_exec_output,
            contained_set: None,
        },
    )
}

/// Walk policy for [`anchor_via_link_follow`]: which output pins to follow and
/// whether to stay inside a box.
struct LinkWalk<'a> {
    follow_pin: fn(&EdGraphPin) -> bool,
    contained_set: Option<&'a BTreeSet<usize>>,
}

/// Breadth-first walk over `walk.follow_pin`-selected output links from `start`,
/// trying each reached node as an anchor. The walk is bounded by graph
/// reachability: a node enters the `visited` set once. Candidates at the
/// nearest resolvable depth must agree on one placement. Conflicting or
/// partially resolved fan-out remains unresolved instead of choosing a wire
/// by export order. The audit records the successful strategy and depth.
///
/// `walk.contained_set` bounds the walk: `None` follows every reachable link
/// (graph-reachability only), `Some(set)` follows only links whose target is
/// in `set`, keeping the walk inside a box.
fn anchor_via_link_follow(
    comment: &CommentBox,
    page: &str,
    start: &[usize],
    strategy: Strategy,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
    walk: LinkWalk,
) -> Classification {
    let LinkWalk {
        follow_pin,
        contained_set,
    } = walk;
    let mut visited: BTreeSet<usize> = start.iter().copied().collect();
    let mut frontier: Vec<usize> = start.to_vec();
    let mut depth = 0usize;
    while !frontier.is_empty() {
        depth += 1;
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
                let in_bounds = contained_set.is_none_or(|set| set.contains(&link.node));
                if in_bounds && visited.insert(link.node) {
                    next.push(link.node);
                }
            }
        }
        next.sort_unstable();
        let mut resolved: Option<Box<PlacedComment>> = None;
        let mut unmatched = false;
        for &candidate in &next {
            if let Classification::Placed(placed) =
                anchor_to_node(comment, page, candidate, strategy, context, recorder)
            {
                if placed.class == PlacementClass::Unresolved
                    || resolved.as_ref().is_some_and(|previous| {
                        previous.block != placed.block || previous.class != placed.class
                    })
                {
                    recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
                    return Classification::unresolved(comment);
                }
                resolved = Some(placed);
            } else {
                unmatched = true;
            }
        }
        if let Some(placed) = resolved {
            if unmatched {
                recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
                return Classification::unresolved(comment);
            }
            recorder.record(strategy);
            recorder.record_depth(depth);
            return Classification::Placed(placed);
        }
        frontier = next;
    }
    // Reachability exhausted with no anchor (a dead-end data/exec chain).
    recorder.record(Strategy::Dropped(DropReason::PinFollowDeadEnd));
    Classification::Unanchored
}

/// Resolve `node` (a contained or owner export) to the statement it produced
/// and build the inline placement. Returns `Unanchored` when no byte map
/// covers the node or no statement covers its range.
///
/// When `page` names a decoded block directly, the anchor resolves inside that
/// block. When it does not (an ubergraph editor page like `EventGraph` or
/// `Input`, which decoded events are not keyed by), the owning event is
/// inferred from the node's byte attribution instead.
///
/// `direct_strategy` is the audit tag the calling cascade branch wants
/// recorded when the direct-statement path resolves; the owner-event path
/// records its own (`OwnerEventStrict` / `OwnerEventPerRange`) more specific
/// tag instead. On failure it records the precise drop reason.
pub(super) fn anchor_to_node(
    comment: &CommentBox,
    page: &str,
    node: usize,
    direct_strategy: Strategy,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    let Some(body) = context.body_for_block(page) else {
        return anchor_via_owner_event(comment, node, context, recorder);
    };
    if let Some(stmt) = branch_statement_for_node(node, body, context.parsed) {
        recorder.record(direct_strategy);
        return Classification::Placed(build_inline_placement(comment, page, stmt.offset()));
    }
    if node_class(node, context.parsed).as_deref() == Some("K2Node_IfThenElse") {
        recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
        return Classification::unresolved(comment);
    }
    // Byte attribution deliberately merges ambiguous same-name calls. The
    // annotation layer can distinguish their linked data inputs without
    // changing ownership used by the decoder.
    if let Some(matches) = call_statements_by_node(node, &[body], context.parsed) {
        if let Some(stmt) = matches.get(&node) {
            recorder.record(direct_strategy);
            return Classification::Placed(build_inline_placement(comment, page, stmt.offset()));
        }
        recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
        return Classification::unresolved(comment);
    }
    let Some(byte_map) = context.byte_map_for_block(page) else {
        recorder.record(Strategy::Dropped(DropReason::NoByteMap));
        return Classification::Unanchored;
    };
    if has_ambiguous_attribution(node, byte_map, context.parsed) {
        recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
        return Classification::unresolved(comment);
    }
    let Some(stmt) = byte_map.statement_for_node(node, body) else {
        recorder.record(Strategy::Dropped(DropReason::NoCoveringStatement));
        return Classification::Unanchored;
    };
    recorder.record(direct_strategy);
    Classification::Placed(build_inline_placement(comment, page, stmt.offset()))
}

/// Match graph calls and branches within events on the source page, including
/// latent continuations. Byte ranges are a fallback for other node types.
fn anchor_via_owner_event(
    comment: &CommentBox,
    node: usize,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    let names: Vec<String> = context
        .parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let event_nodes = crate::bytecode::decode::build_event_node_index(context.parsed, &names);
    let on_page = |name: &str| {
        event_nodes.get(name).is_none_or(|&entry| {
            crate::resolve::enclosing_graph_name(context.parsed, &names, entry)
                == comment.graph_page
        })
    };
    let event_bodies: Vec<(&str, &[Stmt])> = context
        .decoded
        .events
        .iter()
        .filter(|event| on_page(&event.name))
        .map(|event| (event.name.as_str(), event.body.as_slice()))
        .chain(
            context
                .decoded
                .resume_bodies
                .iter()
                .filter_map(|(offset, body)| {
                    context
                        .decoded
                        .resume_owner_events
                        .get(offset)
                        .filter(|owner| on_page(owner))
                        .map(|owner| (owner.as_str(), body.as_slice()))
                }),
        )
        .collect();
    let bodies: Vec<&[Stmt]> = event_bodies.iter().map(|(_, body)| *body).collect();
    if let Some(matches) = call_statements_by_node(node, &bodies, context.parsed) {
        if let Some(stmt) = matches.get(&node) {
            if let Some((event_name, _)) = event_bodies
                .iter()
                .find(|(_, body)| contains_statement(body, stmt))
            {
                recorder.record(Strategy::OwnerEventStrict);
                return Classification::Placed(build_inline_placement(
                    comment,
                    event_name,
                    stmt.offset(),
                ));
            }
        }
        recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
        return Classification::unresolved(comment);
    }
    let branches: Vec<(&str, &Stmt)> = event_bodies
        .iter()
        .filter_map(|(name, body)| {
            branch_statement_for_node(node, body, context.parsed).map(|stmt| (*name, stmt))
        })
        .collect();
    if let [(name, stmt)] = branches[..] {
        recorder.record(Strategy::OwnerEventStrict);
        return Classification::Placed(build_inline_placement(comment, name, stmt.offset()));
    }
    if node_class(node, context.parsed).as_deref() == Some("K2Node_IfThenElse") {
        recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
        return Classification::unresolved(comment);
    }
    anchor_via_event_bytes(comment, node, context, recorder)
}

fn anchor_via_event_bytes(
    comment: &CommentBox,
    node: usize,
    context: &ClassifyContext,
    recorder: &TraceRecorder,
) -> Classification {
    let Some(ubergraph) = context.decoded.byte_maps.ubergraph.as_ref() else {
        recorder.record(Strategy::Dropped(DropReason::NoByteMap));
        return Classification::Unanchored;
    };
    if has_ambiguous_attribution(node, ubergraph, context.parsed) {
        recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
        return Classification::unresolved(comment);
    }
    let Some(partition) = ubergraph.partitions.get(&node) else {
        recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
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
                .filter(|event_name| {
                    partition.owner_events.is_empty()
                        || partition.owner_events.contains(*event_name)
                })
                .map(|event_name| (event_name, resume_body.as_slice()))
        })
        .collect();
    for strategy in [Strategy::OwnerEventStrict, Strategy::OwnerEventPerRange] {
        let candidates: BTreeSet<(&str, usize)> = owner_bodies
            .iter()
            .chain(&chunk_bodies)
            .filter_map(|(event_name, body)| {
                let stmt = match strategy {
                    Strategy::OwnerEventStrict => ubergraph.statement_for_node_in_span(node, body),
                    _ => ubergraph.statement_for_node_in_span_per_range(node, body),
                }?;
                Some((event_name.as_str(), stmt.offset()))
            })
            .collect();
        if candidates.len() > 1 {
            recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
            return Classification::unresolved(comment);
        }
        if let Some((event_name, offset)) = candidates.into_iter().next() {
            recorder.record(strategy);
            return Classification::Placed(build_inline_placement(comment, event_name, offset));
        }
    }
    recorder.record(Strategy::Dropped(DropReason::OwnerEventUnresolved));
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

fn node_class(node: usize, parsed: &crate::types::ParsedAsset) -> Option<String> {
    let (header, _) = parsed.exports.get(node.checked_sub(1)?)?;
    let name = if header.class_index > 0 {
        &parsed
            .exports
            .get((header.class_index - 1) as usize)?
            .0
            .object_name
    } else {
        let import = header.class_index.checked_neg()?.checked_sub(1)?;
        &parsed
            .imports
            .get(usize::try_from(import).ok()?)?
            .object_name
    };
    Some(crate::resolve::short_class(name))
}

fn has_ambiguous_attribution(
    node: usize,
    byte_map: &crate::bytecode::k2node_byte_map::K2NodeByteMap,
    parsed: &crate::types::ParsedAsset,
) -> bool {
    let Some(class) = node_class(node, parsed) else {
        return false;
    };
    if !matches!(
        class.as_str(),
        "K2Node_CallFunction" | "K2Node_VariableSet" | "K2Node_DynamicCast"
    ) {
        return false;
    }
    let Some(partition) = byte_map.partitions.get(&node) else {
        return false;
    };
    byte_map.partitions.iter().any(|(&other, candidate)| {
        other != node
            && node_class(other, parsed).as_deref() == Some(class.as_str())
            && partition.ranges.iter().any(|range| {
                candidate.ranges.iter().any(|other_range| {
                    range.start < other_range.end && other_range.start < range.end
                })
            })
    })
}
