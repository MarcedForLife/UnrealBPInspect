//! Deterministic order over the placed comments before they join the plan.

use super::{PlacedComment, PlacementClass};

/// Deterministic order over placed comments.
///
/// Primary key is the block name so a block's comments group together. Within
/// a block the spec's anchor-collision tie-break applies: box `y`, then `x`,
/// then text. Inline placements additionally key on the statement offset
/// first so two anchors in the same block keep statement order.
pub(super) fn sort_placed(placed: &mut [PlacedComment]) {
    for comment in placed.iter_mut() {
        comment.locations.sort_by(|left, right| {
            left.block
                .cmp(&right.block)
                .then_with(|| class_rank(&left.class).cmp(&class_rank(&right.class)))
                .then_with(|| inline_offset(&left.class).cmp(&inline_offset(&right.class)))
                .then_with(|| inline_path(&left.class).cmp(inline_path(&right.class)))
        });
        comment.locations.dedup();
    }
    placed.sort_by(|left, right| {
        let left_location = left.locations.first();
        let right_location = right.locations.first();
        left_location
            .map(|location| &location.block)
            .cmp(&right_location.map(|location| &location.block))
            .then_with(|| {
                left_location
                    .map(|location| class_rank(&location.class))
                    .cmp(&right_location.map(|location| class_rank(&location.class)))
            })
            .then_with(|| {
                left_location
                    .map(|location| inline_offset(&location.class))
                    .cmp(&right_location.map(|location| inline_offset(&location.class)))
            })
            .then_with(|| left.box_y.cmp(&right.box_y))
            .then_with(|| left.box_x.cmp(&right.box_x))
            .then_with(|| left.text.cmp(&right.text))
    });
}

/// Stable rank so event-wrapping sorts before function-level before inline
/// within one block (header annotations precede body annotations).
fn class_rank(class: &PlacementClass) -> u8 {
    match class {
        PlacementClass::Unresolved => 3,
        PlacementClass::EventWrapping => 0,
        PlacementClass::FunctionLevel => 1,
        PlacementClass::InlineAtStatement { .. } => 2,
    }
}

/// Statement offset for inline placements, `0` for header placements (which
/// already sort ahead via `class_rank`).
fn inline_offset(class: &PlacementClass) -> usize {
    match class {
        PlacementClass::InlineAtStatement {
            statement_offset, ..
        } => *statement_offset,
        _ => 0,
    }
}

fn inline_path(class: &PlacementClass) -> &[usize] {
    match class {
        PlacementClass::InlineAtStatement { statement_path, .. } => statement_path,
        _ => &[],
    }
}
