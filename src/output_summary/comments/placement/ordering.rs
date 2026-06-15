//! Deterministic order over the placed comments before they join the plan.

use super::{PlacedComment, PlacementClass};

/// Deterministic order over placed comments.
///
/// Primary key is the block name so a block's comments group together. Within
/// a block the spec's anchor-collision tie-break applies: box `y`, then `x`,
/// then text. Inline placements additionally key on the statement offset
/// first so two anchors in the same block keep statement order.
pub(super) fn sort_placed(placed: &mut [PlacedComment]) {
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
