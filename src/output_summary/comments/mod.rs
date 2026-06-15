//! EdGraph comment-box extraction model.
//!
//! Comment annotations in the Blueprint (Unreal Blueprint) editor are stored
//! as `EdGraphNode_Comment` exports (box comments) and as `NodeComment`
//! strings on ordinary nodes with the bubble flag set (bubble comments). This
//! module lifts those into a typed model that downstream placement can query,
//! independent of how the comment is later rendered.
//!
//! The model carries two kinds of geometry:
//!
//! - [`CommentBox`], one per comment, with its rectangle, owning graph page,
//!   and bubble metadata.
//! - [`NodeGeometry`], the position of every other graph node, so a box can
//!   be tested for which nodes it spatially contains.
//!
//! Containment is page-scoped (a box only contains nodes drawn on the same
//! graph page) and inclusive on all four edges, matching the editor convention
//! where a box is anchored top-left and width/height grow right and down
//! (`+Y` is down).
//!
//! The [`placement`] submodule classifies each box into an event-wrapping,
//! function-level, or inline placement and resolves its anchor; [`render`]
//! formats a box's text into the summary marker lines. The summary emitter
//! consumes the placement plan via `bytecode::emit::comments`. A few
//! diagnostic accessors (`PlacementPlan::count_class`, the `unanchored`
//! count) are read only from tests, so the module keeps the dead-code allow.
#![allow(dead_code)]

pub(crate) mod audit;
pub(crate) mod extract;
pub(crate) mod placement;
pub(crate) mod render;

/// Class name of the dedicated box-comment export. Bubble comments live on
/// ordinary node exports and are recognised by their bubble-visibility flag
/// rather than this class.
pub(crate) const EDGRAPH_NODE_COMMENT_CLASS: &str = "EdGraphNode_Comment";

/// A single comment annotation lifted from one EdGraph export.
///
/// Box comments (`EdGraphNode_Comment`) carry a real `width`/`height`; bubble
/// comments are point-anchored and report a zero-size rectangle with
/// `owner_export` set to the node they annotate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommentBox {
    /// The comment text (`NodeComment`). Never empty; empty-text exports are
    /// dropped during extraction.
    pub text: String,
    /// Top-left corner X (`NodePosX`, editor units; default 0).
    pub x: i32,
    /// Top-left corner Y (`NodePosY`, editor units; default 0, `+Y` is down).
    pub y: i32,
    /// Box width (`NodeWidth`; 0 for bubble comments).
    pub width: i32,
    /// Box height (`NodeHeight`; 0 for bubble comments).
    pub height: i32,
    /// True for a bubble comment (a `NodeComment` on a non-comment node with
    /// `bCommentBubbleVisible`), false for a dedicated box comment.
    pub is_bubble: bool,
    /// 1-based export index of the node this bubble annotates, or `None` for
    /// box comments (which annotate by spatial containment, not ownership).
    pub owner_export: Option<usize>,
    /// Owning graph page (the `object_name` of the EdGraph ancestor export),
    /// e.g. `"EventGraph"`, `"BeginPlay"`, or a function name. `None` when the
    /// owning page could not be resolved from the outer chain.
    pub graph_page: Option<String>,
}

impl CommentBox {
    /// Whether point `(px, py)` lies inside the box, **inclusive on all four
    /// edges**. Box comments only; bubble comments have a zero-size rectangle
    /// and are never used for containment.
    pub fn contains_point(&self, px: i32, py: i32) -> bool {
        px >= self.x
            && py >= self.y
            && px <= self.x.saturating_add(self.width)
            && py <= self.y.saturating_add(self.height)
    }
}

/// Position of one ordinary graph node, used to test box containment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NodeGeometry {
    /// 1-based export index of the node.
    pub export_index: usize,
    /// Node top-left corner X (`NodePosX`; default 0).
    pub x: i32,
    /// Node top-left corner Y (`NodePosY`; default 0).
    pub y: i32,
    /// Owning graph page, resolved the same way as [`CommentBox::graph_page`].
    pub graph_page: Option<String>,
}

/// The extracted comment model for one asset: every comment box plus the
/// geometry of every other graph node on every page.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CommentModel {
    pub boxes: Vec<CommentBox>,
    pub nodes: Vec<NodeGeometry>,
}

impl CommentModel {
    /// Export indices of nodes spatially contained by `comment`, restricted to
    /// the comment's own graph page. Inclusive on all four edges. Returns an
    /// empty vector for bubble comments and for comments with no resolved page.
    ///
    /// Results are sorted by export index so the output is deterministic
    /// regardless of node-extraction order.
    pub fn contained_nodes(&self, comment: &CommentBox) -> Vec<usize> {
        if comment.is_bubble {
            return Vec::new();
        }
        let Some(page) = comment.graph_page.as_deref() else {
            return Vec::new();
        };
        let mut contained: Vec<usize> = self
            .nodes
            .iter()
            .filter(|node| node.graph_page.as_deref() == Some(page))
            .filter(|node| comment.contains_point(node.x, node.y))
            .map(|node| node.export_index)
            .collect();
        contained.sort_unstable();
        contained
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn box_at(x: i32, y: i32, width: i32, height: i32, page: &str) -> CommentBox {
        CommentBox {
            text: "c".into(),
            x,
            y,
            width,
            height,
            is_bubble: false,
            owner_export: None,
            graph_page: Some(page.into()),
        }
    }

    fn node_at(export_index: usize, x: i32, y: i32, page: &str) -> NodeGeometry {
        NodeGeometry {
            export_index,
            x,
            y,
            graph_page: Some(page.into()),
        }
    }

    #[test]
    fn contains_point_is_inclusive_on_all_edges() {
        let comment = box_at(10, 20, 100, 40, "EventGraph");
        // Corners are inside.
        assert!(comment.contains_point(10, 20)); // top-left
        assert!(comment.contains_point(110, 20)); // top-right (x + width)
        assert!(comment.contains_point(10, 60)); // bottom-left (y + height)
        assert!(comment.contains_point(110, 60)); // bottom-right
                                                  // Interior.
        assert!(comment.contains_point(55, 40));
        // Just outside each edge.
        assert!(!comment.contains_point(9, 40)); // left of x
        assert!(!comment.contains_point(111, 40)); // right of x + width
        assert!(!comment.contains_point(55, 19)); // above y
        assert!(!comment.contains_point(55, 61)); // below y + height
    }

    #[test]
    fn contains_point_handles_negative_origin() {
        // Editor positions are commonly negative; the DecoderTest box is at
        // (-54, -62) with size 944x400.
        let comment = box_at(-54, -62, 944, 400, "EventGraph");
        assert!(comment.contains_point(-54, -62));
        assert!(comment.contains_point(890, 338)); // -54+944, -62+400
        assert!(!comment.contains_point(-55, -62));
        assert!(!comment.contains_point(891, 338));
    }

    #[test]
    fn contained_nodes_are_page_scoped() {
        let model = CommentModel {
            boxes: vec![],
            nodes: vec![
                node_at(2, 50, 50, "EventGraph"),   // inside, same page
                node_at(3, 50, 50, "OtherPage"),    // inside rect, wrong page
                node_at(4, 500, 500, "EventGraph"), // same page, outside rect
            ],
        };
        let comment = box_at(0, 0, 100, 100, "EventGraph");
        assert_eq!(model.contained_nodes(&comment), vec![2]);
    }

    #[test]
    fn contained_nodes_sorted_regardless_of_input_order() {
        let model = CommentModel {
            boxes: vec![],
            nodes: vec![
                node_at(9, 10, 10, "G"),
                node_at(3, 20, 20, "G"),
                node_at(7, 30, 30, "G"),
            ],
        };
        let comment = box_at(0, 0, 100, 100, "G");
        assert_eq!(model.contained_nodes(&comment), vec![3, 7, 9]);
    }

    #[test]
    fn contained_nodes_empty_for_bubble() {
        let model = CommentModel {
            boxes: vec![],
            nodes: vec![node_at(2, 50, 50, "G")],
        };
        let mut bubble = box_at(0, 0, 100, 100, "G");
        bubble.is_bubble = true;
        bubble.owner_export = Some(2);
        assert!(model.contained_nodes(&bubble).is_empty());
    }

    #[test]
    fn contained_nodes_empty_when_page_unresolved() {
        let model = CommentModel {
            boxes: vec![],
            nodes: vec![node_at(2, 50, 50, "G")],
        };
        let mut comment = box_at(0, 0, 100, 100, "G");
        comment.graph_page = None;
        assert!(model.contained_nodes(&comment).is_empty());
    }
}
