//! Build the [`CommentModel`] from already-parsed export data.
//!
//! This is pure parsing over the tagged-property streams the parser already
//! retained in `ParsedAsset.exports`; it adds no new disk reads. It produces
//! the comment boxes (and bubbles) plus the geometry of every other graph
//! node so the model can answer spatial-containment queries.

use super::{CommentBox, CommentModel, NodeGeometry, EDGRAPH_NODE_COMMENT_CLASS};
use crate::prop_query::{find_prop, find_prop_i32, find_prop_str};
use crate::resolve::{enclosing_graph_name, resolve_index, short_class};
use crate::types::{ParsedAsset, PropValue, Property};

/// Reroute (knot) nodes label wire routing, not logic, so their bubble
/// comments are dropped during extraction.
const K2NODE_KNOT_CLASS: &str = "K2Node_Knot";

/// Class of the per-page graph container. Its `object_name` is the page name
/// every node on it resolves to; the container itself is not a node.
const EDGRAPH_CLASS: &str = "EdGraph";

/// Build the comment model for `parsed`.
///
/// `export_names` is the parallel object-name vector used to resolve class and
/// owner indices (same vector the emit prefix pass builds). One pass over the
/// exports classifies each into a box comment, a bubble comment, or an
/// ordinary positioned node; the boxes and node geometry are returned together.
pub(crate) fn build_comment_model(parsed: &ParsedAsset, export_names: &[String]) -> CommentModel {
    let mut model = CommentModel::default();
    for (zero_based, (hdr, props)) in parsed.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class = short_class(&resolve_index(
            &parsed.imports,
            export_names,
            hdr.class_index,
        ));

        // The EdGraph page export is the container, not a node on a page;
        // `enclosing_graph_name` would resolve it to itself, so skip it
        // outright.
        if class == EDGRAPH_CLASS {
            continue;
        }

        let page = enclosing_graph_name(parsed, export_names, one_based);

        if class == EDGRAPH_NODE_COMMENT_CLASS {
            if let Some(comment) = box_comment(props, page.clone()) {
                model.boxes.push(comment);
            }
            // A box comment carries no exec/data role, so it is not added to
            // the node-geometry set.
            continue;
        }

        // Only exports that resolve to an owning EdGraph page are graph nodes;
        // this drops the Blueprint class, variables, and functions, which have
        // no EdGraph ancestor.
        let Some(page) = page else {
            continue;
        };

        // Ordinary node: record its geometry for containment tests, and lift a
        // visible bubble comment if it has one.
        let (x, y) = node_pos(props);
        model.nodes.push(NodeGeometry {
            export_index: one_based,
            x,
            y,
            graph_page: Some(page.clone()),
        });

        if class != K2NODE_KNOT_CLASS {
            if let Some(bubble) = bubble_comment(props, one_based, x, y, Some(page)) {
                model.boxes.push(bubble);
            }
        }
    }
    model
}

/// Read `NodePosX`/`NodePosY`, defaulting either to 0 when absent (the editor
/// omits a coordinate that is zero).
fn node_pos(props: &[Property]) -> (i32, i32) {
    (
        find_prop_i32(props, "NodePosX").unwrap_or(0),
        find_prop_i32(props, "NodePosY").unwrap_or(0),
    )
}

/// Lift a dedicated `EdGraphNode_Comment` export into a [`CommentBox`].
/// Returns `None` when the export has no `NodeComment` text.
fn box_comment(props: &[Property], page: Option<String>) -> Option<CommentBox> {
    let text = find_prop_str(props, "NodeComment")?;
    if text.is_empty() {
        return None;
    }
    let (x, y) = node_pos(props);
    Some(CommentBox {
        text,
        x,
        y,
        width: find_prop_i32(props, "NodeWidth").unwrap_or(0),
        height: find_prop_i32(props, "NodeHeight").unwrap_or(0),
        is_bubble: false,
        owner_export: None,
        graph_page: page,
    })
}

/// Lift a bubble comment from an ordinary node, gated on `bCommentBubbleVisible`.
/// Bubbles are point-anchored (zero size) and own the node they sit on.
fn bubble_comment(
    props: &[Property],
    owner_one_based: usize,
    x: i32,
    y: i32,
    page: Option<String>,
) -> Option<CommentBox> {
    if !find_prop_bool(props, "bCommentBubbleVisible").unwrap_or(false) {
        return None;
    }
    let text = find_prop_str(props, "NodeComment")?;
    if text.is_empty() {
        return None;
    }
    Some(CommentBox {
        text,
        x,
        y,
        width: 0,
        height: 0,
        is_bubble: true,
        owner_export: Some(owner_one_based),
        graph_page: page,
    })
}

/// Read a boolean tagged property by name.
fn find_prop_bool(props: &[Property], name: &str) -> Option<bool> {
    match &find_prop(props, name)?.value {
        PropValue::Bool(value) => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ExportHeader, ImportEntry};

    fn str_prop(name: &str, value: &str) -> Property {
        Property {
            name: name.into(),
            value: PropValue::Str(value.into()),
        }
    }

    fn int_prop(name: &str, value: i32) -> Property {
        Property {
            name: name.into(),
            value: PropValue::Int(value),
        }
    }

    fn bool_prop(name: &str, value: bool) -> Property {
        Property {
            name: name.into(),
            value: PropValue::Bool(value),
        }
    }

    fn header(class_index: i32, outer_index: i32, name: &str) -> ExportHeader {
        ExportHeader {
            class_index,
            super_index: 0,
            outer_index,
            object_name: name.into(),
            serial_offset: 0,
            serial_size: 0,
        }
    }

    /// Build a tiny asset: export 1 is the EdGraph page, exports 2.. are nodes
    /// whose `class_index` points at an import. Import -1 names the class.
    fn asset(
        page_name: &str,
        node_class: &str,
        nodes: Vec<Vec<Property>>,
    ) -> (ParsedAsset, Vec<String>) {
        let imports = vec![
            ImportEntry {
                class_package: "/Script/Engine".into(),
                class_name: "Class".into(),
                object_name: "EdGraph".into(),
                outer_index: 0,
            },
            ImportEntry {
                class_package: "/Script/BlueprintGraph".into(),
                class_name: "Class".into(),
                object_name: node_class.into(),
                outer_index: 0,
            },
        ];
        // class_index -1 => imports[0] (EdGraph), -2 => imports[1] (node class).
        let mut exports = vec![(header(-1, 0, page_name), Vec::new())];
        for node_props in nodes {
            exports.push((header(-2, 1, "node"), node_props));
        }
        let export_names: Vec<String> = exports
            .iter()
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        let parsed = ParsedAsset {
            imports,
            exports,
            pin_data: Default::default(),
            function_signatures: Default::default(),
            bytecode_by_export: Default::default(),
        };
        (parsed, export_names)
    }

    #[test]
    fn box_comment_extracted_with_geometry_and_page() {
        // Export 2 is a comment box on page "EventGraph".
        let imports = vec![
            ImportEntry {
                class_package: "/Script/Engine".into(),
                class_name: "Class".into(),
                object_name: "EdGraph".into(),
                outer_index: 0,
            },
            ImportEntry {
                class_package: "/Script/UnrealEd".into(),
                class_name: "Class".into(),
                object_name: EDGRAPH_NODE_COMMENT_CLASS.into(),
                outer_index: 0,
            },
        ];
        let exports = vec![
            (header(-1, 0, "EventGraph"), Vec::new()),
            (
                header(-2, 1, "EdGraphNode_Comment_0"),
                vec![
                    int_prop("NodePosX", -54),
                    int_prop("NodePosY", -62),
                    int_prop("NodeWidth", 944),
                    int_prop("NodeHeight", 400),
                    str_prop("NodeComment", "A cast with both pins wired"),
                ],
            ),
        ];
        let export_names: Vec<String> = exports
            .iter()
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        let parsed = ParsedAsset {
            imports,
            exports,
            pin_data: Default::default(),
            function_signatures: Default::default(),
            bytecode_by_export: Default::default(),
        };

        let model = build_comment_model(&parsed, &export_names);
        assert_eq!(model.boxes.len(), 1);
        let comment = &model.boxes[0];
        assert_eq!(comment.text, "A cast with both pins wired");
        assert_eq!((comment.x, comment.y), (-54, -62));
        assert_eq!((comment.width, comment.height), (944, 400));
        assert!(!comment.is_bubble);
        assert_eq!(comment.owner_export, None);
        assert_eq!(comment.graph_page.as_deref(), Some("EventGraph"));
        // The comment box itself is not added to the node-geometry set.
        assert!(model.nodes.is_empty());
    }

    #[test]
    fn ordinary_node_geometry_recorded_with_default_y() {
        // Node carries NodePosX but no NodePosY (editor omits zero).
        let (parsed, names) = asset(
            "MyFunc",
            "K2Node_CallFunction",
            vec![vec![int_prop("NodePosX", 352)]],
        );
        let model = build_comment_model(&parsed, &names);
        assert!(model.boxes.is_empty());
        assert_eq!(model.nodes.len(), 1);
        assert_eq!(model.nodes[0].export_index, 2);
        assert_eq!((model.nodes[0].x, model.nodes[0].y), (352, 0));
        assert_eq!(model.nodes[0].graph_page.as_deref(), Some("MyFunc"));
    }

    #[test]
    fn visible_bubble_lifted_and_owned() {
        let (parsed, names) = asset(
            "EventGraph",
            "K2Node_CallFunction",
            vec![vec![
                int_prop("NodePosX", 10),
                int_prop("NodePosY", 20),
                bool_prop("bCommentBubbleVisible", true),
                str_prop("NodeComment", "bubble text"),
            ]],
        );
        let model = build_comment_model(&parsed, &names);
        assert_eq!(model.boxes.len(), 1);
        let bubble = &model.boxes[0];
        assert!(bubble.is_bubble);
        assert_eq!(bubble.owner_export, Some(2));
        assert_eq!((bubble.width, bubble.height), (0, 0));
        assert_eq!(bubble.text, "bubble text");
    }

    #[test]
    fn hidden_bubble_dropped_geometry_kept() {
        let (parsed, names) = asset(
            "EventGraph",
            "K2Node_CallFunction",
            vec![vec![
                int_prop("NodePosX", 10),
                bool_prop("bCommentBubbleVisible", false),
                str_prop("NodeComment", "hidden"),
            ]],
        );
        let model = build_comment_model(&parsed, &names);
        assert!(model.boxes.is_empty());
        assert_eq!(model.nodes.len(), 1);
    }

    #[test]
    fn knot_bubble_dropped() {
        let (parsed, names) = asset(
            "EventGraph",
            K2NODE_KNOT_CLASS,
            vec![vec![
                bool_prop("bCommentBubbleVisible", true),
                str_prop("NodeComment", "reroute label"),
            ]],
        );
        let model = build_comment_model(&parsed, &names);
        assert!(model.boxes.is_empty());
        // The knot's geometry is still recorded for containment.
        assert_eq!(model.nodes.len(), 1);
    }

    #[test]
    fn empty_comment_text_dropped() {
        let imports = vec![
            ImportEntry {
                class_package: "/Script/Engine".into(),
                class_name: "Class".into(),
                object_name: "EdGraph".into(),
                outer_index: 0,
            },
            ImportEntry {
                class_package: "/Script/UnrealEd".into(),
                class_name: "Class".into(),
                object_name: EDGRAPH_NODE_COMMENT_CLASS.into(),
                outer_index: 0,
            },
        ];
        let exports = vec![
            (header(-1, 0, "EventGraph"), Vec::new()),
            (
                header(-2, 1, "EdGraphNode_Comment_0"),
                vec![str_prop("NodeComment", "")],
            ),
        ];
        let export_names: Vec<String> = exports
            .iter()
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        let parsed = ParsedAsset {
            imports,
            exports,
            pin_data: Default::default(),
            function_signatures: Default::default(),
            bytecode_by_export: Default::default(),
        };
        let model = build_comment_model(&parsed, &export_names);
        assert!(model.boxes.is_empty());
    }
}
