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
//! 5. `Fallback`      - no usable anchor; dropped (and counted).
//!
//! Inline and bubble placements anchor through the byte map: contained node
//! (or the bubble's owner) -> disk byte range -> covering statement -> the
//! statement's mem offset, which the emitter keys annotations by. Event and
//! function-level placements need no byte map; they key by block name and
//! attach at the block header.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::stmt::Stmt;
use crate::resolve::{resolve_index, short_class};
use crate::types::{ParsedAsset, PIN_DIRECTION_INPUT, PIN_TYPE_EXEC};

use super::render::render_comment_lines;
use super::{CommentBox, CommentModel};

/// A box covering more than this percentage of a graph page's identifiable
/// nodes is promoted to a function-level description rather than anchored
/// inline. The comparison is strictly greater-than.
const COVERAGE_THRESHOLD_PERCENT: usize = 80;

/// A box containing more than this many event-entry nodes is treated as a
/// layout divider and suppressed (a large organisational grouping, not a
/// per-event annotation). Matches the v1 `MAX_MULTI_EVENT_GROUP_SIZE`.
const MAX_MULTI_EVENT_GROUP_SIZE: usize = 3;

/// Indent applied to an event-wrapping comment, sitting directly above the
/// `EventName():` header. One summary indent level (two spaces).
const EVENT_WRAP_INDENT: &str = "  ";

/// Indent applied to a function-level description, sitting directly below the
/// block signature at body indent (two summary levels, four spaces).
const FUNCTION_LEVEL_INDENT: &str = "    ";

/// Where a placed comment attaches and how the emitter keys it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PlacementClass {
    /// Above the `EventName():` header of `block` (the owning event).
    EventWrapping,
    /// Below the block signature, as a whole-graph description.
    FunctionLevel,
    /// Above the statement at mem offset `statement_offset` in `block`'s body.
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
    let context = ClassifyContext::new(decoded, parsed, export_names);
    let mut plan = PlacementPlan::default();

    // Event-wrapping suppression is page-global: a box over more than the
    // group-size cap of event nodes is a layout divider, dropped outright.
    for comment in &model.boxes {
        match classify(comment, model, &context) {
            Some(Classification::Placed(placed)) => plan.placed.push(*placed),
            Some(Classification::Unanchored) => plan.unanchored += 1,
            Some(Classification::Suppressed) | None => {}
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
    /// Multi-event layout divider, deliberately dropped.
    Suppressed,
}

/// Per-asset lookups the classifier consults, built once.
struct ClassifyContext<'a> {
    decoded: &'a DecodedAsset,
    /// `event_node_export_index -> event_name`, for the EventWrapping check.
    event_node_to_name: BTreeMap<usize, String>,
    /// Carried byte map for statement anchoring; `None` for assets with no
    /// ubergraph (then inline placements cannot anchor and are dropped).
    byte_map: Option<&'a crate::bytecode::k2node_byte_map::UbergraphByteMap>,
    /// Pin data is read here to find a box's execution entry point.
    parsed: &'a ParsedAsset,
}

impl<'a> ClassifyContext<'a> {
    fn new(decoded: &'a DecodedAsset, parsed: &'a ParsedAsset, export_names: &[String]) -> Self {
        let event_node_to_name = build_event_node_to_name(parsed, export_names);
        ClassifyContext {
            decoded,
            event_node_to_name,
            byte_map: decoded.ubergraph_byte_map.as_ref(),
            parsed,
        }
    }

    /// Body slice for `block`, searching events first (the byte map only
    /// covers the ubergraph) then functions.
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
}

/// Classify one box. Returns `None` for a box with no graph page (cannot be
/// placed at all).
fn classify(
    comment: &CommentBox,
    model: &CommentModel,
    context: &ClassifyContext,
) -> Option<Classification> {
    let page = comment.graph_page.clone()?;

    // Bubble comments own one node; anchor to the owner's statement.
    if comment.is_bubble {
        let owner = comment.owner_export?;
        return Some(anchor_to_node(comment, &page, owner, context));
    }

    let contained = model.contained_nodes(comment);
    if contained.is_empty() {
        // A box with no contained nodes has nothing to annotate.
        return None;
    }

    // EventWrapping: the box contains one or more event-entry nodes.
    let event_nodes: Vec<&String> = contained
        .iter()
        .filter_map(|node| context.event_node_to_name.get(node))
        .collect();
    if !event_nodes.is_empty() {
        if event_nodes.len() > MAX_MULTI_EVENT_GROUP_SIZE {
            return Some(Classification::Suppressed);
        }
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
    let page_total = page_node_total(model, &page);
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
    let Some(entry) = exec_entry_point(&contained, model, context) else {
        // Self-contained block with no exec boundary crossing. v1 punted these
        // to the text-cluster fallback we deliberately do not port, so they
        // are dropped here.
        return Some(Classification::Unanchored);
    };
    Some(anchor_to_node(comment, &page, entry, context))
}

/// Resolve `node` (a contained or owner export) to the statement it produced
/// and build the inline placement. Returns `Unanchored` when no byte map
/// covers the node or no statement covers its range.
fn anchor_to_node(
    comment: &CommentBox,
    page: &str,
    node: usize,
    context: &ClassifyContext,
) -> Classification {
    let Some(byte_map) = context.byte_map else {
        return Classification::Unanchored;
    };
    let Some(body) = context.body_for_block(page) else {
        return Classification::Unanchored;
    };
    let Some(stmt) = byte_map.statement_for_node(node, body) else {
        return Classification::Unanchored;
    };
    Classification::Placed(build_inline_placement(comment, page, stmt.offset()))
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

/// Number of identifiable nodes on `page`, the coverage-rule denominator.
fn page_node_total(model: &CommentModel, page: &str) -> usize {
    model
        .nodes
        .iter()
        .filter(|node| node.graph_page.as_deref() == Some(page))
        .count()
}

/// The top-left contained node whose input exec pin links to a node outside
/// the contained set (the box's execution entry point). Ties broken by
/// `(y, x)` then export index, matching v1's top-to-bottom order.
fn exec_entry_point(
    contained: &[usize],
    model: &CommentModel,
    context: &ClassifyContext,
) -> Option<usize> {
    let contained_set: BTreeSet<usize> = contained.iter().copied().collect();
    let mut entries: Vec<(i32, i32, usize)> = Vec::new();
    for &node in contained {
        if node_has_external_exec_input(node, &contained_set, context.parsed) {
            let (x, y) = node_position(model, node);
            entries.push((y, x, node));
        }
    }
    entries.sort_unstable();
    entries.first().map(|&(_, _, node)| node)
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
        .filter(|pin| pin.pin_type == PIN_TYPE_EXEC && pin.direction == PIN_DIRECTION_INPUT)
        .flat_map(|pin| pin.linked_to.iter())
        .any(|link| !contained.contains(&link.node))
}

/// `(x, y)` of `node` from the model geometry, defaulting to `(0, 0)`.
fn node_position(model: &CommentModel, node: usize) -> (i32, i32) {
    model
        .nodes
        .iter()
        .find(|geometry| geometry.export_index == node)
        .map(|geometry| (geometry.x, geometry.y))
        .unwrap_or((0, 0))
}

/// Map each event-entry node export index to its event name.
fn build_event_node_to_name(
    parsed: &ParsedAsset,
    export_names: &[String],
) -> BTreeMap<usize, String> {
    use crate::prop_query::find_prop;
    use crate::types::PropValue;

    const EVENT_CLASSES_WITH_FUNCTION_NAME: [&str; 3] = [
        "K2Node_CustomEvent",
        "K2Node_InputAxisEvent",
        "K2Node_ComponentBoundEvent",
    ];

    let mut map = BTreeMap::new();
    for (zero_based, (hdr, props)) in parsed.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class = short_class(&resolve_index(
            &parsed.imports,
            export_names,
            hdr.class_index,
        ));
        let event_name = if EVENT_CLASSES_WITH_FUNCTION_NAME.contains(&class.as_str()) {
            match find_prop(props, "CustomFunctionName").map(|prop| &prop.value) {
                Some(PropValue::Name(name)) => Some(name.clone()),
                _ => None,
            }
        } else if class == "K2Node_Event" {
            find_prop(props, "EventReference")
                .and_then(|prop| match &prop.value {
                    PropValue::Struct { fields, .. } => find_prop(fields, "MemberName"),
                    _ => None,
                })
                .and_then(|prop| match &prop.value {
                    PropValue::Name(name) => Some(name.clone()),
                    _ => None,
                })
        } else {
            None
        };
        if let Some(name) = event_name {
            map.insert(one_based, name);
        }
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
    use crate::bytecode::asset::Event;
    use crate::bytecode::expr::Expr;
    use crate::output_summary::comments::NodeGeometry;

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
            ubergraph_byte_map: None,
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
            ubergraph_byte_map: None,
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
            ubergraph_byte_map: None,
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

        // Matches the v1 binary exactly: 14 EventWrapping, 18 function-level,
        // 0 inline. The remaining 3 of 35 boxes ("Latches and delays",
        // "Cross-event convergence", "Complex nested symetrical flow gates
        // with event convergence") are multi-event region boxes containing 5,
        // 10, and 4 event nodes, all over MAX_MULTI_EVENT_GROUP_SIZE, so the
        // layout-divider suppression drops them (v1 reported 32 comment runs
        // likewise).
        assert_eq!(model.boxes.len(), 35, "DecoderTest comment-box count");
        assert_eq!(event_wrapping, 14, "EventWrapping count");
        assert_eq!(function_level, 18, "function-level count");
        assert_eq!(inline, 0, "inline count");
        assert_eq!(plan.unanchored, 0, "unanchored count");
        assert_eq!(plan.placed.len(), 32, "total placed");
    }
}
