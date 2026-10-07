//! Whole-pipeline and unit tests for the placement cascade.

use super::*;
use crate::bytecode::asset::{Event, Function};
use crate::bytecode::decode::cross_event_inline::K2NodeClass;
use crate::bytecode::expr::Expr;
use crate::bytecode::k2node_byte_map::{ByteMaps, K2NodeByteMap, K2NodePartition};
use crate::bytecode::stmt::Stmt;
use crate::output_summary::comments::audit::DropReason;
use crate::output_summary::comments::CommentBox;
use crate::output_summary::comments::NodeGeometry;
use crate::types::{
    EdGraphPin, LinkedPin, NodePinData, PIN_DIRECTION_INPUT, PIN_DIRECTION_OUTPUT, PIN_TYPE_EXEC,
};

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
        diagnostics: Vec::new(),
        functions: vec![],
        events: vec![Event {
            name: name.into(),
            body,
            export_index: None,
        }],
        resume_bodies: Default::default(),
        resume_owner_events: Default::default(),
        byte_maps: Default::default(),
    }
}

fn empty_parsed() -> ParsedAsset {
    ParsedAsset {
        version: crate::types::AssetVersion {
            file_ver: 522,
            file_ver_ue5: 0,
        },
        name_table: crate::binary::NameTable::from_names(Vec::new()),
        diagnostics: Vec::new(),
        imports: vec![],
        exports: vec![],
        pin_data: Default::default(),
        function_signatures: Default::default(),
        bytecode_by_export: Default::default(),
    }
}

/// One exec pin in `direction`, optionally linked to `target`.
fn exec_pin(direction: u8, target: Option<usize>) -> EdGraphPin {
    EdGraphPin {
        metadata: None,
        name: "exec".into(),
        pin_type: PIN_TYPE_EXEC.into(),
        direction,
        pin_id: [0; 16],
        linked_to: target
            .map(|node| {
                vec![LinkedPin {
                    node,
                    pin_id: [0; 16],
                }]
            })
            .unwrap_or_default(),
    }
}

/// Pin data for an exec-root node: an exec-output linked to `target` and an
/// unlinked exec-input, so the node drives exec flow but is itself a source.
fn exec_root_pins(target: usize) -> NodePinData {
    NodePinData {
        pins: vec![
            exec_pin(PIN_DIRECTION_INPUT, None),
            exec_pin(PIN_DIRECTION_OUTPUT, Some(target)),
        ],
    }
}

/// Pin data for a pure node: one data-output pin linked to `target`.
fn pure_node_pins(target: usize) -> NodePinData {
    NodePinData {
        pins: vec![EdGraphPin {
            metadata: None,
            name: "Out".into(),
            pin_type: "float".into(),
            direction: PIN_DIRECTION_OUTPUT,
            pin_id: [0; 16],
            linked_to: vec![LinkedPin {
                node: target,
                pin_id: [0; 16],
            }],
        }],
    }
}

/// A decoded asset with one function whose byte map attributes
/// `attributed_node` to a disk range starting at `disk_start`.
fn decoded_with_mapped_function(
    name: &str,
    body: Vec<Stmt>,
    attributed_node: usize,
    disk_start: usize,
) -> DecodedAsset {
    let mut byte_map = K2NodeByteMap::default();
    byte_map.partitions.insert(
        attributed_node,
        K2NodePartition {
            node_id: attributed_node,
            ranges: std::iter::once(disk_start..disk_start + 4).collect(),
            owner_events: Default::default(),
            kind: K2NodeClass::Other,
            macro_kind: None,
            via_fallback: Vec::new(),
        },
    );
    let mut byte_maps = ByteMaps::default();
    byte_maps.functions.insert(name.into(), byte_map);
    DecodedAsset {
        diagnostics: Vec::new(),
        functions: vec![Function {
            name: name.into(),
            body,
            export_index: None,
        }],
        events: vec![],
        resume_bodies: Default::default(),
        resume_owner_events: Default::default(),
        byte_maps,
    }
}

#[test]
fn function_level_when_box_covers_over_threshold() {
    // Page "MyFunc" has 4 nodes; the box contains all 4 (100% > 80%) and
    // node 2 is the page's exec-root (drives exec, no incoming exec link),
    // so both halves of the promotion rule hold.
    let model = CommentModel {
        boxes: vec![box_at("whole graph desc", -10, -10, 500, 500, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 10, 10, "MyFunc"),
            node_geom(4, 20, 20, "MyFunc"),
            node_geom(5, 30, 30, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![], 2, 0);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, exec_root_pins(3));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.count_class(&PlacementClass::FunctionLevel), 1);
    assert_eq!(plan.placed[0].block, "MyFunc");
    assert_eq!(plan.placed[0].lines, vec!["    // \"whole graph desc\""]);
}

/// A box that clears the coverage threshold but contains no exec-root does
/// not promote: the structural half of the rule keeps a dense partial box
/// from being mistaken for a whole-graph description. With no byte map it
/// then drops to the unanchored count.
#[test]
fn over_threshold_without_exec_root_does_not_promote() {
    let model = CommentModel {
        boxes: vec![box_at("dense but not whole", -10, -10, 500, 500, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 10, 10, "MyFunc"),
            node_geom(4, 20, 20, "MyFunc"),
            node_geom(5, 30, 30, "MyFunc"),
        ],
    };
    let decoded = decoded_with_event("MyFunc", vec![call(0, "f")]);
    // Node 2 has an incoming exec link, so it is not a source/root; no
    // other contained node carries exec pins, so the box has no exec-root.
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(
        2,
        NodePinData {
            pins: vec![exec_pin(PIN_DIRECTION_INPUT, Some(99))],
        },
    );
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.count_class(&PlacementClass::FunctionLevel), 0);
    assert_eq!(plan.unanchored, 1);
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
    assert_eq!(plan.count_class(&PlacementClass::Unresolved), 1);
    assert_eq!(plan.unanchored, 1);
}

#[test]
fn bubble_on_pure_node_anchors_via_pin_follow() {
    // Node 2 is pure (no byte attribution); its data output feeds node 3,
    // attributed to disk bytes from 20. The bubble anchors to the
    // statement covering those bytes.
    let model = CommentModel {
        boxes: vec![CommentBox {
            text: "pure note".into(),
            x: 0,
            y: 0,
            width: 10,
            height: 10,
            is_bubble: true,
            owner_export: Some(2),
            graph_page: Some("MyFunc".into()),
        }],
        nodes: vec![],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, pure_node_pins(3));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.unanchored, 0);
    assert_eq!(plan.placed.len(), 1);
    assert_eq!(plan.placed[0].block, "MyFunc");
    assert_eq!(
        plan.placed[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 20
        }
    );
}

#[test]
fn all_pure_box_anchors_through_knot_chain() {
    // The box contains only pure node 2 (25% of the page, below the
    // coverage threshold, no exec pins). Its output reroutes through pure
    // node 9 before reaching the attributed consumer node 3 at depth 2.
    let model = CommentModel {
        boxes: vec![box_at("pure box", -5, -5, 10, 10, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 100, 100, "MyFunc"),
            node_geom(4, 200, 200, "MyFunc"),
            node_geom(5, 300, 300, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, pure_node_pins(9));
    parsed.pin_data.insert(9, pure_node_pins(3));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.unanchored, 0);
    assert_eq!(plan.placed.len(), 1);
    assert_eq!(
        plan.placed[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 20
        }
    );
}

#[test]
fn ubergraph_page_node_anchors_inside_resume_body() {
    // Node 7 compiled into a latent-resume chunk: its bytes (50..51) lie
    // in the resume body of the Delay call at offset 10, which itself
    // sits in event "Ev". The bubble's page is the ubergraph editor page
    // name, so anchoring goes through anchor_via_owner_event; the event
    // body span (10..=10) misses the node, the resume-chain search finds
    // it and keys the placement by the owning event.
    let model = CommentModel {
        boxes: vec![CommentBox {
            text: "after the delay".into(),
            x: 0,
            y: 0,
            width: 10,
            height: 10,
            is_bubble: true,
            owner_export: Some(7),
            graph_page: Some("EventGraph".into()),
        }],
        nodes: vec![],
    };
    let mut byte_map = K2NodeByteMap::default();
    byte_map.partitions.insert(
        7,
        K2NodePartition {
            node_id: 7,
            ranges: std::iter::once(50..51).collect(),
            owner_events: Default::default(),
            kind: K2NodeClass::Other,
            macro_kind: None,
            via_fallback: Vec::new(),
        },
    );
    let decoded = DecodedAsset {
        diagnostics: Vec::new(),
        functions: vec![],
        events: vec![Event {
            name: "Ev".into(),
            body: vec![call(10, "Delay")],
            export_index: None,
        }],
        resume_bodies: std::iter::once((10usize, vec![call(50, "AfterDelay")])).collect(),
        resume_owner_events: std::iter::once((10usize, "Ev".to_string())).collect(),
        byte_maps: ByteMaps {
            ubergraph: Some(byte_map),
            functions: Default::default(),
        },
    };
    let parsed = empty_parsed();
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.unanchored, 0);
    assert_eq!(plan.placed.len(), 1);
    assert_eq!(plan.placed[0].block, "Ev");
    assert_eq!(
        plan.placed[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 50
        }
    );
}

#[test]
fn knot_entry_box_anchors_via_exec_follow() {
    // Node 2 is the box's only exec entry (wired from node 99 outside)
    // but has no byte attribution (a reroute); its exec output leads to
    // contained node 3, which is attributed. The box anchors at node 3's
    // statement instead of dropping.
    let model = CommentModel {
        boxes: vec![box_at("entry is a knot", -5, -5, 120, 120, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 50, 50, "MyFunc"),
            node_geom(4, 500, 500, "MyFunc"),
            node_geom(5, 600, 600, "MyFunc"),
            node_geom(99, -300, 0, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a"), call(20, "b")], 3, 20);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(
        2,
        NodePinData {
            pins: vec![
                exec_pin(PIN_DIRECTION_INPUT, Some(99)),
                exec_pin(PIN_DIRECTION_OUTPUT, Some(3)),
            ],
        },
    );
    parsed.pin_data.insert(
        3,
        NodePinData {
            pins: vec![exec_pin(PIN_DIRECTION_INPUT, Some(2))],
        },
    );
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.unanchored, 0);
    assert_eq!(plan.placed.len(), 1);
    assert_eq!(
        plan.placed[0].class,
        PlacementClass::InlineAtStatement {
            statement_offset: 20
        }
    );
}

#[test]
fn pin_follow_dead_end_stays_unanchored() {
    // Node 2's data chain ends at node 9, which has no attribution and no
    // further links; the box drops to the unanchored count.
    let model = CommentModel {
        boxes: vec![box_at("dead end", -5, -5, 10, 10, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 100, 100, "MyFunc"),
            node_geom(4, 200, 200, "MyFunc"),
            node_geom(5, 300, 300, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a")], 3, 20);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, pure_node_pins(9));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.count_class(&PlacementClass::Unresolved), 1);
    assert_eq!(plan.unanchored, 1);
}

#[test]
fn box_without_contained_nodes_retains_its_text() {
    let model = CommentModel {
        boxes: vec![box_at("empty box", 0, 0, 5, 5, "MyFunc")],
        nodes: vec![node_geom(2, 100, 100, "MyFunc")],
    };
    let decoded = decoded_with_event("MyFunc", vec![]);
    let parsed = empty_parsed();
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.count_class(&PlacementClass::Unresolved), 1);
    assert_eq!(plan.unanchored, 1);
    assert_eq!(plan.placed[0].text, model.boxes[0].text);
}

#[test]
fn placed_comments_sorted_by_block_then_position() {
    // Both boxes cover their page's sole node (100% > 80%), and that node
    // is an exec-root, so both promote to function-level; the plan must
    // order them by block name.
    let model = CommentModel {
        boxes: vec![
            box_at("zzz", -10, -10, 500, 500, "BFunc"),
            box_at("aaa", -10, -10, 500, 500, "AFunc"),
        ],
        nodes: vec![node_geom(2, 0, 0, "AFunc"), node_geom(3, 0, 0, "BFunc")],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![], 2, 0);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, exec_root_pins(99));
    parsed.pin_data.insert(3, exec_root_pins(99));
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
    let decoded = crate::bytecode::decode::decode_asset(&parsed);
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

    // Multi-event region labels remain visible without implying ownership
    // by the first event in render order.
    assert_eq!(model.boxes.len(), 35, "DecoderTest comment-box count");
    assert_eq!(event_wrapping, 7, "EventWrapping count");
    assert_eq!(function_level, 18, "function-level count");
    assert_eq!(inline, 0, "inline count");
    assert_eq!(plan.unanchored, 10, "unresolved count");
    assert_eq!(plan.placed.len(), 35, "total placed");
}

#[test]
fn trace_records_function_level_strategy() {
    // The whole-graph box from `function_level_when_box_covers_over_threshold`
    // must be tagged `FunctionLevel` in the audit trace, with coverage
    // reconstructable from the recorded contained/page-total counts.
    let model = CommentModel {
        boxes: vec![box_at("whole graph desc", -10, -10, 500, 500, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 10, 10, "MyFunc"),
            node_geom(4, 20, 20, "MyFunc"),
            node_geom(5, 30, 30, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![], 2, 0);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, exec_root_pins(3));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.trace.len(), 1);
    assert_eq!(plan.trace[0].strategy, Strategy::FunctionLevel);
    assert_eq!(plan.trace[0].contained, Some(4));
    assert_eq!(plan.trace[0].page_total, Some(4));
    assert_eq!(plan.trace[0].depth, 0);
    assert_eq!(plan.trace[0].placement, Some(("MyFunc".to_string(), None)));
}

/// One trace entry exists per box, in box order, even for drops. The
/// dead-end box (below coverage, data chain ends unattributed) and the
/// page-less box both surface as `Dropped` traces. The page carries four
/// nodes so the single contained node stays under the coverage threshold.
#[test]
fn trace_records_drop_reasons_in_box_order() {
    let model = CommentModel {
        boxes: vec![
            box_at("dead end", -5, -5, 10, 10, "MyFunc"),
            CommentBox {
                text: "no page".into(),
                x: 0,
                y: 0,
                width: 5,
                height: 5,
                is_bubble: false,
                owner_export: None,
                graph_page: None,
            },
        ],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 100, 100, "MyFunc"),
            node_geom(4, 200, 200, "MyFunc"),
            node_geom(5, 300, 300, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![call(10, "a")], 3, 20);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, pure_node_pins(9));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.trace.len(), 2);
    assert_eq!(
        plan.trace[0].strategy,
        Strategy::Dropped(DropReason::PinFollowDeadEnd)
    );
    assert_eq!(
        plan.trace[1].strategy,
        Strategy::Dropped(DropReason::NoGraphPage)
    );
    assert_eq!(plan.trace[1].page, "<none>");
}

/// The audit must not alter `placed`/`unanchored`; the trace is a pure
/// side channel. The plan-building path is env-independent (only the
/// stderr emit reads the env var, never mutating the plan), so a baseline
/// run already establishes the placed/unanchored shape; this asserts the
/// trace rides alongside without disturbing it. Building twice must be
/// identical, including the trace.
#[test]
fn audit_trace_is_a_pure_side_channel() {
    let model = CommentModel {
        boxes: vec![box_at("whole graph desc", -10, -10, 500, 500, "MyFunc")],
        nodes: vec![
            node_geom(2, 0, 0, "MyFunc"),
            node_geom(3, 10, 10, "MyFunc"),
            node_geom(4, 20, 20, "MyFunc"),
            node_geom(5, 30, 30, "MyFunc"),
        ],
    };
    let decoded = decoded_with_mapped_function("MyFunc", vec![], 2, 0);
    let mut parsed = empty_parsed();
    parsed.pin_data.insert(2, exec_root_pins(3));

    let first = build_placement_plan(&decoded, &parsed, &[], &model);
    let second = build_placement_plan(&decoded, &parsed, &[], &model);
    // Placed/unanchored are deterministic and unaffected by the trace.
    assert_eq!(first.placed, second.placed);
    assert_eq!(first.unanchored, second.unanchored);
    // The trace is populated (one entry for the single box) and stable.
    assert_eq!(first.trace, second.trace);
    assert_eq!(first.trace.len(), 1);
    assert_eq!(first.placed.len(), 1);
    // Dropping the trace yields exactly the pre-audit plan shape.
    let mut without_trace = first.clone();
    without_trace.trace.clear();
    assert_eq!(without_trace.placed, first.placed);
    assert_eq!(without_trace.unanchored, first.unanchored);
}

#[test]
fn pure_node_fanout_does_not_choose_the_first_consumer() {
    let model = CommentModel {
        boxes: vec![CommentBox {
            is_bubble: true,
            owner_export: Some(2),
            ..box_at("shared input", 0, 0, 0, 0, "Example")
        }],
        nodes: vec![],
    };
    let mut decoded = decoded_with_mapped_function(
        "Example",
        vec![call(10, "First"), call(20, "Second")],
        3,
        10,
    );
    let byte_map = decoded.byte_maps.functions.get_mut("Example").unwrap();
    let mut second = byte_map.partitions[&3].clone();
    second.node_id = 4;
    second.ranges = std::iter::once(20..21).collect();
    byte_map.partitions.insert(4, second);
    let mut parsed = empty_parsed();
    let mut outputs = pure_node_pins(3);
    outputs.pins[0].linked_to.push(LinkedPin {
        node: 4,
        pin_id: [0; 16],
    });
    parsed.pin_data.insert(2, outputs);
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.placed.len(), 1);
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
    assert_eq!(plan.placed[0].text, "shared input");

    // A longer second path cannot make the first consumer a unique owner.
    parsed.pin_data.get_mut(&2).unwrap().pins[0].linked_to[1].node = 5;
    parsed.pin_data.insert(5, pure_node_pins(4));
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
}

#[test]
fn missing_graph_page_keeps_text_without_claiming_a_function() {
    let mut comment = box_at("author note", 0, 0, 10, 10, "Example");
    comment.graph_page = None;
    let model = CommentModel {
        boxes: vec![comment],
        nodes: vec![],
    };
    let plan = build_placement_plan(
        &decoded_with_event("Event", vec![]),
        &empty_parsed(),
        &[],
        &model,
    );
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
    assert_eq!(plan.placed[0].block, "<unknown graph>");
    assert_eq!(plan.placed[0].text, "author note");
}

#[test]
fn shared_node_does_not_choose_a_resume_owner_by_sort_order() {
    let model = CommentModel {
        boxes: vec![CommentBox {
            is_bubble: true,
            owner_export: Some(7),
            ..box_at("shared continuation", 0, 0, 0, 0, "EventGraph")
        }],
        nodes: vec![],
    };
    let mut decoded = decoded_with_mapped_function("Example", vec![], 7, 50);
    decoded.byte_maps.ubergraph = decoded.byte_maps.functions.remove("Example");
    decoded.functions.clear();
    for (name, offset) in [("First", 10), ("Second", 20)] {
        decoded.events.push(Event {
            name: name.into(),
            body: vec![],
            export_index: None,
        });
        decoded
            .resume_bodies
            .insert(offset, vec![call(50, "Shared")]);
        decoded.resume_owner_events.insert(offset, name.into());
    }
    let plan = build_placement_plan(&decoded, &empty_parsed(), &[], &model);
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
    assert_eq!(plan.placed[0].block, "EventGraph");
}

#[test]
fn box_covering_multiple_events_keeps_graph_scope() {
    use crate::types::{ExportHeader, ImportEntry, PropValue, Property};
    let mut parsed = empty_parsed();
    parsed.imports.push(ImportEntry {
        class_package: String::new(),
        class_name: "Class".into(),
        object_name: "K2Node_CustomEvent".into(),
        outer_index: 0,
    });
    let mut decoded = decoded_with_event("First", vec![]);
    decoded.events.push(Event {
        name: "Second".into(),
        body: vec![],
        export_index: None,
    });
    for name in ["First", "Second"] {
        parsed.exports.push((
            ExportHeader {
                class_index: -1,
                super_index: 0,
                outer_index: 0,
                object_name: name.into(),
                serial_offset: 0,
                serial_size: 0,
            },
            vec![Property {
                name: "CustomFunctionName".into(),
                value: PropValue::Name(name.into()),
            }],
        ));
    }
    let model = CommentModel {
        boxes: vec![box_at("Shared actions", 0, 0, 100, 100, "EventGraph")],
        nodes: vec![
            node_geom(1, 0, 0, "EventGraph"),
            node_geom(2, 50, 0, "EventGraph"),
        ],
    };
    let names = vec!["First".into(), "Second".into()];
    let plan = build_placement_plan(&decoded, &parsed, &names, &model);
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
    assert_eq!(plan.placed[0].block, "EventGraph");
    assert_eq!(plan.placed[0].text, "Shared actions");
}

#[test]
fn box_with_multiple_execution_entries_does_not_choose_by_geometry() {
    let mut decoded = decoded_with_mapped_function(
        "Example",
        vec![call(10, "First"), call(20, "Second")],
        2,
        10,
    );
    let byte_map = decoded.byte_maps.functions.get_mut("Example").unwrap();
    let mut second = byte_map.partitions[&2].clone();
    second.node_id = 3;
    second.ranges = std::iter::once(20..21).collect();
    byte_map.partitions.insert(3, second);
    let mut parsed = empty_parsed();
    for node in [2, 3] {
        parsed.pin_data.insert(
            node,
            NodePinData {
                pins: vec![exec_pin(PIN_DIRECTION_INPUT, Some(99))],
            },
        );
    }
    let model = CommentModel {
        boxes: vec![box_at("Both paths", 0, 0, 100, 100, "Example")],
        nodes: vec![
            node_geom(2, 0, 0, "Example"),
            node_geom(3, 50, 0, "Example"),
        ],
    };
    let plan = build_placement_plan(&decoded, &parsed, &[], &model);
    assert_eq!(plan.placed[0].class, PlacementClass::Unresolved);
}
