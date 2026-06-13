//! Carry the ubergraph [`K2NodeByteMap`] outward from decode to emit, with a
//! node-to-statement covering lookup.
//!
//! The byte map is built during decode and keyed in disk coordinates
//! ([`K2NodePartition::ranges`]). Statement offsets
//! ([`crate::bytecode::stmt::Stmt::offset`]) are serialized-byte (disk)
//! positions too (the same coordinate `resume_bodies` is keyed by), so a
//! node's first attributed disk byte matches statement offsets directly and
//! the lookup is a covering walk over the decoded body, no translation.

use std::collections::BTreeMap;

use crate::bytecode::stmt::Stmt;

use super::K2NodeByteMap;

/// All carried byte maps for one asset: the ubergraph map plus one map per
/// standalone function graph.
///
/// Comment boxes live on a graph page that is either an ubergraph event page
/// or a standalone function page. Events resolve through the single ubergraph
/// map; functions each have their own map, keyed by function name, so a box on
/// a function page anchors against the bytes that function compiled rather than
/// the ubergraph's. Built once per asset during decode and carried on
/// [`crate::bytecode::asset::DecodedAsset`].
#[derive(Default)]
pub(crate) struct ByteMaps {
    /// Ubergraph attribution, `None` for assets with no ubergraph.
    pub ubergraph: Option<UbergraphByteMap>,
    /// Per-function attribution, keyed by function name (the standalone graph
    /// page a comment box reports). `BTreeMap` for deterministic iteration.
    pub functions: BTreeMap<String, UbergraphByteMap>,
}

impl ByteMaps {
    /// The byte map covering `block`, an event name (ubergraph) or a function
    /// name. Events fall back to the single ubergraph map; functions select
    /// their own. Returns `None` when no map covers the block.
    pub fn for_function(&self, function_name: &str) -> Option<&UbergraphByteMap> {
        self.functions.get(function_name)
    }
}

/// One graph's byte map with node-to-statement lookups for emit.
///
/// Built once per asset during ubergraph decode and carried on
/// [`crate::bytecode::asset::DecodedAsset`]. Standalone function bodies carry
/// their own instance in [`ByteMaps::functions`].
pub(crate) struct UbergraphByteMap {
    /// Node-id to disk-byte-range attribution for the graph's script stream.
    pub byte_map: K2NodeByteMap,
}

impl UbergraphByteMap {
    pub fn new(byte_map: K2NodeByteMap) -> Self {
        UbergraphByteMap { byte_map }
    }

    /// The statement in `body` produced by graph node `node_id`, if the node
    /// has a disk-range attribution and a covering statement exists.
    ///
    /// `body` is one decoded function or event body. The node's first disk
    /// byte is matched against the statement tree; the deepest statement
    /// whose offset is at or below it wins (see [`covering_statement`]).
    pub fn statement_for_node<'body>(
        &self,
        node_id: usize,
        body: &'body [Stmt],
    ) -> Option<&'body Stmt> {
        let anchor_disk = self.node_anchor_disk(node_id)?;
        covering_statement(body, anchor_disk)
    }

    /// Like [`Self::statement_for_node`], but only when the node's disk
    /// anchor falls inside `body`'s statement-offset span.
    ///
    /// Used when the owning block is inferred (a comment box on
    /// an ubergraph editor page resolved through the partition's owner
    /// events) rather than named directly: the span requirement stops a
    /// multi-owner node from anchoring into a sibling event whose offsets
    /// all precede the target.
    pub fn statement_for_node_in_span<'body>(
        &self,
        node_id: usize,
        body: &'body [Stmt],
    ) -> Option<&'body Stmt> {
        let anchor_disk = self.node_anchor_disk(node_id)?;
        let (span_min, span_max) = body_offset_span(body)?;
        if !(span_min..=span_max).contains(&anchor_disk) {
            return None;
        }
        covering_statement(body, anchor_disk)
    }

    /// The node's anchor coordinate: the first disk byte of its attributed
    /// ranges.
    fn node_anchor_disk(&self, node_id: usize) -> Option<usize> {
        let partition = self.byte_map.partitions.get(&node_id)?;
        partition.ranges.iter().map(|range| range.start).min()
    }
}

/// Minimum and maximum statement offsets across `body` and every nested child
/// body. `None` for an empty body.
fn body_offset_span(body: &[Stmt]) -> Option<(usize, usize)> {
    let mut span: Option<(usize, usize)> = None;
    let mut merge = |lo: usize, hi: usize| {
        span = Some(match span {
            Some((cur_lo, cur_hi)) => (cur_lo.min(lo), cur_hi.max(hi)),
            None => (lo, hi),
        });
    };
    for stmt in body {
        merge(stmt.offset(), stmt.offset());
        for child in stmt.child_bodies() {
            if let Some((child_lo, child_hi)) = body_offset_span(child) {
                merge(child_lo, child_hi);
            }
        }
    }
    span
}

/// The statement in `body` (or any nested body) whose offset most tightly
/// precedes `target`.
///
/// Statements carry only a start offset, not an end, so "covering" is defined
/// as the statement with the greatest `offset() <= target`, descending into
/// the matched statement's child bodies to find the most specific one. Returns
/// `None` when every statement starts after `target`.
pub(crate) fn covering_statement(body: &[Stmt], target: usize) -> Option<&Stmt> {
    let mut best: Option<&Stmt> = None;
    for stmt in body {
        if stmt.offset() > target {
            continue;
        }
        // This statement starts at or before the target; it is at least as
        // specific as any earlier-starting sibling.
        match best {
            Some(current) if current.offset() >= stmt.offset() => {}
            _ => best = Some(stmt),
        }
        // Descend: a child body may hold a tighter covering statement.
        for child in stmt.child_bodies() {
            if let Some(nested) = covering_statement(child, target) {
                if nested.offset() >= best.map(Stmt::offset).unwrap_or(0) {
                    best = Some(nested);
                }
            }
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;

    fn call(offset: usize) -> Stmt {
        Stmt::Call {
            func: Expr::Var(format!("Call_{offset}")),
            args: vec![],
            offset,
        }
    }

    fn branch(offset: usize, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond: Expr::Var("c".into()),
            then_body,
            else_body,
            offset,
        }
    }

    fn name_of(stmt: &Stmt) -> String {
        match stmt {
            Stmt::Call {
                func: Expr::Var(name),
                ..
            } => name.clone(),
            _ => "<other>".into(),
        }
    }

    #[test]
    fn covering_picks_greatest_offset_at_or_below_target() {
        let body = vec![call(10), call(20), call(30)];
        assert_eq!(name_of(covering_statement(&body, 25).unwrap()), "Call_20");
        assert_eq!(name_of(covering_statement(&body, 30).unwrap()), "Call_30");
        assert_eq!(name_of(covering_statement(&body, 10).unwrap()), "Call_10");
    }

    #[test]
    fn covering_returns_none_when_all_after_target() {
        let body = vec![call(10), call(20)];
        assert!(covering_statement(&body, 5).is_none());
    }

    #[test]
    fn covering_descends_into_child_bodies() {
        // Branch at 20 owns calls at 24 and 28 in its then-body. A target of
        // 26 should resolve to the nested call at 24, not the branch at 20.
        let body = vec![call(10), branch(20, vec![call(24), call(28)], vec![])];
        assert_eq!(name_of(covering_statement(&body, 26).unwrap()), "Call_24");
        assert_eq!(name_of(covering_statement(&body, 28).unwrap()), "Call_28");
        // A target between the branch start and its first child stays on the
        // branch itself.
        assert!(matches!(
            covering_statement(&body, 22),
            Some(Stmt::Branch { offset: 20, .. })
        ));
    }

    #[test]
    fn in_span_lookup_requires_span_containment() {
        use super::super::K2NodePartition;
        use crate::bytecode::decode::cross_event_inline::K2NodeClass;

        // Node 7's bytes start at disk 25 (the minimum across its scattered
        // ranges); statement offsets are disk coordinates, so no translation
        // applies.
        let mut byte_map = K2NodeByteMap::default();
        byte_map.partitions.insert(
            7,
            K2NodePartition {
                node_id: 7,
                ranges: vec![30..31, 25..26],
                owner_events: Default::default(),
                kind: K2NodeClass::Other,
                macro_kind: None,
                via_fallback: Vec::new(),
            },
        );
        let carried = UbergraphByteMap::new(byte_map);

        // Anchor inside the body span resolves to the covering statement.
        let owning_body = vec![call(10), call(20), call(30)];
        assert_eq!(
            name_of(carried.statement_for_node_in_span(7, &owning_body).unwrap()),
            "Call_20"
        );
        // A sibling body whose offsets all precede the anchor is rejected,
        // even though a covering statement exists from below.
        let sibling_body = vec![call(2), call(4)];
        assert!(carried
            .statement_for_node_in_span(7, &sibling_body)
            .is_none());
        // A body that starts after the anchor is rejected too.
        let later_body = vec![call(40), call(50)];
        assert!(carried.statement_for_node_in_span(7, &later_body).is_none());
        // Unknown node resolves to nothing.
        assert!(carried
            .statement_for_node_in_span(99, &owning_body)
            .is_none());
    }

    #[test]
    fn body_offset_span_covers_nested_children() {
        let body = vec![call(10), branch(20, vec![call(24), call(90)], vec![])];
        assert_eq!(body_offset_span(&body), Some((10, 90)));
        assert_eq!(body_offset_span(&[]), None);
    }

    /// End-to-end check that the carried byte map resolves a real graph node
    /// to the statement it produced, against the committed BP_DecoderTest
    /// fixture. Node 113 is the `Release` `K2Node_CallFunction` reached by the
    /// `OnRightReleased` event; its first attributed disk byte must find a
    /// covering statement inside that event's decoded body.
    #[test]
    fn statement_for_node_resolves_decodertest_release() {
        use crate::parser::parse_asset;

        const RELEASE_NODE_ID: usize = 113;
        const OWNING_EVENT: &str = "OnRightReleased";

        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("samples/ue_4.27/BP_DecoderTest.uasset");
        let bytes = std::fs::read(&path).expect("read DecoderTest fixture");
        let parsed = parse_asset(&bytes, false).expect("parse DecoderTest");
        let decoded = crate::bytecode::decode::decode_asset(&parsed, &bytes);

        let carried = decoded
            .byte_maps
            .ubergraph
            .as_ref()
            .expect("DecoderTest has an ubergraph, so the byte map must be carried");

        // The node has a disk-range attribution that names the owning event.
        let partition = carried
            .byte_map
            .partitions
            .get(&RELEASE_NODE_ID)
            .expect("Release node has a partition");
        assert!(
            partition.owner_events.contains(OWNING_EVENT),
            "node {} should be owned by {}, got {:?}",
            RELEASE_NODE_ID,
            OWNING_EVENT,
            partition.owner_events
        );

        let event = decoded
            .events
            .iter()
            .find(|event| event.name == OWNING_EVENT)
            .expect("OnRightReleased event decoded");

        // The disk anchor must resolve to a covering statement whose offset
        // lies within the event's own statement-offset span (not leak to
        // another event).
        let stmt = carried
            .statement_for_node(RELEASE_NODE_ID, &event.body)
            .expect("Release node resolves to a covering statement");
        let body_offsets = collect_offsets(&event.body);
        let max_offset = body_offsets.iter().copied().max().unwrap();
        let min_offset = body_offsets.iter().copied().min().unwrap();
        assert!(
            body_offsets.contains(&stmt.offset()),
            "covering statement offset {} must be a real offset in the body {:?}",
            stmt.offset(),
            body_offsets
        );
        assert!(
            (min_offset..=max_offset).contains(&stmt.offset()),
            "covering offset {} must lie within the event span {}..={}",
            stmt.offset(),
            min_offset,
            max_offset
        );

        // A node id with no partition resolves to nothing.
        assert!(carried
            .statement_for_node(usize::MAX, &event.body)
            .is_none());
    }

    fn collect_offsets(body: &[Stmt]) -> Vec<usize> {
        let mut out = Vec::new();
        for stmt in body {
            out.push(stmt.offset());
            for child in stmt.child_bodies() {
                out.extend(collect_offsets(child));
            }
        }
        out
    }
}
