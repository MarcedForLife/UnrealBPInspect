//! Summary-mode comment annotations: per-block lookup plus the scoped
//! thread-local that interleaves inline annotations at statement emit.
//!
//! The placement classifier (`output_summary::comments::placement`) decides
//! where each authored comment box attaches. This module turns that plan into
//! the two shapes the summary emitter consults:
//!
//! - Header annotations (`event_wrapping` / `function_level`) keyed by block
//!   name, emitted around the block header in `emit_event_block` /
//!   `emit_function_block`.
//! - Inline annotations keyed by `(block, statement_offset)`, installed as a
//!   thread-local around each block's body so the statement-emit arm can look
//!   them up by the statement's mem offset without threading a parameter
//!   through every `Stmt` variant.
//!
//! The thread-local is only ever installed by the summary block emitters, so
//! the `--dump`/`--json` paths (which call `emit_body` without installing it)
//! never render comments, the same way the `ACTIVE_SEQUENCE_MASK` thread-local
//! stays uninstalled on those paths.

use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::bytecode::asset::DecodedAsset;
use crate::output_summary::comments::extract::build_comment_model;
use crate::output_summary::comments::placement::{
    build_placement_plan, PlacedComment, PlacementClass,
};
use crate::output_summary::comments::render::render_comment_lines;
use crate::types::ParsedAsset;

/// Per-block comment annotations for one asset, ready to interleave at emit.
#[derive(Debug, Clone, Default)]
pub(crate) struct CommentEmitPlan {
    /// Lines emitted directly above an event header, keyed by event name.
    event_wrapping: BTreeMap<String, Vec<String>>,
    /// Lines emitted directly below a block signature, keyed by block name.
    function_level: BTreeMap<String, Vec<String>>,
    /// Raw comment texts keyed by block name then statement offset. Inline
    /// annotations are rendered at the consult site with the emitting
    /// statement's actual indent (header classes use fixed indents and stay
    /// pre-rendered).
    inline: BTreeMap<String, BTreeMap<usize, Vec<String>>>,
}

impl CommentEmitPlan {
    /// Build the annotation plan for `decoded`/`parsed`.
    ///
    /// Extracts the comment model, classifies every box, then buckets the
    /// placed comments by block and class. Multiple comments at one anchor
    /// keep the placement plan's deterministic order (block, class, offset,
    /// box y/x, text), so the concatenated line vectors are stable.
    pub(crate) fn build(decoded: &DecodedAsset, parsed: &ParsedAsset) -> Self {
        let export_names: Vec<String> = parsed
            .exports
            .iter()
            .map(|(hdr, _)| hdr.object_name.clone())
            .collect();
        let model = build_comment_model(parsed, &export_names);
        let plan = build_placement_plan(decoded, parsed, &export_names, &model);

        let mut emit_plan = CommentEmitPlan::default();
        for placed in plan.placed {
            emit_plan.insert(placed);
        }
        emit_plan
    }

    fn insert(&mut self, placed: PlacedComment) {
        let PlacedComment {
            block,
            class,
            lines,
            text,
            ..
        } = placed;
        match class {
            PlacementClass::EventWrapping => {
                self.event_wrapping.entry(block).or_default().extend(lines);
            }
            PlacementClass::FunctionLevel => {
                self.function_level.entry(block).or_default().extend(lines);
            }
            PlacementClass::InlineAtStatement { statement_offset } => {
                self.inline
                    .entry(block)
                    .or_default()
                    .entry(statement_offset)
                    .or_default()
                    .push(text);
            }
        }
    }

    /// Event-wrapping lines for `block`, if any.
    pub(crate) fn event_wrapping_lines(&self, block: &str) -> Option<&[String]> {
        self.event_wrapping.get(block).map(Vec::as_slice)
    }

    /// Function-level description lines for `block`, if any.
    pub(crate) fn function_level_lines(&self, block: &str) -> Option<&[String]> {
        self.function_level.get(block).map(Vec::as_slice)
    }

    /// Inline annotation map for `block` (offset -> lines), if any.
    fn inline_for_block(&self, block: &str) -> Option<&BTreeMap<usize, Vec<String>>> {
        self.inline.get(block)
    }
}

thread_local! {
    /// Inline annotation map for the block currently being emitted, or `None`
    /// for blocks with no inline comments and for the `--dump`/`--json` paths
    /// (which never install it). Set by [`with_block_comments`] around each
    /// block's body so the statement-emit arm can prepend annotation lines by
    /// the statement's mem offset.
    static ACTIVE_INLINE_COMMENTS: RefCell<Option<*const BTreeMap<usize, Vec<String>>>> =
        const { RefCell::new(None) };
}

/// Install `block`'s inline annotation map for the duration of `body`,
/// restoring the previous binding on the way out. A no-op installation of
/// `None` is used when recursing into nested bodies that should not inherit
/// the parent block's map.
pub(crate) fn with_block_comments<R>(
    plan: &CommentEmitPlan,
    block: &str,
    body: impl FnOnce() -> R,
) -> R {
    let map = plan.inline_for_block(block);
    with_inline_comments(map, body)
}

/// Lower-level scope helper used both by [`with_block_comments`] and to clear
/// the binding while recursing into pin bodies.
pub(crate) fn with_inline_comments<R>(
    map: Option<&BTreeMap<usize, Vec<String>>>,
    body: impl FnOnce() -> R,
) -> R {
    let next = map.map(|inner| inner as *const _);
    let previous = ACTIVE_INLINE_COMMENTS.with(|cell| cell.replace(next));
    let result = body();
    ACTIVE_INLINE_COMMENTS.with(|cell| *cell.borrow_mut() = previous);
    result
}

/// Inline annotation lines for the statement at `offset` in the active block,
/// rendered with `indent` (the emitting statement's own indent, so the
/// annotation lines up with the construct it annotates). `None` when no
/// comment anchors there (or no map is installed).
pub(crate) fn inline_comment_lines(offset: usize, indent: &str) -> Option<Vec<String>> {
    let map_ptr = ACTIVE_INLINE_COMMENTS.with(|cell| *cell.borrow())?;
    // Safety: the pointer is installed by `with_inline_comments` for the
    // duration of one block's emit and restored before the borrow ends; the
    // map outlives the block body it wraps.
    let map: &BTreeMap<usize, Vec<String>> = unsafe { &*map_ptr };
    let texts = map.get(&offset)?;
    Some(
        texts
            .iter()
            .flat_map(|text| render_comment_lines(text, indent))
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output_summary::comments::placement::PlacedComment;

    fn placed(block: &str, class: PlacementClass, lines: &[&str], text: &str) -> PlacedComment {
        PlacedComment {
            block: block.into(),
            class,
            lines: lines.iter().map(|line| line.to_string()).collect(),
            box_x: 0,
            box_y: 0,
            text: text.into(),
        }
    }

    #[test]
    fn buckets_by_class_and_block() {
        let mut plan = CommentEmitPlan::default();
        plan.insert(placed(
            "Ev",
            PlacementClass::EventWrapping,
            &["  // \"ev\""],
            "ev",
        ));
        plan.insert(placed(
            "Fn",
            PlacementClass::FunctionLevel,
            &["    // \"fn\""],
            "fn",
        ));
        plan.insert(placed(
            "Fn",
            PlacementClass::InlineAtStatement {
                statement_offset: 12,
            },
            &[],
            "inl",
        ));

        assert_eq!(
            plan.event_wrapping_lines("Ev"),
            Some(&["  // \"ev\"".to_string()][..])
        );
        assert_eq!(
            plan.function_level_lines("Fn"),
            Some(&["    // \"fn\"".to_string()][..])
        );
        assert!(plan.event_wrapping_lines("Fn").is_none());

        // Inline buckets hold raw texts; rendering happens at consult time.
        let inline = plan.inline_for_block("Fn").unwrap();
        assert_eq!(inline.get(&12).unwrap(), &vec!["inl".to_string()]);
    }

    #[test]
    fn thread_local_consult_scoped_to_block() {
        let mut plan = CommentEmitPlan::default();
        plan.insert(placed(
            "Fn",
            PlacementClass::InlineAtStatement {
                statement_offset: 40,
            },
            &[],
            "at40",
        ));

        // Outside any installed scope there is no annotation.
        assert!(inline_comment_lines(40, "    ").is_none());

        with_block_comments(&plan, "Fn", || {
            // Rendered at consult with the indent the emitter passes in.
            assert_eq!(
                inline_comment_lines(40, "        "),
                Some(vec!["        // \"at40\"".to_string()])
            );
            // A different offset in the same block has nothing.
            assert!(inline_comment_lines(0, "    ").is_none());
            // Clearing the map (nested-body recursion) suppresses lookups.
            with_inline_comments(None, || {
                assert!(inline_comment_lines(40, "    ").is_none());
            });
            // Restored after the nested scope.
            assert!(inline_comment_lines(40, "    ").is_some());
        });

        // Restored to empty after the block scope.
        assert!(inline_comment_lines(40, "    ").is_none());
    }
}
