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
//! - Inline annotations keyed by the resolved statement's address, installed
//!   around each block's emission. Addresses are compared as integers and never
//!   dereferenced. The decoded asset stays immutable until emission finishes.
//!
//! The thread-local is only ever installed by the summary block emitters, so
//! the `--dump`/`--json` paths (which call `emit_body` without installing it)
//! never render summary annotations. Sequence pin identity is already retained
//! in the decoded statement tree and does not depend on this scope.

use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::scoped_value::ScopedValue;
use crate::output_summary::comments::extract::build_comment_model;
use crate::output_summary::comments::placement::{
    build_placement_plan, PlacedComment, PlacementClass,
};
use crate::output_summary::comments::render::render_comment_lines;
use crate::types::ParsedAsset;

/// Per-block comment annotations for one asset, ready to interleave at emit.
#[derive(Debug, Clone, Default)]
pub(crate) struct CommentEmitPlan {
    /// Authored texts with no unique placement, keyed by source graph page.
    unresolved: BTreeMap<String, Vec<String>>,
    /// Header annotations keyed by all covered events. Shared groups render
    /// once with their event labels, single-event comments precede that header.
    pub(crate) event_wrapping: BTreeMap<Vec<String>, Vec<String>>,
    /// Lines emitted directly below a block signature, keyed by block name.
    function_level: BTreeMap<String, Vec<String>>,
    /// Raw comment texts keyed by block name then resolved statement address. Inline
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
            emit_plan.insert(placed, decoded);
        }
        emit_plan
    }

    fn insert(&mut self, placed: PlacedComment, decoded: &DecodedAsset) {
        if placed.locations.len() > 1
            && placed
                .locations
                .iter()
                .all(|location| location.class == PlacementClass::EventWrapping)
        {
            let blocks = placed
                .locations
                .iter()
                .map(|location| location.block.clone())
                .collect();
            self.event_wrapping
                .entry(blocks)
                .or_default()
                .extend(render_comment_lines(&placed.text, "    "));
            return;
        }
        for location in &placed.locations {
            match &location.class {
                PlacementClass::Unresolved => {
                    self.unresolved
                        .entry(location.block.clone())
                        .or_default()
                        .push(placed.text.clone());
                }
                PlacementClass::EventWrapping => {
                    self.event_wrapping
                        .entry(vec![location.block.clone()])
                        .or_default()
                        .extend(placed.lines.clone());
                }
                PlacementClass::FunctionLevel => {
                    self.function_level
                        .entry(location.block.clone())
                        .or_default()
                        .extend(placed.lines.clone());
                }
                PlacementClass::InlineAtStatement { .. } => {
                    if let Some(statement) = location.statement(decoded) {
                        self.inline
                            .entry(location.block.clone())
                            .or_default()
                            .entry(statement as *const crate::bytecode::stmt::Stmt as usize)
                            .or_default()
                            .push(placed.text.clone());
                    }
                }
            }
        }
    }

    pub(crate) fn unresolved_lines(&self, filters: &[String]) -> Vec<String> {
        let mut lines = Vec::new();
        for (page, texts) in &self.unresolved {
            let heading = format!("  Graph {page:?}:");
            let mut included = false;
            for text in texts {
                if !crate::output_summary::filter::block_matches_filter(
                    &format!("{heading}\n{text}"),
                    filters,
                ) {
                    continue;
                }
                if !included {
                    lines.push(heading.clone());
                    included = true;
                }
                lines.extend(render_comment_lines(text, "    "));
            }
        }
        lines
    }

    /// Event-wrapping lines for `block`, if any.
    pub(crate) fn event_wrapping_lines(&self, block: &str) -> Option<&[String]> {
        self.event_wrapping
            .get(&vec![block.to_owned()])
            .map(Vec::as_slice)
    }

    /// Function-level description lines for `block`, if any.
    pub(crate) fn function_level_lines(&self, block: &str) -> Option<&[String]> {
        self.function_level.get(block).map(Vec::as_slice)
    }

    /// Exact statement annotations for one block, including its resumptions.
    fn inline_for_block(&self, block: &str) -> Option<&BTreeMap<usize, Vec<String>>> {
        self.inline.get(block)
    }
}

thread_local! {
    /// Inline annotation map for the block currently being emitted, or `None`
    /// for blocks with no inline comments and for the `--dump`/`--json` paths
    /// (which never install it). Set by [`with_block_comments`] around each
    /// block's body so the statement-emit arm can prepend annotation lines by
    /// the statement's address. The map is stored by value (cloned in at
    /// scope entry) so the consult path holds no borrow.
    static ACTIVE_INLINE_COMMENTS: RefCell<Option<BTreeMap<usize, Vec<String>>>> =
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
    let next = map.cloned();
    let _guard = ScopedValue::set(&ACTIVE_INLINE_COMMENTS, next);
    body()
}

/// Inline annotation lines for this exact statement in the active block,
/// rendered with `indent` (the emitting statement's own indent, so the
/// annotation lines up with the construct it annotates). `None` when no
/// comment anchors there (or no map is installed).
pub(crate) fn inline_comment_lines(
    statement: &crate::bytecode::stmt::Stmt,
    indent: &str,
) -> Option<Vec<String>> {
    ScopedValue::with_current(&ACTIVE_INLINE_COMMENTS, |map| {
        let texts = map.get(&(statement as *const crate::bytecode::stmt::Stmt as usize))?;
        Some(
            texts
                .iter()
                .flat_map(|text| render_comment_lines(text, indent))
                .collect(),
        )
    })
    .flatten()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output_summary::comments::placement::{CommentLocation, PlacedComment};

    fn decoded_with_function() -> DecodedAsset {
        use crate::bytecode::{asset::Function, expr::Expr, stmt::Stmt};
        DecodedAsset {
            diagnostics: vec![],
            functions: vec![Function {
                name: "Fn".into(),
                export_index: None,
                body: [12, 40]
                    .into_iter()
                    .map(|offset| Stmt::Call {
                        func: Expr::Var("Work".into()),
                        args: vec![],
                        offset,
                    })
                    .collect(),
            }],
            events: vec![],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps: Default::default(),
            function_origins: Default::default(),
            event_origins: Default::default(),
            resume_origins: Default::default(),
        }
    }

    fn placed(block: &str, class: PlacementClass, lines: &[&str], text: &str) -> PlacedComment {
        PlacedComment {
            locations: vec![CommentLocation {
                block: block.into(),
                class,
            }],
            lines: lines.iter().map(|line| line.to_string()).collect(),
            box_x: 0,
            box_y: 0,
            text: text.into(),
        }
    }

    #[test]
    fn buckets_by_class_and_block() {
        let decoded = decoded_with_function();
        let mut plan = CommentEmitPlan::default();
        plan.insert(
            placed("Ev", PlacementClass::EventWrapping, &["  // \"ev\""], "ev"),
            &decoded,
        );
        plan.insert(
            placed(
                "Fn",
                PlacementClass::FunctionLevel,
                &["    // \"fn\""],
                "fn",
            ),
            &decoded,
        );
        plan.insert(
            placed(
                "Fn",
                PlacementClass::InlineAtStatement {
                    statement_offset: 12,
                    statement_path: vec![0, 0],
                },
                &[],
                "inl",
            ),
            &decoded,
        );

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
        assert_eq!(
            inline
                .get(&(&decoded.functions[0].body[0] as *const _ as usize))
                .unwrap(),
            &vec!["inl".to_string()]
        );
    }

    #[test]
    fn thread_local_consult_scoped_to_block() {
        let decoded = decoded_with_function();
        let mut plan = CommentEmitPlan::default();
        plan.insert(
            placed(
                "Fn",
                PlacementClass::InlineAtStatement {
                    statement_offset: 40,
                    statement_path: vec![0, 1],
                },
                &[],
                "at40",
            ),
            &decoded,
        );

        // Outside any installed scope there is no annotation.
        assert!(inline_comment_lines(&decoded.functions[0].body[1], "    ").is_none());

        with_block_comments(&plan, "Fn", || {
            // Rendered at consult with the indent the emitter passes in.
            assert_eq!(
                inline_comment_lines(&decoded.functions[0].body[1], "        "),
                Some(vec!["        // \"at40\"".to_string()])
            );
            // A different offset in the same block has nothing.
            assert!(inline_comment_lines(&decoded.functions[0].body[0], "    ").is_none());
            // Clearing the map (nested-body recursion) suppresses lookups.
            with_inline_comments(None, || {
                assert!(inline_comment_lines(&decoded.functions[0].body[1], "    ").is_none());
            });
            // Restored after the nested scope.
            assert!(inline_comment_lines(&decoded.functions[0].body[1], "    ").is_some());
        });

        // Restored to empty after the block scope.
        assert!(inline_comment_lines(&decoded.functions[0].body[1], "    ").is_none());
    }
    #[test]
    fn unresolved_comments_render_and_filter_by_page_or_text() {
        let decoded = decoded_with_function();
        let mut plan = CommentEmitPlan::default();
        plan.insert(
            placed("Example", PlacementClass::Unresolved, &[], "Keep this note"),
            &decoded,
        );
        let lines = plan.unresolved_lines(&[]);
        assert_eq!(
            lines,
            vec!["  Graph \"Example\":", "    // \"Keep this note\""]
        );
        assert_eq!(plan.unresolved_lines(&["example".into()]), lines);
        assert_eq!(plan.unresolved_lines(&["keep this".into()]), lines);
        assert!(plan.unresolved_lines(&["unrelated".into()]).is_empty());
    }

    #[test]
    fn comments_on_counted_loop_header_statements_are_emitted() {
        use crate::bytecode::{
            expr::Expr,
            stmt::{LoopKind, Stmt},
        };
        let body = vec![Stmt::Loop {
            kind: LoopKind::ForC {
                init: vec![Stmt::Assignment {
                    lhs: Expr::Var("Index".into()),
                    rhs: Expr::Literal("0".into()),
                    offset: 10,
                }],
                increment: vec![Stmt::Call {
                    func: Expr::Var("Advance".into()),
                    args: vec![],
                    offset: 30,
                }],
            },
            cond: None,
            body: vec![],
            completion: None,
            offset: 10,
        }];
        let Stmt::Loop {
            kind: LoopKind::ForC { init, increment },
            ..
        } = &body[0]
        else {
            unreachable!()
        };
        let map = BTreeMap::from([
            (&init[0] as *const Stmt as usize, vec!["initialize".into()]),
            (
                &increment[0] as *const Stmt as usize,
                vec!["advance".into()],
            ),
        ]);
        let lines = with_inline_comments(Some(&map), || {
            crate::bytecode::emit::render_body_lines(&body, &BTreeMap::new())
        });
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.contains("initialize"))
                .count(),
            1
        );
        assert_eq!(
            lines.iter().filter(|line| line.contains("advance")).count(),
            1
        );
        assert!(lines[0].contains("initialize"));
        assert!(lines[1].contains("advance"));
    }

    #[test]
    fn comments_on_flipflop_branch_survive_header_rendering() {
        use crate::bytecode::{
            expr::Expr,
            stmt::{LatchKind, Stmt},
        };
        let body = vec![Stmt::Latch {
            kind: LatchKind::FlipFlop {
                gate_var: "Gate".into(),
                names: None,
            },
            init: vec![],
            offset: 10,
            body: vec![Stmt::Branch {
                cond: Expr::Var("Gate".into()),
                then_body: vec![],
                else_body: vec![],
                offset: 20,
            }],
        }];
        let Stmt::Latch {
            body: latch_body, ..
        } = &body[0]
        else {
            unreachable!()
        };
        let map = BTreeMap::from([(
            &latch_body[0] as *const Stmt as usize,
            vec!["toggle body".into()],
        )]);
        let lines = with_inline_comments(Some(&map), || {
            crate::bytecode::emit::render_body_lines(&body, &BTreeMap::new())
        });
        let note = lines
            .iter()
            .position(|line| line.contains("toggle body"))
            .unwrap();
        assert!(lines[note + 1].contains("A|B:"));
    }
    #[test]
    fn exact_locations_annotate_repeated_offsets_without_claiming_intervening_statements() {
        use crate::bytecode::stmt::Stmt;
        let mut decoded = decoded_with_function();
        let first = decoded.functions[0].body[0].clone();
        decoded.functions[0].body = vec![first.clone(), first.clone(), first];
        let body = &decoded.functions[0].body;
        let mut plan = CommentEmitPlan::default();
        let mut comment = placed(
            "Fn",
            PlacementClass::InlineAtStatement {
                statement_offset: 12,
                statement_path: vec![0, 0],
            },
            &[],
            "Selected operations",
        );
        comment.locations.push(CommentLocation {
            block: "Fn".into(),
            class: PlacementClass::InlineAtStatement {
                statement_offset: 12,
                statement_path: vec![0, 2],
            },
        });
        plan.insert(comment, &decoded);
        let lines = with_block_comments(&plan, "Fn", || {
            crate::bytecode::emit::render_body_lines(body, &BTreeMap::new())
        });
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.contains("Selected operations"))
                .count(),
            2
        );
        assert!(lines[0].contains("Selected operations"));
        assert!(lines[1].contains("Work("));
        assert!(lines[2].contains("Work("));
        assert!(lines[3].contains("Selected operations"));
        assert!(matches!(&body[1], Stmt::Call { .. }));
    }
}
