//! Statement occurrence ancestry retained independently of rendered expressions.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::scoped_value::ScopedValue;
use super::stmt::Stmt;

#[derive(Default)]
pub(crate) struct BodyOrigins {
    pub(crate) original_body: Vec<Stmt>,
    /// Final statement paths to original statement paths. Paths alternate a
    /// statement index and child-body index, using `child_bodies_all` order.
    pub(crate) statement_origins: BTreeMap<Vec<usize>, BTreeSet<Vec<usize>>>,
}

thread_local! {
    static TRANSFERS: RefCell<Option<Vec<(usize, usize)>>> = const { RefCell::new(None) };
}

impl BodyOrigins {
    pub(crate) fn new(body: &[Stmt]) -> Self {
        Self {
            original_body: body.to_vec(),
            statement_origins: Self::statements(body)
                .into_keys()
                .map(|path| (path.clone(), BTreeSet::from([path])))
                .collect(),
        }
    }

    pub(crate) fn apply(&mut self, body: &mut Vec<Stmt>, transform: impl FnOnce(&mut Vec<Stmt>)) {
        let before = body.clone();
        let _guard = ScopedValue::set(&TRANSFERS, Some(Vec::new()));
        transform(body);
        let transfers = TRANSFERS.with(|state| state.borrow_mut().take().unwrap_or_default());
        self.update(&before, body, &transfers);
    }

    pub(crate) fn update(&mut self, before: &[Stmt], after: &[Stmt], transfers: &[(usize, usize)]) {
        if before == after && transfers.is_empty() {
            return;
        }
        let mut by_offset: BTreeMap<usize, BTreeSet<Vec<usize>>> = BTreeMap::new();
        let mut counts = BTreeMap::<usize, usize>::new();
        for (path, stmt) in Self::statements(before) {
            *counts.entry(stmt.offset()).or_default() += 1;
            let sources = self
                .statement_origins
                .get(&path)
                .cloned()
                .unwrap_or_default();
            by_offset
                .entry(stmt.offset())
                .and_modify(|existing| existing.retain(|source| sources.contains(source)))
                .or_insert(sources);
        }
        for &(source, target) in transfers {
            if counts.get(&source) != Some(&1) || counts.get(&target) != Some(&1) {
                continue;
            }
            if let Some(sources) = by_offset.get(&source).cloned() {
                by_offset.entry(target).or_default().extend(sources);
            }
        }
        let preferred = surviving_occurrences(before, after);
        self.statement_origins = Self::statements(after)
            .into_iter()
            .map(|(path, stmt)| {
                (
                    path.clone(),
                    if preferred.contains(&path) {
                        by_offset.get(&stmt.offset()).cloned().unwrap_or_default()
                    } else {
                        BTreeSet::new()
                    },
                )
            })
            .collect();
    }

    pub(crate) fn statements(body: &[Stmt]) -> BTreeMap<Vec<usize>, &Stmt> {
        fn walk<'body>(
            body: &'body [Stmt],
            path: &mut Vec<usize>,
            found: &mut BTreeMap<Vec<usize>, &'body Stmt>,
        ) {
            for (index, stmt) in body.iter().enumerate() {
                path.push(index);
                found.insert(path.clone(), stmt);
                for (child_index, child) in stmt.child_bodies_all().into_iter().enumerate() {
                    path.push(child_index);
                    walk(child, path, found);
                    path.pop();
                }
                path.pop();
            }
        }
        let mut found = BTreeMap::new();
        walk(body, &mut Vec::new(), &mut found);
        found
    }

    /// Transforms call this only when they explicitly absorb a source into a
    /// destination. With no active tracking scope, transforms remain standalone.
    pub(crate) fn record(source_offset: usize, target_offset: usize) {
        TRANSFERS.with(|state| {
            if let Some(transfers) = state.borrow_mut().as_mut() {
                transfers.push((source_offset, target_offset));
            }
        });
    }
}

// A newly inserted wrapper may reuse its child's offset. When the source
// survives, its annotation belongs to that occurrence, not the broad wrapper.
fn surviving_occurrences(before: &[Stmt], after: &[Stmt]) -> BTreeSet<Vec<usize>> {
    let mut originals = BTreeMap::<usize, Vec<&Stmt>>::new();
    for stmt in BodyOrigins::statements(before).values() {
        originals.entry(stmt.offset()).or_default().push(stmt);
    }
    let mut outputs = BTreeMap::<usize, Vec<(Vec<usize>, &Stmt)>>::new();
    for (path, stmt) in BodyOrigins::statements(after) {
        outputs.entry(stmt.offset()).or_default().push((path, stmt));
    }
    let mut preferred = BTreeSet::new();
    for (offset, candidates) in outputs {
        let original = originals
            .get(&offset)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let [original] = original else {
            preferred.extend(candidates.into_iter().map(|(path, _)| path));
            continue;
        };
        if candidates.len() == 1 {
            preferred.insert(candidates[0].0.clone());
            continue;
        }
        let exact: Vec<_> = candidates
            .iter()
            .filter(|(_, stmt)| *stmt == *original)
            .collect();
        if !exact.is_empty() {
            preferred.extend(exact.into_iter().map(|(path, _)| path.clone()));
            continue;
        }
        let same_kind: Vec<_> = candidates
            .iter()
            .filter(|(_, stmt)| std::mem::discriminant(*stmt) == std::mem::discriminant(*original))
            .collect();
        if let [candidate] = same_kind.as_slice() {
            preferred.insert(candidate.0.clone());
        }
    }
    preferred
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::transforms::{expr_transforms, ternary_fold};

    fn assignment(offset: usize, name: &str, value: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name.into()),
            rhs: value,
            offset,
        }
    }
    fn call(offset: usize, value: Expr) -> Stmt {
        Stmt::Call {
            func: Expr::Var("Consume".into()),
            args: vec![value],
            offset,
        }
    }

    #[test]
    fn inlining_keeps_the_computation_source_at_its_consumer() {
        let mut body = vec![
            assignment(
                10,
                "$First",
                Expr::Call {
                    name: "Compute".into(),
                    args: vec![],
                },
            ),
            assignment(20, "$Second", Expr::Var("$First".into())),
            call(30, Expr::Var("$Second".into())),
        ];
        let origins =
            crate::bytecode::decode::transform_stack::apply_transform_stack_to_body(&mut body);
        assert_eq!(body.len(), 1);
        assert_eq!(origins.original_body.len(), 3);
        assert_eq!(
            origins.statement_origins[&vec![0]],
            BTreeSet::from([vec![0], vec![1], vec![2]])
        );
    }

    #[test]
    fn ternary_keeps_both_conditional_sources() {
        let mut body = vec![Stmt::Branch {
            cond: Expr::Var("Enabled".into()),
            then_body: vec![assignment(20, "Result", Expr::Literal("1".into()))],
            else_body: vec![assignment(30, "Result", Expr::Literal("2".into()))],
            offset: 10,
        }];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(&mut body, |body| ternary_fold::fold_ternaries(body));
        assert_eq!(
            origins.statement_origins[&vec![0]],
            BTreeSet::from([vec![0], vec![0, 0, 0], vec![0, 1, 0]])
        );
    }

    #[test]
    fn identical_offsets_do_not_transfer_to_an_unrelated_occurrence() {
        let mut body = vec![
            assignment(10, "$Value", Expr::Literal("1".into())),
            call(20, Expr::Var("$Value".into())),
            call(20, Expr::Literal("2".into())),
        ];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(&mut body, expr_transforms::inline_single_use_temps);
        assert!(!origins
            .statement_origins
            .values()
            .any(|sources| sources.contains(&vec![0])));
    }

    #[test]
    fn no_op_keeps_distinct_occurrences_even_with_equal_offsets() {
        let mut body = vec![
            call(10, Expr::Literal("1".into())),
            call(10, Expr::Literal("1".into())),
        ];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(&mut body, |_| {});
        assert_eq!(
            origins.statement_origins[&vec![0]],
            BTreeSet::from([vec![0]])
        );
        assert_eq!(
            origins.statement_origins[&vec![1]],
            BTreeSet::from([vec![1]])
        );
    }

    #[test]
    fn moved_statement_keeps_its_source_path() {
        let mut body = vec![Stmt::Branch {
            cond: Expr::Var("Enabled".into()),
            then_body: vec![],
            else_body: vec![call(20, Expr::Literal("1".into()))],
            offset: 10,
        }];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(&mut body, |body| {
            crate::bytecode::transforms::invert_empty_then::invert_empty_then_branches(body)
        });
        assert_eq!(
            origins.statement_origins[&vec![0, 0, 0]],
            BTreeSet::from([vec![0, 1, 0]])
        );
    }

    #[test]
    fn deleting_a_statement_does_not_assign_it_to_a_similar_neighbor() {
        let mut body = vec![
            assignment(10, "$Unused", Expr::Literal("1".into())),
            call(20, Expr::Literal("1".into())),
        ];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(
            &mut body,
            crate::bytecode::transforms::dead_stmt::remove_dead_assignments,
        );
        assert_eq!(
            origins.statement_origins[&vec![0]],
            BTreeSet::from([vec![1]])
        );
    }

    #[test]
    fn synthesized_wrapper_does_not_inherit_the_retained_calls_comment() {
        use crate::bytecode::stmt::LatchKind;
        let mut body = vec![
            call(10, Expr::Literal("1".into())),
            call(20, Expr::Literal("2".into())),
        ];
        let mut origins = BodyOrigins::new(&body);
        // DoOnce synthesis retains the call and reuses its offset for a new
        // enclosing latch that may also contain reset statements.
        origins.apply(&mut body, |body| {
            let calls = std::mem::take(body);
            body.push(Stmt::Latch {
                kind: LatchKind::DoOnce {
                    gate_var: "Gate".into(),
                    name: "Work".into(),
                },
                init: vec![],
                body: calls,
                offset: 10,
            });
        });
        assert!(origins.statement_origins[&vec![0]].is_empty());
        assert_eq!(
            origins.statement_origins[&vec![0, 1, 0]],
            BTreeSet::from([vec![0]])
        );
        assert_eq!(
            origins.statement_origins[&vec![0, 1, 1]],
            BTreeSet::from([vec![1]])
        );
        assert_eq!(
            origins
                .statement_origins
                .values()
                .filter(|sources| sources.contains(&vec![0]))
                .count(),
            1
        );
    }

    #[test]
    fn a_new_projection_can_share_one_original_source() {
        let mut body = vec![call(10, Expr::Var("Value".into()))];
        let mut origins = BodyOrigins::new(&body);
        origins.apply(&mut body, |body| body.push(body[0].clone()));
        assert_eq!(
            origins.statement_origins[&vec![0]],
            BTreeSet::from([vec![0]])
        );
        assert_eq!(
            origins.statement_origins[&vec![1]],
            BTreeSet::from([vec![0]])
        );
    }
}

#[cfg(test)]
mod placement_tests {
    use super::*;
    use crate::bytecode::{
        asset::{DecodedAsset, Function},
        expr::Expr,
    };
    use crate::output_summary::comments::placement::{build_placement_plan, PlacementClass};
    use crate::output_summary::comments::{CommentBox, CommentModel};
    use crate::types::{
        AssetVersion, EdGraphPin, ExportHeader, ImportEntry, NodePinData, ParsedAsset, PropValue,
        Property,
    };

    fn parsed_computation() -> ParsedAsset {
        ParsedAsset {
            version: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
            name_table: crate::binary::NameTable::from_names(vec![]),
            diagnostics: vec![],
            imports: vec![ImportEntry {
                class_package: String::new(),
                class_name: "Class".into(),
                object_name: "K2Node_CallFunction".into(),
                outer_index: 0,
            }],
            exports: vec![(
                ExportHeader {
                    class_index: -1,
                    super_index: 0,
                    outer_index: 0,
                    object_name: "Computation".into(),
                    serial_offset: 0,
                    serial_size: 0,
                },
                vec![Property {
                    name: "FunctionReference".into(),
                    value: PropValue::Struct {
                        struct_type: "MemberReference".into(),
                        fields: vec![Property {
                            name: "MemberName".into(),
                            value: PropValue::Name("Compute".into()),
                        }],
                    },
                }],
            )],
            pin_data: [(
                1,
                NodePinData {
                    pins: vec![EdGraphPin {
                        name: "ReturnValue".into(),
                        pin_type: "float".into(),
                        direction: 1,
                        ..Default::default()
                    }],
                },
            )]
            .into_iter()
            .collect(),
            function_signatures: Default::default(),
            bytecode_by_export: Default::default(),
        }
    }

    #[test]
    fn original_computation_comment_follows_inlining_and_distinct_copies() {
        let parsed = parsed_computation();
        let mut body = vec![
            Stmt::Assignment {
                lhs: Expr::Var("$Value".into()),
                rhs: Expr::Call {
                    name: "Compute".into(),
                    args: vec![],
                },
                offset: 10,
            },
            Stmt::Call {
                func: Expr::Var("Consume".into()),
                args: vec![Expr::Var("$Value".into())],
                offset: 20,
            },
        ];
        let mut origins =
            crate::bytecode::decode::transform_stack::apply_transform_stack_to_body(&mut body);
        origins.apply(&mut body, |body| body.push(body[0].clone()));
        let decoded = DecodedAsset {
            function_origins: BTreeMap::from([("Example".into(), origins)]),
            event_origins: Default::default(),
            resume_origins: Default::default(),
            diagnostics: vec![],
            functions: vec![Function {
                name: "Example".into(),
                body,
                export_index: None,
            }],
            events: vec![],
            resume_bodies: Default::default(),
            resume_owner_events: Default::default(),
            byte_maps: Default::default(),
        };
        let model = CommentModel {
            boxes: vec![CommentBox {
                text: "Explain computation".into(),
                x: 0,
                y: 0,
                width: 0,
                height: 0,
                is_bubble: true,
                owner_export: Some(1),
                graph_page: Some("Example".into()),
            }],
            nodes: vec![],
        };
        let plan = build_placement_plan(&decoded, &parsed, &["Computation".into()], &model);
        assert_eq!(plan.unanchored, 0);
        let locations = &plan.placed[0].locations;
        assert_eq!(locations.len(), 2);
        for (index, location) in locations.iter().enumerate() {
            assert_eq!(
                location.class,
                PlacementClass::InlineAtStatement {
                    statement_offset: 20,
                    statement_path: vec![0, index]
                }
            );
            assert!(std::ptr::eq(
                location.statement(&decoded).unwrap(),
                &decoded.functions[0].body[index]
            ));
        }
    }
}
