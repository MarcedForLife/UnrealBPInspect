//! Body transform pipeline: lowers, folds, and normalises the decoded
//! statement tree into its final rendered shape.
//!
//! The pipeline is a data-driven table ([`STACK`]) of named passes run in
//! order by [`apply_transform_stack_to_body`]. Each pass's `doc` records why
//! it sits where it does; the ordering invariants that reduce to a
//! position check are asserted by the `#[test]`s at the bottom of this file,
//! and the prose docs carry the rest.

use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms as tf;

/// One IR transform pass. `run` is the production entry point, applied to a
/// body in place; it is a plain `fn(&mut Vec<Stmt>)`, and passes whose
/// underlying function takes `&mut [Stmt]` are adapted by the closure, which
/// deref-coerces the `Vec`. `name` and `doc` are metadata: the stable
/// identifier the ordering `#[test]`s key on, and the rationale for the pass's
/// position. Both are read by the tests and human readers, not the run loop,
/// hence the dead-code allowance on the library build.
struct Pass {
    #[allow(dead_code)]
    name: &'static str,
    #[allow(dead_code)]
    doc: &'static str,
    run: fn(&mut Vec<Stmt>),
}

/// The ordered transform pipeline. Edits here change decoded output, so any
/// reorder must keep the snapshot and `v2_baseline` byte-identity gates green
/// and respect the ordering `#[test]`s below.
const STACK: &[Pass] = &[
    Pass {
        name: "lower_binary_ops",
        doc: "Convert math-library calls (Less_IntInt, Add_FloatFloat, ...) to typed \
              Expr::Binary so every downstream pass sees operators rather than opaque \
              Call strings. Runs first for that reason.",
        run: |body| tf::lower_binary_ops::lower_binary_ops(body),
    },
    Pass {
        name: "lower_static_library_calls",
        doc: "Rewrite blueprint-function-library static calls to their display form \
              before recognition and folding inspect call shapes.",
        run: |body| tf::lower_static_library_calls::lower_static_library_calls(body),
    },
    Pass {
        name: "lower_array_get_out",
        doc: "Lower the Array_Get out-parameter shape to a plain assignment so later \
              passes see a normal value, not an out-param wrapper.",
        run: |body| tf::lower_array_get_out::lower_array_get_out_to_assignment(body),
    },
    Pass {
        name: "strip_latent_action_info",
        doc: "Drop the synthetic LatentActionInfo argument the compiler threads into \
              latent calls; it is decoder scaffolding, not user content.",
        run: |body| tf::strip_latent_action_info::strip_latent_action_info(body),
    },
    Pass {
        name: "recognize_latches",
        doc: "Recognise DoOnce/FlipFlop latches. Needs the unfolded gate-variable Branch \
              shapes, so it runs before the folds below. The owner-event re-decode subset \
              (decode_owner_event_body in orchestrate.rs) runs this and derive_flipflop_names \
              directly, in the same relative order (checked by recognize_latches_before_flipflop_naming).",
        run: |body| tf::latch_recognition::recognize_latches(body),
    },
    Pass {
        name: "derive_flipflop_names",
        doc: "Derive the A/B-side labels for recognised FlipFlop latches.",
        run: |body| tf::flipflop_naming::derive_flipflop_names(body),
    },
    Pass {
        name: "collapse_nested_doonce",
        doc: "Collapse a DoOnce nested directly inside another into a single latch.",
        run: |body| tf::collapse_nested_doonce::collapse_nested_doonce(body),
    },
    Pass {
        name: "lower_sentinel_cascade",
        doc: "Canonicalise `Temp = X != N; if (Temp)` pairs into `if (X == N)` with then/else \
              swapped, so the cascade matcher (which only accepts direct `==` chains) fires on \
              the enum-switch shape. Must run before cascade_fold.",
        run: |body| tf::lower_sentinel_cascade::lower_sentinel_cascade(body),
    },
    Pass {
        name: "cascade_fold",
        doc: "Collapse Eq-against-literal chains into Stmt::Switch. Cascades take priority over \
              ternary, so this runs before fold_bool_switches.",
        run: |body| tf::cascade_fold::fold_switch_cascades(body),
    },
    Pass {
        name: "refine_loops",
        doc: "Promote While loops to ForC or ForEach. Runs chain-aware over un-inlined \
              cond/increment shapes, so it must precede temp inlining.",
        run: |body| tf::refine_loops::refine_loops(body),
    },
    Pass {
        name: "fold_bool_switches",
        doc: "Collapse two-arm Branch shapes that select between booleans. The structural ternary \
              fold runs later (fold_ternaries) once dead elimination has cleaned the arms.",
        run: |body| tf::ternary_fold::fold_bool_switches(body),
    },
    Pass {
        name: "cse_inline_cluster",
        doc: "Inline adjacent single-use temps in evaluation order, share repeated projections \
              within one call, then inline resulting aliases. Cross-statement sharing needs \
              effects and alias information that the IR does not retain.",
        run: |body| {
            tf::expr_transforms::inline_single_use_temps(body);
            tf::cse_projections::hoist_repeated_projections(body);
            tf::expr_transforms::inline_single_use_temps(body);
        },
    },
    Pass {
        name: "remove_dead_assignments",
        doc: "Sweep the zero-use pure assignments inlining left behind. Runs after \
              cse_inline_cluster.",
        run: |body| tf::dead_stmt::remove_dead_assignments(body),
    },
    Pass {
        name: "strip_scaffold_residue",
        doc: "Remove constant-true noop Branches and empty-pin Sequences. Runs after \
              remove_dead_assignments because some residue arms only become empty once the dead \
              scaffold Assignments inside them are swept.",
        run: |body| tf::strip_scaffold_residue::strip_scaffold_residue(body),
    },
    Pass {
        name: "fold_ternaries",
        doc: "Collapse two-arm Branch shapes whose then/else each hold a single matching \
              Assignment into a ternary. Runs after dead elimination so the surviving Assignments \
              are the real ones.",
        run: |body| tf::ternary_fold::fold_ternaries(body),
    },
    Pass {
        name: "invert_empty_then_branches",
        doc: "Invert `if (cond) {} else { body }` to `if (!cond) { body }`. Runs after \
              cascade_fold / lower_sentinel_cascade / refine_loops have consumed the un-inverted \
              shape, and before normalize_var_names so the negated condition picks up canonical names.",
        run: |body| tf::invert_empty_then::invert_empty_then_branches(body),
    },
    Pass {
        name: "rename_outparam_temps",
        doc: "Collapse unambiguous pure-call out-param temps `$<Call>_<Param>` to `$<Param>`. \
              Runs late (after cse_inline_cluster + remove_dead_assignments) so only surviving \
              temps rename, and before normalize_var_names.",
        run: |body| tf::rename_outparam::rename_outparam_temps(body),
    },
    Pass {
        name: "normalize_var_names",
        doc: "Rename ForC counter temporaries (Temp_int_Loop_Counter_Variable_N -> i/j/k) and \
              struct-construction temporaries (Temp_struct_var_N -> stripped type name). MUST run \
              last so earlier passes see the original Blueprint-generated names.",
        run: |body| tf::var_names::normalize_var_names(body),
    },
];

/// Run the full transform pipeline ([`STACK`]) over one decoded body.
pub(crate) fn apply_transform_stack_to_body(
    body: &mut Vec<Stmt>,
) -> crate::bytecode::body_origins::BodyOrigins {
    let mut origins = crate::bytecode::body_origins::BodyOrigins::new(body);
    for pass in STACK {
        // These passes only rewrite expressions or names. Statement occurrence
        // paths remain identical, even when several statements share an offset.
        if matches!(
            pass.name,
            "lower_binary_ops"
                | "lower_static_library_calls"
                | "lower_array_get_out"
                | "strip_latent_action_info"
                | "fold_bool_switches"
                | "rename_outparam_temps"
                | "normalize_var_names"
        ) {
            (pass.run)(body);
        } else {
            origins.apply(body, pass.run);
        }
    }
    origins
}

#[cfg(test)]
mod tests {
    use super::{apply_transform_stack_to_body, STACK};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::{LoopKind, Stmt};
    use crate::bytecode::transforms::test_fixtures::{assign, call, lit, var};
    use crate::bytecode::transforms::visit::{walk_body_exprs, walk_stmt_children};

    fn pos(name: &str) -> usize {
        STACK
            .iter()
            .position(|pass| pass.name == name)
            .unwrap_or_else(|| panic!("no pass named `{name}` in STACK"))
    }

    #[test]
    fn pass_names_are_unique() {
        let mut names: Vec<&str> = STACK.iter().map(|pass| pass.name).collect();
        let total = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), total, "duplicate pass name in STACK");
    }

    #[test]
    fn every_pass_documents_its_rationale() {
        for pass in STACK {
            assert!(
                !pass.doc.is_empty(),
                "pass `{}` has an empty doc",
                pass.name
            );
        }
    }

    #[test]
    fn lower_binary_ops_runs_first() {
        // Downstream passes assume operators are typed Expr::Binary, not Call strings.
        assert_eq!(pos("lower_binary_ops"), 0);
    }

    #[test]
    fn var_names_runs_last() {
        // Earlier passes must see the original Blueprint-generated temp names.
        assert_eq!(pos("normalize_var_names"), STACK.len() - 1);
    }

    #[test]
    fn sentinel_cascade_before_cascade_fold() {
        assert!(pos("lower_sentinel_cascade") < pos("cascade_fold"));
    }

    #[test]
    fn cascade_fold_before_bool_switch_fold() {
        assert!(pos("cascade_fold") < pos("fold_bool_switches"));
    }

    /// The owner-event re-decode (`decode_owner_event_body` in orchestrate.rs)
    /// runs `recognize_latches` then `derive_flipflop_names` directly; this
    /// asserts the main pipeline keeps the same relative order so the two
    /// stay consistent.
    #[test]
    fn recognize_latches_before_flipflop_naming() {
        assert!(pos("recognize_latches") < pos("derive_flipflop_names"));
    }

    #[test]
    fn refine_loops_before_invert_empty_then() {
        assert!(pos("refine_loops") < pos("invert_empty_then_branches"));
    }

    #[test]
    fn dead_stmt_before_scaffold_strip() {
        assert!(pos("remove_dead_assignments") < pos("strip_scaffold_residue"));
    }

    #[test]
    fn ternary_fold_runs_after_dead_stmt() {
        assert!(pos("remove_dead_assignments") < pos("fold_ternaries"));
    }

    #[test]
    fn rename_outparam_after_cluster_before_var_names() {
        assert!(pos("cse_inline_cluster") < pos("rename_outparam_temps"));
        assert!(pos("rename_outparam_temps") < pos("normalize_var_names"));
    }

    fn break_vector() -> Stmt {
        call(
            "BreakVector",
            vec![var("self.Direction"), var("$BreakVector_X")],
        )
    }

    fn consumer() -> Stmt {
        call("Consume", vec![var("$BreakVector_X")])
    }

    fn call_count(body: &[Stmt], call_name: &str) -> usize {
        let mut count = 0;
        for stmt in body {
            if matches!(stmt, Stmt::Call { func: Expr::Var(name), .. } if name == call_name) {
                count += 1;
            }
            walk_stmt_children(stmt, &mut |children| {
                count += call_count(children, call_name)
            });
        }
        count
    }

    fn expression_call_count(body: &[Stmt], call_name: &str) -> usize {
        let mut count = 0;
        walk_body_exprs(body, &mut |expr| {
            if matches!(expr, Expr::Call { name, .. } if name == call_name) {
                count += 1;
            }
        });
        count
    }

    #[test]
    fn sibling_branches_keep_their_own_output_computations() {
        let mut body = vec![Stmt::Branch {
            cond: var("self.Enabled"),
            then_body: vec![break_vector(), consumer()],
            else_body: vec![break_vector(), consumer()],
            offset: 0,
        }];

        apply_transform_stack_to_body(&mut body);

        let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            panic!("expected both branch arms to remain");
        };
        assert_eq!(call_count(then_body, "BreakVector"), 1);
        assert_eq!(call_count(else_body, "BreakVector"), 1);
        assert_eq!(call_count(then_body, "Consume"), 1);
        assert_eq!(call_count(else_body, "Consume"), 1);
    }

    #[test]
    fn branch_local_computation_does_not_replace_post_branch_call() {
        let mut body = vec![
            Stmt::Branch {
                cond: var("self.Enabled"),
                then_body: vec![break_vector(), consumer()],
                else_body: vec![],
                offset: 0,
            },
            break_vector(),
            consumer(),
        ];

        apply_transform_stack_to_body(&mut body);

        assert_eq!(call_count(&body, "BreakVector"), 2);
    }

    #[test]
    fn loop_evaluations_remain_inside_the_loop() {
        let mut body = vec![
            break_vector(),
            consumer(),
            Stmt::Loop {
                kind: LoopKind::While,
                cond: None,
                body: vec![break_vector(), consumer()],
                completion: Some(vec![break_vector(), consumer()]),
                offset: 0,
            },
        ];

        apply_transform_stack_to_body(&mut body);

        let loop_stmt = body
            .iter()
            .find(|stmt| matches!(stmt, Stmt::Loop { .. }))
            .expect("loop must remain");
        let Stmt::Loop {
            body: loop_body,
            completion,
            ..
        } = loop_stmt
        else {
            unreachable!();
        };
        assert_eq!(call_count(loop_body, "BreakVector"), 1);
        assert_eq!(call_count(completion.as_ref().unwrap(), "BreakVector"), 1);
        assert_eq!(call_count(&body, "BreakVector"), 3);
    }

    #[test]
    fn input_and_output_writes_require_fresh_evaluations() {
        for intervening in [
            assign("self.Direction", lit("NewDirection")),
            assign("$BreakVector_X", lit("42")),
        ] {
            let mut body = vec![
                break_vector(),
                consumer(),
                intervening,
                break_vector(),
                consumer(),
            ];

            apply_transform_stack_to_body(&mut body);

            assert_eq!(call_count(&body, "BreakVector"), 2);
        }
    }

    #[test]
    fn unknown_calls_and_events_require_fresh_evaluations() {
        for intervening in [
            call("MutateDirection", vec![]),
            Stmt::EventCall {
                event_name: "UpdateDirection".into(),
                offset: 0,
            },
        ] {
            let mut body = vec![
                break_vector(),
                consumer(),
                intervening,
                break_vector(),
                consumer(),
            ];

            apply_transform_stack_to_body(&mut body);

            assert_eq!(call_count(&body, "BreakVector"), 2);
        }
    }

    #[test]
    fn output_pin_prefix_does_not_establish_bare_call_purity() {
        for explicit_out in [false, true] {
            let output = var("$CustomAction_Result");
            let output = if explicit_out {
                Expr::Out(Box::new(output))
            } else {
                output
            };
            let invocation = call("CustomAction", vec![output]);
            let mut body = vec![invocation.clone(), invocation];

            apply_transform_stack_to_body(&mut body);

            assert_eq!(call_count(&body, "CustomAction"), 2);
        }
    }

    #[test]
    fn adjacent_calls_named_like_builtins_still_require_callee_identity() {
        let mut body = vec![break_vector(), break_vector()];

        apply_transform_stack_to_body(&mut body);

        assert_eq!(call_count(&body, "BreakVector"), 2);
    }

    #[test]
    fn assignment_output_prefix_does_not_establish_determinism() {
        for call_name in ["RandomFloat", "CustomAction", "GetVelocity"] {
            let first_output = format!("${call_name}_ReturnValue");
            let second_output = format!("${call_name}_ReturnValue_1");
            let evaluation = Expr::Call {
                name: call_name.into(),
                args: vec![],
            };
            let mut body = vec![
                assign(&first_output, evaluation.clone()),
                assign(&second_output, evaluation),
                call("Consume", vec![var(&first_output), var(&second_output)]),
            ];

            apply_transform_stack_to_body(&mut body);

            assert_eq!(expression_call_count(&body, call_name), 2, "{call_name}");
        }
    }
    #[test]
    fn repeated_read_only_projection_still_hoists_in_one_statement() {
        let projection = Expr::FieldAccess {
            recv: Box::new(var("self.State")),
            field: "Value".into(),
        };
        let mut body = vec![call(
            "Consume",
            vec![projection.clone(), projection.clone(), projection],
        )];

        apply_transform_stack_to_body(&mut body);

        let mut projection_count = 0;
        walk_body_exprs(&body, &mut |expr| {
            if matches!(expr, Expr::FieldAccess { field, .. } if field == "Value") {
                projection_count += 1;
            }
        });
        assert_eq!(projection_count, 1);
        assert_eq!(call_count(&body, "Consume"), 1);
    }

    fn field_assign(temp: &str, field: &str, rhs: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: Expr::FieldAccess {
                recv: Box::new(var(temp)),
                field: field.into(),
            },
            rhs,
            offset: 0,
        }
    }

    fn expression_call(name: &str) -> Expr {
        Expr::Call {
            name: name.into(),
            args: vec![],
        }
    }

    fn struct_field_writes(temp: &str) -> Vec<Stmt> {
        vec![
            field_assign(temp, "First", expression_call("ReadFirst")),
            field_assign(temp, "Second", lit("2")),
        ]
    }

    #[test]
    fn struct_field_evaluations_stay_before_later_call_arguments() {
        let temp = "$MakeStruct_Pair";
        let mut body = struct_field_writes(temp);
        body.push(call(
            "Consume",
            vec![expression_call("MutateSource"), var(temp)],
        ));
        let original = body.clone();

        apply_transform_stack_to_body(&mut body);

        assert!(
            body == original,
            "field evaluation must precede MutateSource"
        );
    }

    #[test]
    fn struct_field_evaluations_stay_before_lazy_and_repeated_uses() {
        let temp = "$MakeStruct_Pair";
        for consumer in [
            call(
                "Consume",
                vec![Expr::Ternary {
                    cond: Box::new(var("Enabled")),
                    then_expr: Box::new(var(temp)),
                    else_expr: Box::new(lit("None")),
                }],
            ),
            Stmt::Branch {
                cond: var("Enabled"),
                then_body: vec![call("Consume", vec![var(temp)])],
                else_body: vec![],
                offset: 0,
            },
            Stmt::Loop {
                kind: LoopKind::While,
                cond: Some(Expr::FieldAccess {
                    recv: Box::new(var(temp)),
                    field: "Second".into(),
                }),
                body: vec![call("UpdateState", vec![])],
                completion: None,
                offset: 0,
            },
        ] {
            let mut body = struct_field_writes(temp);
            body.push(consumer);
            let original = body.clone();

            apply_transform_stack_to_body(&mut body);

            assert!(
                body == original,
                "field evaluations must execute once, eagerly"
            );
        }
    }

    #[test]
    fn struct_updates_keep_existing_fields_and_repeated_writes() {
        let temp = "$MakeStruct_Pair";
        let mut body = vec![
            assign(temp, expression_call("LoadExisting")),
            field_assign(temp, "First", expression_call("ReadFirst")),
            field_assign(temp, "First", expression_call("ReadReplacement")),
            call("Consume", vec![var(temp)]),
        ];
        let original = body.clone();

        apply_transform_stack_to_body(&mut body);

        assert!(
            body == original,
            "partial update must retain untouched fields and both calls"
        );
    }

    #[test]
    fn struct_field_writes_preserve_storage_and_cross_scope_references() {
        let temp = "$MakeStruct_Pair";
        for consumer in [
            call("Mutate", vec![Expr::Out(Box::new(var(temp)))]),
            field_assign(temp, "Third", expression_call("ReadThird")),
        ] {
            let mut body = struct_field_writes(temp);
            body.push(consumer);
            body.push(Stmt::Branch {
                cond: var("Enabled"),
                then_body: vec![call("Observe", vec![var(temp)])],
                else_body: vec![],
                offset: 0,
            });
            let original = body.clone();

            apply_transform_stack_to_body(&mut body);

            assert!(
                body == original,
                "storage and later uses must retain the original struct"
            );
        }
    }

    #[test]
    fn struct_field_writes_do_not_invent_complete_constructors() {
        for destination in ["$MakeStruct_Pair", "SavedState", "self.State"] {
            let mut body = struct_field_writes(destination);
            body.push(call("Consume", vec![var(destination)]));
            let original = body.clone();

            apply_transform_stack_to_body(&mut body);

            assert!(
                body == original,
                "a name and two fields cannot prove a complete constructor"
            );
        }
    }

    #[test]
    fn invariant_loop_conditions_do_not_reduce_iteration_count() {
        for condition in [var("Enabled"), var("self.KeepRunning"), lit("true")] {
            for loop_body in [vec![], vec![call("UpdateState", vec![])]] {
                let mut body = vec![Stmt::Loop {
                    kind: LoopKind::While,
                    cond: Some(condition.clone()),
                    body: loop_body,
                    completion: None,
                    offset: 0,
                }];
                let original = body.clone();

                apply_transform_stack_to_body(&mut body);

                assert!(
                    body == original,
                    "invariant conditions still describe repeating loops"
                );
            }
        }
    }

    #[test]
    fn decoded_member_condition_loop_survives_the_full_pipeline() {
        use crate::binary::NameTable;
        use crate::bytecode::decode::decode_asset;
        use crate::bytecode::opcodes::*;
        use crate::types::{AssetVersion, ExportHeader, ImportEntry, ParsedAsset};
        use std::collections::{BTreeMap, HashMap};

        // Disk field paths occupy 17 bytes but their in-memory form occupies 9.
        // The return starts at memory offset 33, after the backward jump to 0.
        let mut bytecode = vec![EX_JUMP_IF_NOT];
        bytecode.extend_from_slice(&33u32.to_le_bytes());
        bytecode.push(EX_INSTANCE_VARIABLE);
        for component in [1i32, 0, 0, 0] {
            bytecode.extend_from_slice(&component.to_le_bytes());
        }
        bytecode.push(EX_VIRTUAL_FUNCTION);
        bytecode.extend_from_slice(&1i32.to_le_bytes());
        bytecode.extend_from_slice(&0i32.to_le_bytes());
        bytecode.push(EX_END_FUNCTION_PARMS);
        bytecode.push(EX_JUMP);
        bytecode.extend_from_slice(&0u32.to_le_bytes());
        bytecode.extend_from_slice(&[EX_RETURN, EX_NOTHING, EX_END_OF_SCRIPT]);
        let asset = ParsedAsset {
            version: AssetVersion {
                file_ver: 522,
                file_ver_ue5: 0,
            },
            name_table: NameTable::from_names(vec!["KeepRunning".into(), "UpdateState".into()]),
            diagnostics: vec![],
            imports: vec![
                ImportEntry {
                    class_package: "/Script/CoreUObject".into(),
                    class_name: "Package".into(),
                    object_name: "/Script/CoreUObject".into(),
                    outer_index: 0,
                },
                ImportEntry {
                    class_package: "/Script/CoreUObject".into(),
                    class_name: "Class".into(),
                    object_name: "Function".into(),
                    outer_index: -1,
                },
            ],
            exports: vec![(
                ExportHeader {
                    class_index: -2,
                    super_index: 0,
                    outer_index: 0,
                    object_name: "LoopProbe".into(),
                    serial_offset: 0,
                    serial_size: 0,
                },
                vec![],
            )],
            pin_data: HashMap::new(),
            function_signatures: BTreeMap::new(),
            bytecode_by_export: BTreeMap::from([(1, (bytecode, 36))]),
        };

        let decoded = decode_asset(&asset);

        assert!(decoded.diagnostics.is_empty(), "{:?}", decoded.diagnostics);
        let function = decoded
            .functions
            .iter()
            .find(|function| function.name == "LoopProbe")
            .unwrap();
        let Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(condition),
            body,
            ..
        } = &function.body[0]
        else {
            panic!("a backedge through UpdateState must remain a loop");
        };
        assert_eq!(condition, &var("self.KeepRunning"));
        assert_eq!(call_count(body, "UpdateState"), 1);
    }
}
