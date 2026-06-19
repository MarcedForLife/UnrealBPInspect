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
        name: "rewrite_reset_doonce_names",
        doc: "Resolve sibling ResetDoOnce(DoOnce_N) arguments back to the matching latch's \
              display name. Runs right after recognize_latches, while the latches are fresh.",
        run: |body| tf::latch_recognition::rewrite_reset_doonce_names(body),
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
        name: "struct_fold",
        doc: "Collapse a contiguous run of field assignments to a temporary into a single \
              Expr::StructConstruct at the use site.",
        run: |body| tf::struct_fold::fold_struct_constructions(body),
    },
    Pass {
        name: "demote_invariant_loops",
        doc: "Demote invariant-cond While loops back to Branches. Some back-edges try_decode_loop \
              accepts come from non-loop control (Sequence pins, IsValid/DoOnce wrappers) whose \
              cond is a single never-mutated Var, which a real While never is. Runs chain-aware \
              over the un-inlined IR, before refine_loops.",
        run: |body| tf::demote_invariant_loops::demote_invariant_loops(body),
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
        doc: "Clean up the single-use artifacts the recognition/fold passes leave, as one fixed \
              sequence (NOT a fixpoint loop; the steps are non-idempotent lowerings): \
              (1) inline single-use temps; (2) cse_pure_calls dedups the pure-call duplicates the \
              BP compiler emits per consumer site (e.g. GetWheelVelocity, BreakHitResult); \
              (3) hoist_repeated_projections hoists repeated projections; (4) re-run the inliner so \
              the `$X = $Cse_N` aliases CSE just created collapse before dead-stmt; \
              (5) inline_uniform_multidef_param_temps inlines a multi-def temp whose defs all assign \
              the same read-only parameter, which CSE leaves referencing soon-to-be-dead defs.",
        run: |body| {
            tf::expr_transforms::inline_single_use_temps(body);
            tf::cse_pure_calls::cse_pure_calls(body);
            tf::cse_projections::hoist_repeated_projections(body);
            tf::expr_transforms::inline_single_use_temps(body);
            tf::expr_transforms::inline_uniform_multidef_param_temps(body);
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
pub(crate) fn apply_transform_stack_to_body(body: &mut Vec<Stmt>) {
    for pass in STACK {
        (pass.run)(body);
    }
}

#[cfg(test)]
mod tests {
    use super::STACK;

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
}
