//! Body transform pipeline: lowers, folds, and normalises the decoded
//! statement tree into its final rendered shape.

// Transform order:
// 0. Binary op lowering converts math-library calls (Less_IntInt,
//    Add_FloatFloat, etc.) to typed Expr::Binary nodes so all
//    downstream passes see operators rather than opaque Call strings.
// 1. Latch recognition needs the unfolded gate-variable Branch shapes.
// 1b. Sentinel-cascade lowering canonicalises `Temp = X != N; if (Temp)`
//    pairs into `if (X == N)` with then/else swapped, so the cascade
//    matcher (which only accepts direct `==` chains) fires on the
//    enum-switch shape.
// 2. Cascade fold collapses any remaining Eq-against-literal chains
//    into Stmt::Switch (cascades take priority over ternary).
// 3. Struct fold collapses contiguous-field-assignment runs into
//    Expr::StructConstruct at the use site.
// 4. Demote invariant-cond Whiles to Branches. Some back-edges that
//    `try_decode_loop` accepts come from non-loop control structures
//    (Sequence pins, IsValid/DoOnce wrappers). Their cond is a single
//    Var that the body never mutates, which a real While never is.
//    Recognizers below run chain-aware against the un-inlined IR, so
//    cond/increment/array still appear as `Var` references to local
//    temp definitions.
// 5. Loop refinement promotes While loops to ForC or ForEach. Runs
//    chain-aware over un-inlined cond/increment shapes.
// 6. Temp inlining cleans up single-use artifacts left over from the
//    above passes. Recurses fully into every nested body (Branch arms,
//    Loop body/completion/ForC slots, Switch case bodies, Sequence pin
//    bodies, Latch init/body) via `walk_stmt_children_mut`.
// 7. Dead-statement removal sweeps zero-use pure assignments that
//    inlining left behind.
// 7b. Scaffold-residue strip removes constant-true noop Branches and
//    empty-pin Sequences. Runs after dead-stmt because some residue
//    arms only become empty once dead scaffold Assignments inside
//    them are swept.
// 8. Ternary fold collapses two-arm Branch shapes whose then/else
//    each contain a single matching Assignment. Runs after dead
//    elimination so the surviving Assignments are the real ones.
// 9. Variable name normalisation renames ForC counter temporaries
//    (Temp_int_Loop_Counter_Variable_N -> i/j/k) and struct-construction
//    temporaries (Temp_struct_var_N -> stripped type name). Runs last so
//    earlier passes see the original Blueprint-generated names.
pub(crate) fn apply_transform_stack_to_body(body: &mut Vec<crate::bytecode::stmt::Stmt>) {
    use crate::bytecode::transforms;
    transforms::lower_binary_ops::lower_binary_ops(body);
    transforms::lower_static_library_calls::lower_static_library_calls(body);
    transforms::lower_array_get_out::lower_array_get_out_to_assignment(body);
    transforms::strip_latent_action_info::strip_latent_action_info(body);
    transforms::latch_recognition::recognize_latches(body);
    transforms::latch_recognition::rewrite_reset_doonce_names(body);
    transforms::flipflop_naming::derive_flipflop_names(body);
    transforms::collapse_nested_doonce::collapse_nested_doonce(body);
    transforms::lower_sentinel_cascade::lower_sentinel_cascade(body);
    transforms::cascade_fold::fold_switch_cascades(body);
    transforms::struct_fold::fold_struct_constructions(body);
    transforms::demote_invariant_loops::demote_invariant_loops(body);
    transforms::refine_loops::refine_loops(body);
    transforms::ternary_fold::fold_bool_switches(body);
    transforms::expr_transforms::inline_single_use_temps(body);
    // Dedupe pure-call duplicates the BP compiler emits per consumer site
    // (e.g. `GetWheelVelocity`, `BreakHitResult`). Runs after the first
    // inliner pass (so single-use pure-call definitions have already been
    // inlined into their consumers) and before dead-stmt removal (which
    // sweeps the `$X = $keeper` chains this pass creates).
    transforms::cse_pure_calls::cse_pure_calls(body);
    transforms::cse_projections::hoist_repeated_projections(body);
    // Re-run the inliner so trivial `$X = $Cse_N` aliases (BP-emitted
    // temp slots whose rhs CSE just rewrote to a Var) collapse before
    // dead-stmt removal.
    transforms::expr_transforms::inline_single_use_temps(body);
    // Inline Blueprint-rematerialised scratch temps (a multi-def temp
    // whose defs all assign the same read-only parameter). CSE leaves the
    // condition var of a hoisted `$Cse` referencing such a temp while its
    // defs become dead; without this the next pass strips the defs and
    // leaves a use of an undefined variable.
    transforms::expr_transforms::inline_uniform_multidef_param_temps(body);
    transforms::dead_stmt::remove_dead_assignments(body);
    // Inlining + dead-stmt removal expose scaffold-shaped
    // `Branch { cond: Literal("true"), then: [], else: [] }` and
    // empty-pin `Sequence` residues. Runs after dead-stmt because
    // some residue arms only become empty once dead Assignments
    // (gate / init temps) inside them are swept.
    transforms::strip_scaffold_residue::strip_scaffold_residue(body);
    transforms::ternary_fold::fold_ternaries(body);
    // Invert `if (cond) {} else { body }` -> `if (!cond) { body }`. Runs
    // after cascade-fold / sentinel-cascade / refine-loops consume the
    // un-inverted shape, and before var-name normalisation so the
    // negated condition picks up the same canonical names.
    transforms::invert_empty_then::invert_empty_then_branches(body);
    // Collapse unambiguous pure-call out-param temps `$<Call>_<Param>` ->
    // `$<Param>`. Runs late (after CSE + inline + dead-stmt) so only
    // surviving temps rename, and before var-name normalisation.
    transforms::rename_outparam::rename_outparam_temps(body);
    transforms::var_names::normalize_var_names(body);
}
