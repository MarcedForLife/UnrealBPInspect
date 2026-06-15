//! Latch-pattern recognition for the IR.
//!
//! A post-pass over the decoded statement tree that finds gated `Stmt::Branch`
//! shapes matching the Blueprint compiler's DoOnce / FlipFlop emission, and
//! rewrites them as `Stmt::Latch` with the appropriate `LatchKind`.
//!
//! Recognises DoOnce and FlipFlop patterns over a single shared walker.
//!
//! The recognizer runs before single-use temp inlining so the gate variable
//! pattern is still intact when matching.
//!
//! Both latches are encoded by the Blueprint compiler as
//! `Temp_bool_IsClosed_Variable[_N]` / `Temp_bool_Has_Been_Initd_Variable[_M]`
//! gate variables for DoOnce, and `Temp_bool_Variable[_N]` for FlipFlop.

mod cross_event;
mod doonce;
mod flipflop;
mod init_check;
mod shared;

// Re-exports: keep every item previously reachable as
// `transforms::latch_recognition::X` resolving unchanged for external
// consumers (decode/mod.rs, k2node_byte_map, region_decode doc refs).
pub use doonce::{rewrite_asset_wide_reset_doonce_names, rewrite_reset_doonce_names};
pub(crate) use shared::LIBRARY_FUNC_PREFIXES;
pub(crate) use shared::{
    DOONCE_CALL_NAME, DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX, FLIPFLOP_TOGGLE_PREFIX,
    RESET_DOONCE_CALL_NAME,
};

use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::visit::descend_into_children;
use cross_event::{try_rewrite_cross_event_doonce_in_sequence, try_rewrite_multi_sequence_doonce};
use doonce::{
    absorb_post_chain_reset_into_else, try_rewrite_compound_doonce, try_rewrite_cross_arm_doonce,
    try_rewrite_doonce, try_rewrite_reset_doonce_pair,
};
use flipflop::{
    build_embedded_flipflop_latch, build_flipflop_latch, build_shared_arms_flipflop_latch,
    detect_flipflop_at, FlipFlopMatch,
};
use init_check::{
    peel_init_check_around_doonce, strip_phantom_init_doonce, unwrap_scaffold_sequence_around_latch,
};

/// Walk a statement body, rewriting recognized latch shapes in-place.
///
/// Recurses into every nested `Vec<Stmt>` (Branch, Sequence, Loop, Switch,
/// Latch) so latches nested inside other constructs are also rewritten.
/// FlipFlop recognition needs to splice across sibling statements, so the
/// entry takes a `Vec` rather than a slice.
pub fn recognize_latches(body: &mut Vec<Stmt>) {
    recognize_in_body(body, &[]);
}

/// When `slot` is a freshly-wrapped `Stmt::Latch`, re-run recognition on its
/// body so DoOnce/FlipFlop nested inside the folded user content also folds.
fn recurse_wrapped_latch(slot: &mut Stmt, ancestors: &[&[Stmt]]) {
    if let Stmt::Latch { body: inner, .. } = slot {
        recognize_in_body(inner, ancestors);
    }
}

/// `ancestors` is innermost-first: each slice is the preceding-siblings
/// view at one outer nesting level. FlipFlop chain resolution searches
/// the current body plus ancestors so a toggle's chained def in a parent
/// scope still resolves.
fn recognize_in_body(body: &mut Vec<Stmt>, ancestors: &[&[Stmt]]) {
    descend_into_children(body, ancestors, &mut |sub_body, child_ancestors| {
        recognize_in_body(sub_body, child_ancestors)
    });

    // Cross-Sequence compound DoOnce: when the BP compiler splits the
    // user-body-wrap DoOnce's scaffold across multiple sibling Sequences
    // or sibling stmts at the same body level. Runs before the
    // ResetDoOnce-pair fold so raw scaffold pieces (especially the
    // bare-suffix init-set the BP compiler emits at the parent body for
    // nested cross-event DoOnces) are still visible. Suffix-matched so
    // adjacent DoOnce macros with different suffixes stay independent.
    if try_rewrite_multi_sequence_doonce(body) {
        // Re-run recursion on any newly-wrapped Latch bodies so nested
        // DoOnce/FlipFlop inside the folded user-body content also folds.
        for stmt in body.iter_mut() {
            recurse_wrapped_latch(stmt, ancestors);
        }
    }

    // ResetDoOnce gate-reset pair. The BP compiler inlines a
    // `ResetDoOnce(<macro>)` macro instance as the 2-statement sequence
    // `IsClosed_<N> = false; Has_Been_Initd_<N> = true`. Run before the
    // compound DoOnce recognizer so the rewritten `Stmt::Call(ResetDoOnce)`
    // is visible to subsequent passes, and so the assignments survive
    // `dead_stmt::remove_dead_assignments` (which only targets Assignment).
    try_rewrite_reset_doonce_pair(body);

    // Cross-event inline DoOnce fold: collapse the 2-pin Sequence shape
    // the walker emits for a cross-event-inlined DoOnce in an outer
    // `if`-else arm. The compiler emits the macro as
    //   Sequence { pin0: [Call(ResetDoOnce, DoOnce_<N>)],
    //              pin1: [Sequence{ pin0: [Branch(cond=gate, empty),
    //                                       Assignment(gate=true),
    //                                       Call(<user_call>, ...)] }] }
    // when the gate variable's owning Latch lives in a sibling event
    // (so the local body has no init-check / init-set / outer suffix).
    // The standard compound-DoOnce recognizer can't match it because
    // pin0 carries the folded ResetDoOnce call instead of raw scaffold
    // pieces and pin1 wraps the user body in an extra Sequence layer.
    // Replace the outer Sequence with the lifted ResetDoOnce sibling
    // plus a `Latch::DoOnce` over the user call, the same shape the
    // 5.3 path produces for this site via `try_rewrite_compound_doonce`.
    if try_rewrite_cross_event_doonce_in_sequence(body) {
        // Recurse into newly-wrapped Latch bodies so any nested
        // DoOnce/FlipFlop in the user call also folds.
        for stmt in body.iter_mut() {
            recurse_wrapped_latch(stmt, ancestors);
        }
    }

    // Post-chain DoOnce reset-into-else absorption. When a
    // DoOnce-inside-if leaves its gate-clear pair fall-through-positioned
    // as a sibling of the outer if (because the BP compiler placed the
    // gate-clear at addresses inside the outer JIN's ELSE-flow direction
    // but outside its THEN range), promote the trailing ResetDoOnce into
    // the outer if's empty else_body so it renders as the structural else
    // of the gate-check rather than as a top-level trailing call.
    absorb_post_chain_reset_into_else(body);

    // Compound DoOnce: BP-emitted macro expansion spanning an init-check
    // Branch + gate-check Branch + their set assignments + a scaffold-only
    // Sequence. Real fixtures always emit this shape; the single-Branch
    // shape below only appears in synthetic tests now.
    if try_rewrite_compound_doonce(body) {
        // Recurse into the wrapping Latch's body so nested
        // DoOnce/FlipFlop inside the user's content also folds.
        if let Some(slot) = body.last_mut() {
            recurse_wrapped_latch(slot, ancestors);
        }
    }

    // Cross-arm compound DoOnce: when the BP compiler splits the DoOnce
    // scaffold across an outer Branch's two arms, the per-arm scan above
    // can't see init-proof for the gate suffix. This pass inspects each
    // top-level Branch and tries to satisfy the missing init-proof from
    // the sibling arm's content (synthetic ResetDoOnce or stray init
    // scaffold pieces). When the pairing holds, the matching arm is
    // rewritten in place into the same `Stmt::Latch::DoOnce` shape the
    // standard recognizer produces.
    if try_rewrite_cross_arm_doonce(body) {
        // Re-run the recognizer on any newly-wrapped Latch bodies so
        // nested DoOnce/FlipFlop inside the arm's content also fold.
        for stmt in body.iter_mut() {
            let Stmt::Branch {
                then_body,
                else_body,
                ..
            } = stmt
            else {
                continue;
            };
            if let Some(slot) = then_body.last_mut() {
                recurse_wrapped_latch(slot, ancestors);
            }
            if let Some(slot) = else_body.last_mut() {
                recurse_wrapped_latch(slot, ancestors);
            }
        }
    }

    // Single-Branch DoOnce. Structural match, no chain resolution needed.
    for stmt in body.iter_mut() {
        if let Some(rewritten) = try_rewrite_doonce(stmt) {
            *stmt = rewritten;
            recurse_wrapped_latch(stmt, ancestors);
        }
    }

    recognize_flipflops_in_body(body, ancestors);

    // Alt-path scaffold cleanup. The region-decode path can leave DoOnce
    // scaffolding partially-folded as a Sequence wrapper
    // around a real Latch and emit a phantom `Latch::DoOnce` whose
    // gate is actually the macro's init guard. Strip the noise so the
    // remaining Latch matches the expected shape.
    strip_phantom_init_doonce(body);
    unwrap_scaffold_sequence_around_latch(body);
    // Peel init/gate-check Branch wrappers whose then-arm holds a
    // recognised `Stmt::Latch::DoOnce` and whose else-arm is empty or
    // pure scaffold. These appear when an outer compound DoOnce wraps
    // an inner DoOnce whose own init-check Branch survived as the
    // inner body's wrapper. Without peeling, the outer Latch renders
    // with a stray `if (Temp_bool_Has_Been_Initd_Variable)` around the
    // inner DoOnce in the final output.
    peel_init_check_around_doonce(body);
}

/// Walk `body` forward, rewriting each detected FlipFlop into a `Stmt::Latch`.
/// On a match the toggle scaffold is drained and the Branch slot replaced; the
/// per-variant index arithmetic accounts for the statements removed before/after
/// the Branch so the walk resumes just past the new Latch.
fn recognize_flipflops_in_body(body: &mut Vec<Stmt>, ancestors: &[&[Stmt]]) {
    let mut idx = 0;
    while idx < body.len() {
        match detect_flipflop_at(body, idx, ancestors) {
            Some(FlipFlopMatch::Standard(consumed_before)) => {
                let rewritten = build_flipflop_latch(&mut body[idx]);
                let start = idx - consumed_before;
                body.drain(start..idx);
                body[start] = rewritten;
                recurse_wrapped_latch(&mut body[start], ancestors);
                idx = start + 1;
            }
            Some(FlipFlopMatch::Embedded(consumer_count)) => {
                let start = idx - consumer_count;
                let consumers: Vec<Stmt> = body.drain(start..idx).collect();
                // idx now points to the branch (shifted down by consumer_count)
                let branch_idx = start;
                let rewritten = build_embedded_flipflop_latch(&mut body[branch_idx], consumers);
                body[branch_idx] = rewritten;
                recurse_wrapped_latch(&mut body[branch_idx], ancestors);
                idx = branch_idx + 1;
            }
            Some(FlipFlopMatch::SharedArms {
                consumed_before,
                consumed_after,
            }) => {
                let start = idx - consumed_before;
                // Take the trailing user content first so we can drop the
                // toggle-scaffold preceding chain and Branch slot
                // independently. `idx + 1 .. idx + 1 + consumed_after`
                // identifies the trailing slice while the Branch still
                // lives at `idx`.
                let absorbed_end = idx + 1 + consumed_after;
                let absorbed: Vec<Stmt> = body.drain((idx + 1)..absorbed_end).collect();
                // Now drop the preceding toggle chain and replace the
                // Branch slot with the wrapped Latch.
                let rewritten = build_shared_arms_flipflop_latch(&mut body[idx], absorbed);
                body.drain(start..idx);
                body[start] = rewritten;
                recurse_wrapped_latch(&mut body[start], ancestors);
                idx = start + 1;
            }
            Some(FlipFlopMatch::TrailingToggle {
                user_body_count,
                toggle_drain,
            }) => {
                // Drop the trailing toggle chain first so its disappearance
                // doesn't shift indices for the user-body drain.
                let toggle_start = idx + 1 + user_body_count;
                body.drain(toggle_start..(toggle_start + toggle_drain));
                let absorbed_end = idx + 1 + user_body_count;
                let absorbed: Vec<Stmt> = body.drain((idx + 1)..absorbed_end).collect();
                let rewritten = build_shared_arms_flipflop_latch(&mut body[idx], absorbed);
                body[idx] = rewritten;
                recurse_wrapped_latch(&mut body[idx], ancestors);
                idx += 1;
            }
            None => {
                idx += 1;
            }
        }
    }
}
