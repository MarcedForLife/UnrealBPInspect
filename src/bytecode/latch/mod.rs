//! DoOnce and FlipFlop latch node transformation. Replaces raw latch bytecode
//! with structured pseudocode (`DoOnce(name) {`, `ResetDoOnce(name)`,
//! `FlipFlop(name) { A|B: { ... } }`). Runs per-event after CFG partitioning
//! in the ubergraph pipeline so events don't interfere.
//!
//! DoOnce uses two hidden vars per instance: `Temp_bool_IsClosed_Variable[_N]`
//! (gate, true = closed) and `Temp_bool_Has_Been_Initd_Variable[_M]`
//! (first-exec flag). The init block sets `Has_Been_Initd` and initial
//! `IsClosed`; each execution the gate check skips when closed, otherwise
//! closes the gate and runs the body. Resets set `IsClosed = false`.
//!
//! FlipFlop adds a `Temp_bool_Variable` toggle negated each execution, with
//! branches for the A and B paths.

mod doonce;
mod flipflop;
mod transform;

#[cfg(test)]
mod tests;

use super::decode::BcStatement;

pub(super) const GATE_PREFIX: &str = "Temp_bool_IsClosed_Variable";
pub(super) const INIT_PREFIX: &str = "Temp_bool_Has_Been_Initd_Variable";

pub use flipflop::precompute_flipflop_names;

/// Detect and transform all latch patterns. When `flipflop_names` is provided
/// (pre-computed from the full UberGraph), use those; otherwise derive locally.
pub fn transform_latch_patterns(
    stmts: &mut Vec<BcStatement>,
    flipflop_names: Option<&[(String, String)]>,
) {
    let has_latches = stmts.iter().any(|s| {
        let trimmed = s.text.trim();
        trimmed.contains(GATE_PREFIX)
            || trimmed.contains(INIT_PREFIX)
            || trimmed.contains("Temp_bool_Variable")
    });
    if !has_latches {
        return;
    }

    let local_names;
    let flipflop_rename_pairs: &[(String, String)] = match flipflop_names {
        Some(names) => names,
        None => {
            local_names = flipflop::precompute_flipflop_names(stmts);
            &local_names
        }
    };

    // Collapse converged FlipFlops first: their branch scaffolding would
    // otherwise interfere with init-block detection.
    flipflop::collapse_converged_flipflops(stmts, flipflop_rename_pairs);

    transform::transform_latches(stmts);

    for (toggle_var, name) in flipflop_rename_pairs {
        flipflop::rename_flipflop_refs(stmts, toggle_var, name);
    }
}
