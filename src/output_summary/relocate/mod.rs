//! Post-structure text pass that relocates orphan `DoOnce(X) { ... }`
//! blocks into the branches of an adjacent `if (...)` whose pin hints
//! attribute `X` to a specific side.
//!
//! The K2 compiler lowers a Branch with DoOnce on each side into flat
//! bytecode, leaving only the Reset calls inside the if and emitting the
//! DoOnce openers AFTER it. The CFG structurer cannot re-nest them on its
//! own. This pass closes the gap by reading `pin_hints_scope` for the
//! current function and moving the orphaned openers back inside.
//!
//! Operates on the pre-`apply_indentation` line list, matching on string
//! prefixes and brace depth, not any structured IR. No-op when no scope
//! is installed, no hints exist for the function, or the line list does
//! not match the expected shape.
//!
//! Submodules, one per pipeline phase:
//!
//! - [`if_block`] — find + parse `if (...) { ... }` (plus optional `else`).
//! - [`matching`] — pick the single `BranchInfo` whose pin-only sets
//!   overlap the body.
//! - [`rewrite`] — pull CONTIGUOUS `DoOnce(X) { ... }` orphans following
//!   the block and splice each one into its pin-derived side, creating an
//!   `else` clause if absent and un-inverting `if (!...)` when needed.

mod if_block;
mod matching;
mod rewrite;

#[cfg(test)]
mod tests;

use crate::pin_hints::BranchHints;
use crate::pin_hints_scope;

use if_block::find_first_actionable_if;
use rewrite::try_relocate_one;

/// Entry point: relocate orphan DoOnces in `lines` using pin hints for the
/// current function key. No-op when no scope is installed.
pub fn relocate_orphan_doonces_via_hints(lines: &mut Vec<String>) {
    let Some(key) = pin_hints_scope::current_function_key() else {
        return;
    };
    pin_hints_scope::with(|scope| {
        if let Some((hints, _map)) = scope {
            relocate_with_hints(lines, &key, hints);
        }
    });
}

/// Core relocation, split out so unit tests can drive it with a synthetic
/// `BranchHints` without installing a thread-local scope.
///
/// Repeatedly scan for an if-block that has an actionable match. Each
/// successful relocation mutates `lines`, so we restart from the top to
/// keep indices consistent. A function has few ifs, so this is cheap.
fn relocate_with_hints(lines: &mut Vec<String>, function_key: &str, hints: &BranchHints) {
    let Some(branches) = hints.by_function.get(function_key) else {
        return;
    };
    while let Some(if_block) = find_first_actionable_if(lines, branches) {
        if !try_relocate_one(lines, &if_block, branches) {
            // Matching was ambiguous or no orphans; exit to avoid looping.
            break;
        }
    }
}
