//! Shared name-shape classification for the transform passes.
//!
//! Both the single-use temp inliner (`expr_transforms`) and dead-statement
//! removal (`dead_stmt`) need to distinguish Blueprint-compiler temporaries
//! from persistent Blueprint variables (member graph variables and function
//! locals). A persistent variable renders as a bare `Var("RotationDifference")`
//! with no qualifying receiver, and writing one is an observable side effect:
//! later code (often a sibling statement after a Branch, not inside an arm)
//! reads the field. Folding such a writeback into an earlier read and deleting
//! it, or sweeping it as a dead candidate, silently drops the write.
//!
//! The two passes therefore share one authoritative test so they agree on
//! exactly which names are eligible for inline-and-delete / dead-sweep.

use crate::bytecode::names::K2NODE_PREFIX;

/// Returns `true` when `name` matches a Blueprint-compiler temporary shape.
///
/// Recognised shapes:
/// - `$`-prefixed compute / cast / common-subexpression slots
///   (`$Subtract_FloatFloat_2`, `$Cse_1`, `$Cast_AsPlayer`).
/// - `Temp_*`, `K2Node_*`, `CallFunc_*` prefixes.
/// - `<Name>_<N>` slots with a trailing `_<digits>` suffix (`Tmp_3`).
///
/// A bare persistent variable name (`RotationDifference`, `TotalRotation`,
/// `TraceRadius`) matches none of these, so callers treat it as a variable
/// that must never be inlined-and-deleted nor swept as a dead candidate.
pub fn is_compiler_temp_name(name: &str) -> bool {
    if name.starts_with('$')
        || name.starts_with("Temp_")
        || name.starts_with(K2NODE_PREFIX)
        || name.starts_with("CallFunc_")
    {
        return true;
    }
    has_numeric_suffix(name)
}

/// Returns `true` when `name` ends in `_<digits>` (e.g. `Tmp_3`,
/// `SomeName_12`), the Blueprint compiler's per-slot numeric suffix.
fn has_numeric_suffix(name: &str) -> bool {
    match name.rsplit_once('_') {
        Some((prefix, suffix)) => {
            !prefix.is_empty() && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit())
        }
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn temp_shapes_accepted() {
        assert!(is_compiler_temp_name("$Subtract_FloatFloat_2"));
        assert!(is_compiler_temp_name("$Cse_1"));
        assert!(is_compiler_temp_name("$Cast_AsPlayer"));
        assert!(is_compiler_temp_name("Temp_bool_IsClosed"));
        assert!(is_compiler_temp_name("Temp_int_Loop_Counter_Variable_0"));
        assert!(is_compiler_temp_name("K2Node_MakeArray"));
        assert!(is_compiler_temp_name("CallFunc_GetActorLocation"));
        assert!(is_compiler_temp_name("Tmp_3"));
        assert!(is_compiler_temp_name("SomeName_12"));
    }

    #[test]
    fn bare_member_names_rejected() {
        assert!(!is_compiler_temp_name("RotationDifference"));
        assert!(!is_compiler_temp_name("TotalRotation"));
        assert!(!is_compiler_temp_name("TraceRadius"));
        assert!(!is_compiler_temp_name("HandScale"));
        // Non-numeric trailing token after `_` is not a slot suffix.
        assert!(!is_compiler_temp_name("Tmp_a"));
        assert!(!is_compiler_temp_name("Some_Name"));
    }
}
