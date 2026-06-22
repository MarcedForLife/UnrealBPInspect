//! Struct break/make folding for the IR.
//!
//! Walks the decoded statement tree and rewrites contiguous runs of
//! field-assignment statements writing into the same temporary
//! variable into a single `Expr::StructConstruct` populated at the
//! variable's first (and only) use site.
//!
//! Pattern (before fold):
//! ```text
//! Tmp_3.X = e1;
//! Tmp_3.Y = e2;
//! Tmp_3.Z = e3;
//! Foo(Tmp_3);
//! ```
//! collapses to:
//! ```text
//! Foo(MakeStruct(X=e1, Y=e2, Z=e3));
//! ```
//!
//! Detection rules:
//!  1. A run of two or more contiguous `Stmt::Assignment` whose lhs is
//!     `Expr::FieldAccess { recv: Var(name), .. }` for the same `name`.
//!  2. The next non-assignment statement (immediately after the run)
//!     contains exactly one occurrence of `Var(name)` and no later
//!     statement in the body references the name.
//!  3. None of the field rhs values contains an `Expr::Unknown`.
//!
//! The struct type name is derived from the Blueprint compiler's temp
//! variable name (`$MakeStruct_<Type>_<N>`), which embeds the originating
//! struct's name. When the temp name doesn't follow this convention the
//! fold falls back to the `<unknown>` placeholder so the rendered shape
//! is still recognisable.

use std::collections::BTreeMap;

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;
use crate::bytecode::transforms::var_refs::{self, Defs, VarScope};
use crate::bytecode::transforms::visit::{
    expr_contains_unknown, walk_stmt_children_mut, walk_stmt_exprs_mut, Action,
};

/// Placeholder used as `StructConstruct::type_name` when the temp name
/// gives no usable type signal. Renders as a "MakeStruct" shape while
/// keeping the marker visible.
const UNKNOWN_TYPE_NAME: &str = "<unknown>";

/// Prefix the Blueprint compiler uses on hidden struct-construction temps.
const MAKE_STRUCT_TEMP_PREFIX: &str = "$MakeStruct_";

/// Derive the struct type name from a Blueprint struct-construction temp
/// variable. Returns `None` when `temp_name` doesn't follow the
/// `$MakeStruct_<TYPE>` (optionally `_<digits>`) convention.
///
/// Examples:
/// - `$MakeStruct_GrippedComponent_Struct_1` -> `GrippedComponent_Struct`
/// - `$MakeStruct_GrippedComponent_Struct` -> `GrippedComponent_Struct`
/// - `$MakeStruct_PlayerState_Struct_12` -> `PlayerState_Struct`
/// - `Temp_struct_var_3` -> `None`
fn derive_struct_type_name(temp_name: &str) -> Option<String> {
    let after_prefix = temp_name.strip_prefix(MAKE_STRUCT_TEMP_PREFIX)?;
    if after_prefix.is_empty() {
        return None;
    }
    // Strip a trailing `_<digits>` suffix if present. Match by scanning
    // back from the end so we don't accidentally strip a numeric segment
    // that's part of the type name (none observed, but the bounded
    // suffix form keeps the rule predictable).
    let bytes = after_prefix.as_bytes();
    let mut digit_run_start = bytes.len();
    while digit_run_start > 0 && bytes[digit_run_start - 1].is_ascii_digit() {
        digit_run_start -= 1;
    }
    let stripped = if digit_run_start > 0
        && digit_run_start < bytes.len()
        && bytes[digit_run_start - 1] == b'_'
    {
        &after_prefix[..digit_run_start - 1]
    } else {
        after_prefix
    };
    if stripped.is_empty() {
        None
    } else {
        Some(stripped.to_string())
    }
}

/// Walk a statement body and fold contiguous-field-assignment runs that
/// build up a temporary struct, then collapse them to a single
/// `Expr::StructConstruct` placed at the variable's use site. Recurses
/// into every nested body so folds happen independently inside
/// branches, sequences, loops, switches, and latches.
pub fn fold_struct_constructions(body: &mut Vec<Stmt>) {
    // Count read uses of every variable across the whole function before
    // folding. A struct temp the Blueprint compiler rematerialises at two
    // consumption points (e.g. the same struct fed to both an event call
    // and an `out` return param) is built by two
    // field-runs and read twice; folding only one run leaves an
    // inline-Make/field-by-field mismatch. Restrict the fold to genuine
    // single-use scratch temps. Read-only: field-write lhs is skipped, so
    // only true uses count.
    let read_counts = var_refs::count_all_var_uses(body);
    fold_in_body(body, &read_counts);
}

fn fold_in_body(body: &mut Vec<Stmt>, read_counts: &BTreeMap<String, usize>) {
    // Top-down: fold runs at this level before recursing, so the
    // FieldAccess lhs shape is still intact when we look at it. After
    // folds at this level land, recurse into every nested body.
    let mut idx = 0;
    while idx < body.len() {
        if let Some(consumed) = try_fold_at(body, idx, read_counts) {
            // The use-site statement is rewritten in place; the
            // run-length statements before it have been removed. Skip
            // past the rewritten statement.
            idx = idx + consumed.use_idx_after_fold + 1;
        } else {
            idx += 1;
        }
    }

    for stmt in body.iter_mut() {
        walk_stmt_children_mut(stmt, &mut |child| fold_in_body(child, read_counts));
    }
}

/// Bookkeeping returned by `try_fold_at` so the caller can advance its
/// index past the rewritten statements without re-scanning.
struct FoldOutcome {
    /// Index of the rewritten use-site statement after the run was
    /// removed.
    use_idx_after_fold: usize,
}

/// Attempt to fold a struct construction starting at `body[start]`.
///
/// Returns `Some(FoldOutcome)` when the body was rewritten. Returns
/// `None` when no fold applies; the body is left unchanged in that
/// case.
fn try_fold_at(
    body: &mut Vec<Stmt>,
    start: usize,
    read_counts: &BTreeMap<String, usize>,
) -> Option<FoldOutcome> {
    let temp_name = match body.get(start) {
        Some(Stmt::Assignment {
            lhs: Expr::FieldAccess { recv, .. },
            ..
        }) => match recv.as_ref() {
            Expr::Var(name) => name.clone(),
            _ => return None,
        },
        _ => return None,
    };

    // Only fold a struct temp read exactly once across the whole function.
    // A temp read more than once is consumed at multiple sites (or
    // rematerialised by the Blueprint compiler into several field-runs);
    // folding a single run there produces an asymmetric duplicate.
    if read_counts.get(&temp_name).copied().unwrap_or(0) != 1 {
        return None;
    }

    let mut run_end = start;
    let mut fields: Vec<(String, Expr)> = Vec::new();
    while run_end < body.len() {
        match &body[run_end] {
            Stmt::Assignment {
                lhs: Expr::FieldAccess { recv, field },
                rhs,
                ..
            } if matches!(recv.as_ref(), Expr::Var(name) if name == &temp_name) => {
                if expr_contains_unknown(rhs) {
                    return None;
                }
                fields.push((field.clone(), rhs.clone()));
                run_end += 1;
            }
            _ => break,
        }
    }

    if fields.len() < 2 {
        return None;
    }

    // The use-site must be the next statement and must contain exactly
    // one occurrence of Var(temp_name). Statements after that may not
    // reference the name (otherwise the fold would lose a use).
    let use_stmt_idx = run_end;
    let use_stmt = body.get(use_stmt_idx)?;
    let use_count_here = count_var_uses_in_stmt(use_stmt, &temp_name);
    if use_count_here != 1 {
        return None;
    }
    for stmt in &body[use_stmt_idx + 1..] {
        if count_var_uses_in_stmt(stmt, &temp_name) > 0 {
            return None;
        }
    }

    let type_name =
        derive_struct_type_name(&temp_name).unwrap_or_else(|| UNKNOWN_TYPE_NAME.to_string());
    let constructor = Expr::StructConstruct { type_name, fields };

    // Splice in: replace the use of Var(temp_name) inside the
    // use-site, then drop the assignment run that built it.
    let use_stmt_mut = &mut body[use_stmt_idx];
    let replaced = substitute_first_var_in_stmt(use_stmt_mut, &temp_name, &constructor);
    if !replaced {
        return None;
    }

    body.drain(start..use_stmt_idx);
    let use_idx_after_fold = start;
    Some(FoldOutcome { use_idx_after_fold })
}

/// Count occurrences of `Expr::Var(name)` in a single statement, recursing
/// into nested bodies and expressions. Visits Assignment lhs as well, so a
/// later `Var(temp_name)` appearing inside an `Assignment::lhs::FieldAccess`
/// (a field-write into the same temp) counts as a use, blocking the fold.
fn count_var_uses_in_stmt(stmt: &Stmt, name: &str) -> usize {
    var_refs::count_var(
        std::slice::from_ref(stmt),
        name,
        VarScope::Deep,
        Defs::VisitLhs,
    )
}

/// Substitute the first occurrence of `Expr::Var(name)` in a statement
/// with `replacement`. Returns `true` on success.
///
/// Uses the SkipUses walker, so Assignment lhs is never visited. The lhs
/// is a def, not a use, and replacing `Var(temp_name)` there with a
/// `StructConstruct` would corrupt the assignment shape
/// (`MakeStruct(...) = SomeCall()`). The lhs arm is unreached on real
/// fixtures while still being a latent footgun.
fn substitute_first_var_in_stmt(stmt: &mut Stmt, name: &str, replacement: &Expr) -> bool {
    let mut substituted = false;
    walk_stmt_exprs_mut(stmt, &mut |expr: &mut Expr| {
        if let Expr::Var(other) = expr {
            if other == name {
                *expr = replacement.clone();
                substituted = true;
                return Action::Stop;
            }
        }
        Action::Continue
    });
    substituted
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{call, lit, var};

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

    #[test]
    fn simple_three_field_fold() {
        let mut body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            field_assign("Tmp_3", "Y", lit("2")),
            field_assign("Tmp_3", "Z", lit("3")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Call { args, .. } = &body[0] else {
            panic!("expected Call");
        };
        let Expr::StructConstruct { type_name, fields } = &args[0] else {
            panic!("expected StructConstruct, got {:?}", args[0]);
        };
        assert_eq!(type_name, UNKNOWN_TYPE_NAME);
        assert_eq!(fields.len(), 3);
        assert_eq!(fields[0].0, "X");
        assert_eq!(fields[1].0, "Y");
        assert_eq!(fields[2].0, "Z");
    }

    #[test]
    fn single_field_does_not_fold() {
        let mut body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        fold_struct_constructions(&mut body);

        // Only one field write, so the run length is below the
        // 2-field threshold and the body is left untouched.
        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Call { .. }));
    }

    #[test]
    fn non_contiguous_does_not_fold() {
        let mut body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            // Interrupt the run with an unrelated call, so the
            // contiguous-run requirement fails.
            call("UnrelatedSideEffect", vec![]),
            field_assign("Tmp_3", "Y", lit("2")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), original_len);
    }

    #[test]
    fn multi_use_does_not_fold() {
        // Tmp_3 used twice after the field run -> no fold.
        let mut body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            field_assign("Tmp_3", "Y", lit("2")),
            call("Foo", vec![var("Tmp_3")]),
            call("Bar", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), original_len);
    }

    #[test]
    fn unknown_rhs_does_not_fold() {
        let unknown = Expr::Unknown {
            reason: "test".into(),
            raw_bytes: vec![0xff],
            offset: 0,
        };
        let mut body = vec![
            field_assign("Tmp_3", "X", unknown),
            field_assign("Tmp_3", "Y", lit("2")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        let original_len = body.len();
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), original_len);
    }

    #[test]
    fn derive_struct_type_name_strips_trailing_digits() {
        assert_eq!(
            derive_struct_type_name("$MakeStruct_GrippedComponent_Struct_1").as_deref(),
            Some("GrippedComponent_Struct"),
        );
        assert_eq!(
            derive_struct_type_name("$MakeStruct_PlayerState_Struct_12").as_deref(),
            Some("PlayerState_Struct"),
        );
    }

    #[test]
    fn derive_struct_type_name_without_trailing_digits() {
        assert_eq!(
            derive_struct_type_name("$MakeStruct_GrippedComponent_Struct").as_deref(),
            Some("GrippedComponent_Struct"),
        );
    }

    #[test]
    fn derive_struct_type_name_unrelated_temp_returns_none() {
        assert!(derive_struct_type_name("Temp_struct_var_3").is_none());
        assert!(derive_struct_type_name("Tmp_3").is_none());
        assert!(derive_struct_type_name("$MakeStruct_").is_none());
    }

    #[test]
    fn fold_resolves_type_from_makestruct_temp() {
        // $MakeStruct_<TYPE>_<N> -> StructConstruct.type_name = <TYPE>.
        let mut body = vec![
            field_assign(
                "$MakeStruct_GrippedComponent_Struct_1",
                "Actor",
                lit("Actor"),
            ),
            field_assign(
                "$MakeStruct_GrippedComponent_Struct_1",
                "Component",
                lit("Component"),
            ),
            call("Foo", vec![var("$MakeStruct_GrippedComponent_Struct_1")]),
        ];
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Call { args, .. } = &body[0] else {
            panic!("expected Call");
        };
        let Expr::StructConstruct { type_name, .. } = &args[0] else {
            panic!("expected StructConstruct, got {:?}", args[0]);
        };
        assert_eq!(type_name, "GrippedComponent_Struct");
    }

    #[test]
    fn fold_falls_back_to_unknown_when_type_unresolvable() {
        // Generic temp name with no `$MakeStruct_` prefix -> still folds,
        // but type_name stays at the unknown placeholder.
        let mut body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            field_assign("Tmp_3", "Y", lit("2")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        fold_struct_constructions(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Call { args, .. } = &body[0] else {
            panic!("expected Call");
        };
        let Expr::StructConstruct { type_name, .. } = &args[0] else {
            panic!("expected StructConstruct, got {:?}", args[0]);
        };
        assert_eq!(type_name, UNKNOWN_TYPE_NAME);
    }

    #[test]
    fn nested_fold_in_branch_arm() {
        let then_body = vec![
            field_assign("Tmp_3", "X", lit("1")),
            field_assign("Tmp_3", "Y", lit("2")),
            call("Foo", vec![var("Tmp_3")]),
        ];
        let mut body = vec![Stmt::Branch {
            cond: lit("true"),
            then_body,
            else_body: vec![],
            offset: 0,
        }];

        fold_struct_constructions(&mut body);

        let Stmt::Branch { then_body, .. } = &body[0] else {
            panic!("expected Branch");
        };
        assert_eq!(then_body.len(), 1);
        let Stmt::Call { args, .. } = &then_body[0] else {
            panic!("expected Call");
        };
        assert!(matches!(args[0], Expr::StructConstruct { .. }));
    }
}
