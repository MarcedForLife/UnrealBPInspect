use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::{LoopKind, Stmt};
use crate::bytecode::transforms::visit::{peel_transparent, resolve_var_chain, walk_expr};

/// True for the literal `1`.
pub(super) fn is_one_literal(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(text) if text == "1")
}

/// True when `expr` is a `Var(name)` or `FieldAccess { field: name }` matching `expected`.
pub(super) fn lhs_matches_var(expr: &Expr, expected: &str) -> bool {
    match expr {
        Expr::Var(name) => name == expected,
        Expr::FieldAccess { field, .. } => field == expected,
        _ => false,
    }
}

/// True when `idx` references the loop counter (bare or field-access form).
pub(super) fn idx_matches_counter(idx: &Expr, counter_name: &str) -> bool {
    match idx {
        Expr::Var(name) => name == counter_name,
        Expr::FieldAccess { field, .. } => field == counter_name,
        _ => false,
    }
}

/// Extract the leaf-variable name from an assignment lhs.
pub(super) fn lhs_var_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Var(name) => Some(name.as_str()),
        Expr::FieldAccess { field, .. } => Some(field.as_str()),
        _ => None,
    }
}

/// Extract the lhs variable name from a `Stmt::Assignment`.
pub(super) fn stmt_assignment_lhs_name(stmt: &Stmt) -> Option<&str> {
    match stmt {
        Stmt::Assignment { lhs, .. } => lhs_var_name(lhs),
        _ => None,
    }
}

/// Extract the lhs name from any expression that can appear on an assignment lhs.
pub(super) fn stmt_lhs_name(expr: &Expr) -> Option<&str> {
    lhs_var_name(expr)
}

/// Extract the counter variable name from a `Stmt::Loop { kind: ForC { .. } }`.
///
/// Looks at the first assignment in the increment body and returns its lhs name.
/// Returns `None` if the increment is empty or the first statement is not an assignment.
pub(super) fn forc_increment_counter(stmt: &Stmt) -> Option<String> {
    let Stmt::Loop {
        kind: LoopKind::ForC { increment, .. },
        ..
    } = stmt
    else {
        return None;
    };
    increment
        .first()
        .and_then(|inc_stmt| stmt_assignment_lhs_name(inc_stmt))
        .map(str::to_string)
}

/// Loose structural equality on two `Expr` values.
///
/// Transparent wrappers (`Out`, `Interface`, `Persistent`) peel through on
/// either side before comparison so a callee-side OUT marker doesn't cause
/// `out X` and bare `X` to mismatch.
pub(crate) fn exprs_equivalent(a: &Expr, b: &Expr) -> bool {
    let a = peel_transparent(a);
    let b = peel_transparent(b);
    match (a, b) {
        (Expr::Var(left), Expr::Var(right)) => left == right,
        (Expr::Literal(left), Expr::Literal(right)) => left == right,
        (
            Expr::FieldAccess {
                recv: lr,
                field: lf,
            },
            Expr::FieldAccess {
                recv: rr,
                field: rf,
            },
        ) => lf == rf && exprs_equivalent(lr, rr),
        (Expr::Call { name: ln, args: la }, Expr::Call { name: rn, args: ra }) => {
            ln == rn
                && la.len() == ra.len()
                && la.iter().zip(ra).all(|(x, y)| exprs_equivalent(x, y))
        }
        _ => false,
    }
}

/// Chain-aware variant of `expr_references_var`: treats every `Var($temp)`
/// encountered as transparent and follows it through `scopes` via
/// `resolve_var_chain` before continuing the walk. This is what
/// `extract_increment` needs to recognise the counter through
/// un-inlined cond temps (e.g. `Var($BooleanAND_*)` -> `And(...,
/// Var($Less_IntInt_*))` -> `Lt(Counter, Array_Length(arr))`). The
/// scope stack lets the walk follow chains that hop between the loop
/// body and a parent scope where the def lives.
///
/// `depth_budget` caps the walk so a malformed chain can't loop forever.
pub(super) fn expr_references_var_chain(expr: &Expr, name: &str, scopes: &[&[Stmt]]) -> bool {
    fn walk(expr: &Expr, name: &str, scopes: &[&[Stmt]], depth_budget: u32) -> bool {
        if depth_budget == 0 {
            return expr_references_var(expr, name);
        }
        match expr {
            Expr::Var(other) => {
                if other == name {
                    return true;
                }
                if let Some(resolved) = resolve_var_chain(scopes, other) {
                    walk(resolved, name, scopes, depth_budget - 1)
                } else {
                    false
                }
            }
            Expr::FieldAccess { recv, field } => {
                field == name || walk(recv, name, scopes, depth_budget)
            }
            Expr::Index { recv, idx } => {
                walk(recv, name, scopes, depth_budget) || walk(idx, name, scopes, depth_budget)
            }
            Expr::Binary { lhs, rhs, .. } => {
                walk(lhs, name, scopes, depth_budget) || walk(rhs, name, scopes, depth_budget)
            }
            Expr::Unary { operand, .. } => walk(operand, name, scopes, depth_budget),
            Expr::Cast { inner, .. } => walk(inner, name, scopes, depth_budget),
            Expr::Call { args, .. } => args.iter().any(|arg| walk(arg, name, scopes, depth_budget)),
            Expr::MethodCall { recv, args, .. } => {
                walk(recv, name, scopes, depth_budget)
                    || args.iter().any(|arg| walk(arg, name, scopes, depth_budget))
            }
            Expr::ArrayLit(items) => items
                .iter()
                .any(|item| walk(item, name, scopes, depth_budget)),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                walk(cond, name, scopes, depth_budget)
                    || walk(then_expr, name, scopes, depth_budget)
                    || walk(else_expr, name, scopes, depth_budget)
            }
            Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
                walk(inner, name, scopes, depth_budget)
            }
            Expr::Resume { inner, .. } => walk(inner, name, scopes, depth_budget),
            Expr::StructConstruct { fields, .. } => fields
                .iter()
                .any(|(_, value)| walk(value, name, scopes, depth_budget)),
            Expr::Switch {
                index,
                cases,
                default,
            } => {
                walk(index, name, scopes, depth_budget)
                    || cases.iter().any(|case| {
                        walk(&case.value, name, scopes, depth_budget)
                            || walk(&case.body, name, scopes, depth_budget)
                    })
                    || walk(default, name, scopes, depth_budget)
            }
            Expr::Literal(_) | Expr::Unknown { .. } => false,
        }
    }
    walk(expr, name, scopes, 8)
}

/// Recursively walk `expr` checking whether any `Var` or `FieldAccess` matches `name`.
fn expr_references_var(expr: &Expr, name: &str) -> bool {
    let mut found = false;
    walk_expr(expr, &mut |inner: &Expr| match inner {
        Expr::Var(other) if other == name => found = true,
        Expr::FieldAccess { field, .. } if field == name => found = true,
        _ => {}
    });
    found
}
