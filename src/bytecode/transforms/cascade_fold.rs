//! Cascade-to-switch folding for the IR.
//!
//! Walks the decoded statement tree and rewrites chains of nested
//! `Stmt::Branch` whose conditions are all `<expr> == <literal>`
//! comparisons against a structurally identical left-hand-side into a
//! single `Stmt::Switch`. This is the implicit shape Blueprint compilers
//! emit for an enum or integer switch (an if-else-if-else cascade).
//!
//! Example:
//! ```text
//! if (X == 1) { A }
//! else if (X == 2) { B }
//! else if (X == 3) { C }
//! else { D }
//! ```
//! folds to:
//! ```text
//! switch (X) {
//!   case 1: A
//!   case 2: B
//!   case 3: C
//!   default: D
//! }
//! ```
//!
//! The fold fires when at least two consecutive Branches share the same
//! lhs. The innermost non-empty else becomes the default block. Recurses
//! into all nested bodies, including a freshly-built switch's case
//! bodies, so cascades inside a case fold independently.

use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{Stmt, SwitchCase};
use crate::bytecode::transforms::visit::{
    descend_into_children, resolve_expr_chain, resolve_var_chain, scope_stack,
};

/// Walk a statement body, rewriting `if (X == c1) {} else if (X == c2) {} ...`
/// chains into `Stmt::Switch`. Recurses into every nested `Vec<Stmt>` so
/// nested cascades are folded independently.
pub fn fold_switch_cascades(body: &mut [Stmt]) {
    fold_in_body(body, &[]);
}

/// `ancestors` is innermost-first slice of preceding-sibling bodies at each
/// outer nesting level. The chain-resolution probes search the current body
/// plus `ancestors` so a head Branch's `Var($X)` cond can resolve to its
/// defining `<lhs> == <literal>` assignment when the def lives in a parent
/// body, not the same scope as the Branch.
fn fold_in_body(body: &mut [Stmt], ancestors: &[&[Stmt]]) {
    // Top-down: fold cascades anchored at each statement BEFORE recursing
    // into children. A premature recursion would collapse the inner
    // Branch chain into a Switch and prevent the outer fold from seeing
    // the original cascade shape.
    //
    // The chain-resolution probe needs an immutable view of `body` for
    // `resolve_var_chain`. We can't hold an immutable borrow while also
    // mutating `body[idx]`, so each iteration first runs the non-mutating
    // probe to decide whether the head Branch's cond chain-resolves to an
    // Eq-against-literal cascade, then performs the mutation in a second
    // step using the discovered common lhs.
    let mut idx = 0;
    while idx < body.len() {
        // Build the chain-resolution scope stack for `body[idx]`: preceding
        // siblings (`body[..idx]`) innermost, then `ancestors`. Names
        // referenced from `body[idx]`'s cond may resolve to defs in any of
        // those scopes.
        let head: &[Stmt] = &body[..idx];
        let scopes = scope_stack(head, ancestors);

        if let Some(common_lhs) = probe_cascade_head(&body[idx], &scopes) {
            // If the head Branch's cond is a chain-resolved Var, capture
            // its case-value rhs as a clone NOW, while we still have an
            // immutable view of `body`. The drain consumes ownership of
            // each Branch's cond, and a chain-resolved head can't extract
            // its rhs from in-place (the cond is a Var, the Eq is at the
            // chain target). The drain accepts an optional pre-cloned
            // case_value to use for the head only.
            let head_case_value = head_chain_case_value(&body[idx], &scopes);
            if let Some(switch) = try_fold_at(&mut body[idx], &common_lhs, head_case_value) {
                body[idx] = switch;
            }
        }
        idx += 1;
    }

    // Now descend into every nested body so any cascades that appear
    // inside case bodies, then-bodies, etc. fold independently. Each
    // sub-body inherits the parent's preceding siblings (`body[..i]`)
    // as its innermost ancestor, so chain resolution from inside a
    // then-body or case body can walk back to defs at the parent level.
    descend_into_children(body, ancestors, &mut |sub_body, child_ancestors| {
        fold_in_body(sub_body, child_ancestors)
    });
}

/// Probe whether `stmt` anchors a foldable cascade. Returns the common lhs
/// expression when `collect_chain_lhs` accepts the head Branch. The head's
/// cond may be either a direct `Binary{Eq, lhs, literal}` or `Var($X)` whose
/// chain resolves to one through `scopes`. The inner chain (else_body[0],
/// etc.) is matched directly without chain resolution because Blueprint's
/// compiler emits the chained shape with literal `Eq`s nested inside the
/// else arms.
fn probe_cascade_head(stmt: &Stmt, scopes: &[&[Stmt]]) -> Option<Expr> {
    collect_chain_lhs(stmt, scopes)
}

/// One link in an Eq-against-literal cascade: the case value expression
/// (lifted from the rhs) and the then-body that runs when the lhs equals
/// it.
struct CascadeLink {
    case_value: Expr,
    body: Vec<Stmt>,
}

/// If `stmt` is a `Stmt::Branch` that anchors a cascade of two or more
/// `<expr> == <literal>` comparisons, consume the chain and return the
/// equivalent `Stmt::Switch`. Returns `None` (and leaves `stmt` unchanged)
/// otherwise.
///
/// Chain shape:
/// ```text
/// Branch { cond: lhs == c1, then_body: A,
///   else_body: [Branch { cond: lhs == c2, then_body: B,
///     else_body: [Branch { cond: lhs == c3, then_body: C,
///       else_body: D }] }] }
/// ```
/// Innermost non-empty `D` becomes the default block.
fn try_fold_at(stmt: &mut Stmt, common_lhs: &Expr, head_case_value: Option<Expr>) -> Option<Stmt> {
    let outer_offset = match stmt {
        Stmt::Branch { offset, .. } => *offset,
        _ => return None,
    };

    let (links, default_body) = drain_chain(stmt, common_lhs, head_case_value);
    if links.len() < 2 {
        // The probe accepted, but draining produced fewer than two links.
        // This should not happen given the same predicate logic, but guard
        // anyway so the caller's `stmt` is untouched.
        return None;
    }

    let cases = links
        .into_iter()
        .map(|link| SwitchCase {
            values: vec![link.case_value],
            body: link.body,
        })
        .collect();

    let default = if default_body.is_empty() {
        None
    } else {
        Some(default_body)
    };

    Some(Stmt::Switch {
        expr: common_lhs.clone(),
        cases,
        default,
        offset: outer_offset,
    })
}

/// Probe `stmt` non-destructively, returning the common lhs expression
/// when its branch chain forms a foldable cascade of two or more
/// Eq-against-literal comparisons. The head Branch's cond may be a
/// `Var($X)` that chain-resolves through `scopes` to an
/// Eq-against-literal expression; inner Branches must already carry the
/// canonical `Eq` shape (`lower_sentinel_cascade` runs before this pass
/// to normalize sentinel-driven chains, and Blueprint never emits a
/// chain whose inner else arms hide their cond behind a temp).
fn collect_chain_lhs(stmt: &Stmt, scopes: &[&[Stmt]]) -> Option<Expr> {
    let first_lhs = match_eq_literal(stmt, scopes)?.0.clone();
    let mut current = stmt;
    let mut chain_len = 0usize;

    // Inner-link matching uses an empty scope stack: nested Branches must
    // already carry a direct Eq cond, no chain resolution.
    let no_scopes: &[&[Stmt]] = &[];

    while let Some((lhs, _value)) =
        match_eq_literal(current, if chain_len == 0 { scopes } else { no_scopes })
    {
        if *lhs != first_lhs {
            return None;
        }
        chain_len += 1;

        let else_body = match current {
            Stmt::Branch { else_body, .. } => else_body,
            _ => unreachable!("match_eq_literal returned for non-branch"),
        };
        match else_body.as_slice() {
            [Stmt::Branch { .. }] => {
                current = &else_body[0];
            }
            _ => break,
        }
    }

    if chain_len >= 2 {
        Some(first_lhs)
    } else {
        None
    }
}

/// Tear the chain apart, returning each link's (case_value, then_body)
/// plus the innermost else as the candidate default body. `stmt` must
/// be the outermost Branch and must already have passed
/// [`collect_chain_lhs`] for `common_lhs`.
///
/// `head_case_value`, when provided, is the pre-cloned case-value
/// expression for the head Branch (used when the head's cond is a
/// chain-resolved `Var($X)` and the rhs lives at the chain target).
/// Subsequent links extract their case-value from the in-place `cond`
/// Binary as before. The probe stage (`probe_cascade_head`) is
/// responsible for capturing this clone before mutation begins.
fn drain_chain(
    stmt: &mut Stmt,
    common_lhs: &Expr,
    head_case_value: Option<Expr>,
) -> (Vec<CascadeLink>, Vec<Stmt>) {
    let mut links = Vec::new();
    let mut cursor: &mut Stmt = stmt;
    let mut head_case_value = head_case_value;
    loop {
        let advance = matches_link_direct(cursor, common_lhs);
        let advance_via_head_chain =
            head_case_value.is_some() && matches!(cursor, Stmt::Branch { .. });
        if !advance && !advance_via_head_chain {
            break;
        }
        // Take fields out of the current branch.
        let Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } = cursor
        else {
            break;
        };
        let case_value = if let Some(pre_cloned) = head_case_value.take() {
            // Head link with chain-resolved cond. Leave the cond Var in
            // place, the Branch is dropped wholesale by the surrounding
            // rewrite.
            let _ = cond;
            pre_cloned
        } else {
            match std::mem::replace(cond, Expr::Literal(String::new())) {
                Expr::Binary { rhs, .. } => *rhs,
                // Should not happen, matches_link_direct confirmed the shape.
                other => other,
            }
        };
        let body = std::mem::take(then_body);
        links.push(CascadeLink { case_value, body });

        // Decide whether the else_body is another link (descend) or the
        // terminal default body (extract and stop).
        let descend = match else_body.as_slice() {
            [next] => matches_link_direct(next, common_lhs),
            _ => false,
        };
        if descend {
            // Move into else_body[0]; pop the singleton out of the
            // outer Vec so we own a &mut to the Branch struct.
            let inner = else_body.remove(0);
            *else_body = vec![inner];
            cursor = &mut else_body[0];
        } else {
            // Extract the else_body as the default and stop.
            let default = std::mem::take(else_body);
            return (links, default);
        }
    }
    (links, Vec::new())
}

/// Predicate variant of `match_eq_literal` that also requires the lhs
/// to equal `common_lhs` structurally. Direct match only, no chain
/// resolution; used by the drain for non-head links.
fn matches_link_direct(stmt: &Stmt, common_lhs: &Expr) -> bool {
    let no_scopes: &[&[Stmt]] = &[];
    match match_eq_literal(stmt, no_scopes) {
        Some((lhs, _value)) => lhs == common_lhs,
        None => false,
    }
}

/// If `stmt` is a head Branch whose cond is `Var($X)` and the chain
/// resolves to `<lhs> == <case_value>` through `scopes`, return the
/// deep-resolved case_value. Returns `None` if the cond is already a
/// direct Binary (no pre-cloning needed) or if the chain doesn't
/// resolve. Deep-resolving the rhs covers the case where the chain hop
/// reaches `Eq(lhs, Var($N))` and `$N` further resolves to the actual
/// case literal.
fn head_chain_case_value(stmt: &Stmt, scopes: &[&[Stmt]]) -> Option<Expr> {
    let Stmt::Branch { cond, .. } = stmt else {
        return None;
    };
    let Expr::Var(name) = cond else {
        return None;
    };
    let resolved = resolve_var_chain(scopes, name)?;
    let Expr::Binary { op, rhs, .. } = resolved else {
        return None;
    };
    if *op != BinaryOp::Eq {
        return None;
    }
    let rhs_deep = resolve_expr_chain(rhs, scopes);
    if !is_case_value(&rhs_deep) {
        return None;
    }
    Some(rhs_deep)
}

/// Return `(lhs, rhs)` if `stmt` is `Stmt::Branch` whose condition is
/// `<lhs> == <literal>`. The literal can be any `Expr::Literal(_)`,
/// any `Expr::Var(_)` resolving to a name token (enums often appear as
/// `Var("EFoo::Bar")`), or any `Expr::Cast` wrapping the same. The
/// caller's chain check enforces that all lhs values are structurally
/// equal.
///
/// `chain_scopes` lets the matcher peel a `Var($X)` cond through
/// `resolve_var_chain` before structurally matching `Binary{Eq, ..}`.
/// Pass the scope stack where the cond's defining assignment(s) might
/// live (innermost first). Pass `&[]` when chain resolution is not
/// desired (nested chain links).
fn match_eq_literal<'a>(
    stmt: &'a Stmt,
    chain_scopes: &[&'a [Stmt]],
) -> Option<(&'a Expr, &'a Expr)> {
    let Stmt::Branch { cond, .. } = stmt else {
        return None;
    };
    let resolved = match cond {
        Expr::Var(name) => resolve_var_chain(chain_scopes, name)?,
        other => other,
    };
    let Expr::Binary { op, lhs, rhs } = resolved else {
        return None;
    };
    if *op != BinaryOp::Eq {
        return None;
    }
    if !is_case_value(rhs) {
        return None;
    }
    Some((lhs.as_ref(), rhs.as_ref()))
}

/// Accept Literal, named-enum Var (e.g. `EFoo::Bar`), or a Cast wrapping
/// either as a switch case-value rhs.
fn is_case_value(expr: &Expr) -> bool {
    match expr {
        Expr::Literal(_) => true,
        Expr::Var(name) => name.contains("::"),
        Expr::Cast { inner, .. } => is_case_value(inner),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::expr::BinaryOp;
    use crate::bytecode::stmt::Stmt;
    use crate::bytecode::transforms::test_fixtures::{lit, var};

    fn eq(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Eq,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn lt(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn call_stmt(name: &str) -> Stmt {
        Stmt::Call {
            func: Expr::Var(name.into()),
            args: vec![],
            offset: 0,
        }
    }

    fn branch(cond: Expr, then_body: Vec<Stmt>, else_body: Vec<Stmt>) -> Stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset: 0x10,
        }
    }

    #[test]
    fn simple_two_case_cascade() {
        let inner = branch(eq(var("X"), lit("2")), vec![call_stmt("B")], vec![]);
        let outer = branch(eq(var("X"), lit("1")), vec![call_stmt("A")], vec![inner]);
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } = &body[0]
        else {
            panic!("expected Stmt::Switch");
        };
        assert_eq!(expr, &var("X"));
        assert_eq!(cases.len(), 2);
        assert!(default.is_none());
    }

    #[test]
    fn three_case_with_default() {
        let inner3 = branch(
            eq(var("State"), lit("3")),
            vec![call_stmt("C")],
            vec![call_stmt("D")],
        );
        let inner2 = branch(
            eq(var("State"), lit("2")),
            vec![call_stmt("B")],
            vec![inner3],
        );
        let outer = branch(
            eq(var("State"), lit("1")),
            vec![call_stmt("A")],
            vec![inner2],
        );
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } = &body[0]
        else {
            panic!("expected Stmt::Switch");
        };
        assert_eq!(expr, &var("State"));
        assert_eq!(cases.len(), 3);
        let default_body = default.as_ref().expect("default expected");
        assert_eq!(default_body.len(), 1);
    }

    #[test]
    fn mismatched_lhs_does_not_fold() {
        let inner = branch(eq(var("Y"), lit("2")), vec![call_stmt("B")], vec![]);
        let outer = branch(eq(var("X"), lit("1")), vec![call_stmt("A")], vec![inner]);
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    #[test]
    fn non_eq_chain_does_not_fold() {
        let inner = branch(lt(var("X"), lit("2")), vec![call_stmt("B")], vec![]);
        let outer = branch(lt(var("X"), lit("1")), vec![call_stmt("A")], vec![inner]);
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    #[test]
    fn nested_cascade_inside_case_recurses() {
        // Outer cascade on X, then-body of one case contains a nested
        // cascade on Y. After folding, both fold independently.
        let nested_inner = branch(eq(var("Y"), lit("2")), vec![call_stmt("Y2")], vec![]);
        let nested_outer = branch(
            eq(var("Y"), lit("1")),
            vec![call_stmt("Y1")],
            vec![nested_inner],
        );
        let case2 = branch(eq(var("X"), lit("2")), vec![nested_outer], vec![]);
        let outer = branch(eq(var("X"), lit("1")), vec![call_stmt("A")], vec![case2]);
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        let Stmt::Switch { cases, .. } = &body[0] else {
            panic!("outer should be Switch");
        };
        assert_eq!(cases.len(), 2);
        // Case 2's body should now contain a nested Switch.
        let nested = &cases[1].body;
        assert_eq!(nested.len(), 1);
        assert!(
            matches!(nested[0], Stmt::Switch { .. }),
            "nested cascade should fold inside the case body"
        );
    }

    #[test]
    fn single_branch_does_not_fold() {
        let only = branch(
            eq(var("X"), lit("1")),
            vec![call_stmt("A")],
            vec![call_stmt("D")],
        );
        let mut body = vec![only];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Branch { .. }));
    }

    fn assign(name: &str, rhs: Expr) -> Stmt {
        Stmt::Assignment {
            lhs: var(name),
            rhs,
            offset: 0,
        }
    }

    #[test]
    fn chain_resolved_head_cond_folds() {
        // Head Branch's cond is `Var($t)`; the chain resolves to
        // `X == 1` via an Assignment elsewhere in body. Inner chain
        // links carry direct Eq cond (typical post-lower_sentinel
        // shape, plus a hand-written lead-in temp).
        //
        // body:
        //   $t = X == 1
        //   if ($t) { A }
        //   else if (X == 2) { B }
        //   else if (X == 3) { C }
        let inner3 = branch(eq(var("X"), lit("3")), vec![call_stmt("C")], vec![]);
        let inner2 = branch(eq(var("X"), lit("2")), vec![call_stmt("B")], vec![inner3]);
        let head = branch(var("t"), vec![call_stmt("A")], vec![inner2]);
        let mut body = vec![assign("t", eq(var("X"), lit("1"))), head];

        fold_switch_cascades(&mut body);

        // Body now: [Assignment($t = X==1), Switch{...}]. The
        // Assignment is left in place; the inliner / dead-stmt pass
        // cleans it up later.
        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        let Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } = &body[1]
        else {
            panic!("expected Stmt::Switch at body[1]");
        };
        assert_eq!(expr, &var("X"));
        assert_eq!(cases.len(), 3);
        assert!(default.is_none());
        assert_eq!(cases[0].values, vec![lit("1")]);
        assert_eq!(cases[1].values, vec![lit("2")]);
        assert_eq!(cases[2].values, vec![lit("3")]);
    }

    #[test]
    fn chain_resolved_head_with_var_alias_hop_folds() {
        // The head's chain has an intermediate `Var` alias hop:
        //   $u = $t
        //   $t = X == 1
        //   if ($u) { A }
        //   else if (X == 2) { B }
        // Chain walk: $u -> $t -> Binary{Eq, X, 1}.
        let inner = branch(eq(var("X"), lit("2")), vec![call_stmt("B")], vec![]);
        let head = branch(var("u"), vec![call_stmt("A")], vec![inner]);
        let mut body = vec![
            assign("u", var("t")),
            assign("t", eq(var("X"), lit("1"))),
            head,
        ];

        fold_switch_cascades(&mut body);

        // The two Assignment slots remain; only the cascade folded.
        assert_eq!(body.len(), 3);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Assignment { .. }));
        let Stmt::Switch { expr, cases, .. } = &body[2] else {
            panic!("expected Stmt::Switch at body[2]");
        };
        assert_eq!(expr, &var("X"));
        assert_eq!(cases.len(), 2);
    }

    #[test]
    fn chain_resolved_head_lhs_must_match_inner_links() {
        // Head chain resolves to `X == 1`, but inner chain compares Y.
        // `collect_chain_lhs` rejects: only one link's lhs would match.
        let inner = branch(eq(var("Y"), lit("2")), vec![call_stmt("B")], vec![]);
        let head = branch(var("t"), vec![call_stmt("A")], vec![inner]);
        let mut body = vec![assign("t", eq(var("X"), lit("1"))), head];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        assert!(matches!(body[1], Stmt::Branch { .. }));
    }

    #[test]
    fn enum_var_rhs_folds() {
        let inner = branch(
            eq(var("State"), var("EState::Idle")),
            vec![call_stmt("Idle")],
            vec![],
        );
        let outer = branch(
            eq(var("State"), var("EState::Active")),
            vec![call_stmt("Active")],
            vec![inner],
        );
        let mut body = vec![outer];

        fold_switch_cascades(&mut body);

        assert_eq!(body.len(), 1);
        assert!(matches!(body[0], Stmt::Switch { .. }));
    }

    /// The cascade head's cond temp `$t` is defined in the PARENT scope,
    /// not in the same body as the head Branch. The chain-aware probe
    /// must walk through `ancestors` to find the def. Cascade lives
    /// inside the then-body of an outer Branch; the temp def is at the
    /// outer level alongside the Branch.
    #[test]
    fn chain_resolved_head_with_parent_scope_def_folds() {
        // outer scope:
        //   $t = X == 1
        //   if (cond_outer) {
        //       if ($t) { A }
        //       else if (X == 2) { B }
        //       else if (X == 3) { C }
        //   }
        let inner3 = branch(eq(var("X"), lit("3")), vec![call_stmt("C")], vec![]);
        let inner2 = branch(eq(var("X"), lit("2")), vec![call_stmt("B")], vec![inner3]);
        let head = branch(var("t"), vec![call_stmt("A")], vec![inner2]);
        let outer_branch = Stmt::Branch {
            cond: var("cond_outer"),
            then_body: vec![head],
            else_body: vec![],
            offset: 0x0,
        };
        let mut body = vec![assign("t", eq(var("X"), lit("1"))), outer_branch];

        fold_switch_cascades(&mut body);

        // body[0] is the temp def. body[1] is the outer Branch; its
        // then-body should now hold a folded Switch.
        assert_eq!(body.len(), 2);
        assert!(matches!(body[0], Stmt::Assignment { .. }));
        let Stmt::Branch { then_body, .. } = &body[1] else {
            panic!("expected outer Branch at body[1]");
        };
        assert_eq!(then_body.len(), 1, "cascade should fold into one Switch");
        let Stmt::Switch { expr, cases, .. } = &then_body[0] else {
            panic!("expected Stmt::Switch inside outer Branch's then-body");
        };
        assert_eq!(expr, &var("X"));
        assert_eq!(cases.len(), 3);
        assert_eq!(cases[0].values, vec![lit("1")]);
        assert_eq!(cases[1].values, vec![lit("2")]);
        assert_eq!(cases[2].values, vec![lit("3")]);
    }
}
