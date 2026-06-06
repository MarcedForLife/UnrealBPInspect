//! ForEach recognizer tests, including the matchers exposed for fine-
//! grained verification (`match_foreach_cond`, `match_foreach_increment`,
//! `exprs_equivalent`). Negative cases live in `negatives.rs`.

use super::super::refine_loops::{
    exprs_equivalent, match_foreach_cond, match_foreach_increment, refine_loops,
};
use super::super::test_fixtures::{assign_expr as assign, lit};
use super::*;
use crate::bytecode::expr::{BinaryOp, Expr};
use crate::bytecode::stmt::{LoopKind, Stmt};

/// Body shape variants for the ForEach recognizer driver. Each shape
/// mirrors a Blueprint-emitted lowering of the same semantic loop; the
/// recognizer must promote all of them.
#[derive(Clone, Copy)]
enum ForeachBodyShape {
    /// `[Item = arr[counter], Use(), counter_inc]`. Expected body after
    /// strip = `[Use()]`. `item` field = "Item".
    Simple,
    /// `[mirror = counter, $Array_Get_Item = arr[mirror], Work(),
    /// counter_inc]`. Expected after strip = `[Work()]`. item =
    /// `$Array_Get_Item`.
    IndexMirror,
    /// `[mirror = counter, BreakHitResult, $IsValid, $Array_Get_Item =
    /// arr[mirror], Use(), counter_inc]`. Expected after strip =
    /// `[BreakHitResult, $IsValid, Use()]`. item = `$Array_Get_Item`.
    PreFetchUserCode,
}

/// Where the loop's cond-temp def lives. Mirrors the cond-def axis used
/// by the ForC driver.
#[derive(Clone, Copy)]
enum CondDefLocation {
    Direct,
    BodyHead,
    ParentScope,
}

#[test]
fn while_refines_to_foreach_cases() {
    struct Case {
        label: &'static str,
        shape: ForeachBodyShape,
        cond_def: CondDefLocation,
        expected_item: &'static str,
        // Loop is at parent stmts[loop_idx] after refinement. The
        // ParentScope cond-temp def is dropped as a bound-expr leak,
        // so its loop ends up at idx 0.
        loop_idx: usize,
        // Body length after fetch+mirror strip + increment move. BodyHead
        // keeps the inlined cond-temp def in the body (adds 1); ParentScope
        // does not affect body length (the leaked sibling lives outside it).
        expected_body_len: usize,
    }

    let counter_simple = "Temp_int_Loop_Counter_Variable_0";
    let counter_other = "Temp_int_Loop_Counter_Variable";
    let mirror = "Temp_int_Array_Index_Variable";
    let cond_temp = "$Less_IntInt_1";

    let cases = vec![
        Case {
            label: "post_inline_simple",
            shape: ForeachBodyShape::Simple,
            cond_def: CondDefLocation::Direct,
            expected_item: "Item",
            loop_idx: 0,
            expected_body_len: 1,
        },
        Case {
            label: "post_inline_through_index_mirror",
            shape: ForeachBodyShape::IndexMirror,
            cond_def: CondDefLocation::Direct,
            expected_item: "$Array_Get_Item",
            loop_idx: 0,
            expected_body_len: 1,
        },
        Case {
            label: "post_inline_pre_fetch_user_code",
            shape: ForeachBodyShape::PreFetchUserCode,
            cond_def: CondDefLocation::Direct,
            expected_item: "$Array_Get_Item",
            loop_idx: 0,
            expected_body_len: 3,
        },
        Case {
            label: "pre_inline_simple",
            shape: ForeachBodyShape::Simple,
            cond_def: CondDefLocation::BodyHead,
            expected_item: "Item",
            loop_idx: 0,
            expected_body_len: 2,
        },
        Case {
            label: "pre_inline_through_index_mirror",
            shape: ForeachBodyShape::IndexMirror,
            cond_def: CondDefLocation::BodyHead,
            expected_item: "$Array_Get_Item",
            loop_idx: 0,
            expected_body_len: 2,
        },
        Case {
            label: "pre_inline_pre_fetch_user_code",
            shape: ForeachBodyShape::PreFetchUserCode,
            cond_def: CondDefLocation::BodyHead,
            expected_item: "$Array_Get_Item",
            loop_idx: 0,
            expected_body_len: 4,
        },
        // The parent-scope cond-temp def is the canonical bound-expr leak
        // (`$Less_IntInt_1 = counter < Array_Length(Items)`). A real for-loop
        // keeps it as the head cond, but a ForEach has no editor-graph
        // counterpart for it, so the refine pass drops it. The loop
        // therefore ends up at idx 0 with no surviving sibling.
        Case {
            label: "parent_scope_simple",
            shape: ForeachBodyShape::Simple,
            cond_def: CondDefLocation::ParentScope,
            expected_item: "Item",
            loop_idx: 0,
            expected_body_len: 1,
        },
    ];

    for case in cases {
        let counter = match case.shape {
            ForeachBodyShape::Simple => counter_simple,
            ForeachBodyShape::IndexMirror => counter_simple,
            ForeachBodyShape::PreFetchUserCode => counter_other,
        };
        let array_expr = match case.shape {
            ForeachBodyShape::Simple => var("Items"),
            ForeachBodyShape::IndexMirror => var("MyArray"),
            ForeachBodyShape::PreFetchUserCode => var("Hits"),
        };
        let mut body = match case.shape {
            ForeachBodyShape::Simple => vec![
                assign(
                    var("Item"),
                    Expr::Index {
                        recv: Box::new(array_expr.clone()),
                        idx: Box::new(var(counter)),
                    },
                ),
                call_stmt("Use"),
                counter_inc(counter),
            ],
            ForeachBodyShape::IndexMirror => vec![
                assign(var(mirror), var(counter)),
                assign(
                    var("$Array_Get_Item"),
                    Expr::Index {
                        recv: Box::new(array_expr.clone()),
                        idx: Box::new(var(mirror)),
                    },
                ),
                call_stmt("Work"),
                counter_inc(counter),
            ],
            ForeachBodyShape::PreFetchUserCode => vec![
                assign(var(mirror), var(counter)),
                call_stmt("BreakHitResult"),
                assign(
                    var("$IsValid"),
                    Expr::Call {
                        name: "IsValid".into(),
                        args: vec![var("$Hit")],
                    },
                ),
                assign(
                    var("$Array_Get_Item"),
                    Expr::Index {
                        recv: Box::new(array_expr.clone()),
                        idx: Box::new(var(mirror)),
                    },
                ),
                call_stmt("Use"),
                counter_inc(counter),
            ],
        };

        let canonical_cond = counter_lt_array_length(counter, array_expr.clone());
        let mut stmts = match case.cond_def {
            CondDefLocation::Direct => vec![while_loop(canonical_cond, body)],
            CondDefLocation::BodyHead => {
                body.insert(0, assign(var(cond_temp), canonical_cond));
                vec![while_loop(var(cond_temp), body)]
            }
            CondDefLocation::ParentScope => vec![
                assign(var(cond_temp), canonical_cond),
                while_loop(var(cond_temp), body),
            ],
        };

        refine_loops(&mut stmts);

        let Stmt::Loop {
            kind,
            cond,
            body: loop_body,
            ..
        } = &stmts[case.loop_idx]
        else {
            panic!(
                "case {}: expected Loop at idx {}",
                case.label, case.loop_idx
            );
        };
        let LoopKind::ForEach { item, array } = kind else {
            panic!(
                "case {}: expected ForEach, got {}",
                case.label,
                loop_kind_name(kind)
            );
        };
        assert_eq!(item, case.expected_item, "case {}: item field", case.label);
        assert!(
            exprs_equivalent(array, &array_expr),
            "case {}: array field",
            case.label
        );
        assert!(
            cond.is_none(),
            "case {}: ForEach cond should be implicit",
            case.label
        );
        assert_eq!(
            loop_body.len(),
            case.expected_body_len,
            "case {}: body length after refine",
            case.label
        );
        // The ParentScope cond-temp def is the bound-expr leak; after the
        // drop the loop is the only surviving top-level statement.
        if matches!(case.cond_def, CondDefLocation::ParentScope) {
            assert_eq!(
                stmts.len(),
                1,
                "case {}: parent-scope bound-expr leak should be dropped, \
                 leaving only the loop",
                case.label
            );
        }
    }
}

/// Build the multi-break ForEach fixture: a ForEach-shaped While whose
/// body has a nested `if` carrying a `Stmt::Break` and a second
/// `array[counter]` re-fetch. `with_break` toggles whether the nested
/// `if` carries the break, exercising the scope gate.
fn multi_break_foreach(counter: &str, array: Expr, with_break: bool) -> Vec<Stmt> {
    let defining_fetch = assign(
        var("Item"),
        Expr::Index {
            recv: Box::new(array.clone()),
            idx: Box::new(var(counter)),
        },
    );
    let re_fetch = assign(
        var("Out"),
        Expr::Index {
            recv: Box::new(array.clone()),
            idx: Box::new(var(counter)),
        },
    );
    let mut guard_then = vec![re_fetch];
    if with_break {
        guard_then.push(Stmt::Break { offset: 0 });
    }
    let guard = Stmt::Branch {
        cond: var("$CanConsume"),
        then_body: guard_then,
        else_body: Vec::new(),
        offset: 0,
    };
    let body = vec![defining_fetch, guard, counter_inc(counter)];
    vec![while_loop(counter_lt_array_length(counter, array), body)]
}

/// A multi-break ForEach (break present in a nested guard) rewrites
/// the nested `array[counter]` re-fetch to the loop variable and keeps
/// the break.
#[test]
fn multi_break_foreach_substitutes_nested_refetch() {
    let counter = "Temp_int_Loop_Counter_Variable";
    let mut stmts = multi_break_foreach(counter, var("Items"), true);
    refine_loops(&mut stmts);

    let Stmt::Loop {
        kind,
        body: loop_body,
        ..
    } = &stmts[0]
    else {
        panic!("expected Loop");
    };
    assert!(matches!(kind, LoopKind::ForEach { .. }), "expected ForEach");
    // Body = [defining-fetch stripped -> gone, guard]. The defining fetch
    // is removed; the guard remains.
    let guard = loop_body
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Branch { then_body, .. } => Some(then_body),
            _ => None,
        })
        .expect("guard branch present");
    // Nested re-fetch rewritten to the loop var.
    let re_fetch_rhs = guard.iter().find_map(|stmt| match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name),
            rhs,
            ..
        } if name == "Out" => Some(rhs),
        _ => None,
    });
    assert_eq!(
        re_fetch_rhs,
        Some(&var("Item")),
        "nested re-fetch should become the loop var"
    );
    // Break preserved.
    assert!(
        guard.iter().any(|stmt| matches!(stmt, Stmt::Break { .. })),
        "break preserved in guard"
    );
}

/// Scope gate: the same ForEach WITHOUT a break leaves the nested
/// `array[counter]` re-fetch untouched (plain ForEach loops stay
/// byte-identical; a later CSE pass dedups such re-fetches).
#[test]
fn plain_foreach_does_not_substitute_nested_refetch() {
    let counter = "Temp_int_Loop_Counter_Variable";
    let mut stmts = multi_break_foreach(counter, var("Items"), false);
    refine_loops(&mut stmts);

    let Stmt::Loop {
        body: loop_body, ..
    } = &stmts[0]
    else {
        panic!("expected Loop");
    };
    let guard = loop_body
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Branch { then_body, .. } => Some(then_body),
            _ => None,
        })
        .expect("guard branch present");
    let re_fetch_rhs = guard.iter().find_map(|stmt| match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name),
            rhs,
            ..
        } if name == "Out" => Some(rhs),
        _ => None,
    });
    // Untouched: still the raw index-fetch, not the loop var.
    assert!(
        matches!(re_fetch_rhs, Some(Expr::Index { .. })),
        "plain ForEach should leave the nested re-fetch as a raw index"
    );
}

/// `match_foreach_cond` accepts the canonical free-call form
/// `Array_Length(array)`. The static-library MethodCall shape lowers
/// to this Call before the matcher runs (see
/// `transforms::lower_static_library_calls`).
#[test]
fn foreach_cond_accepts_canonical_call_form() {
    let cond = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("Counter")),
        rhs: Box::new(Expr::Call {
            name: "Array_Length".into(),
            args: vec![var("Items")],
        }),
    };
    let (counter, array) = match_foreach_cond(&cond, &[], &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// `match_foreach_increment` accepts the un-inlined temp form where the
/// addition itself sits in a separate `$Add_IntInt_*` temp. Resolved via
/// the chain walk through the loop body.
#[test]
fn foreach_increment_accepts_temp_form() {
    let increment = vec![assign(var("Counter"), var("$Add_IntInt_1"))];
    let body = vec![assign(
        var("$Add_IntInt_1"),
        Expr::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(var("Counter")),
            rhs: Box::new(lit("1")),
        },
    )];
    assert!(match_foreach_increment(&increment, "Counter", &body, &[]));
}

/// `match_foreach_cond` accepts the break-flag-wrapped form
/// `(!flag) && (counter < Array_Length(array))`, which Blueprint emits
/// for ForEach-with-break trampolines.
#[test]
fn foreach_cond_accepts_break_flag_and_form() {
    let canonical = counter_lt_array_length("Counter", var("Items"));
    let break_flag_not = Expr::Unary {
        op: crate::bytecode::expr::UnaryOp::Not,
        operand: Box::new(var("Temp_bool_True_if_break_was_hit_Variable")),
    };
    let cond = Expr::Binary {
        op: BinaryOp::And,
        lhs: Box::new(break_flag_not),
        rhs: Box::new(canonical),
    };
    let (counter, array) = match_foreach_cond(&cond, &[], &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// Symmetric variant: break-flag on the right, canonical on the left.
#[test]
fn foreach_cond_accepts_break_flag_and_swapped() {
    let canonical = counter_lt_array_length("Counter", var("Items"));
    let break_flag_not = Expr::Call {
        name: "Not_PreBool".into(),
        args: vec![var("Temp_bool_True_if_break_was_hit_Variable")],
    };
    let cond = Expr::Binary {
        op: BinaryOp::And,
        lhs: Box::new(canonical),
        rhs: Box::new(break_flag_not),
    };
    let (counter, array) = match_foreach_cond(&cond, &[], &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// AND-wrapped non-canonical cond does NOT match. The break-flag wrapper
/// only opens the door when the other operand is the canonical foreach cond.
#[test]
fn foreach_cond_rejects_break_flag_and_non_canonical_inner() {
    let break_flag_not = Expr::Unary {
        op: crate::bytecode::expr::UnaryOp::Not,
        operand: Box::new(var("Temp_bool_True_if_break_was_hit_Variable")),
    };
    let non_canonical = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("Counter")),
        rhs: Box::new(lit("10")), // not Array_Length(_)
    };
    let cond = Expr::Binary {
        op: BinaryOp::And,
        lhs: Box::new(break_flag_not),
        rhs: Box::new(non_canonical),
    };
    assert!(match_foreach_cond(&cond, &[], &[]).is_none());
}

/// AND with a non-break-flag-not LHS (e.g. arbitrary BinaryOp) does NOT match.
#[test]
fn foreach_cond_rejects_and_with_non_break_flag_lhs() {
    let canonical = counter_lt_array_length("Counter", var("Items"));
    let arbitrary = Expr::Binary {
        op: BinaryOp::Gt,
        lhs: Box::new(var("Other")),
        rhs: Box::new(lit("0")),
    };
    let cond = Expr::Binary {
        op: BinaryOp::And,
        lhs: Box::new(arbitrary),
        rhs: Box::new(canonical),
    };
    assert!(match_foreach_cond(&cond, &[], &[]).is_none());
}

/// Multiple fetches in the body: the matcher picks the one whose array
/// matches the loop's `Array_Length` argument. Mirrors a nested-loop
/// shape where an inner-loop fetch sits inside the outer body.
#[test]
fn foreach_picks_fetch_matching_outer_array() {
    let counter = "Temp_int_Loop_Counter_Variable";
    let mirror = "Temp_int_Array_Index_Variable";
    let outer_array = var("Outer");
    let inner_array = var("Inner");
    let body = vec![
        assign(var(mirror), var(counter)),
        // Inner-loop fetch using a different array; should NOT be picked.
        assign(
            var("$Inner_Get"),
            Expr::Index {
                recv: Box::new(inner_array),
                idx: Box::new(var("InnerCounter")),
            },
        ),
        // Outer-loop fetch matching the cond's array.
        assign(
            var("$Array_Get_Item"),
            Expr::Index {
                recv: Box::new(outer_array.clone()),
                idx: Box::new(var(mirror)),
            },
        ),
        counter_inc(counter),
    ];
    let cond = counter_lt_array_length(counter, outer_array.clone());
    let mut stmts = vec![while_loop(cond, body)];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, body, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    let LoopKind::ForEach { item, array } = kind else {
        panic!("expected ForEach, got {}", loop_kind_name(kind));
    };
    assert_eq!(item, "$Array_Get_Item");
    assert_eq!(*array, outer_array);
    // Inner fetch survives; outer fetch and mirror are stripped.
    assert_eq!(body.len(), 1, "inner-array fetch should remain");
}

/// `expr_is_index_fetch` peels through `Out` wrappers when comparing the
/// receiver to the array expression so a callee-side OUT marker on
/// either side doesn't break detection.
#[test]
fn exprs_equivalent_peels_out_wrappers() {
    let a = Expr::Out(Box::new(var("X")));
    let b = var("X");
    assert!(exprs_equivalent(&a, &b));
    assert!(exprs_equivalent(&b, &a));
}

/// Pre-inline shape with break-flag wrapper: cond is
/// `Var($BooleanAND_1)`, body-head defines it as
/// `Binary(And, Not_PreBool($flag), Var($Less_IntInt_1))`, and
/// `$Less_IntInt_1` is itself a body-level temp resolving to the
/// canonical Lt cond. Two layers of chain resolution required.
#[test]
fn foreach_cond_accepts_break_flag_and_pre_inline_chain() {
    let outer_temp = "$BooleanAND_1";
    let inner_temp = "$Less_IntInt_1";
    let body = vec![
        assign(
            var(outer_temp),
            Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(Expr::Call {
                    name: "Not_PreBool".into(),
                    args: vec![var("Temp_bool_True_if_break_was_hit_Variable")],
                }),
                rhs: Box::new(var(inner_temp)),
            },
        ),
        assign(
            var(inner_temp),
            counter_lt_array_length("Counter", var("Items")),
        ),
    ];
    let (counter, array) =
        match_foreach_cond(&var(outer_temp), &body, &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// Pre-inline ForEach shape: increment use+def both inside body,
/// chain-substitution should still produce ForEach with a self-contained
/// increment slot (no orphan temp ref).
#[test]
fn foreach_increment_self_contained_when_def_lives_in_body() {
    let counter = "Temp_int_Loop_Counter_Variable_0";
    let add_temp = "$Add_IntInt_1";
    let array_expr = var("Items");
    let body = vec![
        assign(
            var(add_temp),
            Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
        ),
        assign(
            var("Item"),
            Expr::Index {
                recv: Box::new(array_expr.clone()),
                idx: Box::new(var(counter)),
            },
        ),
        call_stmt("Use"),
        assign(var(counter), var(add_temp)),
    ];
    let mut stmts = vec![while_loop(
        counter_lt_array_length(counter, array_expr.clone()),
        body,
    )];

    refine_loops(&mut stmts);

    let Stmt::Loop { kind, body, .. } = &stmts[0] else {
        panic!("expected Loop");
    };
    let LoopKind::ForEach { item, .. } = kind else {
        panic!("expected ForEach, got {}", loop_kind_name(kind));
    };
    assert_eq!(item, "Item");
    // Body retains Use() only; fetch line was stripped, the now-orphaned
    // increment temp def should also be gone.
    assert_eq!(body.len(), 1);
    assert!(
        !body.iter().any(
            |stmt| matches!(stmt, Stmt::Assignment { lhs: Expr::Var(name), .. } if name == add_temp)
        ),
        "body-local increment temp def should have been removed",
    );
}

/// Two-level chain: cond resolves to `Lt(counter, Var($ArrayLen))`, and
/// `$ArrayLen` itself resolves to `Call("Array_Length", arr)`. The
/// matcher must walk the inner Var sub-expression to its terminal Call
/// before structural matching, otherwise the rhs stays as an opaque
/// `Var` and `match_canonical_foreach_cond` rejects.
#[test]
fn foreach_cond_walks_inner_array_length_temp() {
    let cond_temp = "$Less_IntInt";
    let length_temp = "$Array_Length";
    let body = vec![
        assign(
            var(cond_temp),
            Expr::Binary {
                op: BinaryOp::Lt,
                lhs: Box::new(var("Counter")),
                rhs: Box::new(var(length_temp)),
            },
        ),
        assign(
            var(length_temp),
            Expr::Call {
                name: "Array_Length".into(),
                args: vec![var("Items")],
            },
        ),
    ];
    let (counter, array) = match_foreach_cond(&var(cond_temp), &body, &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// Two-level chain inside the break-flag wrapper: outer cond temp
/// resolves to `Binary{And, Var($notFlag), Var($lt)}` and both inner
/// temps need a chain hop to expose `Not_PreBool(...)` and
/// `Lt(counter, Array_Length(arr))` respectively.
#[test]
fn foreach_cond_walks_break_flag_and_two_level_chain() {
    let outer_temp = "$BooleanAND";
    let not_temp = "$Not_PreBool";
    let lt_temp = "$Less_IntInt";
    let body = vec![
        assign(
            var(outer_temp),
            Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(var(not_temp)),
                rhs: Box::new(var(lt_temp)),
            },
        ),
        assign(
            var(not_temp),
            Expr::Call {
                name: "Not_PreBool".into(),
                args: vec![var("Temp_bool_True_if_break_was_hit_Variable")],
            },
        ),
        assign(
            var(lt_temp),
            counter_lt_array_length("Counter", var("Items")),
        ),
    ];
    let (counter, array) =
        match_foreach_cond(&var(outer_temp), &body, &[]).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(array, var("Items"));
}

/// Two-level chain on the increment rhs: `Counter = Var($Add)` and
/// `$Add = Binary{Add, Counter, Var($one)}` and `$one = Literal("1")`.
/// `match_foreach_increment` must walk the inner one-temp through the
/// chain to recognise the canonical `+ 1` increment.
#[test]
fn foreach_increment_walks_inner_one_literal_temp() {
    let increment = vec![assign(var("Counter"), var("$Add_IntInt"))];
    let one_temp = "$IntLiteral_One";
    let body = vec![
        assign(
            var("$Add_IntInt"),
            Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var("Counter")),
                rhs: Box::new(var(one_temp)),
            },
        ),
        assign(var(one_temp), lit("1")),
    ];
    assert!(match_foreach_increment(&increment, "Counter", &body, &[]));
}

/// Sanity check: the chain walk on the rhs is shallow (Var -> non-Var
/// terminal). It does NOT recurse into the terminal's sub-expressions,
/// which would substitute a multi-assigned array name through a
/// scope-level alias and change the user-facing array reference.
/// Pre-inline shape with `NestedActors = $X` in the ancestor scope:
/// the match must return `Var("NestedActors")`, not `Var("$X")`.
#[test]
fn foreach_cond_preserves_user_facing_array_name_through_alias() {
    let array_alias_target = "$GetAllChildActors_ChildActors";
    let cond = Expr::Binary {
        op: BinaryOp::Lt,
        lhs: Box::new(var("Counter")),
        rhs: Box::new(Expr::Call {
            name: "Array_Length".into(),
            args: vec![var("NestedActors")],
        }),
    };
    // Ancestor scope contains `NestedActors = $X` (a multi-write
    // function-local that the inliner can't substitute).
    let ancestor = vec![assign(var("NestedActors"), var(array_alias_target))];
    let ancestors: Vec<&[Stmt]> = vec![&ancestor];
    let (counter, array) = match_foreach_cond(&cond, &[], &ancestors).expect("expected match");
    assert_eq!(counter, "Counter");
    assert_eq!(
        array,
        var("NestedActors"),
        "array operand stays at the user-facing name; deep substitution would change it"
    );
}
