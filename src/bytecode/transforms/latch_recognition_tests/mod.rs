//! Tests for `latch_recognition`. Extracted from the production module so
//! the recognizer chain stays separated from its synthetic-shape fixtures.
//!
//! Sub-modules group tests by recognizer family. Common helpers live here
//! at `pub(super)` visibility so each sub-module can pull them in via
//! `use super::*`.

mod doonce;
mod flipflop;
mod negatives;
mod reset_doonce;

use super::test_fixtures::{assign, lit, var};
use crate::bytecode::expr::{Expr, UnaryOp};
use crate::bytecode::stmt::Stmt;

pub(super) fn call(name: &str) -> Expr {
    Expr::Call {
        name: name.to_string(),
        args: vec![],
    }
}

pub(super) fn call_stmt(name: &str) -> Stmt {
    Stmt::Call {
        func: call(name),
        args: vec![],
        offset: 0,
    }
}

pub(super) fn doonce_branch(gate_name: &str, body: Vec<Stmt>) -> Stmt {
    let mut then_body = vec![assign(gate_name, lit("true"))];
    then_body.extend(body);
    Stmt::Branch {
        cond: Expr::Unary {
            op: UnaryOp::Not,
            operand: Box::new(var(gate_name)),
        },
        then_body,
        else_body: vec![],
        offset: 0x10,
    }
}

pub(super) fn flipflop_post_inline(toggle: &str, arm_a: Vec<Stmt>, arm_b: Vec<Stmt>) -> Vec<Stmt> {
    vec![
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: Expr::Unary {
                op: UnaryOp::Not,
                operand: Box::new(var(toggle)),
            },
            offset: 0x10,
        },
        Stmt::Branch {
            cond: var(toggle),
            then_body: arm_a,
            else_body: arm_b,
            offset: 0x14,
        },
    ]
}

pub(super) fn flipflop_pre_inline(
    toggle: &str,
    temp: &str,
    arm_a: Vec<Stmt>,
    arm_b: Vec<Stmt>,
) -> Vec<Stmt> {
    vec![
        Stmt::Assignment {
            lhs: var(temp),
            rhs: Expr::Unary {
                op: UnaryOp::Not,
                operand: Box::new(var(toggle)),
            },
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: var(temp),
            offset: 0x14,
        },
        Stmt::Branch {
            cond: var(toggle),
            then_body: arm_a,
            else_body: arm_b,
            offset: 0x18,
        },
    ]
}

/// Two-hop alias chain: `$alias = !toggle; $mid = $alias; toggle = $mid;
/// if (toggle) { ... }`. The chain-aware matcher must walk from the
/// toggle update through both temp aliases to confirm the negation.
pub(super) fn flipflop_alias_chained(
    toggle: &str,
    alias: &str,
    mid: &str,
    arm_a: Vec<Stmt>,
    arm_b: Vec<Stmt>,
) -> Vec<Stmt> {
    vec![
        Stmt::Assignment {
            lhs: var(alias),
            rhs: Expr::Unary {
                op: UnaryOp::Not,
                operand: Box::new(var(toggle)),
            },
            offset: 0x10,
        },
        Stmt::Assignment {
            lhs: var(mid),
            rhs: var(alias),
            offset: 0x14,
        },
        Stmt::Assignment {
            lhs: var(toggle),
            rhs: var(mid),
            offset: 0x18,
        },
        Stmt::Branch {
            cond: var(toggle),
            then_body: arm_a,
            else_body: arm_b,
            offset: 0x1c,
        },
    ]
}

/// Build the scaffold-only Sequence the BP compiler emits for a DoOnce
/// macro instance. `init_var` and `gate_var` mirror the per-instance
/// `Has_Been_Initd_Variable_<N>` / `IsClosed_Variable_<N>` names.
pub(super) fn doonce_scaffold_sequence(init_var: &str, gate_var: &str) -> Stmt {
    let init_pin = vec![
        Stmt::Branch {
            cond: var(init_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x100,
        },
        assign(init_var, lit("true")),
        assign(gate_var, lit("true")),
    ];
    let gate_pin = vec![
        Stmt::Branch {
            cond: var(gate_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x110,
        },
        assign(gate_var, lit("true")),
    ];
    Stmt::Sequence {
        pins: vec![init_pin, gate_pin],
        offset: 0x120,
    }
}

/// Build a scaffold-leading Sequence: pin 0 holds the
/// init scaffold (all scaffold), pin 1 starts with the gate scaffold
/// then trails into the user body. The BP compiler emits this shape
/// when a DoOnce sits inside an outer if-arm and the user body falls
/// through into the gate pin via post-pop continuation.
pub(super) fn doonce_scaffold_leading_sequence(
    init_var: &str,
    gate_var: &str,
    embedded_user_body: Vec<Stmt>,
) -> Stmt {
    let init_pin = vec![
        Stmt::Branch {
            cond: var(init_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x100,
        },
        assign(init_var, lit("true")),
        assign(gate_var, lit("true")),
    ];
    let mut gate_pin = vec![
        Stmt::Branch {
            cond: var(gate_var),
            then_body: vec![],
            else_body: vec![],
            offset: 0x110,
        },
        assign(gate_var, lit("true")),
    ];
    gate_pin.extend(embedded_user_body);
    Stmt::Sequence {
        pins: vec![init_pin, gate_pin],
        offset: 0x120,
    }
}

/// Build the BP-emitted ResetDoOnce gate-reset pair:
/// `IsClosed_Variable<suffix> = false; Has_Been_Initd_Variable<suffix> = true`.
pub(super) fn reset_doonce_pair(suffix: &str) -> Vec<Stmt> {
    let gate = format!("Temp_bool_IsClosed_Variable{}", suffix);
    let init = format!("Temp_bool_Has_Been_Initd_Variable{}", suffix);
    vec![assign(&gate, lit("false")), assign(&init, lit("true"))]
}

pub(super) fn assert_reset_doonce_call(stmt: &Stmt, expected_name: &str) {
    let Stmt::Call { func, args, .. } = stmt else {
        panic!(
            "expected Stmt::Call, got {:?}",
            super::test_fixtures::stmt_kind(stmt)
        );
    };
    match func {
        Expr::Var(name) => assert_eq!(name, "ResetDoOnce"),
        _ => panic!("expected Expr::Var(ResetDoOnce) as func"),
    }
    assert_eq!(args.len(), 1);
    match &args[0] {
        Expr::Var(name) => assert_eq!(name, expected_name),
        _ => panic!("expected Expr::Var arg"),
    }
}

pub(super) fn not_pre_bool_call(toggle: &str) -> Expr {
    Expr::Call {
        name: "Not_PreBool".to_string(),
        args: vec![var(toggle)],
    }
}

pub(super) fn not_unary(toggle: &str) -> Expr {
    Expr::Unary {
        op: UnaryOp::Not,
        operand: Box::new(var(toggle)),
    }
}

/// Build the embedded-flip shape:
/// ```text
/// consumer_0; ...; consumer_n;
/// if (toggle) { } else { toggle = neg_toggle }
/// ```
pub(super) fn embedded_flip_body(
    toggle: &str,
    neg_toggle: Expr,
    consumers: Vec<Stmt>,
) -> Vec<Stmt> {
    let mut body = consumers;
    body.push(Stmt::Branch {
        cond: var(toggle),
        then_body: vec![],
        else_body: vec![Stmt::Assignment {
            lhs: var(toggle),
            rhs: neg_toggle,
            offset: 0x20,
        }],
        offset: 0x24,
    });
    body
}

// Consumer stmt that assigns a field from toggle_var.
pub(super) fn field_from_toggle(toggle: &str) -> Stmt {
    Stmt::Assignment {
        lhs: Expr::FieldAccess {
            recv: Box::new(var("self")),
            field: "FlyEnabled".to_string(),
        },
        rhs: var(toggle),
        offset: 0x10,
    }
}

/// Build the canonical 2-stmt else chain `$tmp = !toggle; toggle = $tmp`
/// inside a Branch with empty then_body, with the supplied consumers as
/// preceding siblings.
pub(super) fn embedded_flip_two_stmt_chain_body(
    toggle: &str,
    temp_name: &str,
    neg_toggle: Expr,
    consumers: Vec<Stmt>,
) -> Vec<Stmt> {
    let mut body = consumers;
    body.push(Stmt::Branch {
        cond: var(toggle),
        then_body: vec![],
        else_body: vec![
            Stmt::Assignment {
                lhs: var(temp_name),
                rhs: neg_toggle,
                offset: 0x20,
            },
            Stmt::Assignment {
                lhs: var(toggle),
                rhs: var(temp_name),
                offset: 0x24,
            },
        ],
        offset: 0x28,
    });
    body
}
