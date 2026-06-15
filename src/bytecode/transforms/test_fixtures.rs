//! Shared `Expr`/`Stmt` builders for transform unit tests.
//!
//! Each transform module's test suite previously redefined the same
//! handful of small constructors (`var`, `lit`, `assign`, `call`).
//! Centralising them keeps the bodies one canonical shape; the rare
//! file-specific variants stay local at their call sites.

use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;

/// `Expr::Var(name)`.
pub(crate) fn var(name: &str) -> Expr {
    Expr::Var(name.to_string())
}

/// `Expr::Literal(value)`.
pub(crate) fn lit(value: &str) -> Expr {
    Expr::Literal(value.to_string())
}

/// `Stmt::Assignment` with a `Var(lhs_name)` lhs and offset 0.
pub(crate) fn assign(lhs_name: &str, rhs: Expr) -> Stmt {
    Stmt::Assignment {
        lhs: var(lhs_name),
        rhs,
        offset: 0,
    }
}

/// `Stmt::Assignment` taking an arbitrary `Expr` lhs (for `FieldAccess`,
/// `Index`, etc.) and offset 0.
pub(crate) fn assign_expr(lhs: Expr, rhs: Expr) -> Stmt {
    Stmt::Assignment {
        lhs,
        rhs,
        offset: 0,
    }
}

/// `Stmt::Call` with a `Var(name)` callee and offset 0.
pub(crate) fn call(name: &str, args: Vec<Expr>) -> Stmt {
    Stmt::Call {
        func: var(name),
        args,
        offset: 0,
    }
}

/// Variant-name extractor for friendlier assertion failure output. The
/// statement-IR transforms tests hit this often when a recognizer
/// produces the wrong shape; a string label is easier to read in panic
/// messages than the full `Stmt` debug dump.
pub(crate) fn stmt_kind(stmt: &Stmt) -> &'static str {
    match stmt {
        Stmt::Assignment { .. } => "Assignment",
        Stmt::Call { .. } => "Call",
        Stmt::Branch { .. } => "Branch",
        Stmt::Sequence { .. } => "Sequence",
        Stmt::Loop { .. } => "Loop",
        Stmt::Switch { .. } => "Switch",
        Stmt::Latch { .. } => "Latch",
        Stmt::Return { .. } => "Return",
        Stmt::EventCall { .. } => "EventCall",
        Stmt::Break { .. } => "Break",
        Stmt::Unknown { .. } => "Unknown",
    }
}
