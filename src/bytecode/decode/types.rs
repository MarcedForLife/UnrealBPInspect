use std::cell::OnceCell;

use super::super::readers::*;
use super::super::resolve::*;
use super::ir;
use super::ir::Expr;
use crate::binary::NameTable;
use crate::types::ImportEntry;

/// Byte-offset span `(start, end)` into `BcStatement.text`. Tuple rather
/// than `Range<usize>` so `StmtKind` can stay `Copy`.
pub type TextSpan = (usize, usize);

/// Classification of a `BcStatement` for strict pattern-matching.
///
/// Populated at construction via [`StmtKind::classify`] from the text surface.
/// Variants that carry arguments hold [`TextSpan`] / `usize` slices into
/// `BcStatement.text` rather than owned strings so the enum stays `Copy` and
/// callers can query it cheaply via [`BcStatement::if_jump`] /
/// [`BcStatement::jump_target`] / etc. The text form is retained for rendering.
/// `kind` must be refreshed via [`BcStatement::reclassify`] or
/// [`BcStatement::set_text`] whenever a pass rewrites `.text` in a way that
/// would change its classification or shift its field offsets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StmtKind {
    /// `pop_flow` — end of a pushed continuation scope.
    PopFlow,
    /// `pop_flow_if_not(COND)` — conditional scope exit. `cond` spans the
    /// condition body inside `BcStatement.text`.
    PopFlowIfNot { cond: TextSpan },
    /// `push_flow 0xHEX` — save a continuation offset.
    PushFlow { target: usize },
    /// `continue_if_not(COND)` — synthetic ForEach-body marker. `cond` spans
    /// the condition body inside `BcStatement.text`.
    ContinueIfNot { cond: TextSpan },
    /// `if !(COND) jump 0xHEX` — conditional forward jump. `cond` spans the
    /// condition body inside `BcStatement.text`.
    IfJump { cond: TextSpan, target: usize },
    /// `jump 0xHEX` — unconditional jump.
    Jump { target: usize },
    /// `jump_computed(EXPR)` — computed jump (Switch dispatch).
    JumpComputed,
    /// `return nop` — end-of-function sentinel.
    ReturnNop,
    /// `return` — bare return from the function.
    BareReturn,
    /// Anything else — assignment, function call, synthetic marker, phantom,
    /// or any statement that isn't load-bearing for flow structuring.
    Other,
}

impl StmtKind {
    /// Classify a statement by inspecting its text and capturing field offsets
    /// / values for variants that carry arguments. Cheap prefix/literal checks
    /// only; for full AST parsing of the tail see [`super::parse_stmt`].
    pub fn classify(text: &str) -> Self {
        if text == super::super::POP_FLOW {
            return StmtKind::PopFlow;
        }
        if text == super::super::RETURN_NOP {
            return StmtKind::ReturnNop;
        }
        if text == super::super::BARE_RETURN {
            return StmtKind::BareReturn;
        }
        if let Some(inner) = text.strip_prefix("pop_flow_if_not(") {
            if inner.ends_with(')') {
                let start = "pop_flow_if_not(".len();
                let end = text.len() - 1;
                return StmtKind::PopFlowIfNot { cond: (start, end) };
            }
        }
        if let Some(rest) = text.strip_prefix("push_flow 0x") {
            if let Ok(target) = usize::from_str_radix(rest, 16) {
                return StmtKind::PushFlow { target };
            }
        }
        if let Some(inner) = text.strip_prefix("continue_if_not(") {
            if inner.ends_with(')') {
                let start = "continue_if_not(".len();
                let end = text.len() - 1;
                return StmtKind::ContinueIfNot { cond: (start, end) };
            }
        }
        if text.starts_with("jump_computed(") {
            return StmtKind::JumpComputed;
        }
        if text.starts_with("if !(") {
            if let Some(jump_pos) = text.rfind(") jump 0x") {
                if let Ok(target) = usize::from_str_radix(&text[jump_pos + 9..], 16) {
                    let cond_start = 5;
                    let cond_end = jump_pos;
                    return StmtKind::IfJump {
                        cond: (cond_start, cond_end),
                        target,
                    };
                }
            }
        }
        if let Some(rest) = text.strip_prefix("jump 0x") {
            if let Ok(target) = usize::from_str_radix(rest, 16) {
                return StmtKind::Jump { target };
            }
        }
        StmtKind::Other
    }

    /// True for `pop_flow_if_not` / `push_flow` / `continue_if_not` —
    /// condition-carrier sinks that couple inlined temps to flow structure.
    /// Used by `inline_single_use_temps` to decide whether a jump-anchor temp
    /// can be phantomed safely (see docs/remaining-work.md phantom workstream).
    #[inline]
    pub fn is_flow_opcode_consumer(self) -> bool {
        matches!(
            self,
            StmtKind::PopFlowIfNot { .. }
                | StmtKind::PushFlow { .. }
                | StmtKind::ContinueIfNot { .. }
        )
    }
}

#[derive(Clone)]
pub struct BcStatement {
    /// In-memory bytecode offset (adjusted for FName size differences).
    pub mem_offset: usize,
    /// Absorbed offsets from removed statements, so `OffsetMap` can still
    /// resolve jump targets that pointed at them. Populated by transform
    /// passes. Empty for most statements.
    pub offset_aliases: Vec<usize>,
    pub text: String,
    /// Set by inlining passes to mark a statement as folded into a consumer.
    /// The statement is kept in the vector so its `mem_offset` still anchors
    /// jump-target resolution, but its `text` is blank and pattern-matchers /
    /// text emission should skip it via [`BcStatementSliceExt::live`].
    pub inlined_away: bool,
    /// Strict classification of `text`. See [`StmtKind`].
    pub kind: StmtKind,
    /// Lazy parse of `(lhs, rhs)` for assignment-shaped `Other` statements.
    /// Outer `Option` (via `OnceCell::get`) distinguishes "not yet parsed"
    /// from "parsed". Inner `Option` distinguishes "is assignment, here's
    /// the tree" from "not an assignment shape, don't retry". Reset on any
    /// `.text` rewrite that goes through [`Self::set_text`] / [`Self::reclassify`].
    assignment_cache: OnceCell<Option<(Expr, Expr)>>,
    /// Lazy parse of the condition expression for `PopFlowIfNot`,
    /// `ContinueIfNot`, `IfJump`. Inner `None` means "no cond for this kind".
    cond_cache: OnceCell<Option<Expr>>,
}

impl BcStatement {
    pub fn new(mem_offset: usize, text: impl Into<String>) -> Self {
        let text = text.into();
        let kind = StmtKind::classify(&text);
        Self {
            mem_offset,
            text,
            offset_aliases: Vec::new(),
            inlined_away: false,
            kind,
            assignment_cache: OnceCell::new(),
            cond_cache: OnceCell::new(),
        }
    }

    /// Refresh `kind` after a pass rewrites `.text`. Cheap — parses only prefix
    /// literals. Call this whenever text is replaced by a transform. Also
    /// invalidates the lazy expression caches, since the parsed trees hang off
    /// the old text.
    #[inline]
    pub fn reclassify(&mut self) {
        self.kind = StmtKind::classify(&self.text);
        self.assignment_cache = OnceCell::new();
        self.cond_cache = OnceCell::new();
    }

    /// Replace `.text` and keep `.kind` in sync. Preferred over raw
    /// `stmt.text = ...` assignment when the new text could change
    /// classification (e.g. rewriting a jump form, inserting a continue marker).
    #[inline]
    pub fn set_text(&mut self, text: impl Into<String>) {
        self.text = text.into();
        self.reclassify();
    }

    /// Update the target offset of a target-carrying statement
    /// (`Jump`, `IfJump`, `PushFlow`). No-op for other kinds. Rewrites
    /// the text via `set_text`, preserving the `if !(COND)` prefix
    /// on `IfJump` and the `push_flow` / `jump` opcode keywords.
    pub fn rewrite_target(&mut self, new_target: usize) {
        let new_text = match self.kind {
            StmtKind::Jump { .. } => format!("jump 0x{:x}", new_target),
            StmtKind::PushFlow { .. } => format!("push_flow 0x{:x}", new_target),
            StmtKind::IfJump {
                cond: (start, end), ..
            } => {
                let cond_str = self.text[start..end].to_owned();
                format!("if !({}) jump 0x{:x}", cond_str, new_target)
            }
            _ => return,
        };
        self.set_text(new_text);
    }

    /// Lazy-parsed `(lhs, rhs)` for assignment-shaped statements. Returns
    /// `None` for flow opcodes, synthetic markers, call-as-statement lines,
    /// and phantom (inlined-away) statements. The parse runs once per
    /// statement and is cached, reset on [`Self::set_text`] / [`Self::reclassify`].
    pub fn assignment(&self) -> Option<(&Expr, &Expr)> {
        if self.inlined_away {
            return None;
        }
        if !matches!(self.kind, StmtKind::Other) {
            return None;
        }
        let cached = self.assignment_cache.get_or_init(|| {
            let eq_pos = ir::top_level_eq_split(&self.text)?;
            let lhs_text = self.text[..eq_pos].trim();
            let rhs_text = self.text[eq_pos + 1..].trim();
            let lhs = ir::parse_expr(lhs_text);
            let rhs = ir::parse_expr(rhs_text);
            Some((lhs, rhs))
        });
        cached.as_ref().map(|(lhs, rhs)| (lhs, rhs))
    }

    /// Lazy-parsed condition expression for the three cond-carrying kinds
    /// (`PopFlowIfNot`, `ContinueIfNot`, `IfJump`). Returns `None` for every
    /// other kind and for phantom statements.
    pub fn cond_expr(&self) -> Option<&Expr> {
        if self.inlined_away {
            return None;
        }
        let cached = self.cond_cache.get_or_init(|| {
            let slice = self
                .if_jump()
                .map(|(cond, _)| cond)
                .or_else(|| self.pop_flow_if_not_cond())
                .or_else(|| self.continue_if_not_cond())?;
            Some(ir::parse_expr(slice))
        });
        cached.as_ref()
    }

    /// True when this statement is live — not inlined-away. Use when
    /// pattern-matching or counting statements; use the raw slice when
    /// building offset maps or CFGs that need every anchor.
    #[inline]
    pub fn is_live(&self) -> bool {
        !self.inlined_away
    }

    /// Extract `(cond, target)` from an `if !(COND) jump 0xHEX` statement.
    /// Uses the cached [`StmtKind`]; keep it in sync via [`Self::set_text`]
    /// when rewriting `.text`.
    #[inline]
    pub fn if_jump(&self) -> Option<(&str, usize)> {
        match self.kind {
            StmtKind::IfJump {
                cond: (start, end),
                target,
            } => Some((&self.text[start..end], target)),
            _ => None,
        }
    }

    /// Extract the target offset from an unconditional `jump 0xHEX`.
    #[inline]
    pub fn jump_target(&self) -> Option<usize> {
        match self.kind {
            StmtKind::Jump { target } => Some(target),
            _ => None,
        }
    }

    /// Extract the saved continuation offset from `push_flow 0xHEX`.
    #[inline]
    pub fn push_flow_target(&self) -> Option<usize> {
        match self.kind {
            StmtKind::PushFlow { target } => Some(target),
            _ => None,
        }
    }

    /// Extract the condition from a `pop_flow_if_not(COND)` statement.
    #[inline]
    pub fn pop_flow_if_not_cond(&self) -> Option<&str> {
        match self.kind {
            StmtKind::PopFlowIfNot { cond: (start, end) } => Some(&self.text[start..end]),
            _ => None,
        }
    }

    /// Extract the condition from a `continue_if_not(COND)` statement.
    #[inline]
    pub fn continue_if_not_cond(&self) -> Option<&str> {
        match self.kind {
            StmtKind::ContinueIfNot { cond: (start, end) } => Some(&self.text[start..end]),
            _ => None,
        }
    }
}

/// Slice extension giving pattern-matching passes an iteration view that
/// skips phantom (inlined-away) statements. `OffsetMap` / CFG construction
/// keep using the raw slice so phantoms still anchor jump resolution.
pub trait BcStatementSliceExt {
    fn live(&self) -> Box<dyn Iterator<Item = (usize, &BcStatement)> + '_>;
}

impl BcStatementSliceExt for [BcStatement] {
    fn live(&self) -> Box<dyn Iterator<Item = (usize, &BcStatement)> + '_> {
        Box::new(self.iter().enumerate().filter(|(_, s)| s.is_live()))
    }
}

/// Immutable context shared across recursive decode calls. Split from the
/// mutable `pos`/`mem_adj` state to avoid borrow conflicts.
pub struct DecodeCtx<'a> {
    pub(super) bytecode: &'a [u8],
    pub(super) name_table: &'a NameTable,
    pub(super) imports: &'a [ImportEntry],
    pub(super) export_names: &'a [String],
    pub(super) ue5: i32,
}

impl<'a> DecodeCtx<'a> {
    pub(super) fn read_obj_ref(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_obj_ref(self.bytecode, pos, self.imports, self.export_names, mem_adj)
    }

    pub(super) fn read_field_path(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_field_path(self.bytecode, pos, self.name_table, mem_adj)
    }

    pub(super) fn read_fname_with_adj(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_fname_with_adj(self.bytecode, pos, self.name_table, mem_adj)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::decode::ir::Expr;

    #[test]
    fn assignment_returns_some_for_assign_text() {
        let stmt = BcStatement::new(0, "$Foo = Bar(1, 2)");
        let (lhs, rhs) = stmt.assignment().expect("assignment shape");
        assert_eq!(lhs, &Expr::Var("$Foo".to_owned()));
        assert_eq!(
            rhs,
            &Expr::Call {
                name: "Bar".to_owned(),
                args: vec![Expr::Literal("1".to_owned()), Expr::Literal("2".to_owned()),],
            }
        );
    }

    #[test]
    fn assignment_returns_none_for_call_line() {
        let stmt = BcStatement::new(0, "Foo(1, 2)");
        assert!(stmt.assignment().is_none());
    }

    #[test]
    fn assignment_returns_none_for_flow_opcode() {
        let cases = [
            "pop_flow",
            "push_flow 0x1234",
            "if !(x) jump 0x5678",
            "pop_flow_if_not(cond)",
            "continue_if_not(cond)",
            "jump 0x1000",
            "return",
            "return nop",
        ];
        for text in cases {
            let stmt = BcStatement::new(0, text);
            assert!(
                stmt.assignment().is_none(),
                "expected None for flow opcode {:?}",
                text
            );
        }
    }

    #[test]
    fn assignment_returns_none_for_phantom() {
        let mut stmt = BcStatement::new(0, "$Foo = Bar(1)");
        stmt.inlined_away = true;
        assert!(stmt.assignment().is_none());
    }

    #[test]
    fn assignment_cache_idempotent() {
        let stmt = BcStatement::new(0, "$Foo = Bar(1)");
        let (lhs1, rhs1) = stmt.assignment().expect("first call");
        let (lhs2, rhs2) = stmt.assignment().expect("second call");
        assert!(std::ptr::eq(lhs1, lhs2), "lhs pointer should be stable");
        assert!(std::ptr::eq(rhs1, rhs2), "rhs pointer should be stable");
    }

    #[test]
    fn cond_expr_returns_some_for_if_jump() {
        let stmt = BcStatement::new(0, "if !(a > b) jump 0x100");
        let cond = stmt.cond_expr().expect("cond");
        assert_eq!(
            cond,
            &Expr::Binary {
                op: ">".to_owned(),
                lhs: Box::new(Expr::Var("a".to_owned())),
                rhs: Box::new(Expr::Var("b".to_owned())),
            }
        );
    }

    #[test]
    fn cond_expr_returns_some_for_pop_flow_if_not() {
        let stmt = BcStatement::new(0, "pop_flow_if_not(IsValid(self))");
        let cond = stmt.cond_expr().expect("cond");
        assert_eq!(
            cond,
            &Expr::Call {
                name: "IsValid".to_owned(),
                args: vec![Expr::Var("self".to_owned())],
            }
        );
    }

    #[test]
    fn cond_expr_returns_some_for_continue_if_not() {
        let stmt = BcStatement::new(0, "continue_if_not(IsValid(self))");
        let cond = stmt.cond_expr().expect("cond");
        assert_eq!(
            cond,
            &Expr::Call {
                name: "IsValid".to_owned(),
                args: vec![Expr::Var("self".to_owned())],
            }
        );
    }

    #[test]
    fn cond_expr_returns_none_for_other_kinds() {
        let cases = [
            "push_flow 0x1234",
            "jump 0x1000",
            "pop_flow",
            "return",
            "return nop",
            "$Foo = Bar(1)",
            "Foo(1, 2)",
        ];
        for text in cases {
            let stmt = BcStatement::new(0, text);
            assert!(stmt.cond_expr().is_none(), "expected None for {:?}", text);
        }
    }

    #[test]
    fn set_text_invalidates_caches() {
        let mut stmt = BcStatement::new(0, "$Foo = Bar(1)");
        assert!(stmt.assignment().is_some());
        stmt.set_text("pop_flow");
        assert!(stmt.assignment().is_none());
        assert!(stmt.cond_expr().is_none());
    }
}
