//! Typed IR data definitions shared by the parser and printer.
//!
//! TODO(5d.2): the decoder does not directly emit a ternary `a ? b : c`
//! shape (it comes from later transforms) or a braced struct-construct
//! shape. `Ternary` and `StructConstruct` variants are intentionally
//! left unpopulated by the parser. `Select` is likewise unused because
//! the decoder emits `SelectFloat(t, f, cond)` as a regular call,
//! later passes may rewrite into `Select`, but parsing the call form
//! is sufficient for the current slices.

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Literal(String),
    Var(String),
    Call {
        name: String,
        args: Vec<Expr>,
    },
    MethodCall {
        recv: Box<Expr>,
        name: String,
        args: Vec<Expr>,
    },
    FieldAccess {
        recv: Box<Expr>,
        field: String,
    },
    Index {
        recv: Box<Expr>,
        idx: Box<Expr>,
    },
    Binary {
        op: String,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: String,
        operand: Box<Expr>,
    },
    Cast {
        ty: String,
        inner: Box<Expr>,
    },
    StructConstruct {
        ty: String,
        fields: Vec<(String, Expr)>,
    },
    Select {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    Switch {
        scrut: Box<Expr>,
        arms: Vec<SwitchArm>,
        default: Option<Box<Expr>>,
    },
    Ternary {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Wraps an inner expression with a trailing metadata annotation
    /// such as `[persistent]` or `/*resume:0xHEX*/`. The `trailer`
    /// field carries the verbatim separator + marker (e.g.
    /// `" [persistent]"` or `" /*resume:0x000f*/"`) so
    /// `fmt_expr(parse_expr(input)) == input` holds byte-for-byte for
    /// the markers this slice handles. Semantics are preserved by the
    /// downstream text-based passes that still match on the marker.
    Trailer {
        inner: Box<Expr>,
        trailer: String,
    },
    /// Wraps an inner expression with an `out ` parameter-direction
    /// prefix emitted by the decoder on Blueprint out-params. The inner
    /// shape (bare variable, array subscript, method call) parses and
    /// prints through the normal expression path, this variant only
    /// carries the prefix so `fmt_expr(parse_expr(input)) == input`
    /// holds byte-for-byte.
    Out(Box<Expr>),
    /// A bracketed array literal `[e1, e2, ...]` emitted by the decoder
    /// for `MakeArray` / empty array out-param defaults. Elements are
    /// whatever shape the decoder picks per slot. Empty `[]` is a valid
    /// zero-element literal. `fmt_expr` re-emits `[e1, e2, ...]` with
    /// `, ` separators so `fmt_expr(parse_expr(input)) == input` holds
    /// byte-for-byte.
    ArrayLit(Vec<Expr>),
    Unknown(String),
}

impl Expr {
    /// Visit every `Expr` node in the tree rooted at `self`, parents first.
    /// Keeps the variant list in one place so callers stop reinventing the
    /// recursive walk across transforms and tests.
    pub fn walk<'a>(&'a self, f: &mut impl FnMut(&'a Expr)) {
        f(self);
        match self {
            Expr::Call { args, .. } => {
                for arg in args {
                    arg.walk(f);
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                recv.walk(f);
                for arg in args {
                    arg.walk(f);
                }
            }
            Expr::FieldAccess { recv, .. } => recv.walk(f),
            Expr::Index { recv, idx } => {
                recv.walk(f);
                idx.walk(f);
            }
            Expr::Binary { lhs, rhs, .. } => {
                lhs.walk(f);
                rhs.walk(f);
            }
            Expr::Unary { operand, .. } => operand.walk(f),
            Expr::Cast { inner, .. } => inner.walk(f),
            Expr::StructConstruct { fields, .. } => {
                for (_, value) in fields {
                    value.walk(f);
                }
            }
            Expr::Select {
                cond,
                then_expr,
                else_expr,
            }
            | Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.walk(f);
                then_expr.walk(f);
                else_expr.walk(f);
            }
            Expr::Switch {
                scrut,
                arms,
                default,
            } => {
                scrut.walk(f);
                for arm in arms {
                    arm.pat.walk(f);
                    arm.body.walk(f);
                }
                if let Some(default_expr) = default {
                    default_expr.walk(f);
                }
            }
            Expr::Trailer { inner, .. } | Expr::Out(inner) => inner.walk(f),
            Expr::ArrayLit(items) => {
                for item in items {
                    item.walk(f);
                }
            }
            Expr::Literal(_) | Expr::Var(_) | Expr::Unknown(_) => {}
        }
    }

    /// Mutable counterpart to [`Expr::walk`]. Parents still visit first so
    /// callers can replace a node before its children get a chance to see
    /// the stale value.
    pub fn walk_mut(&mut self, f: &mut impl FnMut(&mut Expr)) {
        f(self);
        match self {
            Expr::Call { args, .. } => {
                for arg in args {
                    arg.walk_mut(f);
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                recv.walk_mut(f);
                for arg in args {
                    arg.walk_mut(f);
                }
            }
            Expr::FieldAccess { recv, .. } => recv.walk_mut(f),
            Expr::Index { recv, idx } => {
                recv.walk_mut(f);
                idx.walk_mut(f);
            }
            Expr::Binary { lhs, rhs, .. } => {
                lhs.walk_mut(f);
                rhs.walk_mut(f);
            }
            Expr::Unary { operand, .. } => operand.walk_mut(f),
            Expr::Cast { inner, .. } => inner.walk_mut(f),
            Expr::StructConstruct { fields, .. } => {
                for (_, value) in fields {
                    value.walk_mut(f);
                }
            }
            Expr::Select {
                cond,
                then_expr,
                else_expr,
            }
            | Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.walk_mut(f);
                then_expr.walk_mut(f);
                else_expr.walk_mut(f);
            }
            Expr::Switch {
                scrut,
                arms,
                default,
            } => {
                scrut.walk_mut(f);
                for arm in arms {
                    arm.pat.walk_mut(f);
                    arm.body.walk_mut(f);
                }
                if let Some(default_expr) = default {
                    default_expr.walk_mut(f);
                }
            }
            Expr::Trailer { inner, .. } | Expr::Out(inner) => inner.walk_mut(f),
            Expr::ArrayLit(items) => {
                for item in items {
                    item.walk_mut(f);
                }
            }
            Expr::Literal(_) | Expr::Var(_) | Expr::Unknown(_) => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct SwitchArm {
    pub pat: Expr,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Assignment {
        lhs: Expr,
        rhs: Expr,
    },
    /// Compound-assignment statement such as `x += y` or `x -= y`.
    /// The decoder emits these verbatim for delegate binds
    /// (`.OnEvent_Bind += $CreateDelegate_...`). `op` is the two-char
    /// literal (`"+="` or `"-="`), kept as a `String` because `Stmt`
    /// is `Clone`-able and interning two static literals isn't worth
    /// the complexity.
    CompoundAssign {
        op: String,
        lhs: Expr,
        rhs: Expr,
    },
    Call {
        expr: Expr,
    },
    PopFlow,
    PopFlowIfNot {
        cond: Expr,
    },
    PushFlow {
        target: usize,
    },
    ContinueIfNot {
        cond: Expr,
    },
    IfJump {
        cond: Expr,
        target: usize,
    },
    Jump {
        target: usize,
    },
    JumpComputed {
        expr: Expr,
    },
    ReturnNop,
    BareReturn,
    /// Wraps an inner statement with a trailing metadata annotation
    /// such as `[persistent]` or `/*resume:0xHEX*/`. See
    /// [`Expr::Trailer`] for the trailer shape; the statement-level
    /// variant exists because some lines (e.g. bare `Delay(...)
    /// /*resume:0x000f*/`) parse as a [`Stmt::Call`] whose trailer is
    /// cleaner kept at the statement level than pushed into the call
    /// expression.
    WithTrailer {
        inner: Box<Stmt>,
        trailer: String,
    },
    /// Post-structure comment line. The stored string is the trimmed
    /// line starting with `//`. The caller owns indentation, so the
    /// printer emits the stored text verbatim with no leading padding.
    Comment(String),
    /// Post-structure block-close marker. Matches a trimmed line that
    /// is exactly `}`. Indentation is owned by the caller.
    BlockClose,
    /// Post-structure `break` keyword line emitted by loop-rewrite
    /// passes. Matches a trimmed line that is exactly `break`.
    Break,
    /// Post-structure `if (COND) {` block header. Carries the typed
    /// condition expression, the caller owns indentation. Falls back to
    /// `Stmt::Unknown` whenever `cond` would be `Expr::Unknown`, the
    /// printer emits exactly `if ({fmt_expr(cond)}) {`.
    IfOpen {
        cond: Expr,
    },
    /// Post-structure `} else {` block separator. Unit variant, caller
    /// owns indentation. The printer emits exactly `} else {`.
    Else,
    Unknown(String),
}
