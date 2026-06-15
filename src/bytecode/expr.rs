//! Expression intermediate representation (IR) for the decoder.
//!
//! Operators are typed enums (`BinaryOp`, `UnaryOp`, `CastKind`)
//! rather than `String` fields, so transforms can pattern-match
//! exhaustively and the compiler catches new operators that aren't
//! handled. No node carries verbatim text that a downstream pass has
//! to re-parse.
//!
//! Trailers are one variant per marker (`Persistent`, `Resume`), each
//! carrying its structured payload as typed fields rather than a
//! single opaque text wrapper. New trailers get their own variants.
//!
//! `Out` stays as a structural wrapper, it marks a Blueprint
//! out-parameter, which is a real ABI distinction at the call site,
//! not a cosmetic prefix. Statement-level switch dispatch is modelled
//! by `Stmt::Switch`; the inline (expression-position) form of
//! `EX_SwitchValue` is modelled by `Expr::Switch` so embedded
//! sub-expressions stay structured rather than collapsing into a
//! `Call` placeholder.
//!
//! `Expr::Unknown` is the diagnostic escape hatch, mirroring
//! `Stmt::Unknown`. When an operand is `Unknown`, the containing
//! statement's decoder bubbles up to `Stmt::Unknown` because the
//! whole statement can no longer be trusted.

/// An expression node in the decoder's statement tree.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Expr {
    /// A scalar literal whose textual form was produced by the
    /// constant-opcode decoders (int, float, string, name, vector,
    /// rotator, etc.).
    Literal(String),

    /// A bare variable reference (local, parameter, or member).
    Var(String),

    /// A free-function call (`name(args)`).
    Call { name: String, args: Vec<Expr> },

    /// A method call on a receiver (`recv.name(args)`).
    MethodCall {
        recv: Box<Expr>,
        name: String,
        args: Vec<Expr>,
    },

    /// A field access (`recv.field`).
    FieldAccess { recv: Box<Expr>, field: String },

    /// An array subscript (`recv[idx]`).
    Index { recv: Box<Expr>, idx: Box<Expr> },

    /// A binary operator application. The operator vocabulary is
    /// fixed by `BinaryOp`.
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    /// A unary operator application. The operator vocabulary is
    /// fixed by `UnaryOp`.
    Unary { op: UnaryOp, operand: Box<Expr> },

    /// A typed coercion from `EX_PRIMITIVE_CAST`. Transparent UE5
    /// casts (Large World Coordinates double/float, obj-to-iface)
    /// elide the wrapper and surface as the inner expression.
    Cast { kind: CastKind, inner: Box<Expr> },

    /// A bracketed array literal `[e1, e2, ...]` from the
    /// `MakeArray` opcode. Empty `[]` is valid.
    ArrayLit(Vec<Expr>),

    /// A ternary `cond ? then : else`. Not produced directly by
    /// the decoder, populated by later expression-level transforms.
    Ternary {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },

    /// Marks a Blueprint out-parameter at a call site. Structural,
    /// the inner expression is the storage the callee writes into.
    Out(Box<Expr>),

    /// An interface-context wrapper from `EX_INTERFACE_CONTEXT`.
    /// Distinct from `Cast` because the runtime semantics differ
    /// from a primitive cast.
    Interface(Box<Expr>),

    /// Inner expression assigned into a persistent frame slot
    /// (`EX_LET_VALUE_ON_PERSISTENT_FRAME`). Wraps the right-hand
    /// side so downstream passes avoid inlining across event
    /// boundaries.
    Persistent(Box<Expr>),

    /// Latent-call resume marker. `target` is the bytecode mem
    /// offset the latent action resumes at.
    Resume { inner: Box<Expr>, target: usize },

    /// Inline `switch` from `EX_SwitchValue` at expression position.
    /// Each case carries an expression body (single result expression),
    /// distinct from `Stmt::Switch` whose case bodies are statement
    /// vectors. `default` is always present in the IR; renderers may
    /// omit it when it resolves to the `$Select_Default` sentinel that
    /// the compiler emits for switches without an explicit default arm.
    Switch {
        index: Box<Expr>,
        cases: Vec<SwitchExprCase>,
        default: Box<Expr>,
    },

    /// A folded struct constructor (`Make<Type>(field=value, ...)`).
    /// Not produced directly by the decoder, populated by the
    /// statement-level struct-fold transform when it collapses a
    /// contiguous run of field assignments to a temporary into a
    /// single-expression constructor. `type_name` records the struct
    /// type name when the transform can determine it; otherwise the
    /// transform falls back to `"<unknown>"` so the rendered shape is
    /// still recognisable.
    StructConstruct {
        type_name: String,
        fields: Vec<(String, Expr)>,
    },

    /// Diagnostic escape hatch for operands the decoder cannot
    /// classify. The containing statement bubbles this up to
    /// `Stmt::Unknown`.
    Unknown {
        reason: String,
        raw_bytes: Vec<u8>,
        offset: usize,
    },
}

/// One arm of an `Expr::Switch`. Holds a case-value expression and a
/// case-body expression. Distinct from `stmt::SwitchCase`, whose body
/// is a `Vec<Stmt>` because statement-level switches have multi-stmt
/// arms; the expression-position switch produced by `EX_SwitchValue`
/// has one result expression per arm.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SwitchExprCase {
    pub value: Expr,
    pub body: Expr,
}

/// Binary operators recognised by the decoder. Grouped by category,
/// alphabetised within each category so future additions land at a
/// predictable spot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum BinaryOp {
    // Arithmetic.
    /// `lhs + rhs`
    Add,
    /// `lhs / rhs`
    Div,
    /// `lhs % rhs`
    Mod,
    /// `lhs * rhs`
    Mul,
    /// `lhs - rhs`
    Sub,

    // Comparison.
    /// `lhs == rhs`
    Eq,
    /// `lhs >= rhs`
    Ge,
    /// `lhs > rhs`
    Gt,
    /// `lhs <= rhs`
    Le,
    /// `lhs < rhs`
    Lt,
    /// `lhs != rhs`
    Ne,

    // Logical.
    /// `lhs && rhs`
    And,
    /// `lhs || rhs`
    Or,

    // Bitwise.
    /// `lhs & rhs`
    BitAnd,
    /// `lhs | rhs`
    BitOr,
    /// `lhs << rhs`
    Shl,
    /// `lhs >> rhs`
    Shr,
    /// `lhs ^ rhs`
    Xor,
}

/// Unary operators recognised by the decoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum UnaryOp {
    /// Bitwise complement (`~operand`).
    BitNot,
    /// Arithmetic negation (`-operand`).
    Neg,
    /// Logical negation (`!operand`).
    Not,
}

/// Source-level symbol for a binary operator (`+`, `==`, `&&`, etc.).
/// Shared by every emitter so the symbol mapping has one source of truth.
pub(crate) fn binary_op_symbol(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Mod => "%",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::Ge => ">=",
        BinaryOp::And => "&&",
        BinaryOp::Or => "||",
        BinaryOp::BitAnd => "&",
        BinaryOp::BitOr => "|",
        BinaryOp::Xor => "^",
        BinaryOp::Shl => "<<",
        BinaryOp::Shr => ">>",
    }
}

/// Source-level symbol for a unary operator (`!`, `-`, `~`).
/// Shared by every emitter so the symbol mapping has one source of truth.
pub(crate) fn unary_op_symbol(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Not => "!",
        UnaryOp::Neg => "-",
        UnaryOp::BitNot => "~",
    }
}

/// Typed coercion. Covers both `EX_PRIMITIVE_CAST` (UE4 / UE5
/// renumbered byte set) and the dedicated object-cast opcodes
/// (`EX_DynamicCast`, `EX_MetaCast`, `EX_ObjToInterfaceCast`,
/// `EX_CrossInterfaceCast`, `EX_InterfaceToObjCast`). Variants that
/// target a specific class or interface carry the resolved type
/// name so renderers and transforms have it without re-resolving
/// the original `class_obj_idx`. Transparent casts (UE5 LWC
/// double/float) are not represented because the decoder elides
/// them.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CastKind {
    /// Dynamic class cast (`EX_DynamicCast`, `EX_MetaCast`).
    /// Renders as `Cast<Target>(x)`, matching the Blueprint editor
    /// `Cast` node terminology.
    Class { target: String },
    /// Object/cross-interface cast targeting a specific interface
    /// (`EX_ObjToInterfaceCast`, `EX_CrossInterfaceCast`).
    ToInterface { target: String },
    /// Interface unwrap to its underlying object reference
    /// (`EX_InterfaceToObjCast`).
    ToObject,
    /// Truthiness coercion (`CST_ObjectToBool`, `CST_InterfaceToBool`).
    ToBool,
    /// Cast opcode/byte the decoder did not recognise. The raw byte
    /// is preserved for diagnostics.
    Other(u8),
}
