//! Tests for the summary emitter. Extracted from the production module
//! so the walker stays focused on emission logic; expression-rendering
//! coverage and ForC header fixtures live here.

#[cfg(test)]
mod tests {
    use super::super::summary::{emit_summary, expr_to_string};
    use crate::bytecode::asset::{DecodedAsset, Event, Function};
    use crate::bytecode::expr::{BinaryOp, CastKind, Expr, SwitchExprCase, UnaryOp};
    use crate::bytecode::stmt::{LatchKind, Stmt};

    fn empty_asset() -> DecodedAsset {
        DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    #[test]
    fn empty_asset_emits_empty_string() {
        assert_eq!(emit_summary(&empty_asset()), "");
    }

    #[test]
    fn break_stmt_renders_as_break() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "Loop".into(),
                body: vec![Stmt::Break { offset: 0x20 }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        assert_eq!(emit_summary(&asset), "function Loop {\n    break\n}\n");
    }

    #[test]
    fn single_event_with_one_assignment_emits_correctly() {
        let asset = DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "ReceiveTick".into(),
                body: vec![Stmt::Assignment {
                    lhs: Expr::Var("Counter".into()),
                    rhs: Expr::Literal("0".into()),
                    offset: 0x10,
                }],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let result = emit_summary(&asset);
        assert_eq!(result, "event ReceiveTick {\n    Counter = 0\n}\n");
    }

    #[test]
    fn unknown_stmt_emits_diagnostic_comment() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "Foo".into(),
                body: vec![Stmt::Unknown {
                    reason: "bad opcode".into(),
                    raw_bytes: vec![0xab],
                    offset: 0x20,
                    length: 1,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let result = emit_summary(&asset);
        assert!(result.contains("// UNKNOWN at 0x20: bad opcode [1 bytes]"));
    }

    #[test]
    fn expr_to_string_covers_each_variant() {
        // Literal
        assert_eq!(expr_to_string(&Expr::Literal("42".into())), "42");

        // Var
        assert_eq!(expr_to_string(&Expr::Var("MyVar".into())), "MyVar");

        // Call
        assert_eq!(
            expr_to_string(&Expr::Call {
                name: "Foo".into(),
                args: vec![Expr::Literal("1".into())]
            }),
            "Foo(1)"
        );

        // MethodCall
        assert_eq!(
            expr_to_string(&Expr::MethodCall {
                recv: Box::new(Expr::Var("self".into())),
                name: "Bar".into(),
                args: vec![]
            }),
            "self.Bar()"
        );

        // FieldAccess
        assert_eq!(
            expr_to_string(&Expr::FieldAccess {
                recv: Box::new(Expr::Var("obj".into())),
                field: "Health".into()
            }),
            "obj.Health"
        );

        // Index
        assert_eq!(
            expr_to_string(&Expr::Index {
                recv: Box::new(Expr::Var("Arr".into())),
                idx: Box::new(Expr::Literal("0".into()))
            }),
            "Arr[0]"
        );

        // Binary
        assert_eq!(
            expr_to_string(&Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var("a".into())),
                rhs: Box::new(Expr::Var("b".into()))
            }),
            "(a + b)"
        );

        // Unary
        assert_eq!(
            expr_to_string(&Expr::Unary {
                op: UnaryOp::Not,
                operand: Box::new(Expr::Var("flag".into()))
            }),
            "!flag"
        );

        // Casts: dynamic class -> Cast<T>(x), coercions -> (x as Type)
        assert_eq!(
            expr_to_string(&Expr::Cast {
                kind: CastKind::ToBool,
                inner: Box::new(Expr::Var("obj".into()))
            }),
            "(obj as bool)"
        );
        assert_eq!(
            expr_to_string(&Expr::Cast {
                kind: CastKind::Class {
                    target: "MyActor".into()
                },
                inner: Box::new(Expr::Var("actor".into()))
            }),
            "Cast<MyActor>(actor)"
        );
        assert_eq!(
            expr_to_string(&Expr::Cast {
                kind: CastKind::ToInterface {
                    target: "Interactable_BI_C".into()
                },
                inner: Box::new(Expr::Var("actor".into()))
            }),
            "(actor as Interactable_BI_C)"
        );
        assert_eq!(
            expr_to_string(&Expr::Cast {
                kind: CastKind::ToObject,
                inner: Box::new(Expr::Var("iface".into()))
            }),
            "(iface as Object)"
        );
        assert_eq!(
            expr_to_string(&Expr::Cast {
                kind: CastKind::Other(0x46),
                inner: Box::new(Expr::Var("x".into()))
            }),
            "(x as cast_0x46)"
        );

        // ArrayLit
        assert_eq!(
            expr_to_string(&Expr::ArrayLit(vec![
                Expr::Literal("1".into()),
                Expr::Literal("2".into())
            ])),
            "[1, 2]"
        );

        // Ternary
        assert_eq!(
            expr_to_string(&Expr::Ternary {
                cond: Box::new(Expr::Var("ok".into())),
                then_expr: Box::new(Expr::Literal("1".into())),
                else_expr: Box::new(Expr::Literal("0".into()))
            }),
            "ok ? 1 : 0"
        );

        // Out
        assert_eq!(
            expr_to_string(&Expr::Out(Box::new(Expr::Var("result".into())))),
            "out result"
        );

        // Interface
        assert_eq!(
            expr_to_string(&Expr::Interface(Box::new(Expr::Var("iface".into())))),
            "(iface as Interface)"
        );

        // Persistent
        assert_eq!(
            expr_to_string(&Expr::Persistent(Box::new(Expr::Var("slot".into())))),
            "[persistent] slot"
        );

        // Resume
        assert_eq!(
            expr_to_string(&Expr::Resume {
                inner: Box::new(Expr::Var("latent".into())),
                target: 0xff
            }),
            "latent /*resume:0xff*/"
        );

        // Unknown
        assert_eq!(
            expr_to_string(&Expr::Unknown {
                reason: "bad".into(),
                raw_bytes: vec![],
                offset: 0x5
            }),
            "/*?bad@0x5?*/"
        );
    }

    /// Statement-level method call whose receiver is a ternary must wrap
    /// the receiver in parens. Without parens, `cond ? L : R.Foo()`
    /// reads as `cond ? L : (R.Foo())`, a different program.
    #[test]
    fn stmt_call_ternary_receiver_gets_parens() {
        let ternary_recv = Expr::Ternary {
            cond: Box::new(Expr::Var("LeftHand".into())),
            then_expr: Box::new(Expr::Var("self.LeftHand".into())),
            else_expr: Box::new(Expr::Var("self.RightHand".into())),
        };
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "ReleaseGrip".into(),
                body: vec![Stmt::Call {
                    func: Expr::FieldAccess {
                        recv: Box::new(ternary_recv),
                        field: "OnGripReleased".into(),
                    },
                    args: vec![],
                    offset: 0,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let result = emit_summary(&asset);
        assert!(
            result.contains("(LeftHand ? self.LeftHand : self.RightHand).OnGripReleased()"),
            "expected parens around ternary receiver, got:\n{}",
            result
        );
    }

    /// `Expr::Switch` renders inline as
    /// `switch(idx) { 0: a, 1: b }` with the default suppressed when it
    /// is the compiler's `$Select_Default*` sentinel, otherwise
    /// `switch(idx) { 0: a, default: c }`.
    #[test]
    fn switch_expr_renders_v1_shape() {
        let cases = vec![
            SwitchExprCase {
                value: Expr::Literal("0".into()),
                body: Expr::Literal("\"a\"".into()),
            },
            SwitchExprCase {
                value: Expr::Literal("1".into()),
                body: Expr::Literal("\"b\"".into()),
            },
        ];
        // Default is the $Select_Default sentinel; rendering omits it.
        let switch_with_sentinel = Expr::Switch {
            index: Box::new(Expr::Var("idx".into())),
            cases: cases.clone(),
            default: Box::new(Expr::Var("$Select_Default_3".into())),
        };
        assert_eq!(
            expr_to_string(&switch_with_sentinel),
            "switch(idx) { 0: \"a\", 1: \"b\" }"
        );

        // Real default expression renders after the case list.
        let switch_with_default = Expr::Switch {
            index: Box::new(Expr::Var("idx".into())),
            cases,
            default: Box::new(Expr::Literal("\"d\"".into())),
        };
        assert_eq!(
            expr_to_string(&switch_with_default),
            "switch(idx) { 0: \"a\", 1: \"b\", default: \"d\" }"
        );
    }

    /// Build a ForC test asset wrapping the given init/cond/increment.
    fn forc_asset(init: Vec<Stmt>, cond: Option<Expr>, increment: Vec<Stmt>) -> DecodedAsset {
        use crate::bytecode::asset::Event;
        use crate::bytecode::stmt::LoopKind;
        let loop_stmt = Stmt::Loop {
            kind: LoopKind::ForC { init, increment },
            cond,
            body: vec![],
            completion: None,
            offset: 0,
        };
        DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "Test".into(),
                body: vec![loop_stmt],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    /// Canonical ForC with `<` cond renders as Pascal `for (i = 0 to N - 1)`.
    #[test]
    fn forc_canonical_lt_renders_pascal_minus_one() {
        let counter = "i";
        let init_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let inc_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var(counter.into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0,
        };
        let cond = Some(Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Var("N".into())),
        });
        let asset = forc_asset(vec![init_stmt], cond, vec![inc_stmt]);
        let result = emit_summary(&asset);
        assert!(
            result.contains("for (i = 0 to N - 1) {"),
            "expected Pascal `to N - 1` header, got:\n{}",
            result
        );
    }

    /// Canonical ForC with `<=` cond renders as Pascal `for (i = 0 to N)`.
    /// The bound expression is unwrapped so `(TraceSockets - 1)` becomes
    /// `TraceSockets - 1` in the rendered header.
    #[test]
    fn forc_canonical_le_renders_pascal_unwrapped_bound() {
        let counter = "Temp_int_Variable";
        let init_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let inc_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Var("$Add_IntInt".into()),
            offset: 0,
        };
        let cond = Some(Expr::Binary {
            op: BinaryOp::Le,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Binary {
                op: BinaryOp::Sub,
                lhs: Box::new(Expr::Var("TraceSockets".into())),
                rhs: Box::new(Expr::Literal("1".into())),
            }),
        });
        let asset = forc_asset(vec![init_stmt], cond, vec![inc_stmt]);
        let result = emit_summary(&asset);
        assert!(
            result.contains("for (Temp_int_Variable = 0 to TraceSockets - 1) {"),
            "expected Pascal `to TraceSockets - 1` header, got:\n{}",
            result
        );
    }

    /// A ForC with empty `init` is non-canonical and falls back to C-style.
    #[test]
    fn forc_without_init_falls_back_to_c_style() {
        let counter = "i";
        let inc_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var(counter.into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0,
        };
        let cond = Some(Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Var("N".into())),
        });
        let asset = forc_asset(vec![], cond, vec![inc_stmt]);
        let result = emit_summary(&asset);
        assert!(
            result.contains("for (; (i < N); i = (i + 1)) {"),
            "expected C-style fallback, got:\n{}",
            result
        );
    }

    /// A ForC whose init has multiple statements is non-canonical and
    /// falls back to C-style emission.
    #[test]
    fn forc_multi_stmt_init_falls_back_to_c_style() {
        let counter = "i";
        let init_a = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let init_b = Stmt::Assignment {
            lhs: Expr::Var("j".into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let inc_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(Expr::Var(counter.into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0,
        };
        let cond = Some(Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Var("N".into())),
        });
        let asset = forc_asset(vec![init_a, init_b], cond, vec![inc_stmt]);
        let result = emit_summary(&asset);
        // C-style header carries both inits, joined with ", ".
        assert!(
            result.contains("for (i = 0, j = 0;"),
            "expected C-style header with multi-stmt init, got:\n{}",
            result
        );
    }

    /// A ForC whose increment does not target the init counter is
    /// non-canonical and falls back to C-style.
    #[test]
    fn forc_mismatched_increment_falls_back_to_c_style() {
        let init_stmt = Stmt::Assignment {
            lhs: Expr::Var("i".into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let inc_stmt = Stmt::Assignment {
            lhs: Expr::Var("j".into()),
            rhs: Expr::Literal("1".into()),
            offset: 0,
        };
        let cond = Some(Expr::Binary {
            op: BinaryOp::Lt,
            lhs: Box::new(Expr::Var("i".into())),
            rhs: Box::new(Expr::Var("N".into())),
        });
        let asset = forc_asset(vec![init_stmt], cond, vec![inc_stmt]);
        let result = emit_summary(&asset);
        assert!(
            result.contains("for (i = 0; (i < N); j = 1) {"),
            "expected C-style fallback for mismatched increment, got:\n{}",
            result
        );
    }

    /// Build an event asset wrapping a single FlipFlop latch.
    fn flipflop_event_asset(
        gate_var: &str,
        names: Option<(&str, &str)>,
        body: Vec<Stmt>,
    ) -> DecodedAsset {
        let latch = Stmt::Latch {
            kind: LatchKind::FlipFlop {
                gate_var: gate_var.into(),
                names: names.map(|(a, b)| (a.into(), b.into())),
            },
            init: vec![],
            body,
            offset: 0,
        };
        DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "Test".into(),
                body: vec![latch],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    /// `names = Some(("X", "X"))` plus a wrapping `Branch { else: [] }`
    /// renders as `FlipFlop(X) { A|B: { <then-body> } }`.
    #[test]
    fn flipflop_named_with_inner_branch_renders_a_b_block() {
        let consumer = Stmt::Assignment {
            lhs: Expr::FieldAccess {
                recv: Box::new(Expr::Var("self".into())),
                field: "FlyEnabled".into(),
            },
            rhs: Expr::Var("$FlyEnabled_IsA".into()),
            offset: 0,
        };
        let inner_branch = Stmt::Branch {
            cond: Expr::Var("$FlyEnabled_IsA".into()),
            then_body: vec![consumer],
            else_body: vec![],
            offset: 0,
        };
        let asset = flipflop_event_asset(
            "Temp_bool_Variable",
            Some(("FlyEnabled", "FlyEnabled")),
            vec![inner_branch],
        );
        let result = emit_summary(&asset);
        assert!(
            result.contains("FlipFlop(FlyEnabled) {"),
            "expected unquoted FlipFlop header, got:\n{}",
            result
        );
        assert!(
            result.contains("A|B: {"),
            "expected A|B block header, got:\n{}",
            result
        );
        assert!(
            result.contains("self.FlyEnabled = $FlyEnabled_IsA"),
            "expected consumer stmt inside A|B body, got:\n{}",
            result
        );
        // Drop the A:/B: label comment.
        assert!(
            !result.contains("// A:"),
            "expected no `// A:` comment, got:\n{}",
            result
        );
    }

    /// `names = None` falls back to the legacy `FlipFlop("<gate>") { ... }`
    /// form and emits the body verbatim (no `A|B:` wrapper).
    #[test]
    fn flipflop_unnamed_falls_back_to_quoted_gate_var() {
        let consumer = Stmt::Assignment {
            lhs: Expr::Var("temp".into()),
            rhs: Expr::Literal("0".into()),
            offset: 0,
        };
        let asset = flipflop_event_asset("Temp_bool_Variable", None, vec![consumer]);
        let result = emit_summary(&asset);
        assert!(
            result.contains("FlipFlop(\"Temp_bool_Variable\") {"),
            "expected legacy quoted-gate header, got:\n{}",
            result
        );
        assert!(
            !result.contains("A|B"),
            "unnamed FlipFlop should not emit A|B block, got:\n{}",
            result
        );
    }

    /// Distinct A/B labels render as `FlipFlop(A|B)`. Body-shape suppression
    /// of the `if (cond)` wrapper still applies.
    #[test]
    fn flipflop_distinct_labels_render_pair_form() {
        let inner_branch = Stmt::Branch {
            cond: Expr::Var("$gate".into()),
            then_body: vec![],
            else_body: vec![],
            offset: 0,
        };
        let asset = flipflop_event_asset(
            "Temp_bool_Variable",
            Some(("Foo", "Bar")),
            vec![inner_branch],
        );
        let result = emit_summary(&asset);
        assert!(
            result.contains("FlipFlop(Foo|Bar) {"),
            "expected pair-form header, got:\n{}",
            result
        );
    }
}
