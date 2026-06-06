//! Tests for `block`. Extracted from the production module so the
//! decoder dispatch stays focused; synthetic-byte-stream fixtures and
//! signature-driven OUT-arg coverage live here.

#[cfg(test)]
mod tests {
    use super::super::block::{decode_assignment, decode_call, wrap_out_args};
    use super::super::ctx::DecodeCtx;
    use crate::binary::NameTable;
    use crate::bytecode::expr::Expr;
    use crate::bytecode::opcodes::*;
    use crate::bytecode::stmt::Stmt;

    fn make_name_table(names: &[&str]) -> NameTable {
        NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
    }

    fn make_ctx<'a>(
        stream: &'a [u8],
        name_table: &'a NameTable,
        imports: &'a [crate::types::ImportEntry],
        export_names: &'a [String],
        ue5: i32,
    ) -> DecodeCtx<'a> {
        DecodeCtx::new(stream, name_table, imports, export_names, ue5)
    }

    use super::super::test_fixtures::{put_fname, put_i32};

    /// Build an `Expr::MethodCall` with a class-literal receiver.
    /// Mirrors what `decode_expr` produces from `EX_CONTEXT` over a
    /// resolved class object reference whose name lands in the
    /// static-library list.
    fn class_literal_methodcall(class: &str, name: &str, args: Vec<Expr>) -> Expr {
        Expr::MethodCall {
            recv: Box::new(Expr::Literal(class.to_string())),
            name: name.to_string(),
            args,
        }
    }

    /// Apply the same shape transformation `decode_call` performs
    /// after `decode_expr` returns. Mirrors the post-`decode_expr`
    /// match in `decode_call` so the canonical-shape rule is testable
    /// without re-encoding bytecode for the receiver.
    fn canonicalise_method_call(expr: Expr, offset: usize) -> Stmt {
        use crate::bytecode::transforms::lower_static_library_calls::is_static_library_class_literal;
        match expr {
            Expr::Call { name, args } => Stmt::Call {
                func: Expr::Var(name),
                args,
                offset,
            },
            Expr::MethodCall { recv, name, args } if is_static_library_class_literal(&recv) => {
                Stmt::Call {
                    func: Expr::Var(name),
                    args,
                    offset,
                }
            }
            Expr::MethodCall { recv, name, args } => Stmt::Call {
                func: Expr::FieldAccess { recv, field: name },
                args,
                offset,
            },
            other => Stmt::Call {
                func: other,
                args: vec![],
                offset,
            },
        }
    }

    #[test]
    fn static_library_methodcall_decodes_to_canonical_call() {
        // KismetArrayLibrary.Array_Length(arr) at statement level.
        let mc = class_literal_methodcall(
            "KismetArrayLibrary",
            "Array_Length",
            vec![Expr::Var("arr".into())],
        );
        let stmt = canonicalise_method_call(mc, 0);
        match stmt {
            Stmt::Call { func, args, .. } => {
                assert_eq!(func, Expr::Var("Array_Length".into()));
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected canonical Call"),
        }
    }

    #[test]
    fn instance_methodcall_keeps_field_access_shape() {
        // some_obj.Foo(x) is a real method call, must not collapse.
        let mc = Expr::MethodCall {
            recv: Box::new(Expr::Var("some_obj".into())),
            name: "Foo".into(),
            args: vec![Expr::Var("x".into())],
        };
        let stmt = canonicalise_method_call(mc, 0);
        match stmt {
            Stmt::Call { func, .. } => assert!(matches!(func, Expr::FieldAccess { .. })),
            _ => panic!("expected Stmt::Call with FieldAccess func"),
        }
    }

    use super::super::test_fixtures::put_field_path;

    #[test]
    fn assignment_with_local_out_lhs_keeps_out_wrapper() {
        // EX_LET <field-path> <EX_LOCAL_OUT_VARIABLE OutSlot> <EX_INT_CONST 7>
        // The lhs decodes to Expr::Out(Var("OutSlot")); decode_assignment
        // preserves the Out wrapper so downstream passes (dead_stmt,
        // single-use inlining) treat the slot as an ABI-significant
        // out-parameter write and keep the assignment alive.
        let name_table = make_name_table(&["OutSlot"]);
        let mut stream = vec![EX_LET];
        put_field_path(&mut stream, 0);
        stream.push(EX_LOCAL_OUT_VARIABLE);
        put_field_path(&mut stream, 0);
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 7);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let stmt = decode_assignment(&mut pos, &ctx);
        match stmt {
            Stmt::Assignment { lhs, rhs, .. } => {
                assert_eq!(lhs, Expr::Out(Box::new(Expr::Var("OutSlot".into()))));
                assert_eq!(rhs, Expr::Literal("7".into()));
            }
            _ => panic!("expected Stmt::Assignment"),
        }
    }

    #[test]
    fn end_to_end_decode_call_produces_canonical_shape() {
        // EX_VIRTUAL_FUNCTION as a top-level call (no EX_CONTEXT) yields
        // Expr::Call from decode_expr; decode_call wraps it as the
        // canonical Stmt::Call { func: Var(name), .. } shape.
        let name_table = make_name_table(&["Foo"]);
        let mut stream = vec![EX_VIRTUAL_FUNCTION];
        put_fname(&mut stream, 0);
        stream.push(EX_END_FUNCTION_PARMS);
        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let stmt = decode_call(&mut pos, &ctx);
        match stmt {
            Stmt::Call { func, .. } => match func {
                Expr::Var(name) => assert!(name.contains("Foo"), "name = {}", name),
                _ => panic!("expected Var func, got non-Var"),
            },
            _ => panic!("expected Stmt::Call"),
        }
    }

    fn build_signature_map_with_out_param(
        func_name: &str,
        out_position: usize,
        param_count: usize,
    ) -> std::collections::BTreeMap<String, crate::types::FunctionSignature> {
        const CPF_PARM: u64 = 0x80;
        const CPF_OUT_PARM: u64 = 0x100;
        let params: Vec<crate::types::ParamInfo> = (0..param_count)
            .map(|idx| {
                let mut flags = CPF_PARM;
                if idx == out_position {
                    flags |= CPF_OUT_PARM;
                }
                crate::types::ParamInfo {
                    name: format!("p{}", idx),
                    type_name: "int".into(),
                    flags,
                }
            })
            .collect();
        let mut map = std::collections::BTreeMap::new();
        map.insert(
            func_name.to_string(),
            crate::types::FunctionSignature {
                params,
                return_type: None,
            },
        );
        map
    }

    fn ctx_with_signatures<'a>(
        stream: &'a [u8],
        name_table: &'a NameTable,
        signatures: &'a std::collections::BTreeMap<String, crate::types::FunctionSignature>,
    ) -> DecodeCtx<'a> {
        DecodeCtx {
            function_signatures: Some(signatures),
            ..DecodeCtx::new(stream, name_table, &[], &[], 0)
        }
    }

    #[test]
    fn wrap_out_args_wraps_known_out_position() {
        let signatures = build_signature_map_with_out_param("MyFunc", 2, 3);
        let name_table = make_name_table(&[]);
        let stream: [u8; 0] = [];
        let ctx = ctx_with_signatures(&stream, &name_table, &signatures);
        let stmt = Stmt::Call {
            func: Expr::Var("MyFunc".into()),
            args: vec![
                Expr::Var("a".into()),
                Expr::Var("b".into()),
                Expr::Var("c".into()),
            ],
            offset: 0,
        };
        let wrapped = wrap_out_args(stmt, &ctx);
        let Stmt::Call { args, .. } = wrapped else {
            panic!("expected Stmt::Call");
        };
        assert_eq!(args[0], Expr::Var("a".into()));
        assert_eq!(args[1], Expr::Var("b".into()));
        assert_eq!(args[2], Expr::Out(Box::new(Expr::Var("c".into()))));
    }

    #[test]
    fn wrap_out_args_unknown_callee_passes_through() {
        let signatures: std::collections::BTreeMap<String, crate::types::FunctionSignature> =
            std::collections::BTreeMap::new();
        let name_table = make_name_table(&[]);
        let stream: [u8; 0] = [];
        let ctx = ctx_with_signatures(&stream, &name_table, &signatures);
        let stmt = Stmt::Call {
            func: Expr::Var("Unknown".into()),
            args: vec![Expr::Var("a".into()), Expr::Var("b".into())],
            offset: 0,
        };
        let wrapped = wrap_out_args(stmt, &ctx);
        let Stmt::Call { args, .. } = wrapped else {
            panic!("expected Stmt::Call");
        };
        assert_eq!(args[0], Expr::Var("a".into()));
        assert_eq!(args[1], Expr::Var("b".into()));
    }

    #[test]
    fn wrap_out_args_does_not_double_wrap() {
        let signatures = build_signature_map_with_out_param("MyFunc", 1, 2);
        let name_table = make_name_table(&[]);
        let stream: [u8; 0] = [];
        let ctx = ctx_with_signatures(&stream, &name_table, &signatures);
        // Pre-wrapped Out (e.g. from EX_LOCAL_OUT_VARIABLE on the caller side).
        let stmt = Stmt::Call {
            func: Expr::Var("MyFunc".into()),
            args: vec![
                Expr::Var("a".into()),
                Expr::Out(Box::new(Expr::Var("b".into()))),
            ],
            offset: 0,
        };
        let wrapped = wrap_out_args(stmt, &ctx);
        let Stmt::Call { args, .. } = wrapped else {
            panic!("expected Stmt::Call");
        };
        // Stays single-wrapped.
        assert_eq!(args[1], Expr::Out(Box::new(Expr::Var("b".into()))));
    }

    #[test]
    fn wrap_out_args_handles_args_longer_than_signature() {
        // Signature says 2 params, call passes 3. Extra args left alone.
        let signatures = build_signature_map_with_out_param("MyFunc", 1, 2);
        let name_table = make_name_table(&[]);
        let stream: [u8; 0] = [];
        let ctx = ctx_with_signatures(&stream, &name_table, &signatures);
        let stmt = Stmt::Call {
            func: Expr::Var("MyFunc".into()),
            args: vec![
                Expr::Var("a".into()),
                Expr::Var("b".into()),
                Expr::Var("extra".into()),
            ],
            offset: 0,
        };
        let wrapped = wrap_out_args(stmt, &ctx);
        let Stmt::Call { args, .. } = wrapped else {
            panic!("expected Stmt::Call");
        };
        assert_eq!(args[1], Expr::Out(Box::new(Expr::Var("b".into()))));
        assert_eq!(args[2], Expr::Var("extra".into()));
    }
}
