//! Tests for `block`. Extracted from the production module so the
//! decoder dispatch stays focused; synthetic-byte-stream fixtures and
//! signature-driven OUT-arg coverage live here.

#[cfg(test)]
mod tests {
    use super::super::block::{decode_assignment, decode_call};
    use super::super::ctx::DecodeCtx;
    use super::super::expr_decode::{decode_expr, wrap_out_args};
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
            recv: Box::new(Expr::Literal(class.into())),
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

    #[test]
    fn output_wrapping_requires_exact_signature_and_is_idempotent() {
        let signatures = build_signature_map_with_out_param("ReadValue", 1, 2);
        let signature = signatures.get("ReadValue");
        let arguments = vec![Expr::Var("input".into()), Expr::Var("result".into())];
        let wrapped = wrap_out_args(arguments.clone(), signature);
        assert_eq!(wrapped[0], arguments[0]);
        assert_eq!(wrapped[1], Expr::Out(Box::new(arguments[1].clone())));
        assert_eq!(wrap_out_args(wrapped.clone(), signature), wrapped);
        assert_eq!(wrap_out_args(arguments.clone(), None), arguments);
        let expanded = vec![
            Expr::Var("first".into()),
            Expr::Var("second".into()),
            Expr::Var("third".into()),
        ];
        assert_eq!(wrap_out_args(expanded.clone(), signature), expanded);
    }

    #[test]
    fn imported_nested_call_uses_qualified_signature_before_shortening_name() {
        let imports = vec![
            crate::types::ImportEntry {
                class_package: "Synthetic".into(),
                class_name: "Class".into(),
                object_name: "Sensor".into(),
                outer_index: 0,
            },
            crate::types::ImportEntry {
                class_package: "Synthetic".into(),
                class_name: "Function".into(),
                object_name: "ReadValue".into(),
                outer_index: -1,
            },
        ];
        let mut signatures = build_signature_map_with_out_param("Sensor.ReadValue", 0, 1);
        signatures.insert(
            "ReadValue".into(),
            crate::types::FunctionSignature {
                params: vec![crate::types::ParamInfo {
                    name: "input".into(),
                    type_name: "object".into(),
                    flags: 0x80,
                }],
                return_type: None,
            },
        );
        let name_table = make_name_table(&["Consume", "Result"]);
        let mut stream = vec![EX_VIRTUAL_FUNCTION];
        put_fname(&mut stream, 0);
        stream.push(EX_FINAL_FUNCTION);
        put_i32(&mut stream, -2);
        stream.push(EX_LOCAL_VARIABLE);
        put_field_path(&mut stream, 1);
        stream.extend([EX_END_FUNCTION_PARMS, EX_END_FUNCTION_PARMS]);
        let context = DecodeCtx {
            function_signatures: Some(&signatures),
            ..make_ctx(&stream, &name_table, &imports, &[], 0)
        };
        let Expr::Call { args, .. } = decode_expr(&mut 0, &context) else {
            panic!("expected outer call")
        };
        let Expr::Call { name, args } = &args[0] else {
            panic!("expected imported inner call")
        };
        assert_eq!(name, "ReadValue");
        assert!(matches!(args[0], Expr::Out(_)));

        signatures.remove("Sensor.ReadValue");
        let context = DecodeCtx {
            function_signatures: Some(&signatures),
            ..make_ctx(&stream, &name_table, &imports, &[], 0)
        };
        let Expr::Call { args, .. } = decode_expr(&mut 0, &context) else {
            panic!("expected call")
        };
        let Expr::Call { args, .. } = &args[0] else {
            panic!("expected imported inner call")
        };
        assert!(
            !matches!(args[0], Expr::Out(_)),
            "unrelated local signature must not annotate imported call"
        );
    }
    #[test]
    fn ambiguous_virtual_signature_does_not_borrow_local_output_direction() {
        let mut signatures = build_signature_map_with_out_param("ReadValue", 0, 1);
        signatures.insert(
            "Sensor.ReadValue".into(),
            crate::types::FunctionSignature {
                params: vec![crate::types::ParamInfo {
                    name: "input".into(),
                    type_name: "object".into(),
                    flags: 0x80,
                }],
                return_type: None,
            },
        );
        let name_table = make_name_table(&["ReadValue", "Result"]);
        for (opcode, expected_out) in [
            (EX_VIRTUAL_FUNCTION, false),
            (EX_LOCAL_VIRTUAL_FUNCTION, true),
        ] {
            let mut stream = vec![opcode];
            put_fname(&mut stream, 0);
            stream.push(EX_LOCAL_VARIABLE);
            put_field_path(&mut stream, 1);
            stream.push(EX_END_FUNCTION_PARMS);
            let context = DecodeCtx {
                function_signatures: Some(&signatures),
                ..make_ctx(&stream, &name_table, &[], &[], 0)
            };
            let Expr::Call { args, .. } = decode_expr(&mut 0, &context) else {
                panic!("expected call")
            };
            assert_eq!(matches!(args[0], Expr::Out(_)), expected_out);
        }
    }
}
