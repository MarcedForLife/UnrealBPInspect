//! Tests for `var_names`. Extracted from the production module so the
//! renamer stays focused on its passes; counter/struct rename fixtures
//! live here.

#[cfg(test)]
mod tests {
    use super::super::test_fixtures::{assign_expr as assign, lit, var};
    use super::super::var_names::{
        counter_name_at_depth, normalize_var_names, struct_short_name, UNKNOWN_TYPE_NAME,
    };
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::{LoopKind, Stmt, SwitchCase};

    fn forc_loop(counter: &str, body: Vec<Stmt>) -> Stmt {
        // ForC increment: counter = counter + 1
        let increment = vec![assign(
            var(counter),
            Expr::Binary {
                op: crate::bytecode::expr::BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
        )];
        Stmt::Loop {
            kind: LoopKind::ForC {
                init: vec![],
                increment,
            },
            cond: Some(Expr::Binary {
                op: crate::bytecode::expr::BinaryOp::Lt,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("10")),
            }),
            body,
            completion: None,
            offset: 0,
        }
    }

    // Counter-var renaming.

    #[test]
    fn counter_rename_depth_0_gets_i() {
        let counter = "Temp_int_var_3";
        let inner = assign(var("Out"), var(counter));
        let mut body = vec![forc_loop(counter, vec![inner])];
        normalize_var_names(&mut body);

        // The loop body should reference "i" now, not "Temp_int_var_3".
        let Stmt::Loop {
            body: loop_body,
            cond,
            kind: LoopKind::ForC { increment, .. },
            ..
        } = &body[0]
        else {
            panic!("expected ForC loop");
        };
        // cond should use "i"
        let Expr::Binary { lhs, .. } = cond.as_ref().unwrap() else {
            panic!("expected binary cond");
        };
        assert_eq!(*lhs.as_ref(), var("i"), "cond lhs should be 'i'");
        // increment should use "i"
        let Stmt::Assignment { lhs: inc_lhs, .. } = &increment[0] else {
            panic!("expected assignment in increment");
        };
        assert_eq!(*inc_lhs, var("i"), "increment lhs should be 'i'");
        // body should use "i"
        let Stmt::Assignment { rhs: body_rhs, .. } = &loop_body[0] else {
            panic!("expected assignment in body");
        };
        assert_eq!(*body_rhs, var("i"), "body rhs should be 'i'");
    }

    #[test]
    fn counter_rename_nested_gets_j() {
        let outer_counter = "Temp_int_var_1";
        let inner_counter = "Temp_int_var_2";
        let inner_loop = forc_loop(inner_counter, vec![assign(var("X"), var(inner_counter))]);
        let mut body = vec![forc_loop(outer_counter, vec![inner_loop])];
        normalize_var_names(&mut body);

        let Stmt::Loop {
            body: outer_body, ..
        } = &body[0]
        else {
            panic!("expected outer ForC loop");
        };
        let Stmt::Loop {
            body: inner_body, ..
        } = &outer_body[0]
        else {
            panic!("expected inner ForC loop");
        };
        // inner loop body should use "j"
        let Stmt::Assignment { rhs, .. } = &inner_body[0] else {
            panic!("expected assignment in inner body");
        };
        assert_eq!(*rhs, var("j"), "inner counter should be 'j'");
    }

    #[test]
    fn non_temp_int_counter_not_renamed() {
        // If the increment var does not start with TEMP_INT_PREFIX, leave it alone.
        let counter = "MyCounter";
        let inner = assign(var("Out"), var(counter));
        let mut body = vec![forc_loop(counter, vec![inner])];
        normalize_var_names(&mut body);

        let Stmt::Loop {
            body: loop_body, ..
        } = &body[0]
        else {
            panic!("expected ForC loop");
        };
        let Stmt::Assignment { rhs, .. } = &loop_body[0] else {
            panic!("expected assignment in body");
        };
        assert_eq!(
            *rhs,
            var("MyCounter"),
            "non-temp counter should not be renamed"
        );
    }

    // Struct-temp renaming.

    /// Drives single-temp struct renaming across (lhs, type_name)
    /// permutations. The struct-init stmt is the only body statement;
    /// the test asserts on the renamed (or preserved) lhs after pass.
    #[test]
    fn struct_temp_single_rename_cases() {
        struct Case {
            label: &'static str,
            old_name: &'static str,
            type_name: String,
            expected_name: &'static str,
        }
        let cases = vec![
            Case {
                label: "renamed_from_fvector",
                old_name: "Temp_struct_var_5",
                type_name: "FVector".to_string(),
                expected_name: "Vector",
            },
            Case {
                label: "unknown_type_not_renamed",
                old_name: "Temp_struct_var_2",
                type_name: UNKNOWN_TYPE_NAME.to_string(),
                expected_name: "Temp_struct_var_2",
            },
            Case {
                label: "no_f_prefix_used_as_is",
                old_name: "Temp_struct_var_0",
                type_name: "LinearColor".to_string(),
                expected_name: "LinearColor",
            },
            Case {
                label: "non_temp_lhs_not_renamed",
                old_name: "MyStruct",
                type_name: "FVector".to_string(),
                expected_name: "MyStruct",
            },
        ];
        for case in cases {
            let struct_init = assign(
                var(case.old_name),
                Expr::StructConstruct {
                    type_name: case.type_name.clone(),
                    fields: vec![],
                },
            );
            let mut body = vec![struct_init];
            normalize_var_names(&mut body);

            let Stmt::Assignment { lhs, .. } = &body[0] else {
                panic!("case {}: expected assignment", case.label);
            };
            assert_eq!(
                *lhs,
                var(case.expected_name),
                "case {}: lhs after rename",
                case.label,
            );
        }
    }

    #[test]
    fn struct_temp_rename_propagates_to_use_site() {
        // Two-stmt body: the renamer must update both the init lhs and
        // the use-site rhs that references the same temp.
        let old_name = "Temp_struct_var_5";
        let struct_init = assign(
            var(old_name),
            Expr::StructConstruct {
                type_name: "FVector".to_string(),
                fields: vec![],
            },
        );
        let use_stmt = assign(var("Out"), var(old_name));
        let mut body = vec![struct_init, use_stmt];
        normalize_var_names(&mut body);

        let Stmt::Assignment { lhs, .. } = &body[0] else {
            panic!("expected assignment");
        };
        assert_eq!(*lhs, var("Vector"), "init lhs should be renamed");
        let Stmt::Assignment { rhs, .. } = &body[1] else {
            panic!("expected assignment");
        };
        assert_eq!(*rhs, var("Vector"), "use site should be renamed");
    }

    #[test]
    fn two_struct_temps_same_type_get_suffixed() {
        let name1 = "Temp_struct_var_0";
        let name2 = "Temp_struct_var_1";
        let stmt1 = assign(
            var(name1),
            Expr::StructConstruct {
                type_name: "FVector".to_string(),
                fields: vec![],
            },
        );
        let stmt2 = assign(
            var(name2),
            Expr::StructConstruct {
                type_name: "FVector".to_string(),
                fields: vec![],
            },
        );
        let use1 = assign(var("A"), var(name1));
        let use2 = assign(var("B"), var(name2));
        let mut body = vec![stmt1, stmt2, use1, use2];
        normalize_var_names(&mut body);

        // First gets "Vector", second gets "Vector_1".
        let Stmt::Assignment { lhs: lhs1, .. } = &body[0] else {
            panic!()
        };
        let Stmt::Assignment { lhs: lhs2, .. } = &body[1] else {
            panic!()
        };
        assert_eq!(*lhs1, var("Vector"));
        assert_eq!(*lhs2, var("Vector_1"));
    }

    #[test]
    fn counter_name_at_depth_beyond_k() {
        assert_eq!(counter_name_at_depth(0), "i");
        assert_eq!(counter_name_at_depth(1), "j");
        assert_eq!(counter_name_at_depth(2), "k");
        assert_eq!(counter_name_at_depth(3), "loop_3");
        assert_eq!(counter_name_at_depth(10), "loop_10");
    }

    #[test]
    fn struct_short_name_strips_f_prefix() {
        assert_eq!(struct_short_name("FVector"), Some("Vector".to_string()));
        assert_eq!(struct_short_name("FRotator"), Some("Rotator".to_string()));
        assert_eq!(
            struct_short_name("FTransform"),
            Some("Transform".to_string())
        );
        // 'F' not followed by uppercase: keep as-is.
        assert_eq!(struct_short_name("Ffoo"), Some("Ffoo".to_string()));
        // No F prefix: keep as-is.
        assert_eq!(
            struct_short_name("LinearColor"),
            Some("LinearColor".to_string())
        );
        // Unknown placeholder: None.
        assert_eq!(struct_short_name(UNKNOWN_TYPE_NAME), None);
        assert_eq!(struct_short_name(""), None);
    }

    #[test]
    fn switch_case_bodies_normalized() {
        let counter = "Temp_int_var_7";
        let loop_in_case = forc_loop(counter, vec![assign(var("Out"), var(counter))]);
        let mut body = vec![Stmt::Switch {
            expr: lit("0"),
            cases: vec![SwitchCase {
                values: vec![lit("0")],
                body: vec![loop_in_case],
            }],
            default: None,
            offset: 0,
        }];
        normalize_var_names(&mut body);

        let Stmt::Switch { cases, .. } = &body[0] else {
            panic!("expected switch");
        };
        let Stmt::Loop {
            body: loop_body, ..
        } = &cases[0].body[0]
        else {
            panic!("expected ForC loop in case");
        };
        let Stmt::Assignment { rhs, .. } = &loop_body[0] else {
            panic!("expected assignment in loop body");
        };
        assert_eq!(*rhs, var("i"), "counter in switch case body should be 'i'");
    }
}
