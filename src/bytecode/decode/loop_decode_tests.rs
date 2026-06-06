//! Tests for `loop_decode`. Extracted from the production module so the
//! decoder file stays focused on the back-edge fast-path.

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::super::loop_decode::try_decode_loop;
    use super::super::test_fixtures::{empty_name_table, identity_map, stmt_kind, u32_le, ue4_ctx};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::opcodes::*;
    use crate::bytecode::stmt::{LoopKind, Stmt};
    use crate::bytecode::transforms::refine_loops::refine_loops;

    /// Drive the production `refine_loops` pass over a synthetic
    /// `Loop { While, cond, body+increment }` and return the refined
    /// `(kind, cond)` plus the leftover body. Lets test cases that used
    /// the old in-file `refine_foreach` shadow exercise the same shape
    /// against the real production matcher.
    fn refine_via_production(
        cond: Expr,
        increment: Vec<Stmt>,
        mut body: Vec<Stmt>,
    ) -> (LoopKind, Option<Expr>, Vec<Stmt>) {
        body.extend(increment);
        let mut stmts = vec![Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(cond),
            body,
            completion: None,
            offset: 0,
        }];
        refine_loops(&mut stmts);
        let Some(Stmt::Loop {
            kind,
            cond,
            body: refined_body,
            ..
        }) = stmts.into_iter().next()
        else {
            panic!("expected a Stmt::Loop after refinement");
        };
        (kind, cond, refined_body)
    }

    /// Build a synthetic While loop:
    ///   0x00 EX_JUMP_IF_NOT target=0x0C
    ///   0x01..0x05 target operand
    ///   0x05 EX_NOTHING       (cond expression placeholder)
    ///   0x06 EX_NOTHING       (body, single statement)
    ///   0x07 EX_JUMP target=0x00
    ///   0x08..0x0C target operand
    ///   0x0C EX_NOTHING       (post-loop landing)
    ///   0x0D EX_END_OF_SCRIPT
    fn while_loop_stream() -> (Vec<u8>, BTreeMap<usize, usize>) {
        let mut stream = Vec::new();
        stream.push(EX_JUMP_IF_NOT);
        stream.extend_from_slice(&u32_le(0x0C));
        stream.push(EX_NOTHING); // cond
        stream.push(EX_NOTHING); // body
        stream.push(EX_JUMP);
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_NOTHING); // post-loop
        stream.push(EX_END_OF_SCRIPT);

        let map = identity_map(&[0, 5, 6, 7, 0x0C, 0x0D]);
        (stream, map)
    }

    #[test]
    fn while_loop_decodes_with_no_increment() {
        let (stream, map) = while_loop_stream();
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected Stmt::Loop");
        match stmt {
            Stmt::Loop {
                kind, completion, ..
            } => {
                assert!(matches!(kind, LoopKind::While), "expected While");
                assert!(completion.is_none());
            }
            other => panic!("expected Stmt::Loop, got {}", stmt_kind(&other)),
        }
        // pos should land past the back-edge jump (5 bytes for jump),
        // i.e. at 0x0C.
        assert_eq!(pos, 0x0C);
    }

    /// A While loop whose body ends with a `Counter = Counter + 1`
    /// assignment refines to `LoopKind::ForC` with the increment
    /// drained out of the body, given a cond that references `Counter`.
    /// Mirrors the trailing-assignment discriminator that production
    /// `refine_loops` uses.
    #[test]
    fn forc_drains_trailing_counter_assignment() {
        let counter = "Counter";
        let increment_stmt = Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Binary {
                op: crate::bytecode::expr::BinaryOp::Add,
                lhs: Box::new(Expr::Var(counter.into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0x10,
        };
        let body_stmt = Stmt::Call {
            func: Expr::Var("Body".into()),
            args: vec![],
            offset: 0x05,
        };
        let cond = Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Literal("10".into())),
        };

        let (kind, cond_after, body_after) =
            refine_via_production(cond, vec![], vec![body_stmt, increment_stmt]);

        let LoopKind::ForC { increment, .. } = kind else {
            panic!("expected ForC after refinement");
        };
        assert_eq!(increment.len(), 1);
        assert!(matches!(increment[0], Stmt::Assignment { .. }));
        assert_eq!(
            body_after.len(),
            1,
            "body should retain the non-increment stmt"
        );
        assert!(cond_after.is_some(), "ForC cond must be preserved");
    }

    /// A While loop whose trailing body assignment doesn't appear in
    /// the cond stays a While. The unrelated assignment stays in body.
    #[test]
    fn while_skips_unrelated_trailing_assignment() {
        let unrelated = Stmt::Assignment {
            lhs: Expr::Var("Other".into()),
            rhs: Expr::Literal("1".into()),
            offset: 0x10,
        };
        let cond = Expr::Var("Counter".into());

        let (kind, _, body_after) = refine_via_production(cond, vec![], vec![unrelated]);

        assert!(matches!(kind, LoopKind::While), "should stay While");
        assert_eq!(body_after.len(), 1, "body must be unchanged");
    }

    /// A conditional with no back-edge in its body should NOT be
    /// recognised as a loop. The classic if/else dispatch handles it.
    ///
    ///   0x00 EX_JUMP_IF_NOT target=0x07
    ///   0x05 EX_NOTHING   (cond)
    ///   0x06 EX_NOTHING   (then-body, falls through)
    ///   0x07 EX_NOTHING   (else target / post)
    ///   0x08 EX_END_OF_SCRIPT
    #[test]
    fn branch_without_back_edge_is_not_loop() {
        let mut stream = vec![EX_JUMP_IF_NOT];
        stream.extend_from_slice(&u32_le(0x07));
        stream.push(EX_NOTHING); // cond
        stream.push(EX_NOTHING); // then-body
        stream.push(EX_NOTHING); // post
        stream.push(EX_END_OF_SCRIPT);

        let map = identity_map(&[0, 5, 6, 7, 8]);
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let result = try_decode_loop(&mut pos, stream.len(), &ctx);
        assert!(result.is_none(), "no back-edge -> not a loop");
        assert_eq!(pos, 0, "pos must be unchanged on non-match");
    }

    /// A loop whose body contains an inner `EX_JUMP` to a forward
    /// target (e.g. a break-like pattern) should still match on the
    /// final back-edge, not on the inner forward jump.
    #[test]
    fn loop_with_inner_forward_jump_picks_back_edge() {
        // Layout:
        //   0x00 EX_JUMP_IF_NOT target=0x12
        //   0x05 EX_NOTHING       (cond)
        //   0x06 EX_NOTHING       (body 1)
        //   0x07 EX_JUMP target=0x12  (forward break)
        //   0x0C EX_NOTHING       (body 2, after break path)
        //   0x0D EX_JUMP target=0x00 (back-edge)
        //   0x12 EX_NOTHING       (post-loop)
        //   0x13 EX_END_OF_SCRIPT
        let mut stream = vec![EX_JUMP_IF_NOT];
        stream.extend_from_slice(&u32_le(0x12));
        stream.push(EX_NOTHING); // cond
        stream.push(EX_NOTHING); // body 1
        stream.push(EX_JUMP);
        stream.extend_from_slice(&u32_le(0x12));
        stream.push(EX_NOTHING); // body 2
        stream.push(EX_JUMP);
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_NOTHING); // post-loop
        stream.push(EX_END_OF_SCRIPT);

        let map = identity_map(&[0, 5, 6, 7, 0x0C, 0x0D, 0x12, 0x13]);
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected loop");
        assert!(matches!(stmt, Stmt::Loop { .. }));
        // pos lands past the back-edge at 0x0D + 5 = 0x12.
        assert_eq!(pos, 0x12);
    }

    // ForEach refinement helpers and tests.

    fn counter_lt_array_length_cond(counter: &str, array: Expr) -> Expr {
        Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Call {
                name: "Array_Length".into(),
                args: vec![array],
            }),
        }
    }

    fn counter_increment_stmt(counter: &str) -> Stmt {
        Stmt::Assignment {
            lhs: Expr::Var(counter.into()),
            rhs: Expr::Binary {
                op: crate::bytecode::expr::BinaryOp::Add,
                lhs: Box::new(Expr::Var(counter.into())),
                rhs: Box::new(Expr::Literal("1".into())),
            },
            offset: 0x40,
        }
    }

    /// Synthetic ForC body that matches the canonical ForEach pattern.
    /// Body has `Item = Array[Counter]; DoWork(Item);`. After production
    /// refinement, the loop is `LoopKind::ForEach { item: "Item", array:
    /// Var("Items") }` with the index-fetch line dropped.
    #[test]
    fn foreach_recognises_canonical_pattern() {
        let counter = "Counter";
        let array_expr = Expr::Var("Items".into());
        let cond = counter_lt_array_length_cond(counter, array_expr.clone());
        let increment = vec![counter_increment_stmt(counter)];
        let body = vec![
            Stmt::Assignment {
                lhs: Expr::Var("Item".into()),
                rhs: Expr::Index {
                    recv: Box::new(array_expr.clone()),
                    idx: Box::new(Expr::Var(counter.into())),
                },
                offset: 0x10,
            },
            Stmt::Call {
                func: Expr::Var("DoWork".into()),
                args: vec![Expr::Var("Item".into())],
                offset: 0x20,
            },
        ];

        let (kind, cond_after, body_after) = refine_via_production(cond, increment, body);
        match kind {
            LoopKind::ForEach { item, array } => {
                assert_eq!(item, "Item");
                assert!(matches!(array, Expr::Var(name) if name == "Items"));
            }
            other => panic!("expected ForEach, got {:?}", std::mem::discriminant(&other)),
        }
        assert!(cond_after.is_none(), "ForEach cond must be implicit");
        assert_eq!(body_after.len(), 1, "fetch line should be dropped");
        assert!(matches!(body_after[0], Stmt::Call { .. }));
    }

    /// ForEach via `Array_Get` stdlib call instead of an Index opcode.
    /// Same outcome: refinement to ForEach with the fetch dropped.
    #[test]
    fn foreach_recognises_array_get_call() {
        let counter = "Counter";
        let array_expr = Expr::Var("Targets".into());
        let cond = counter_lt_array_length_cond(counter, array_expr.clone());
        let increment = vec![counter_increment_stmt(counter)];
        let body = vec![Stmt::Assignment {
            lhs: Expr::Var("Target".into()),
            rhs: Expr::Call {
                name: "Array_Get".into(),
                args: vec![array_expr.clone(), Expr::Var(counter.into())],
            },
            offset: 0x10,
        }];

        let (kind, _, _) = refine_via_production(cond, increment, body);
        assert!(matches!(kind, LoopKind::ForEach { .. }));
    }

    /// A ForC that does NOT match the canonical pattern (cond is a
    /// counter limit, not Array_Length) should stay a ForC.
    #[test]
    fn foreach_leaves_unrelated_forc_alone() {
        let counter = "Counter";
        let cond = Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Literal("10".into())),
        };
        let increment = vec![counter_increment_stmt(counter)];
        let body = vec![Stmt::Call {
            func: Expr::Var("Tick".into()),
            args: vec![],
            offset: 0x10,
        }];

        let (kind, cond_after, _) = refine_via_production(cond, increment, body);
        assert!(matches!(kind, LoopKind::ForC { .. }));
        assert!(cond_after.is_some(), "ForC cond must be preserved");
    }

    /// Index-mirror line (`Temp_int_0 = Counter`) preceding the fetch
    /// should be dropped together with the fetch when the loop refines
    /// to ForEach.
    #[test]
    fn foreach_drops_index_mirror_line() {
        let counter = "Counter";
        let array_expr = Expr::Var("Items".into());
        let cond = counter_lt_array_length_cond(counter, array_expr.clone());
        let increment = vec![counter_increment_stmt(counter)];
        let body = vec![
            // Index-mirror: Temp_int_0 = Counter
            Stmt::Assignment {
                lhs: Expr::Var("Temp_int_0".into()),
                rhs: Expr::Var(counter.into()),
                offset: 0x08,
            },
            Stmt::Assignment {
                lhs: Expr::Var("Item".into()),
                rhs: Expr::Index {
                    recv: Box::new(array_expr.clone()),
                    idx: Box::new(Expr::Var(counter.into())),
                },
                offset: 0x10,
            },
            Stmt::Call {
                func: Expr::Var("DoWork".into()),
                args: vec![],
                offset: 0x20,
            },
        ];

        let (kind, _, body_after) = refine_via_production(cond, increment, body);
        assert!(matches!(kind, LoopKind::ForEach { .. }));
        assert_eq!(
            body_after.len(),
            1,
            "index-mirror and fetch lines should both be dropped"
        );
        assert!(matches!(body_after[0], Stmt::Call { .. }));
    }

    /// Synthetic ForEach trampoline shape: header + jump_if_not,
    /// push_flow + jump past back-edge, increment, back-edge,
    /// completion, displaced block ending with pop_flow.
    /// Verifies the decoder splices the displaced block into the body
    /// and routes the post-back-edge range into completion.
    fn foreach_trampoline_stream() -> (Vec<u8>, BTreeMap<usize, usize>) {
        // Layout (mem == disk for this synthetic stream):
        //   0x00 EX_JUMP_IF_NOT skip=0x21    (loop head)
        //   0x05 EX_NOTHING                  (cond)
        //   0x06 EX_NOTHING                  (in-body content before push)
        //   0x07 EX_PUSH_EXECUTION_FLOW resume=0x11   (5 bytes)
        //   0x0c EX_JUMP target=0x22         (5 bytes, displaced jump)
        //   0x11 EX_NOTHING                  (increment placeholder)
        //   0x12 EX_NOTHING                  (more increment)
        //   0x13 EX_NOTHING                  (more increment)
        //   ...padding to 0x1c
        //   0x1c EX_JUMP back=0x00           (back-edge, ends at 0x21)
        //   0x21 EX_NOTHING                  (completion content, post back-edge)
        //   0x22 EX_NOTHING                  (displaced body content)
        //   0x23 EX_POP_EXECUTION_FLOW       (1 byte; pop_flow ends displaced)
        //   0x24 EX_END_OF_SCRIPT
        let mut stream = Vec::new();
        stream.push(EX_JUMP_IF_NOT); // 0x00
        stream.extend_from_slice(&u32_le(0x21)); // skip target -> resume after back-edge
        stream.push(EX_NOTHING); // 0x05 cond
        stream.push(EX_NOTHING); // 0x06 pre-trampoline body
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x07
        stream.extend_from_slice(&u32_le(0x11)); // resume = byte after the EX_JUMP at 0x0c
        stream.push(EX_JUMP); // 0x0c
        stream.extend_from_slice(&u32_le(0x22)); // displaced target
        stream.push(EX_NOTHING); // 0x11 increment 1
        stream.push(EX_NOTHING); // 0x12 increment 2
        stream.push(EX_NOTHING); // 0x13
        stream.push(EX_NOTHING); // 0x14
        stream.push(EX_NOTHING); // 0x15
        stream.push(EX_NOTHING); // 0x16
        stream.push(EX_NOTHING); // 0x17
        stream.push(EX_NOTHING); // 0x18
        stream.push(EX_NOTHING); // 0x19
        stream.push(EX_NOTHING); // 0x1a
        stream.push(EX_NOTHING); // 0x1b
        stream.push(EX_JUMP); // 0x1c back-edge
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_NOTHING); // 0x21 completion
        stream.push(EX_NOTHING); // 0x22 displaced body content
        stream.push(EX_POP_EXECUTION_FLOW); // 0x23 displaced terminator
        stream.push(EX_END_OF_SCRIPT); // 0x24
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        (stream, identity_map(&boundaries))
    }

    #[test]
    fn foreach_trampoline_absorbs_displaced_body() {
        let (stream, map) = foreach_trampoline_stream();
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected Stmt::Loop");
        match stmt {
            Stmt::Loop {
                kind,
                body,
                completion,
                ..
            } => {
                assert!(
                    matches!(kind, LoopKind::While),
                    "decoder emits While; ForEach refinement runs later"
                );
                assert!(
                    !body.is_empty(),
                    "absorbed body should contain decoded statements"
                );
                assert!(
                    completion.is_some(),
                    "completion range [back_edge_end..displaced_start) should populate"
                );
            }
            other => panic!("expected Stmt::Loop, got {}", stmt_kind(&other)),
        }
        // pos lands past the back-edge jump (0x1c + 5 = 0x21).
        assert_eq!(pos, 0x21);
    }

    /// A loop containing a push_flow that is NOT a trampoline (no
    /// matching jump-past-back-edge) must NOT trigger absorption. The
    /// existing While behaviour stays intact.
    #[test]
    fn loop_with_inner_sequence_push_does_not_absorb() {
        // Layout:
        //   0x00 EX_JUMP_IF_NOT skip=0x12
        //   0x05 EX_NOTHING                  cond
        //   0x06 EX_PUSH_EXECUTION_FLOW resume=0x0c (Sequence-style push)
        //   0x0b EX_NOTHING                  inline body
        //   0x0c EX_POP_EXECUTION_FLOW       Sequence pop, NOT a trampoline
        //   0x0d EX_JUMP back=0x00
        //   0x12 EX_END_OF_SCRIPT
        let mut stream = vec![EX_JUMP_IF_NOT];
        stream.extend_from_slice(&u32_le(0x12));
        stream.push(EX_NOTHING); // 0x05 cond
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x06
        stream.extend_from_slice(&u32_le(0x0c)); // resume target inside body
        stream.push(EX_NOTHING); // 0x0b body
        stream.push(EX_POP_EXECUTION_FLOW); // 0x0c
        stream.push(EX_JUMP); // 0x0d
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_END_OF_SCRIPT); // 0x12
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected Stmt::Loop");
        match stmt {
            Stmt::Loop { completion, .. } => {
                assert!(
                    completion.is_none(),
                    "non-trampoline push must not produce a completion block"
                );
            }
            other => panic!("expected Stmt::Loop, got {}", stmt_kind(&other)),
        }
    }

    /// Break-with-flag ForEach trampoline: the displaced block has no
    /// inner `EX_POP_EXECUTION_FLOW` and terminates via the function
    /// epilogue's `EX_RETURN`. Resume target is canonical (after_jump)
    /// here; the discriminator is the missing inner pop.
    fn breakflag_trampoline_stream() -> (Vec<u8>, BTreeMap<usize, usize>) {
        // Layout (mem == disk):
        //   0x00 EX_JUMP_IF_NOT skip=0x21
        //   0x05 EX_NOTHING                  cond
        //   0x06 EX_NOTHING                  pre-trampoline body
        //   0x07 EX_PUSH_EXECUTION_FLOW resume=0x11   (canonical)
        //   0x0c EX_JUMP target=0x22                  (displaced)
        //   0x11..0x1c EX_NOTHING padding (increment range)
        //   0x1c EX_JUMP back=0x00                    (back-edge)
        //   0x21 EX_NOTHING                           (completion)
        //   0x22 EX_NOTHING                           (displaced body content)
        //   0x23 EX_NOTHING                           (more body, no inner pop)
        //   0x24 EX_RETURN                            (function epilogue terminates displaced)
        //   0x25 EX_END_OF_SCRIPT
        let mut stream = Vec::new();
        stream.push(EX_JUMP_IF_NOT); // 0x00
        stream.extend_from_slice(&u32_le(0x21));
        stream.push(EX_NOTHING); // 0x05 cond
        stream.push(EX_NOTHING); // 0x06 pre-trampoline
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x07
        stream.extend_from_slice(&u32_le(0x11));
        stream.push(EX_JUMP); // 0x0c
        stream.extend_from_slice(&u32_le(0x22));
        stream.extend(std::iter::repeat_n(EX_NOTHING, 0x1c - 0x11));
        stream.push(EX_JUMP); // 0x1c back-edge
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_NOTHING); // 0x21 completion
        stream.push(EX_NOTHING); // 0x22 displaced body
        stream.push(EX_NOTHING); // 0x23 displaced body
        stream.push(EX_RETURN); // 0x24 epilogue terminator
        stream.push(EX_END_OF_SCRIPT); // 0x25
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        (stream, identity_map(&boundaries))
    }

    #[test]
    fn breakflag_trampoline_absorbs_via_return_terminator() {
        let (stream, map) = breakflag_trampoline_stream();
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected Stmt::Loop");
        match stmt {
            Stmt::Loop {
                kind,
                body,
                completion,
                ..
            } => {
                assert!(
                    matches!(kind, LoopKind::While),
                    "decoder emits While; ForEach refinement runs later"
                );
                assert!(
                    !body.is_empty(),
                    "absorbed body should contain decoded statements"
                );
                assert!(
                    completion.is_some(),
                    "completion range should populate when displaced block lies past back-edge"
                );
            }
            other => panic!("expected Stmt::Loop, got {}", stmt_kind(&other)),
        }
        assert_eq!(pos, 0x21);
    }

    /// A trampoline whose push.resume target lies past the back-edge
    /// (neither at the increment nor at/before the loop head) must NOT
    /// trigger absorption. Guards against absorbing non-foreach
    /// patterns whose resume target falls outside the foreach windows.
    #[test]
    fn far_resume_rejects_absorption() {
        // Layout (mem == disk):
        //   0x00 EX_JUMP_IF_NOT skip=0x21
        //   0x05 EX_NOTHING                  cond
        //   0x06 EX_NOTHING                  pre-trampoline
        //   0x07 EX_PUSH_EXECUTION_FLOW resume=0x24  (FAR past back-edge)
        //   0x0c EX_JUMP target=0x22         (displaced)
        //   0x11..0x1c EX_NOTHING padding
        //   0x1c EX_JUMP back=0x00
        //   0x21 EX_NOTHING                  (completion)
        //   0x22 EX_NOTHING                  (displaced body)
        //   0x23 EX_POP_EXECUTION_FLOW       (inner pop present)
        //   0x24 EX_END_OF_SCRIPT
        let mut stream = Vec::new();
        stream.push(EX_JUMP_IF_NOT);
        stream.extend_from_slice(&u32_le(0x21));
        stream.push(EX_NOTHING); // 0x05
        stream.push(EX_NOTHING); // 0x06
        stream.push(EX_PUSH_EXECUTION_FLOW); // 0x07
        stream.extend_from_slice(&u32_le(0x24)); // resume far past back-edge
        stream.push(EX_JUMP); // 0x0c
        stream.extend_from_slice(&u32_le(0x22));
        stream.extend(std::iter::repeat_n(EX_NOTHING, 0x1c - 0x11));
        stream.push(EX_JUMP); // 0x1c back-edge
        stream.extend_from_slice(&u32_le(0x00));
        stream.push(EX_NOTHING); // 0x21
        stream.push(EX_NOTHING); // 0x22
        stream.push(EX_POP_EXECUTION_FLOW); // 0x23
        stream.push(EX_END_OF_SCRIPT); // 0x24
        let boundaries: Vec<usize> = (0..=stream.len()).collect();
        let map = identity_map(&boundaries);
        let names = empty_name_table();
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_loop(&mut pos, stream.len(), &ctx).expect("expected Stmt::Loop");
        match stmt {
            Stmt::Loop { completion, .. } => {
                assert!(
                    completion.is_none(),
                    "far-resume trampoline must not produce a completion block"
                );
            }
            other => panic!("expected Stmt::Loop, got {}", stmt_kind(&other)),
        }
    }

    /// Round-trip check: after absorption, the post-inline ForEach
    /// matcher in `transforms::refine_loops` can locate an
    /// `Item = Array[Counter]` index-fetch in the body produced by the
    /// synthetic trampoline.
    #[test]
    fn absorbed_body_carries_index_fetch_for_refinement() {
        let counter = "Counter";
        let array_expr = Expr::Var("Items".into());
        let body = vec![
            Stmt::Assignment {
                lhs: Expr::Var("Item".into()),
                rhs: Expr::Index {
                    recv: Box::new(array_expr.clone()),
                    idx: Box::new(Expr::Var(counter.into())),
                },
                offset: 0x10,
            },
            Stmt::Call {
                func: Expr::Var("DoWork".into()),
                args: vec![Expr::Var("Item".into())],
                offset: 0x20,
            },
        ];
        let cond = Expr::Binary {
            op: crate::bytecode::expr::BinaryOp::Lt,
            lhs: Box::new(Expr::Var(counter.into())),
            rhs: Box::new(Expr::Call {
                name: "Array_Length".into(),
                args: vec![array_expr.clone()],
            }),
        };
        let increment = vec![counter_increment_stmt(counter)];

        let (kind, _, _) = refine_via_production(cond, increment, body);
        assert!(
            matches!(kind, LoopKind::ForEach { .. }),
            "absorbed body should activate ForEach refinement"
        );
    }
}
