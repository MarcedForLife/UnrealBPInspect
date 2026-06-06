//! Tests for `decode/cascade_decode.rs`. Extracted from the production
//! module so the switch-dispatch recognizer stays focused on its
//! decoding logic; the synthetic opcode-stream fixtures live here.

use super::cascade_decode::*;
use crate::binary::NameTable;
use crate::bytecode::decode::test_fixtures::{
    empty_name_table, identity_map, stmt_kind, u32_le, ue4_ctx, ue4_ctx_with_exports,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::stmt::Stmt;

/// Append an `EX_INT_CONST <value>` (5 bytes total).
fn push_int_const(stream: &mut Vec<u8>, value: i32) {
    stream.push(EX_INT_CONST);
    stream.extend_from_slice(&value.to_le_bytes());
}

/// Append a 13-byte `EX_LOCAL_VARIABLE` referencing the named field
/// at `name_idx` in the test name table. Layout:
/// `EX_LOCAL_VARIABLE(1) + path_num=1(4) + FName(8) + owner=0(4)`.
fn push_local_var(stream: &mut Vec<u8>, name_idx: i32) {
    stream.push(EX_LOCAL_VARIABLE);
    stream.extend_from_slice(&1i32.to_le_bytes()); // path_num
    stream.extend_from_slice(&name_idx.to_le_bytes()); // FName.idx
    stream.extend_from_slice(&0i32.to_le_bytes()); // FName.instance
    stream.extend_from_slice(&0i32.to_le_bytes()); // owner
}

/// Append an `EX_CALL_MATH` whose object index is `export_idx`
/// (positive 1-based index into the synthetic `export_names` table).
/// Bytes: `EX_CALL_MATH(1) + i32 export_idx(4) + arg_bytes +
/// EX_END_FUNCTION_PARMS(1)`.
fn push_callmath(stream: &mut Vec<u8>, export_idx: i32, arg_bytes: &[u8]) {
    stream.push(EX_CALL_MATH);
    stream.extend_from_slice(&export_idx.to_le_bytes());
    stream.extend_from_slice(arg_bytes);
    stream.push(EX_END_FUNCTION_PARMS);
}

/// Build the args portion of a NotEqual_IntInt call: lhs is a local
/// variable read at name index `lhs_name_idx`, rhs is an int literal.
fn build_ne_args(lhs_name_idx: i32, rhs_value: i32) -> Vec<u8> {
    let mut bytes = Vec::new();
    push_local_var(&mut bytes, lhs_name_idx);
    push_int_const(&mut bytes, rhs_value);
    bytes
}

/// Build a name table seeded with the names the dispatch fixtures
/// reference. Returns the table plus the index of `Status`. Other
/// names live at fixed indices (caller hard-codes them).
fn dispatch_name_table() -> NameTable {
    NameTable::from_names(vec!["Status".into(), "tmp".into()])
}

/// Synthesize a `NotEqual_IntInt(Status, value)` callmath body.
/// `Status` lives at name index 0 in `dispatch_name_table()`.
fn ne_status_eq(stream: &mut Vec<u8>, value: i32) {
    let args = build_ne_args(0, value);
    push_callmath(stream, /* export_idx = */ 1, &args);
}

/// Build a synthetic dispatch-table stream with `case_count` cases.
/// Returns the bytecode and the disk position of every case body's
/// first byte (so tests can verify body splits).
///
/// Layout per case n in 0..case_count:
///   `EX_JUMP_IF_NOT target=CASE_n  <NotEqual_IntInt(Status, n)>`
/// After the last pair:
///   `EX_JUMP target=CONVERGE`
/// Then case bodies:
///   CASE_0: EX_INT_CONST(100*0+1)  EX_NOTHING
///   CASE_1: EX_INT_CONST(100*1+1)  EX_NOTHING
///   ...
///   CONVERGE: EX_END_OF_SCRIPT
///
/// Each EX_INT_CONST is 5 bytes; each EX_NOTHING is 1 byte; case
/// bodies are therefore 6 bytes each.
fn build_inline_dispatch(case_count: usize) -> (Vec<u8>, Vec<usize>, usize) {
    // Pair size: EX_JUMP_IF_NOT(1) + target(4) + Ne callmath. The
    // callmath is EX_CALL_MATH(1) + obj(4) + EX_LOCAL_VARIABLE(13)
    // + EX_INT_CONST(5) + EX_END_FUNCTION_PARMS(1) = 24 bytes.
    // Total pair = 5 + 28 = 33 bytes (the local variable's
    // FFieldPath is 1+4+8+4 = 17 bytes total: opcode + path_num +
    // FName + owner; EX_INT_CONST is 1 + 4 = 5; sum = 28).
    let pair_size = 33;
    let term_jump_size = 5;
    let case_body_size = 6;

    let dispatch_size = pair_size * case_count + term_jump_size;
    let mut stream = Vec::new();

    // Compute case offsets and the converge offset up front. Cases
    // begin at `dispatch_size` and run sequentially.
    let case_offsets: Vec<usize> = (0..case_count)
        .map(|idx| dispatch_size + idx * case_body_size)
        .collect();
    let converge_offset = dispatch_size + case_count * case_body_size;

    // Emit the dispatch pairs.
    for (idx, &case_off) in case_offsets.iter().enumerate() {
        stream.push(EX_JUMP_IF_NOT);
        stream.extend_from_slice(&u32_le(case_off as u32));
        ne_status_eq(&mut stream, idx as i32);
    }
    // Emit the terminating jump to the converge offset.
    stream.push(EX_JUMP);
    stream.extend_from_slice(&u32_le(converge_offset as u32));

    // Emit each case body: a unique INT_CONST so the test can verify
    // the right body landed in the right case, plus an EX_NOTHING
    // padding byte (so the total body size matches `case_body_size`).
    for idx in 0..case_count {
        push_int_const(&mut stream, (idx as i32) * 100 + 1);
        stream.push(EX_NOTHING);
    }
    stream.push(EX_END_OF_SCRIPT);

    (stream, case_offsets, converge_offset)
}

/// Build identity mem_to_disk for every opcode boundary in
/// `case_offsets ++ [dispatch_start..]`. Tests pass identity-mapped
/// targets so jumps land on the offsets we encoded.
fn build_identity_map(stream: &[u8]) -> std::collections::BTreeMap<usize, usize> {
    // Every byte position is technically a candidate; the recognizer
    // only resolves jump targets, so we map every offset 0..len()
    // to itself. That matches `identity_map`'s semantics for streams
    // whose mem and disk coordinates coincide.
    let boundaries: Vec<usize> = (0..=stream.len()).collect();
    identity_map(&boundaries)
}

/// Produce the export-names table for the dispatch fixtures. Index 1
/// (positive 1-based) resolves to `NotEqual_IntInt`, the function
/// the recognizer keys on.
fn dispatch_export_names() -> Vec<String> {
    vec!["NotEqual_IntInt".to_string()]
}

#[test]
fn two_case_dispatch_table_decodes_to_switch() {
    let (stream, _case_offsets, converge_offset) = build_inline_dispatch(2);
    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let stmt = try_decode_jumpifnot_cascade(&mut pos, stream.len(), &ctx)
        .expect("expected Stmt::Switch from a 2-case dispatch");
    match stmt {
        Stmt::Switch {
            cases,
            default,
            expr,
            ..
        } => {
            assert_eq!(cases.len(), 2, "expected 2 cases");
            assert!(
                default.is_none(),
                "default should be None for in-table dispatch"
            );
            // Switch expression is the lhs of NotEqual: Status.
            assert_eq!(expr, Expr::Var("Status".into()));
            // Case 0 value is literal "0", case 1 is "1". Each
            // canonical case carries exactly one value.
            assert_eq!(cases[0].values, vec![Expr::Literal("0".into())]);
            assert_eq!(cases[1].values, vec![Expr::Literal("1".into())]);
            // Each case body should be non-empty (the EX_INT_CONST
            // decodes to a Stmt::Unknown since it's an expression
            // outside a recognised statement, but it should still
            // appear). We verify that *something* landed in each.
            assert!(!cases[0].body.is_empty(), "case 0 body should not be empty");
            assert!(!cases[1].body.is_empty(), "case 1 body should not be empty");
        }
        other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
    }
    assert_eq!(
        pos, converge_offset,
        "*pos should advance to the converge offset after a successful match"
    );
}

#[test]
fn four_case_dispatch_table_with_distinct_bodies() {
    let (stream, case_offsets, converge_offset) = build_inline_dispatch(4);
    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let stmt = try_decode_jumpifnot_cascade(&mut pos, stream.len(), &ctx)
        .expect("expected Stmt::Switch from a 4-case dispatch");
    match stmt {
        Stmt::Switch {
            cases,
            default,
            expr,
            offset,
        } => {
            assert_eq!(offset, 0, "switch offset should be the dispatch head");
            assert_eq!(cases.len(), 4, "expected 4 cases");
            assert!(default.is_none());
            assert_eq!(expr, Expr::Var("Status".into()));
            for (idx, case) in cases.iter().enumerate() {
                assert_eq!(
                    case.values,
                    vec![Expr::Literal(idx.to_string())],
                    "case {} values mismatch",
                    idx
                );
                assert!(
                    !case.body.is_empty(),
                    "case {} body should not be empty",
                    idx
                );
            }
            // Sanity: case offsets are monotonically increasing.
            for window in case_offsets.windows(2) {
                assert!(window[0] < window[1]);
            }
        }
        other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
    }
    assert_eq!(pos, converge_offset);
}

#[test]
fn genuine_if_elseif_chain_does_not_match() {
    // Two `[EX_JUMP_IF_NOT NotEqual]` pairs WITHOUT a terminating
    // EX_JUMP after them. This is the genuine if-elseif shape that
    // should keep flowing through decode_branch ->
    // lower_sentinel_cascade -> fold_switch_cascades.
    //
    // Pair size 28; total dispatch bytes 56; immediately after the
    // last pair we put EX_NOTHING (a non-jump opcode) so the
    // terminating-jump check fails.
    let mut stream = Vec::new();
    // Pair 1: JumpIfNot target=0x80, cond = NotEqual(Status, 0).
    stream.push(EX_JUMP_IF_NOT);
    stream.extend_from_slice(&u32_le(0x80));
    ne_status_eq(&mut stream, 0);
    // Pair 2: JumpIfNot target=0x90, cond = NotEqual(Status, 1).
    stream.push(EX_JUMP_IF_NOT);
    stream.extend_from_slice(&u32_le(0x90));
    ne_status_eq(&mut stream, 1);
    // No terminating EX_JUMP, just an EX_NOTHING placeholder.
    stream.push(EX_NOTHING);
    stream.push(EX_END_OF_SCRIPT);

    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let result = try_decode_jumpifnot_cascade(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "genuine if-elseif chain (no terminating EX_JUMP) must not match, got {:?}",
        result.as_ref().map(stmt_kind)
    );
    assert_eq!(pos, 0, "*pos must not advance on mismatch");
}

#[test]
fn single_jumpifnot_does_not_match() {
    // One pair only — fewer than 2 pairs cannot form a dispatch.
    let mut stream = Vec::new();
    stream.push(EX_JUMP_IF_NOT);
    stream.extend_from_slice(&u32_le(0x80));
    ne_status_eq(&mut stream, 0);
    // Even with a terminating EX_JUMP, one pair isn't enough.
    stream.push(EX_JUMP);
    stream.extend_from_slice(&u32_le(0x100));
    stream.push(EX_END_OF_SCRIPT);

    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let result = try_decode_jumpifnot_cascade(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "single-pair chain must not match, got {:?}",
        result.as_ref().map(stmt_kind)
    );
    assert_eq!(pos, 0);
}

#[test]
fn non_ne_condition_does_not_match() {
    // First pair's condition is an EqualEqual_ call, not NotEqual_.
    // The recognizer should bail out cleanly. To synthesize this
    // shape we point EX_CALL_MATH at export index 2, which resolves
    // to "EqualEqual_IntInt".
    let mut stream = Vec::new();
    // Pair 1: cond = EqualEqual_IntInt(Status, 0).
    stream.push(EX_JUMP_IF_NOT);
    stream.extend_from_slice(&u32_le(0x80));
    let args = build_ne_args(0, 0);
    push_callmath(&mut stream, /* export_idx = */ 2, &args);
    // Pair 2: cond = EqualEqual_IntInt(Status, 1).
    stream.push(EX_JUMP_IF_NOT);
    stream.extend_from_slice(&u32_le(0x90));
    let args2 = build_ne_args(0, 1);
    push_callmath(&mut stream, /* export_idx = */ 2, &args2);
    stream.push(EX_JUMP);
    stream.extend_from_slice(&u32_le(0x100));
    stream.push(EX_END_OF_SCRIPT);

    let names = dispatch_name_table();
    let exports = vec![
        "NotEqual_IntInt".to_string(),   // index 1
        "EqualEqual_IntInt".to_string(), // index 2
    ];
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let result = try_decode_jumpifnot_cascade(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "EqualEqual_ condition must not match the NotEqual_ recognizer, got {:?}",
        result.as_ref().map(stmt_kind)
    );
    assert_eq!(pos, 0);
}

// Helper-predicate tests below pin the structural gates without
// needing the full bytecode synthesis above.

#[test]
fn extract_ne_call_accepts_notequal_intint() {
    let call = Expr::Call {
        name: "NotEqual_IntInt".into(),
        args: vec![Expr::Var("Status".into()), Expr::Literal("0".into())],
    };
    let (lhs, rhs) = extract_ne_call(&call).expect("expected Ne match");
    assert_eq!(lhs, Expr::Var("Status".into()));
    assert_eq!(rhs, Expr::Literal("0".into()));
}

#[test]
fn extract_ne_call_rejects_equal_call() {
    let call = Expr::Call {
        name: "EqualEqual_IntInt".into(),
        args: vec![Expr::Var("Status".into()), Expr::Literal("0".into())],
    };
    assert!(extract_ne_call(&call).is_none());
}

#[test]
fn extract_ne_call_rejects_wrong_arity() {
    let call = Expr::Call {
        name: "NotEqual_IntInt".into(),
        args: vec![Expr::Var("Status".into())],
    };
    assert!(extract_ne_call(&call).is_none());
}

#[test]
fn peek_terminating_jump_recognizes_ex_jump() {
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(0x42));
    let names = empty_name_table();
    let map = identity_map(&[0, 5]);
    let ctx = ue4_ctx(&stream, &names, &map);

    let term = peek_terminating_jump(0, stream.len(), &ctx).expect("expected EX_JUMP recognition");
    assert_eq!(term.target_mem, 0x42);
    assert_eq!(term.after_jump, 5);
}

#[test]
fn peek_terminating_jump_rejects_non_jump() {
    let stream = vec![EX_NOTHING];
    let names = empty_name_table();
    let map = identity_map(&[0, 1]);
    let ctx = ue4_ctx(&stream, &names, &map);

    assert!(peek_terminating_jump(0, stream.len(), &ctx).is_none());
}

/// Build a synthetic shared-target dispatch stream. The first
/// `shared_count` pairs all target the same case body (CASE_a); the
/// remaining `tail_count` pairs each target a distinct body
/// (CASE_b, CASE_c, ...). After the last pair sits a single
/// `EX_POP_EXECUTION_FLOW` (1 byte) instead of an `EX_JUMP`. Case
/// bodies follow with `EX_INT_CONST` + `EX_NOTHING` padding so each
/// body is 6 bytes.
fn build_shared_dispatch(shared_count: usize, tail_count: usize) -> (Vec<u8>, Vec<usize>, usize) {
    let pair_size = 33;
    let pop_flow_size = 1;
    let case_body_size = 6;
    let total_pairs = shared_count + tail_count;
    let unique_bodies = 1 + tail_count;

    let dispatch_size = pair_size * total_pairs + pop_flow_size;
    let mut stream = Vec::new();

    // Body offsets: shared body is at `dispatch_size`; each tail
    // body follows, 6 bytes apart.
    let body_offsets: Vec<usize> = (0..unique_bodies)
        .map(|idx| dispatch_size + idx * case_body_size)
        .collect();
    let after_bodies = dispatch_size + unique_bodies * case_body_size;

    // Emit the dispatch pairs. Pairs 0..shared_count target body 0;
    // pair `shared_count + i` targets body `1 + i`.
    for idx in 0..shared_count {
        stream.push(EX_JUMP_IF_NOT);
        stream.extend_from_slice(&u32_le(body_offsets[0] as u32));
        ne_status_eq(&mut stream, idx as i32);
    }
    for tail_idx in 0..tail_count {
        stream.push(EX_JUMP_IF_NOT);
        stream.extend_from_slice(&u32_le(body_offsets[1 + tail_idx] as u32));
        ne_status_eq(&mut stream, (shared_count + tail_idx) as i32);
    }
    stream.push(EX_POP_EXECUTION_FLOW);

    // Emit each unique case body.
    for idx in 0..unique_bodies {
        push_int_const(&mut stream, (idx as i32) * 100 + 1);
        stream.push(EX_NOTHING);
    }
    stream.push(EX_END_OF_SCRIPT);

    (stream, body_offsets, after_bodies)
}

#[test]
fn shared_target_dispatch_with_pop_flow_decodes_to_switch() {
    // 3 cases share body 0; 1 case has its own body. Mirrors a
    // shared-body dispatch shape (3 enum values share one case body,
    // a 4th has its own).
    let (stream, body_offsets, _) = build_shared_dispatch(3, 1);
    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let stmt = try_decode_jumpifnot_cascade_shared(&mut pos, stream.len(), &ctx)
        .expect("expected Stmt::Switch from a shared-target dispatch");
    match stmt {
        Stmt::Switch {
            cases,
            default,
            expr,
            ..
        } => {
            assert_eq!(
                cases.len(),
                2,
                "expected one case per unique target (3 shared + 1 distinct)"
            );
            assert!(default.is_none());
            assert_eq!(expr, Expr::Var("Status".into()));
            // First case carries the merged values for the shared
            // body (0, 1, 2). Second case is the distinct tail body (3).
            assert_eq!(
                cases[0].values,
                vec![
                    Expr::Literal("0".into()),
                    Expr::Literal("1".into()),
                    Expr::Literal("2".into()),
                ],
            );
            assert_eq!(cases[1].values, vec![Expr::Literal("3".into())]);
            for (idx, case) in cases.iter().enumerate() {
                assert!(
                    !case.body.is_empty(),
                    "case {} body should not be empty",
                    idx
                );
            }
        }
        other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
    }
    // Body offsets are a sanity check: shared body at index 0,
    // distinct body at index 1.
    assert_eq!(body_offsets.len(), 2);
}

#[test]
fn shared_target_dispatch_without_shared_target_does_not_match() {
    // Build a 4-case dispatch where every target is distinct AND
    // termination is pop_flow rather than EX_JUMP. The recognizer
    // should bail because there's no shared target (this shape is
    // ambiguous with the canonical recognizer's expected pattern;
    // we deliberately require at least one shared target to fire).
    let (stream, _, _) = build_shared_dispatch(0, 4);
    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let result = try_decode_jumpifnot_cascade_shared(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "no-shared-target dispatch should not match the shared recognizer, got {:?}",
        result.as_ref().map(stmt_kind)
    );
    assert_eq!(pos, 0);
}

#[test]
fn canonical_dispatch_with_ex_jump_terminator_does_not_match_shared_recognizer() {
    // The canonical 4-case dispatch (terminating EX_JUMP, distinct
    // targets) should be claimed by `try_decode_jumpifnot_cascade`,
    // not the shared recognizer. The shared recognizer must decline
    // when the byte after the last pair is EX_JUMP rather than
    // pop_flow.
    let (stream, _case_offsets, _converge_offset) = build_inline_dispatch(4);
    let names = dispatch_name_table();
    let exports = dispatch_export_names();
    let map = build_identity_map(&stream);
    let ctx = ue4_ctx_with_exports(&stream, &names, &map, &exports);

    let mut pos = 0;
    let result = try_decode_jumpifnot_cascade_shared(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "canonical dispatch must not be claimed by the shared recognizer"
    );
    assert_eq!(pos, 0);
}

#[test]
fn resolve_target_uses_mem_to_disk_when_present() {
    let stream = vec![EX_NOTHING];
    let names = empty_name_table();
    let mut map = std::collections::BTreeMap::new();
    map.insert(0x10, 0x18);
    let ctx = ue4_ctx(&stream, &names, &map);

    assert_eq!(resolve_target(0x10, &ctx), Some(0x18));
    // A miss against a present map means the target is not on any known
    // opcode boundary; resolution must fail instead of guessing raw mem.
    assert_eq!(resolve_target(0x99, &ctx), None);
}
