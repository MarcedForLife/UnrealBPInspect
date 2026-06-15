//! Tests for `decode/naked_if.rs` (Form B). The recogniser enters at
//! `EX_POP_FLOW_IF_NOT` and synthesises a `Stmt::Branch` when the
//! bytes form `pop_flow_if_not(non-literal cond) + body + pop_flow`.
//!
//! These tests exercise the public entry directly and use synthetic
//! `DecodeCtx` instances built with `test_fixtures`. Real-fixture
//! coverage (the user-visible naked-if at a tick event's sequence
//! pin) is asserted by the regression suite over committed fixtures.

use std::cell::RefCell;
use std::collections::BTreeMap;

use super::ctx::{mark_claimed, Claim, DecodeCtx, LoopBreakGuard, OwnerId};
use super::naked_if::try_decode_naked_if;
use crate::binary::NameTable;
use crate::bytecode::decode::test_fixtures::{
    empty_name_table, identity_map, put_field_path, stmt_kind, u32_le,
};
use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::stmt::Stmt;

/// Variant of `ue4_ctx` that wires a caller-supplied claim map so a
/// test can pre-populate `OwnerId::DoOnceGate` claims and verify
/// Form B's claim-bypass logic.
fn ue4_ctx_with_claims<'a>(
    bytecode: &'a [u8],
    name_table: &'a NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
    claims: &'a RefCell<BTreeMap<usize, Claim>>,
) -> DecodeCtx<'a> {
    DecodeCtx {
        mem_to_disk: Some(mem_to_disk),
        claimed: Some(claims),
        ..DecodeCtx::new(bytecode, name_table, &[], &[], 0)
    }
}

/// Layout offsets for an `EX_INSTANCE_VARIABLE` cond. The opcode byte
/// is followed by an `FFieldPath` operand whose on-disk shape is
/// `i32 path_num + path_num * (i32 name_idx + i32 instance) + i32 owner`.
/// `put_field_path` emits the canonical `path_num=1, owner=0` form,
/// adding 16 bytes to the 1-byte opcode.
const INSTANCE_VAR_OPERAND_BYTES: usize = 16;
const POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES: usize = 1 + 1 + INSTANCE_VAR_OPERAND_BYTES;

/// Build a `(stream, boundaries, name_table)` triple for a canonical
/// naked-if at offset 0 with cond `self.MyCond`:
///
/// ```text
///   0x00 EX_POP_FLOW_IF_NOT
///   0x01 EX_INSTANCE_VARIABLE <field_path("MyCond")>   (1 + 16 bytes)
///   0x12 EX_NOTHING                                      (body stmt)
///   0x13 EX_POP_EXECUTION_FLOW                           (closes frame)
///   0x14 EX_END_OF_SCRIPT
/// ```
fn naked_if_with_var_cond_stream() -> (Vec<u8>, Vec<usize>, NameTable) {
    let names = NameTable::from_names(vec!["MyCond".to_string()]);
    let mut stream = vec![EX_POP_FLOW_IF_NOT];
    stream.push(EX_INSTANCE_VARIABLE);
    put_field_path(&mut stream, 0); // name index 0 -> "MyCond"
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    let pop_offset = body_offset + 1;
    let end_offset = pop_offset + 1;
    stream.push(EX_NOTHING); // body
    stream.push(EX_POP_EXECUTION_FLOW); // closing pop
    stream.push(EX_END_OF_SCRIPT);
    let boundaries = vec![0, body_offset, pop_offset, end_offset, end_offset + 1];
    (stream, boundaries, names)
}

#[test]
fn canonical_naked_if_decodes_as_branch_with_empty_else() {
    let (stream, boundaries, names) = naked_if_with_var_cond_stream();
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    let stmt = try_decode_naked_if(&mut pos, stream.len(), &ctx).expect("expected Stmt::Branch");
    match stmt {
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset,
        } => {
            assert!(else_body.is_empty(), "else_body should be empty");
            // The recogniser records the pop_flow_if_not's disk offset
            // (0x00) as the construct's offset.
            assert_eq!(offset, 0x00, "offset should point at pop_flow_if_not");
            assert!(
                matches!(cond, Expr::Var(ref name) if name == "self.MyCond"),
                "cond should be Var(\"self.MyCond\"), got {:?}",
                cond
            );
            assert_eq!(
                then_body.len(),
                1,
                "then_body should hold one stmt (the EX_NOTHING body), got {}",
                then_body.len()
            );
        }
        other => panic!("expected Stmt::Branch, got {:?}", stmt_kind(&other)),
    }
    let expected_pos = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES + 1 + 1; // body byte + pop byte
    assert_eq!(
        pos, expected_pos,
        "pos should resume one byte past the matching pop"
    );
}

#[test]
fn doonce_init_tail_with_claim_bails() {
    // Synthesize the DoOnce init-block tail shape:
    //   0x00 EX_POP_FLOW_IF_NOT cond=EX_FALSE
    //   0x02 EX_LET_BOOL <Var(Temp_bool_IsClosed_Variable_4)> EX_TRUE
    //   ...  EX_POP_EXECUTION_FLOW
    //
    // The exact body bytes don't matter: we just need a claim covering
    // the entry offset. Form B's claim check (`claimed_end_for`) is
    // owner-agnostic, it bails whenever the entry sits inside any claim;
    // a surviving prescan-style owner stands in for the claim here.
    let names = empty_name_table();
    let mut stream = vec![EX_POP_FLOW_IF_NOT, EX_FALSE];
    stream.push(EX_NOTHING); // dummy body
    stream.push(EX_POP_EXECUTION_FLOW);
    stream.push(EX_END_OF_SCRIPT);
    let boundaries = vec![0, 2, 3, 4, 5];
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let claim_owner = OwnerId::IsValid { jin_disk: 0 };
    mark_claimed(&ctx, 0, stream.len(), claim_owner);

    let mut pos = 0;
    let result = try_decode_naked_if(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "DoOnce init-tail under a claim must NOT match Form B"
    );
    assert_eq!(pos, 0, "pos must be unchanged when None returned");
}

#[test]
fn constant_cond_true_bails() {
    // pop_flow_if_not(true) without a claim. Defense-in-depth: even
    // when the prescan didn't fire, the literal-cond bail keeps Form
    // B from synthesising `if (true) { ... }`.
    let names = empty_name_table();
    let mut stream = vec![EX_POP_FLOW_IF_NOT, EX_TRUE];
    stream.push(EX_NOTHING);
    stream.push(EX_POP_EXECUTION_FLOW);
    stream.push(EX_END_OF_SCRIPT);
    let boundaries = vec![0, 2, 3, 4, 5];
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    let result = try_decode_naked_if(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "literal-cond pop_flow_if_not(true) must NOT match Form B"
    );
    assert_eq!(pos, 0, "pos must be unchanged when None returned");
}

#[test]
fn constant_cond_false_bails() {
    let names = empty_name_table();
    let mut stream = vec![EX_POP_FLOW_IF_NOT, EX_FALSE];
    stream.push(EX_NOTHING);
    stream.push(EX_POP_EXECUTION_FLOW);
    stream.push(EX_END_OF_SCRIPT);
    let boundaries = vec![0, 2, 3, 4, 5];
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    let result = try_decode_naked_if(&mut pos, stream.len(), &ctx);
    assert!(
        result.is_none(),
        "literal-cond pop_flow_if_not(false) must NOT match Form B"
    );
    assert_eq!(pos, 0, "pos must be unchanged when None returned");
}

#[test]
fn missing_matching_pop_flow_bails() {
    // pop_flow_if_not(Var("MyCond")) followed by body with NO pop_flow
    // before EOF. Form B's depth-walk must not find a matching pop
    // within the visible range.
    let names = NameTable::from_names(vec!["MyCond".to_string()]);
    let mut stream = vec![EX_POP_FLOW_IF_NOT];
    stream.push(EX_INSTANCE_VARIABLE);
    put_field_path(&mut stream, 0);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    stream.push(EX_NOTHING); // body byte 1
    stream.push(EX_NOTHING); // body byte 2 (still no pop_flow)
    let scan_limit = body_offset + 2;
    stream.push(EX_END_OF_SCRIPT); // outside scan_limit
    let boundaries = vec![0, body_offset, body_offset + 1, scan_limit, scan_limit + 1];
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    let result = try_decode_naked_if(&mut pos, scan_limit, &ctx);
    assert!(
        result.is_none(),
        "missing matching pop_flow must cause bail to None"
    );
    assert_eq!(pos, 0, "pos must be unchanged when None returned");
}

/// Build a stream for a loop break-guard: a `pop_flow_if_not(non-literal
/// cond)` whose body has NO balancing `EX_POP_EXECUTION_FLOW` before the
/// range end (the false path resumes the loop increment instead). The
/// caller decides whether the body is flat or carries a nested push.
///
/// ```text
///   0x00 EX_POP_FLOW_IF_NOT
///   0x01 EX_INSTANCE_VARIABLE <field_path("MyCond")>   (1 + 16 bytes)
///   0x12 <body bytes ...>                              (no pop_flow)
/// ```
fn loop_break_guard_stream(body: &[u8]) -> (Vec<u8>, Vec<usize>, NameTable) {
    let names = NameTable::from_names(vec!["MyCond".to_string()]);
    let mut stream = vec![EX_POP_FLOW_IF_NOT, EX_INSTANCE_VARIABLE];
    put_field_path(&mut stream, 0);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    let mut boundaries = vec![0, body_offset];
    let mut cursor = body_offset;
    for &byte in body {
        stream.push(byte);
        cursor += 1;
        boundaries.push(cursor);
    }
    (stream, boundaries, names)
}

/// A loop-break-guard hint whose true-body ends at `tail` and whose
/// false-path `continuation` lands inside `[scope_start, scope_end)`.
fn break_guard(
    tail: usize,
    scope_start: usize,
    scope_end: usize,
    continuation: usize,
) -> LoopBreakGuard {
    LoopBreakGuard {
        tail,
        scope_start,
        scope_end,
        continuation,
        displaced_start: 0,
        owner: OwnerId::CfgRegion { region_id: 0 },
    }
}

#[test]
fn loop_break_guard_recovers_flat_body() {
    // Flat terminal body (one EX_NOTHING), no balancing pop. With an
    // active loop-break-guard hint whose continuation lands in scope, the
    // recogniser recovers the guard bounded by the loop tail.
    let (stream, boundaries, names) = loop_break_guard_stream(&[EX_NOTHING]);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    let tail = body_offset + 1; // one byte past the body byte
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);
    // continuation 0x05 is inside scope [0x00, 0x40); the loop tail is
    // the displaced terminator at `tail`.
    ctx.loop_break_guard
        .set(Some(break_guard(tail, 0x00, 0x40, 0x05)));

    let mut pos = 0;
    let stmt = try_decode_naked_if(&mut pos, stream.len(), &ctx)
        .expect("loop break-guard should recover a Branch");
    let Stmt::Branch {
        then_body,
        else_body,
        offset,
        ..
    } = stmt
    else {
        panic!("expected Stmt::Branch");
    };
    assert_eq!(offset, 0, "offset points at the guard's pop_flow_if_not");
    assert!(else_body.is_empty());
    assert_eq!(then_body.len(), 1, "the one body stmt is captured");
    assert_eq!(pos, tail, "pos advances to the loop tail");
    // The recovered body is claimed under the loop owner so the disk-order
    // re-walk skips it.
    assert!(
        claims.borrow().contains_key(&body_offset),
        "guard body must be claimed for dedup"
    );
}

#[test]
fn loop_break_guard_declines_continuation_out_of_scope() {
    // Same flat body, but the continuation lands OUTSIDE the loop scope:
    // the discriminator rejects it (not a loop break).
    let (stream, boundaries, names) = loop_break_guard_stream(&[EX_NOTHING]);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    let tail = body_offset + 1;
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);
    // continuation 0x99 is NOT in scope [0x00, 0x40).
    ctx.loop_break_guard
        .set(Some(break_guard(tail, 0x00, 0x40, 0x99)));

    let mut pos = 0;
    assert!(
        try_decode_naked_if(&mut pos, stream.len(), &ctx).is_none(),
        "out-of-scope continuation must decline"
    );
    assert_eq!(pos, 0, "pos unchanged on decline");
}

#[test]
fn loop_break_guard_declines_body_with_nested_flow() {
    // Body carries an EX_PUSH_EXECUTION_FLOW (an inner loop's break
    // trampoline). The simple tail bound can't reconstruct that nesting,
    // so the recogniser declines (the depth-2 nested-loop case).
    let mut body = vec![EX_PUSH_EXECUTION_FLOW];
    body.extend_from_slice(&u32_le(0)); // push target operand
    body.push(EX_NOTHING);
    let (stream, boundaries, names) = loop_break_guard_stream(&body);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    let tail = body_offset + body.len();
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);
    ctx.loop_break_guard
        .set(Some(break_guard(tail, 0x00, 0x100, 0x05)));

    let mut pos = 0;
    assert!(
        try_decode_naked_if(&mut pos, stream.len(), &ctx).is_none(),
        "a body with a nested push_flow must decline"
    );
    assert_eq!(pos, 0, "pos unchanged on decline");
}

#[test]
fn unbalanced_guard_without_loop_context_returns_none() {
    // No balancing pop and NO loop-break-guard hint: the recogniser must
    // fall through to None (the pre-fix behaviour). This guards the gate
    // that keeps the loop fallback dormant in non-loop contexts.
    let (stream, boundaries, names) = loop_break_guard_stream(&[EX_NOTHING]);
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);
    // loop_break_guard left as None.

    let mut pos = 0;
    assert!(
        try_decode_naked_if(&mut pos, stream.len(), &ctx).is_none(),
        "no loop context means no break-guard recovery"
    );
    assert_eq!(pos, 0, "pos unchanged");
}

#[test]
fn non_pop_flow_if_not_opcode_returns_none() {
    let stream = vec![EX_NOTHING, EX_END_OF_SCRIPT];
    let map = identity_map(&[0, 1, 2]);
    let names = empty_name_table();
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    assert!(try_decode_naked_if(&mut pos, stream.len(), &ctx).is_none());
    assert_eq!(pos, 0, "pos must be unchanged");
}

#[test]
fn nested_push_pop_inside_body_balances_to_outer_pop() {
    // Simulate a body that contains an inner `push_flow + pop_flow`
    // pair (e.g. a nested IsValid sub-Branch). The depth-walk must
    // skip the inner pair and stop at the outer pop_flow.
    let names = NameTable::from_names(vec!["MyCond".to_string()]);
    let push_flow_target_dummy = 0u32;
    let mut stream = vec![EX_POP_FLOW_IF_NOT];
    stream.push(EX_INSTANCE_VARIABLE);
    put_field_path(&mut stream, 0);
    let body_offset = POP_FLOW_IF_NOT_PLUS_INSTANCE_VAR_BYTES;
    stream.push(EX_PUSH_EXECUTION_FLOW); // body[0] inner push
    stream.extend_from_slice(&u32_le(push_flow_target_dummy));
    let inner_pop_offset = body_offset + 1 + 4;
    stream.push(EX_POP_EXECUTION_FLOW); // INNER pop (closes inner push)
    let body_filler_offset = inner_pop_offset + 1;
    stream.push(EX_NOTHING); // body filler
    let outer_pop_offset = body_filler_offset + 1;
    stream.push(EX_POP_EXECUTION_FLOW); // OUTER pop (closes pop_flow_if_not)
    stream.push(EX_END_OF_SCRIPT);
    let boundaries = vec![
        0,
        body_offset,
        inner_pop_offset,
        body_filler_offset,
        outer_pop_offset,
        outer_pop_offset + 1,
        outer_pop_offset + 2,
    ];
    let map = identity_map(&boundaries);
    let claims = RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_claims(&stream, &names, &map, &claims);

    let mut pos = 0;
    let stmt =
        try_decode_naked_if(&mut pos, stream.len(), &ctx).expect("expected nested Stmt::Branch");
    let Stmt::Branch { offset, .. } = stmt else {
        panic!("expected Stmt::Branch, got {:?}", stmt_kind(&stmt));
    };
    assert_eq!(offset, 0, "offset should point at outer pop_flow_if_not");
    assert_eq!(
        pos,
        outer_pop_offset + 1,
        "pos should resume one byte past the OUTER pop, not the inner one"
    );
}
