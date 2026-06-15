//! Tests for `decode/branch.rs`. Extracted from the production module so
//! the control-flow recognizer stays focused on the decoder; the
//! synthetic opcode-stream fixtures that exercise each shape live here.

use super::branch::*;
use super::ctx::DecodeCtx;
use crate::bytecode::decode::test_fixtures::{
    empty_name_table, identity_map, stmt_kind, u32_le, ue4_ctx, ue4_ctx_with_events,
};
use crate::bytecode::opcodes::*;
use crate::bytecode::stmt::Stmt;
use std::collections::BTreeMap;

#[test]
fn classic_if_then_decodes_branch_with_empty_else() {
    // Layout (offsets in mem == disk because no FName operands):
    //   0x00 EX_JUMP_IF_NOT target=0x07
    //   0x01..0x05 target operand
    //   0x05 EX_NOTHING (cond)
    //   0x06 EX_NOTHING (then-body)
    //   0x07 EX_NOTHING (post-construct)
    //   0x08 EX_END_OF_SCRIPT
    let mut stream = vec![EX_JUMP_IF_NOT];
    stream.extend_from_slice(&u32_le(7));
    stream.push(EX_NOTHING); // cond
    stream.push(EX_NOTHING); // then body
    stream.push(EX_NOTHING); // post-construct (else target)
    stream.push(EX_END_OF_SCRIPT);

    let boundaries = vec![0, 5, 6, 7, 8];
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let ctx = ue4_ctx(&stream, &names, &map);

    let mut pos = 0;
    let outcome = decode_branch(&mut pos, stream.len(), &ctx);
    match outcome.stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            assert!(
                else_body.is_empty(),
                "expected empty else, got {} stmts",
                else_body.len()
            );
            // then-body: cond expression plus the then EX_NOTHING
            // become Unknown stmts; we just verify recursion produced
            // some statements without crashing.
            assert!(!then_body.is_empty() || pos == 7);
        }
        other => panic!("expected Stmt::Branch, got {:?}", stmt_kind(&other)),
    }
    assert_eq!(pos, 7, "resume should land on else target");
}

#[test]
fn classic_if_then_else_decodes_branch_with_both_bodies() {
    // Layout:
    //   0x00 EX_JUMP_IF_NOT target=0x0B
    //   0x01..0x05 target operand
    //   0x05 EX_NOTHING (cond)
    //   0x06 EX_NOTHING (then body)
    //   0x07 EX_JUMP target=0x0C
    //   0x08..0x0C target operand
    //   0x0C EX_NOTHING (else body) <- target=0x0B is offset 11
    // Adjust: place else at 0x0C exactly.
    // Recompute: opcodes
    //   off 0: EX_JUMP_IF_NOT (1 byte) target operand 4 bytes -> next at 5
    //   off 5: EX_NOTHING (1 byte) -> 6  (cond)
    //   off 6: EX_NOTHING (1 byte) -> 7  (then body)
    //   off 7: EX_JUMP (1 byte) target=0x0D operand 4 bytes -> 12
    //   off 12: EX_NOTHING (else body) -> 13
    //   off 13: EX_END_OF_SCRIPT
    let mut stream = vec![EX_JUMP_IF_NOT];
    stream.extend_from_slice(&u32_le(12)); // else target
    stream.push(EX_NOTHING); // cond
    stream.push(EX_NOTHING); // then body
    stream.push(EX_JUMP);
    stream.extend_from_slice(&u32_le(13)); // post-construct
    stream.push(EX_NOTHING); // else body
    stream.push(EX_END_OF_SCRIPT);

    let boundaries = vec![0, 5, 6, 7, 12, 13, 14];
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let ctx = ue4_ctx(&stream, &names, &map);

    let mut pos = 0;
    let outcome = decode_branch(&mut pos, stream.len(), &ctx);
    match outcome.stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            assert!(!then_body.is_empty(), "then body should have stmts");
            assert!(!else_body.is_empty(), "else body should have stmts");
        }
        other => panic!("expected Stmt::Branch, got {:?}", stmt_kind(&other)),
    }
    assert_eq!(pos, 13, "resume should land past else body");
}

/// Build a `DecodeCtx` with `owned_ranges` and a `claimed` map. The
/// IsValid macro tests need a backward-target JIN whose enclosing
/// scope owns disjoint disk ranges; the simpler `ue4_ctx` helpers
/// don't expose those fields.
fn ue4_ctx_with_owned_and_claimed<'a>(
    bytecode: &'a [u8],
    name_table: &'a crate::binary::NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
    owned: &'a [std::ops::Range<usize>],
    claimed: &'a std::cell::RefCell<BTreeMap<usize, super::ctx::Claim>>,
) -> DecodeCtx<'a> {
    DecodeCtx {
        mem_to_disk: Some(mem_to_disk),
        owned_ranges: Some(owned),
        claimed: Some(claimed),
        ..DecodeCtx::new(bytecode, name_table, &[], &[], 0)
    }
}

/// Backward-target IsValid macro followed by an unconditional EX_JUMP
/// to a displaced valid-pin body in another owned segment. The
/// recogniser must claim that segment as the then_range and not leave
/// it for the outer linear sweep.
///
/// Layout (mem == disk, identity translation; offsets pulled from a
/// real tick-event IsValid pattern):
///   0x00 EX_NOTHING (placeholder so pos 0 isn't a JIN target)
///   0x01 EX_NOTHING (displaced valid-pin body head, segment start)
///   0x02 EX_NOTHING (more body)
///   0x03 EX_END_OF_SCRIPT (segment end marker)
///   ...gap (bytes belong to other owners)...
///   0x10 EX_NOTHING (displaced invalid-pin body head)
///   0x11 EX_POP_EXECUTION_FLOW (terminator)
///   0x12 EX_NOTHING (filler)
///   ...gap...
///   0x20 EX_JUMP_IF_NOT target=0x10  (the IsValid JIN, backward)
///       0x21..0x25 target operand
///   0x25 EX_NOTHING (cond)
///   0x26 EX_TRACEPOINT (instrumentation, skipped by recogniser)
///   0x27 EX_JUMP target=0x01         (post-JIN jump to valid body)
///       0x28..0x2c target operand
///   0x2c EX_END_OF_SCRIPT (range end)
#[test]
fn isvalid_backward_with_jump_follow_claims_displaced_body() {
    let mut stream = vec![EX_NOTHING; 0x2d];
    stream[0x00] = EX_NOTHING;
    stream[0x01] = EX_NOTHING;
    stream[0x02] = EX_NOTHING;
    stream[0x03] = EX_END_OF_SCRIPT;
    stream[0x10] = EX_NOTHING;
    stream[0x11] = EX_POP_EXECUTION_FLOW;
    stream[0x12] = EX_NOTHING;
    stream[0x20] = EX_JUMP_IF_NOT;
    let target_bytes = u32_le(0x10);
    stream[0x21..0x25].copy_from_slice(&target_bytes);
    stream[0x25] = EX_NOTHING;
    stream[0x26] = EX_TRACEPOINT;
    stream[0x27] = EX_JUMP;
    let jump_bytes = u32_le(0x01);
    stream[0x28..0x2c].copy_from_slice(&jump_bytes);
    stream[0x2c] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x2c).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x01..0x04, 0x10..0x13, 0x20..0x2d];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    let mut pos = 0x20;
    let outcome = decode_branch(&mut pos, 0x2d, &ctx);
    match outcome.stmt {
        Stmt::Branch {
            then_body,
            else_body,
            ..
        } => {
            assert!(
                !then_body.is_empty(),
                "then_body should contain decoded valid-pin body, got empty"
            );
            assert!(
                !else_body.is_empty(),
                "else_body should contain decoded invalid-pin body, got empty"
            );
        }
        other => panic!("expected Stmt::Branch, got {:?}", stmt_kind(&other)),
    }
    let claims = claimed.borrow();
    assert!(
        claims
            .iter()
            .any(|(&start, claim)| start == 0x01 && claim.end == 0x04),
        "claimed map should contain valid-pin segment 0x01..0x04, got {:?}",
        claims
    );
    assert!(
        claims
            .iter()
            .any(|(&start, claim)| start == 0x10 && claim.end == 0x12),
        "claimed map should contain invalid-pin else range 0x10..0x12, got {:?}",
        claims
    );
}

/// Backward-target IsValid macro with no post-JIN JUMP. Falls back to
/// the existing inline-body shape (then_range covers the rest of the
/// scope's range, no claim added for the valid-pin segment).
#[test]
fn isvalid_backward_without_post_jin_jump_falls_back() {
    let mut stream = vec![EX_NOTHING; 0x18];
    stream[0x00] = EX_NOTHING;
    stream[0x01] = EX_POP_EXECUTION_FLOW;
    stream[0x10] = EX_JUMP_IF_NOT;
    let target_bytes = u32_le(0x00);
    stream[0x11..0x15].copy_from_slice(&target_bytes);
    stream[0x15] = EX_NOTHING;
    stream[0x16] = EX_NOTHING;
    stream[0x17] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x17).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x00..0x02, 0x10..0x18];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    let mut pos = 0x10;
    let outcome = decode_branch(&mut pos, 0x18, &ctx);
    match outcome.stmt {
        Stmt::Branch { else_body, .. } => {
            assert!(!else_body.is_empty(), "else_body should hold backward body");
        }
        other => panic!("expected Stmt::Branch, got {:?}", stmt_kind(&other)),
    }
    let claims = claimed.borrow();
    // Only the else range should be claimed, not the valid-pin
    // segment (0x00..0x02 here): without a post-JIN JUMP the
    // fallback path doesn't follow into another owned segment.
    let has_else_claim = claims
        .iter()
        .any(|(&start, claim)| start == 0x00 && claim.end == 0x02);
    assert!(
        has_else_claim,
        "backward else range 0x00..0x02 should be claimed, got {:?}",
        claims
    );
}

/// Backward-target IsValid with a post-JIN JUMP whose target falls
/// outside the enclosing owned ranges. Recogniser must NOT claim and
/// must fall back to the existing inline-body shape.
#[test]
fn isvalid_backward_with_jump_out_of_partition_falls_back() {
    let mut stream = vec![EX_NOTHING; 0x30];
    stream[0x10] = EX_NOTHING;
    stream[0x11] = EX_POP_EXECUTION_FLOW;
    stream[0x20] = EX_JUMP_IF_NOT;
    let target_bytes = u32_le(0x10);
    stream[0x21..0x25].copy_from_slice(&target_bytes);
    stream[0x25] = EX_NOTHING;
    stream[0x26] = EX_JUMP;
    // Target 0x01 is NOT inside any owned range, so the recogniser
    // must reject this JUMP and fall back.
    let jump_bytes = u32_le(0x01);
    stream[0x27..0x2b].copy_from_slice(&jump_bytes);
    stream[0x2b] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x2b).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x10..0x12, 0x20..0x2c];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    let mut pos = 0x20;
    let _outcome = decode_branch(&mut pos, 0x2c, &ctx);
    let claims = claimed.borrow();
    // Should NOT contain the out-of-partition target as a claim.
    assert!(
        !claims.iter().any(|(&start, _)| start == 0x01),
        "out-of-partition target must not be claimed, got {:?}",
        claims
    );
}

/// Bare-trampoline tail-JIN THEN arm: post-JIN unconditional jump
/// lands on a tracepoint+EX_JUMP trampoline whose target is a
/// canonical chain head (instrumentation + EX_PUSH_EXECUTION_FLOW +
/// EX_JUMP). The recogniser must follow through the trampoline and
/// claim/decode the chain at the target rather than the trampoline
/// jump.
///
/// Layout (mem == disk; offsets mirror a real tail-JIN trampoline
/// pattern at reduced scale):
///   0x10 chain head: EX_PUSH_EXECUTION_FLOW continuation=0x18
///       0x11..0x15 continuation operand
///   0x15 EX_JUMP target=0x18 (chain body jump)
///       0x16..0x1a target operand
///   0x1a EX_POP_EXECUTION_FLOW (chain terminator)
///   0x18 EX_NOTHING (chain continuation pin body)
///   ...gap...
///   0x30 ELSE arm head (canonical chain shape, mirrors THEN)
///   0x30 EX_PUSH_EXECUTION_FLOW continuation=0x38
///       0x31..0x35 operand
///   0x35 EX_JUMP target=0x38
///       0x36..0x3a operand
///   0x3a EX_POP_EXECUTION_FLOW
///   0x38 EX_NOTHING
///   ...gap...
///   0x50 BARE-TRAMPOLINE arm head: EX_JUMP target=0x10
///       0x51..0x55 operand
///   ...gap...
///   0x70 JIN: EX_JUMP_IF_NOT target=0x30 (ELSE)
///       0x71..0x75 operand
///   0x75 EX_NOTHING (cond)
///   0x76 EX_JUMP target=0x50 (post-JIN, THEN target = trampoline)
///       0x77..0x7b operand
///   0x7b EX_END_OF_SCRIPT
#[test]
fn tail_jin_bare_trampoline_then_arm_decodes_chain_at_target() {
    let mut stream = vec![EX_NOTHING; 0x7c];
    // THEN arm body chain (target of the trampoline)
    stream[0x10] = EX_PUSH_EXECUTION_FLOW;
    stream[0x11..0x15].copy_from_slice(&u32_le(0x18));
    stream[0x15] = EX_JUMP;
    stream[0x16..0x1a].copy_from_slice(&u32_le(0x18));
    stream[0x1a] = EX_POP_EXECUTION_FLOW;
    stream[0x18] = EX_NOTHING;
    // ELSE arm head (canonical chain shape)
    stream[0x30] = EX_PUSH_EXECUTION_FLOW;
    stream[0x31..0x35].copy_from_slice(&u32_le(0x38));
    stream[0x35] = EX_JUMP;
    stream[0x36..0x3a].copy_from_slice(&u32_le(0x38));
    stream[0x3a] = EX_POP_EXECUTION_FLOW;
    stream[0x38] = EX_NOTHING;
    // Bare trampoline: EX_JUMP at 0x50 targeting THEN chain head at 0x10
    stream[0x50] = EX_JUMP;
    stream[0x51..0x55].copy_from_slice(&u32_le(0x10));
    // JIN at 0x70 (ELSE = 0x30)
    stream[0x70] = EX_JUMP_IF_NOT;
    stream[0x71..0x75].copy_from_slice(&u32_le(0x30));
    stream[0x75] = EX_NOTHING;
    stream[0x76] = EX_JUMP;
    stream[0x77..0x7b].copy_from_slice(&u32_le(0x50));
    stream[0x7b] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x7b).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x10..0x1b, 0x30..0x3b, 0x50..0x55, 0x70..0x7c];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    // tail_jin_arm_ranges should fire and report the THEN range as
    // [0x10, chain_end) (the chain at the trampoline target), not
    // the trampoline jump's range.
    let arms =
        tail_jin_arm_ranges(0x70, 0x7c, &ctx).expect("bare-trampoline arm should be recognised");
    let (then_start, then_end) = arms.then_range;
    let (else_start, else_end) = arms.else_range;
    assert_eq!(
        then_start, 0x10,
        "THEN arm head should move through trampoline to chain at 0x10"
    );
    assert!(
        then_end > then_start,
        "THEN arm should have non-empty extent, got {:#x}..{:#x}",
        then_start,
        then_end
    );
    assert_eq!(else_start, 0x30, "ELSE arm head should be canonical chain");
    assert!(
        else_end > else_start,
        "ELSE arm should have non-empty extent"
    );
}

/// Canonical chain-head tail-JIN (no trampoline). Regression check:
/// the existing shape (instrumentation + EX_PUSH_EXECUTION_FLOW at
/// the arm head) must still be recognised after the bare-trampoline
/// extension.
#[test]
fn tail_jin_chain_head_arm_still_recognised() {
    let mut stream = vec![EX_NOTHING; 0x7c];
    // THEN arm head: canonical chain
    stream[0x10] = EX_PUSH_EXECUTION_FLOW;
    stream[0x11..0x15].copy_from_slice(&u32_le(0x18));
    stream[0x15] = EX_JUMP;
    stream[0x16..0x1a].copy_from_slice(&u32_le(0x18));
    stream[0x1a] = EX_POP_EXECUTION_FLOW;
    stream[0x18] = EX_NOTHING;
    // ELSE arm head: canonical chain
    stream[0x30] = EX_PUSH_EXECUTION_FLOW;
    stream[0x31..0x35].copy_from_slice(&u32_le(0x38));
    stream[0x35] = EX_JUMP;
    stream[0x36..0x3a].copy_from_slice(&u32_le(0x38));
    stream[0x3a] = EX_POP_EXECUTION_FLOW;
    stream[0x38] = EX_NOTHING;
    // JIN at 0x70 (ELSE = 0x30)
    stream[0x70] = EX_JUMP_IF_NOT;
    stream[0x71..0x75].copy_from_slice(&u32_le(0x30));
    stream[0x75] = EX_NOTHING;
    stream[0x76] = EX_JUMP;
    // Post-JIN jump to canonical THEN head at 0x10 (no trampoline).
    stream[0x77..0x7b].copy_from_slice(&u32_le(0x10));
    stream[0x7b] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x7b).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x10..0x1b, 0x30..0x3b, 0x70..0x7c];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    let arms = tail_jin_arm_ranges(0x70, 0x7c, &ctx)
        .expect("canonical chain-head arm should still be recognised");
    assert_eq!(arms.then_range.0, 0x10);
    assert_eq!(arms.else_range.0, 0x30);
}

/// Bare-trampoline arm whose target is NOT a chain head (e.g. a
/// plain assignment / EX_NOTHING). Recogniser must decline.
#[test]
fn tail_jin_bare_trampoline_target_not_chain_head_declines() {
    let mut stream = vec![EX_NOTHING; 0x7c];
    // THEN arm trampoline target at 0x10 is just EX_NOTHING, not a
    // chain head.
    stream[0x10] = EX_NOTHING;
    // ELSE arm head: canonical chain (so only THEN side fails)
    stream[0x30] = EX_PUSH_EXECUTION_FLOW;
    stream[0x31..0x35].copy_from_slice(&u32_le(0x38));
    stream[0x35] = EX_JUMP;
    stream[0x36..0x3a].copy_from_slice(&u32_le(0x38));
    stream[0x3a] = EX_POP_EXECUTION_FLOW;
    stream[0x38] = EX_NOTHING;
    // Bare trampoline at 0x50 targeting non-chain-head 0x10
    stream[0x50] = EX_JUMP;
    stream[0x51..0x55].copy_from_slice(&u32_le(0x10));
    stream[0x70] = EX_JUMP_IF_NOT;
    stream[0x71..0x75].copy_from_slice(&u32_le(0x30));
    stream[0x75] = EX_NOTHING;
    stream[0x76] = EX_JUMP;
    stream[0x77..0x7b].copy_from_slice(&u32_le(0x50));
    stream[0x7b] = EX_END_OF_SCRIPT;

    let boundaries: Vec<usize> = (0..=0x7b).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x10..0x11, 0x30..0x3b, 0x50..0x55, 0x70..0x7c];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    assert!(
        tail_jin_arm_ranges(0x70, 0x7c, &ctx).is_none(),
        "bare-trampoline target that isn't a chain head must decline"
    );
}

/// Bare-trampoline whose target mem doesn't resolve via the
/// `mem_to_disk` map (e.g. cross-asset jump or stale operand).
/// Recogniser must decline.
#[test]
fn tail_jin_bare_trampoline_target_unresolved_declines() {
    let mut stream = vec![EX_NOTHING; 0x7c];
    // ELSE arm head: canonical chain
    stream[0x30] = EX_PUSH_EXECUTION_FLOW;
    stream[0x31..0x35].copy_from_slice(&u32_le(0x38));
    stream[0x35] = EX_JUMP;
    stream[0x36..0x3a].copy_from_slice(&u32_le(0x38));
    stream[0x3a] = EX_POP_EXECUTION_FLOW;
    stream[0x38] = EX_NOTHING;
    // Bare trampoline at 0x50 targeting an out-of-band mem 0xdead
    // that has no entry in the mem_to_disk map below.
    stream[0x50] = EX_JUMP;
    stream[0x51..0x55].copy_from_slice(&u32_le(0xdead));
    stream[0x70] = EX_JUMP_IF_NOT;
    stream[0x71..0x75].copy_from_slice(&u32_le(0x30));
    stream[0x75] = EX_NOTHING;
    stream[0x76] = EX_JUMP;
    stream[0x77..0x7b].copy_from_slice(&u32_le(0x50));
    stream[0x7b] = EX_END_OF_SCRIPT;

    // Identity map intentionally OMITS 0xdead so the trampoline
    // target translation fails.
    let boundaries: Vec<usize> = (0..=0x7b).collect();
    let map = identity_map(&boundaries);
    let names = empty_name_table();
    let owned: Vec<std::ops::Range<usize>> = vec![0x30..0x3b, 0x50..0x55, 0x70..0x7c];
    let claimed = std::cell::RefCell::new(BTreeMap::new());
    let ctx = ue4_ctx_with_owned_and_claimed(&stream, &names, &map, &owned, &claimed);

    assert!(
        tail_jin_arm_ranges(0x70, 0x7c, &ctx).is_none(),
        "bare-trampoline whose target mem doesn't resolve must decline"
    );
}

#[test]
fn cross_event_jump_target_emits_event_call() {
    // Layout: an EX_JUMP whose target equals event_2's mem entry.
    //   0x00 EX_JUMP target=0x10
    //   0x05 EX_END_OF_SCRIPT
    let mut stream = vec![EX_JUMP];
    stream.extend_from_slice(&u32_le(0x10));
    stream.push(EX_END_OF_SCRIPT);

    let mut map = BTreeMap::new();
    map.insert(0, 0);
    map.insert(5, 5);
    // 0x10 is in mem coords but not in this slice.
    let mut entries = BTreeMap::new();
    entries.insert(0x10usize, "EventTwo".to_string());

    let names = empty_name_table();
    let ctx = ue4_ctx_with_events(&stream, &names, &map, Some(&entries));

    let mut pos = 0;
    let stmt_opt = decode_jump(&mut pos, stream.len(), &ctx);
    match stmt_opt {
        Some(Stmt::EventCall { event_name, .. }) => {
            assert_eq!(event_name, "EventTwo");
        }
        other => panic!(
            "expected Stmt::EventCall, got {:?}",
            other.as_ref().map(stmt_kind)
        ),
    }
}

#[test]
fn region_arm_extents_walks_arms_bounded_by_exit() {
    use crate::bytecode::cfg::{BasicBlock, ControlFlowGraph};
    // Build a hand-rolled CFG:
    //   Block 0: 0x00..0x10 - JIN entry, succs [1, 3]
    //   Block 1: 0x10..0x18 - then-step-1, succ [2]
    //   Block 2: 0x18..0x20 - then-step-2, succ [4] (exit)
    //   Block 3: 0x20..0x28 - else, succ [4]
    //   Block 4: 0x28..0x30 - exit (region_exit)
    //   Block 5: synthetic sink, opcodes empty
    let specs: &[(usize, usize, &[usize])] = &[
        (0x00, 0x10, &[1, 3]),
        (0x10, 0x18, &[2]),
        (0x18, 0x20, &[4]),
        (0x20, 0x28, &[4]),
        (0x28, 0x30, &[]),
    ];
    let mut blocks: Vec<BasicBlock> = specs
        .iter()
        .enumerate()
        .map(|(id, &(start, end, _))| BasicBlock {
            id,
            start,
            end,
            opcodes: vec![start],
        })
        .collect();
    let sink_id = blocks.len();
    blocks.push(BasicBlock {
        id: sink_id,
        start: usize::MAX,
        end: usize::MAX,
        opcodes: Vec::new(),
    });
    let mut successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut predecessors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (id, &(_, _, succs)) in specs.iter().enumerate() {
        successors.insert(id, succs.to_vec());
        for &succ in succs {
            predecessors.entry(succ).or_default().push(id);
        }
    }
    successors.insert(4, vec![sink_id]);
    predecessors.entry(sink_id).or_default().push(4);
    successors.entry(sink_id).or_default();
    predecessors.entry(sink_id).or_default();
    let cfg = ControlFlowGraph {
        blocks,
        successors,
        predecessors,
        entry: 0,
        sink: sink_id,
    };
    // Then arm walks blocks 1 and 2; their adjacent ranges merge into
    // a single span. Else arm covers block 3 only. Unresolved arm
    // (None) yields an empty span list. Entry that IS the exit (4)
    // likewise produces empty.
    let extents = region_arm_extents(&[Some(1), Some(3), None, Some(4)], 4, &cfg);
    assert_eq!(extents[0], vec![0x10..0x20]);
    assert_eq!(extents[1], vec![0x20..0x28]);
    assert!(extents[2].is_empty());
    assert!(extents[3].is_empty());
}
