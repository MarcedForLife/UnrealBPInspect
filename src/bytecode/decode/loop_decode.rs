//! Loop recognition for the bytecode decoder.
//!
//! Recognises the back-edge shape whose head is `EX_JUMP_IF_NOT` and
//! emits `LoopKind::While` for every detected loop. The detection runs
//! before the regular `decode_branch` dispatch so a conditional whose
//! body terminates with a back-edge isn't first classified as an
//! if/else.
//!
//! Loop-shape refinement is split between this module and
//! `transforms::refine_loops`. The decoder owns the back-edge fast-path
//! (every recognised loop emits `LoopKind::While`); ForC and ForEach
//! refinement runs later in `transforms::refine_loops`, after
//! `inline_single_use_temps` has resolved condition temporaries. Both
//! halves are needed: this module preserves source-level shape from the
//! opcode stream, and `refine_loops` covers patterns that only become
//! visible once temp inlining has happened.

use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;
use crate::bytecode::stmt::{LoopKind, Stmt};

use super::branch::decode_subrange;
use super::ctx::{DecodeCtx, LoopBreakGuard, OwnerId};
use super::expr_decode::decode_expr;

/// Operand width for `EX_JUMP` / `EX_JUMP_IF_NOT`. Both encode a
/// `CodeSkipSizeType` (u32) in mem coordinates.
const JUMP_TARGET_BYTES: usize = 4;
/// Total byte length of a single `EX_JUMP` instruction (opcode +
/// target operand).
const JUMP_INSTR_BYTES: usize = 1 + JUMP_TARGET_BYTES;
/// Total byte length of a single `EX_PUSH_EXECUTION_FLOW` instruction.
/// Same operand layout as a jump: opcode + 4-byte target.
const PUSH_INSTR_BYTES: usize = 1 + JUMP_TARGET_BYTES;

/// Try to decode a loop construct at `*pos`. Returns `Some(Stmt::Loop)`
/// when the bytes form a recognisable While or ForC loop, with `*pos`
/// advanced past the entire loop. Returns `None` and leaves `*pos`
/// unchanged when the conditional isn't a loop head, so the caller can
/// fall through to `decode_branch`.
pub(crate) fn try_decode_loop(pos: &mut usize, range_end: usize, ctx: &DecodeCtx) -> Option<Stmt> {
    if *pos >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode.get(*pos)? != &EX_JUMP_IF_NOT {
        return None;
    }
    let head_offset = *pos;

    let body_start_disk = head_offset + 1 + JUMP_TARGET_BYTES;
    if body_start_disk >= range_end {
        return None;
    }

    // Peek the conditional's target without committing `*pos`. We need
    // both the condition expression and the body extent before deciding
    // whether the construct is a loop.
    let mut peek_cursor = head_offset + 1;
    let post_loop_target_mem = read_bc_u32(ctx.bytecode, &mut peek_cursor) as usize;
    let cond_expr_disk = peek_cursor;

    // The condition expression sits between the jump operand and the
    // body. Decoding it gives us the body-start disk position.
    let mut cond_cursor = cond_expr_disk;
    let cond = decode_expr(&mut cond_cursor, ctx);
    let body_disk = cond_cursor;
    if body_disk >= range_end {
        return None;
    }

    let back_edge = find_back_edge(ctx, body_disk, range_end, head_offset)?;

    // The body extends from after the cond expression up to the
    // back-edge `EX_JUMP` (exclusive). The post-loop position is the
    // disk index immediately after the back-edge instruction.
    let body_end_disk = back_edge.jump_disk;
    let resume_disk = back_edge.jump_disk + JUMP_INSTR_BYTES;
    if resume_disk > range_end {
        return None;
    }

    // A back-edge that lands right at body_disk means an empty body,
    // which real Blueprint loops never produce.
    if body_end_disk == body_disk {
        return None;
    }

    // Verify the EX_JUMP_IF_NOT skip target (when condition is false)
    // matches resume_disk. For a real loop, the skip target IS the
    // post-loop landing, so it resolves to the byte immediately after
    // the back-edge jump. Branch and guarded-event shapes skip to a
    // nearby continuation (far from any spurious back-edge), so their
    // skip target doesn't match the spurious resume.
    //
    // Translate the skip target from mem to disk. When it has no entry
    // in the map, there's no FName drift at that position and mem == disk,
    // so we use the raw mem coordinate directly.
    if let Some(mem_to_disk) = ctx.mem_to_disk {
        let post_loop_disk = mem_to_disk
            .get(&post_loop_target_mem)
            .copied()
            .unwrap_or(post_loop_target_mem);
        if post_loop_disk != resume_disk {
            // Nested-ForEach trampoline (gated, dispatch-scoped): a nested
            // ForEach carved as a disk-order sibling reaches the inner loop head during the
            // outer's displaced-body decode. Its JIN skip target is the
            // post-loop landing reached via the trampoline pop, which
            // legitimately differs from the back-edge resume. Bypass the
            // strict gate ONLY when the dispatch helper set
            // `loop_dispatch_relaxed` AND the skip target is a flow-pop
            // block (`EX_POP_EXECUTION_FLOW`) that converges to the loop
            // exit. `loop_dispatch_relaxed` is reachable from no path other
            // than `try_dispatch_loop_body_loop_region_at`, so the linear
            // sweep and sibling-walk callers keep the strict rejection and
            // no unrelated head (e.g. head=0x1140) is relaxed.
            if !(ctx.loop_dispatch_relaxed.get()
                && skip_target_is_flow_pop_block(ctx, post_loop_disk))
            {
                return None;
            }
        }
    }

    // ForEach loops emit the user-visible body via a trampoline
    // (EX_PUSH_EXECUTION_FLOW followed immediately by an EX_JUMP past
    // the back-edge) that returns to the increment via EX_POP_EXECUTION_FLOW.
    // When that pattern is present, splice the displaced block back into
    // the body so downstream ForEach refinement can see the index-fetch.
    let absorbed = absorb_displaced_body(
        ctx,
        head_offset,
        body_disk,
        body_end_disk,
        range_end,
        resume_disk,
    );
    // The disk byte ranges the loop body decode covers, in the order it
    // decodes them. For an absorbed ForEach trampoline these are three
    // disjoint ranges (pre-trampoline body, displaced block, increment);
    // for a contiguous loop, the single body range. The body-dedup claim
    // (below) registers each so the disk-order re-walk skips them instead
    // of re-emitting the body as a dead post-loop tail.
    let mut body_byte_ranges: Vec<(usize, usize)> = Vec::new();
    // Loop-break if/else: when the displaced body is a break if/else, its
    // inner break-test forms an `IfThenElse` region carved as a disk-order
    // sibling of the loop. The byte-range dedup claim below suppresses only
    // the disk-order sweep; it cannot stop the region walker from descending into that
    // sibling region and re-emitting the continue body as a post-loop guard.
    // Record the displaced range so the loop region's `Stmt::Loop` emit can
    // mark those sibling regions consumed (mirrors the nested-loop sibling
    // suppression in `try_dispatch_loop_body_loop_region_at`).
    let mut break_if_else_displaced: Option<(usize, usize)> = None;
    let (body_stmts, completion) = match absorbed {
        Some(layout) => decode_absorbed_loop_body(
            ctx,
            layout,
            body_disk,
            body_end_disk,
            head_offset,
            resume_disk,
            &mut body_byte_ranges,
            &mut break_if_else_displaced,
        ),
        None => {
            body_byte_ranges.push((body_disk, body_end_disk));
            (decode_subrange(body_disk, body_end_disk, ctx), None)
        }
    };

    // Body byte range is non-zero but every opcode is claim-owned by
    // another construct (e.g. DoOnce scaffold), so decoding produced no
    // statements. The JIN isn't actually a loop head, fall through to
    // normal branch decode instead of emitting an empty Loop that the
    // demote pass would later turn into an empty Branch.
    if body_stmts.is_empty() && body_end_disk > body_disk {
        return None;
    }

    register_loop_body_dedup_claims(ctx, &body_byte_ranges, break_if_else_displaced);

    // All loops are emitted as While here. ForC and ForEach refinement
    // runs in transforms::refine_loops after inline_single_use_temps
    // has resolved condition temporaries to their final shapes.
    *pos = resume_disk;

    Some(Stmt::Loop {
        kind: LoopKind::While,
        cond: Some(cond),
        body: body_stmts,
        completion,
        offset: head_offset,
    })
}

/// Decode the body and completion of an absorbed ForEach/ForC trampoline
/// loop from its `DisplacedBodyLayout`. Returns the body statements and the
/// optional completion block.
///
/// The three disjoint disk ranges the body spans (pre-trampoline body,
/// displaced block, increment) are appended to `body_byte_ranges` so the
/// disk-order re-walk skips them, and a loop-break if/else displaced range
/// is recorded in `break_if_else_displaced` for sibling-region suppression.
#[allow(clippy::too_many_arguments)]
fn decode_absorbed_loop_body(
    ctx: &DecodeCtx,
    layout: DisplacedBodyLayout,
    body_disk: usize,
    body_end_disk: usize,
    head_offset: usize,
    resume_disk: usize,
    body_byte_ranges: &mut Vec<(usize, usize)>,
    break_if_else_displaced: &mut Option<(usize, usize)>,
) -> (Vec<Stmt>, Option<Vec<Stmt>>) {
    body_byte_ranges.push((body_disk, layout.push_disk));
    body_byte_ranges.push((layout.displaced_start, layout.pop_disk));
    body_byte_ranges.push((layout.after_jump_disk, body_end_disk));
    if layout.break_if_else.is_some() {
        *break_if_else_displaced = Some((layout.displaced_start, layout.pop_disk));
    }
    // Execution order: pre-trampoline body, displaced block,
    // then the increment range that runs when the displaced
    // block's pop_flow returns to `after_jump_disk`. Keeping
    // the increment as the trailing statement preserves the
    // ForC discrimination that `transforms::refine_loops`
    // relies on.
    let mut stmts = decode_subrange(body_disk, layout.push_disk, ctx);
    if let Some(shape) = layout.break_if_else {
        // Loop-break if/else: the displaced block is a loop break if/else whose
        // break-test is an `EX_JUMP_IF_NOT` (not `EX_POP_FLOW_IF_NOT`,
        // so the flow-pop break-guard path never engages). Decode the
        // true-arm as `break` and the false-arm as the continue body.
        stmts.extend(decode_break_if_else(ctx, &layout, &shape));
    } else {
        // The displaced block may carry a loop-internal `if` break
        // guard: an `EX_POP_FLOW_IF_NOT` whose false path pops the
        // trampoline frame and resumes the loop increment rather than
        // closing a nested frame, so it has no balancing
        // `EX_POP_EXECUTION_FLOW`. Install the loop-break-guard context
        // so the naked-if recognizer can recover it, bounded by the
        // displaced terminator (`pop_disk`) and discriminated by the
        // continuation landing inside `[head_offset, resume_disk)`.
        let break_guard = break_guard_for_displaced_body(ctx, &layout, head_offset, resume_disk);
        let _break_guard_scope = break_guard.map(|guard| ctx.with_loop_break_guard(guard));
        stmts.extend(decode_subrange(
            layout.displaced_start,
            layout.pop_disk,
            ctx,
        ));
    }
    stmts.extend(decode_subrange(layout.after_jump_disk, body_end_disk, ctx));
    let completion = if layout.completion_start < layout.completion_end {
        let completion_block = decode_subrange(layout.completion_start, layout.completion_end, ctx);
        if completion_block.is_empty() {
            None
        } else {
            Some(completion_block)
        }
    } else {
        None
    };
    (stmts, completion)
}

/// Register dedup claims over a decoded loop's body byte ranges so the
/// region walker's disk-order sweep doesn't re-emit them as a dead
/// post-loop tail.
///
/// The body bytes are emitted inside the `Stmt::Loop` but `decode_subrange`
/// never claims them. Each range is marked claimed under the active loop
/// region owner (`loop_completion_region`, installed by `try_emit_loop_region`
/// or the nested/dual-role dispatch helpers).
///
/// When `break_if_else_displaced` is set, the break-test forms an
/// `IfThenElse` region carved as a disk-order sibling of the loop that
/// `mark_region_consumed` doesn't reach; mark every region whose entry
/// block falls inside the displaced range dispatched so the sibling walk
/// skips it (otherwise the continue body re-emits as a post-loop guard).
fn register_loop_body_dedup_claims(
    ctx: &DecodeCtx,
    body_byte_ranges: &[(usize, usize)],
    break_if_else_displaced: Option<(usize, usize)>,
) {
    if let Some(region_id) = ctx.loop_completion_region.get() {
        for &(range_start, range_end_disk) in body_byte_ranges {
            super::ctx::mark_claimed(
                ctx,
                range_start,
                range_end_disk,
                OwnerId::CfgRegion { region_id },
            );
        }
    }

    if let (Some((displaced_start, displaced_end)), Some(cfg), Some(region_tree)) =
        (break_if_else_displaced, ctx.cfg, ctx.region_tree)
    {
        let mut dispatched = ctx.dispatched_loop_regions.borrow_mut();
        for (region_id, region) in region_tree.regions.iter().enumerate() {
            let Some(entry_block) = cfg.blocks.get(region.entry) else {
                continue;
            };
            if entry_block.start >= displaced_start && entry_block.start < displaced_end {
                dispatched.insert(region_id);
            }
        }
    }
}

/// Disk-coordinate layout of an absorbed displaced ForEach body.
struct DisplacedBodyLayout {
    /// Disk offset of the `EX_PUSH_EXECUTION_FLOW` opcode at the end of
    /// the in-range body. Body content stops here.
    push_disk: usize,
    /// Disk offset of the byte immediately after the trampoline EX_JUMP.
    /// The increment range begins here and runs to the back-edge.
    after_jump_disk: usize,
    /// Disk offset where the displaced block starts (target of the
    /// EX_JUMP that follows the push_flow).
    displaced_start: usize,
    /// Disk offset of the `EX_POP_EXECUTION_FLOW` that terminates the
    /// displaced block. Body content from the displaced range stops here.
    pop_disk: usize,
    /// Disk offset where the post-back-edge completion range begins.
    /// Equals the byte after the back-edge `EX_JUMP`.
    completion_start: usize,
    /// Disk offset where the completion range ends (exclusive).
    /// Equals `displaced_start`.
    completion_end: usize,
    /// When `Some`, the displaced block is a loop break if/else: an
    /// `EX_JUMP_IF_NOT` break-test whose true-arm sets the break flag and
    /// resumes the trampoline frame (the break path), and whose false-arm
    /// runs the loop's continue body. The displaced block has TWO
    /// `EX_POP_EXECUTION_FLOW` (one per arm); `pop_disk` is extended to the
    /// LAST so the whole if/else is in range. `try_decode_loop` decodes the
    /// false-arm as the else and synthesizes `Stmt::Break` for the true-arm.
    break_if_else: Option<BreakIfElse>,
}

/// Disk-coordinate layout of a loop break if/else inside a displaced
/// ForEach/ForC body. The break-test is an `EX_JUMP_IF_NOT`
/// (a normal Branch), NOT an `EX_POP_FLOW_IF_NOT`, so the existing
/// `EX_POP_FLOW_IF_NOT`-keyed break-guard recogniser never fires on it.
#[derive(Clone, Copy, Debug)]
struct BreakIfElse {
    /// Disk offset of the `EX_JUMP_IF_NOT` break-test opcode.
    break_test_disk: usize,
    /// Disk offset of the false-arm (continue body) start. This is the
    /// break-test's skip target: where execution lands when the break
    /// condition is false.
    false_arm_start: usize,
    /// Disk offset of the false-arm's terminating `EX_POP_EXECUTION_FLOW`
    /// (the last pop). The whole displaced block ends one byte past this.
    last_pop: usize,
}

/// Look for the trampoline shape inside `[body_start..body_end)`:
/// an `EX_PUSH_EXECUTION_FLOW` whose immediate next opcode is an
/// `EX_JUMP` past `body_end`, where the displaced target's block
/// terminates with `EX_POP_EXECUTION_FLOW` (canonical) or with the
/// function epilogue's pop / `EX_RETURN` / `EX_END_OF_SCRIPT`
/// (break-with-flag), and the push's resume target either lands
/// at the increment (canonical) or back at the loop head
/// (break-with-flag).
///
/// Returns the absorbed body layout when the pattern matches; returns
/// `None` (caller falls through to the existing While/ForC behaviour)
/// when the shape isn't a recognisable displaced-body trampoline.
fn absorb_displaced_body(
    ctx: &DecodeCtx,
    loop_head_disk: usize,
    body_start: usize,
    body_end: usize,
    range_end: usize,
    back_edge_end: usize,
) -> Option<DisplacedBodyLayout> {
    let mem_to_disk = ctx.mem_to_disk?;

    // Walk the loop body looking for the trampoline. The push_flow must
    // be followed (at the next opcode boundary, ignoring instrumentation)
    // by an EX_JUMP whose target lies past back_edge_end and inside
    // range_end.
    let mut cursor = body_start;
    while cursor < body_end {
        if cursor >= ctx.bytecode.len() {
            return None;
        }
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_PUSH_EXECUTION_FLOW {
            if let Some(layout) = match_trampoline_at(
                ctx,
                cursor,
                loop_head_disk,
                body_end,
                range_end,
                back_edge_end,
                mem_to_disk,
            ) {
                return Some(layout);
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// Validate the trampoline pattern starting at `push_disk` and build
/// the absorbed-body layout if every sanity check passes.
///
/// The trampoline fingerprint is push followed (after instrumentation)
/// by an `EX_JUMP` whose target lies past the back-edge and inside
/// `range_end`. The push's resume target is permissive, two real shapes
/// appear in fixtures:
///
/// - Canonical ForEach: resume lands at the byte after the trampoline
///   jump (the increment runs on every iteration).
/// - Break-with-flag ForEach: resume lands at or before the loop head
///   (the cond is re-checked each iteration).
///
/// The displaced block can terminate either at an inner
/// `EX_POP_EXECUTION_FLOW` (canonical) or, when iteration is gated by
/// `EX_POP_FLOW_IF_NOT` and break paths jump straight to the function
/// epilogue, at the first reachable `EX_POP_EXECUTION_FLOW` / `EX_RETURN`
/// / `EX_END_OF_SCRIPT`.
fn match_trampoline_at(
    ctx: &DecodeCtx,
    push_disk: usize,
    loop_head_disk: usize,
    body_end: usize,
    range_end: usize,
    back_edge_end: usize,
    mem_to_disk: &std::collections::BTreeMap<usize, usize>,
) -> Option<DisplacedBodyLayout> {
    if push_disk + PUSH_INSTR_BYTES > body_end {
        return None;
    }
    let mut peek = push_disk + 1;
    let resume_target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;

    // Skip any FName-drift padding and instrumentation opcodes the
    // partition introduces between the push and its paired EX_JUMP.
    let jump_disk = next_opcode_after(ctx, push_disk, body_end)?;
    if jump_disk >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode[jump_disk] != EX_JUMP {
        return None;
    }
    if jump_disk + JUMP_INSTR_BYTES > body_end {
        return None;
    }
    let mut jump_peek = jump_disk + 1;
    let displaced_target_mem = read_bc_u32(ctx.bytecode, &mut jump_peek) as usize;
    let after_jump_disk = jump_disk + JUMP_INSTR_BYTES;

    let resume_disk = mem_to_disk
        .get(&resume_target_mem)
        .copied()
        .unwrap_or(resume_target_mem);

    // Resume must either land at the increment (canonical) or at/before
    // the loop head (break-with-flag re-checks cond on each iteration).
    // Anything else isn't a foreach trampoline.
    let resume_at_increment = resume_disk == after_jump_disk;
    let resume_in_head_region = resume_disk <= loop_head_disk;
    if !(resume_at_increment || resume_in_head_region) {
        return None;
    }

    // The displaced target must land past the back-edge and within range.
    let displaced_disk = mem_to_disk
        .get(&displaced_target_mem)
        .copied()
        .unwrap_or(displaced_target_mem);
    if displaced_disk < back_edge_end || displaced_disk >= range_end {
        return None;
    }

    // Find the displaced block's terminator. Real fixtures use either an
    // inner `EX_POP_EXECUTION_FLOW` or, when break paths jump straight to
    // the function epilogue, the function's `EX_RETURN` / `EX_END_OF_SCRIPT`.
    let terminator_disk = scan_for_displaced_terminator(ctx, displaced_disk, range_end)?;

    // Loop-break if/else: the displaced block may be a loop break if/else whose true-arm
    // (break) and false-arm (continue body) each terminate with their own
    // `EX_POP_EXECUTION_FLOW`. `scan_for_displaced_terminator` stops at the
    // FIRST pop (the true-arm terminator), which truncates the if/else
    // mid-way. When the break-if/else shape is present, extend the displaced
    // terminator to the LAST pop so the whole construct is in range.
    let break_if_else = detect_break_if_else(ctx, displaced_disk, terminator_disk, range_end);
    let pop_disk = break_if_else.map_or(terminator_disk, |shape| shape.last_pop);

    Some(DisplacedBodyLayout {
        push_disk,
        after_jump_disk,
        displaced_start: displaced_disk,
        pop_disk,
        completion_start: back_edge_end,
        completion_end: displaced_disk,
        break_if_else,
    })
}

/// Detect the loop break if/else shape inside a displaced ForEach/ForC
/// body whose first terminator is `first_pop` (the value
/// `scan_for_displaced_terminator` returned).
///
/// The fingerprint: an `EX_JUMP_IF_NOT` break-test before `first_pop` whose
/// skip target lands one byte past `first_pop` (so the true-arm ends at
/// `first_pop` and the false-arm begins right after it), and whose false-arm
/// terminates with a second `EX_POP_EXECUTION_FLOW`. Both arms resume the
/// same trampoline frame: the true-arm has set the loop's break flag (so the
/// recheck exits), the false-arm has not (so iteration continues).
///
/// Returns `None` when the displaced block is the canonical single-pop
/// ForEach body or any other shape, leaving the existing first-pop bound
/// (and the `EX_POP_FLOW_IF_NOT`-keyed break-guard path) untouched. The gate
/// is the `EX_JUMP_IF_NOT`-opens-the-break-test discriminator: real
/// flow-pop break loops use `EX_POP_FLOW_IF_NOT` and never match here.
fn detect_break_if_else(
    ctx: &DecodeCtx,
    displaced_start: usize,
    first_pop: usize,
    range_end: usize,
) -> Option<BreakIfElse> {
    // The true-arm terminator must itself be an `EX_POP_EXECUTION_FLOW`
    // (the break path). `scan_for_displaced_terminator` also accepts
    // `EX_RETURN` / `EX_END_OF_SCRIPT`; those are the function-epilogue
    // break shape, not this two-pop continue/break if/else.
    if ctx.bytecode.get(first_pop)? != &EX_POP_EXECUTION_FLOW {
        return None;
    }
    let false_arm_start = first_pop + 1;
    if false_arm_start >= range_end {
        return None;
    }

    // Walk `[displaced_start, first_pop)` for the break-test: an
    // `EX_JUMP_IF_NOT` whose skip target is exactly `false_arm_start`.
    // Tracking opcode boundaries keeps a nested operand from masquerading
    // as the JIN opcode byte.
    let break_test_disk = find_break_test(ctx, displaced_start, first_pop, false_arm_start)?;

    // The false-arm must terminate with its own `EX_POP_EXECUTION_FLOW`.
    let last_pop = scan_for_displaced_terminator(ctx, false_arm_start, range_end)?;
    if ctx.bytecode.get(last_pop)? != &EX_POP_EXECUTION_FLOW {
        return None;
    }

    Some(BreakIfElse {
        break_test_disk,
        false_arm_start,
        last_pop,
    })
}

/// Scan `[start, end)` for the loop-break break-test: an `EX_JUMP_IF_NOT` whose
/// resolved skip target is `expected_skip_disk` (the false-arm / continue
/// start) AND whose true-arm `[JIN, first_pop)` is a flat break-flag-set, not
/// a nested loop head.
///
/// The true-arm must NOT contain an `EX_PUSH_EXECUTION_FLOW` (a trampoline,
/// i.e. a nested loop / Sequence) nor a back-edge `EX_JUMP` (target at or
/// before the candidate JIN, i.e. the candidate is itself a loop head). The
/// nested-loop discriminator is what keeps `Loop_ForEachNested` from matching:
/// its OUTER displaced body holds the INNER loop, whose head JIN skips to the
/// outer's continue landing (so the skip-target check alone would match the
/// inner head), but the inner head's true-arm carries the inner trampoline and
/// back-edge, which this rejects.
fn find_break_test(
    ctx: &DecodeCtx,
    start: usize,
    end: usize,
    expected_skip_disk: usize,
) -> Option<usize> {
    let mem_to_disk = ctx.mem_to_disk?;
    let mut cursor = start;
    while cursor < end {
        if cursor >= ctx.bytecode.len() {
            return None;
        }
        if ctx.bytecode[cursor] == EX_JUMP_IF_NOT {
            let mut peek = cursor + 1;
            let skip_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let skip_disk = mem_to_disk.get(&skip_mem).copied().unwrap_or(skip_mem);
            if skip_disk == expected_skip_disk && !true_arm_is_loop_head(ctx, cursor, end) {
                return Some(cursor);
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// True when the candidate break-test JIN at `jin_disk` is actually a loop
/// head: its true-arm `[after JIN, true_arm_end)` contains an
/// `EX_PUSH_EXECUTION_FLOW` (a nested trampoline) or a back-edge `EX_JUMP`
/// (target at or before `jin_disk`). A real loop-break break-flag-set true-arm has
/// neither, so this returns false for it.
fn true_arm_is_loop_head(ctx: &DecodeCtx, jin_disk: usize, true_arm_end: usize) -> bool {
    let mem_to_disk = ctx.mem_to_disk;
    let scan_end = true_arm_end.min(ctx.bytecode.len());
    let mut cursor = jin_disk + 1 + JUMP_TARGET_BYTES;
    while cursor < scan_end {
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_PUSH_EXECUTION_FLOW {
            return true;
        }
        if opcode == EX_JUMP && cursor + JUMP_INSTR_BYTES <= scan_end {
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let target_disk = mem_to_disk
                .and_then(|map| map.get(&target_mem).copied())
                .unwrap_or(target_mem);
            if target_disk <= jin_disk {
                return true;
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return true;
        }
        cursor += length;
    }
    false
}

/// Decode a displaced loop break if/else into statements: any pre-arm
/// code, then a `Branch` whose true-arm is `Stmt::Break` (the break-flag
/// set in the bytecode true-arm) and whose false-arm is the loop's continue
/// body.
///
/// The break-test is `layout.break_if_else`'s `EX_JUMP_IF_NOT`. Its cond
/// expression sits after the opcode + 4-byte skip operand, mirroring the
/// loop-head layout in `try_decode_loop`. The true-arm bytes only set the
/// loop's break flag (a compiler bookkeeping LET the editor graph models as
/// the `break` pin), so they are dropped in favour of a synthesized
/// `Stmt::Break`. The false-arm decodes via `decode_subrange`, the same path
/// every other body range uses, so nested constructs recurse normally.
fn decode_break_if_else(
    ctx: &DecodeCtx,
    layout: &DisplacedBodyLayout,
    shape: &BreakIfElse,
) -> Vec<Stmt> {
    // Pre-arm code between the displaced block start and the break-test
    // (e.g. a shared array-element fetch). For the observed ForEach/ForC
    // break loops this is loop-internal bookkeeping the refiner folds away;
    // decoding it here keeps it in the body so a future shape that carries
    // real pre-arm statements does not silently drop them.
    let mut stmts = decode_subrange(layout.displaced_start, shape.break_test_disk, ctx);

    let cond_disk = shape.break_test_disk + 1 + JUMP_TARGET_BYTES;
    let mut cond_cursor = cond_disk;
    let cond = decode_expr(&mut cond_cursor, ctx);

    let else_body = decode_subrange(shape.false_arm_start, shape.last_pop, ctx);

    stmts.push(Stmt::Branch {
        cond,
        then_body: vec![Stmt::Break {
            offset: shape.break_test_disk,
        }],
        else_body,
        offset: shape.break_test_disk,
    });
    stmts
}

/// Build the loop-break-guard context for an absorbed ForEach loop's
/// displaced body, or `None` when there is no active loop region to own
/// the recovered guard's body claim.
///
/// The guard's true-body is bounded by the displaced terminator
/// (`pop_disk`, the loop continue point). The discriminator scope is
/// `[head_offset, resume_disk)`. The false-path continuation is the
/// trampoline frame's pushed target (the loop increment the matching pop
/// resumes), read from the trampoline `EX_PUSH_EXECUTION_FLOW` operand.
///
/// The owning region comes from `ctx.loop_completion_region` (the active
/// `RegionKind::Loop` being emitted). Without it there is no stable owner
/// for the dedup claim, so the recogniser's loop fallback stays dormant.
fn break_guard_for_displaced_body(
    ctx: &DecodeCtx,
    layout: &DisplacedBodyLayout,
    head_offset: usize,
    resume_disk: usize,
) -> Option<LoopBreakGuard> {
    let region_id = ctx.loop_completion_region.get()?;
    let mut peek = layout.push_disk + 1;
    let continuation_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
    let continuation = ctx
        .mem_to_disk
        .and_then(|map| map.get(&continuation_mem).copied())
        .unwrap_or(continuation_mem);
    Some(LoopBreakGuard {
        tail: layout.pop_disk,
        scope_start: head_offset,
        scope_end: resume_disk,
        continuation,
        displaced_start: layout.displaced_start,
        owner: OwnerId::CfgRegion { region_id },
    })
}

/// Return the disk offset of the next *non-instrumentation* opcode after
/// `from`, bounded by `limit`. Skips `EX_WIRE_TRACEPOINT`,
/// `EX_TRACEPOINT`, and `EX_INSTRUMENTATION_EVENT` so the trampoline
/// match isn't fooled by editor-emitted bookkeeping between the push
/// and its paired EX_JUMP.
fn next_opcode_after(ctx: &DecodeCtx, from: usize, limit: usize) -> Option<usize> {
    let length = opcode_length_at(from, ctx.bytecode, ctx.ue5, ctx.name_table);
    if length == 0 {
        return None;
    }
    let mut cursor = from + length;
    while cursor < limit {
        let opcode = *ctx.bytecode.get(cursor)?;
        if !is_instrumentation_opcode(opcode) {
            return Some(cursor);
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// True for opcodes that carry no semantic content and live between
/// real statements. Tracepoint and wire-tracepoint markers are emitted
/// by the editor for runtime debugging and are dropped by `decode_one`
/// elsewhere; for trampoline matching we step past them too.
fn is_instrumentation_opcode(opcode: u8) -> bool {
    matches!(
        opcode,
        EX_WIRE_TRACEPOINT | EX_TRACEPOINT | EX_INSTRUMENTATION_EVENT
    )
}

/// Scan forward from `start` for the first flow-control terminator that
/// can end a foreach displaced block: an `EX_POP_EXECUTION_FLOW`
/// (canonical, the trampoline's pop_flow back to the increment), an
/// `EX_RETURN`, or an `EX_END_OF_SCRIPT` (break-with-flag, when the
/// displaced block exits via the function epilogue without an inner
/// pop). The walk is bounded by `range_end` (the partition's upper
/// bound, e.g. the next loop head or the function's bytecode end).
/// Returns `None` if no terminator is reached before `range_end` or any
/// opcode reports zero length. Takes the first matching statement without
/// nesting bookkeeping.
fn scan_for_displaced_terminator(ctx: &DecodeCtx, start: usize, range_end: usize) -> Option<usize> {
    let mut cursor = start;
    while cursor < range_end {
        if cursor >= ctx.bytecode.len() {
            return None;
        }
        let opcode = ctx.bytecode[cursor];
        if matches!(opcode, EX_POP_EXECUTION_FLOW | EX_RETURN | EX_END_OF_SCRIPT) {
            return Some(cursor);
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
    }
    None
}

/// Nested-ForEach trampoline (gated): true when the basic block starting at
/// `skip_disk` (the `EX_JUMP_IF_NOT` skip target) terminates with `EX_POP_EXECUTION_FLOW`.
/// This is the narrow displaced-trampoline shape: the inner ForEach's
/// false-path lands on a flow-pop block that converges to the loop exit,
/// so its skip target legitimately differs from the back-edge resume. The
/// block start byte is usually instrumentation (tracepoint), so the check
/// looks at the block's TERMINATOR opcode, not the start byte.
///
/// Reached only when `loop_dispatch_relaxed` is set (the nested-ForEach dispatch
/// helper's `try_emit_loop_region` call), so it scopes the gate bypass to
/// the inner-loop dispatch and leaves every other caller on the strict
/// `post_loop_disk == resume_disk` rejection.
fn skip_target_is_flow_pop_block(ctx: &DecodeCtx, skip_disk: usize) -> bool {
    let Some(cfg) = ctx.cfg else {
        return false;
    };
    let Some(block) = cfg.blocks.iter().find(|block| block.start == skip_disk) else {
        return false;
    };
    let Some(&terminator_addr) = block.opcodes.last() else {
        return false;
    };
    ctx.bytecode.get(terminator_addr).copied() == Some(EX_POP_EXECUTION_FLOW)
}

/// Description of a back-edge `EX_JUMP` at the trailing edge of a loop
/// body.
struct BackEdge {
    /// Disk position of the `EX_JUMP` opcode byte.
    jump_disk: usize,
}

/// Walk forward from `body_start` looking for an `EX_JUMP` whose target
/// is at or before `head_offset` (i.e. a back-edge into the loop head)
/// AND that lands at `range_end` or at the byte immediately before a
/// reachable statement boundary. Returns the back-edge with the
/// largest disk position so an inner loop's back-edge inside the body
/// doesn't get picked up as the outer's terminator.
///
/// The walk respects `opcode_length_at` so nested constructs don't
/// contribute spurious matches: every byte we examine is the start of
/// an opcode, not an operand.
fn find_back_edge(
    ctx: &DecodeCtx,
    body_start: usize,
    range_end: usize,
    head_offset: usize,
) -> Option<BackEdge> {
    let mut cursor = body_start;
    let mut last: Option<BackEdge> = None;
    while cursor < range_end {
        if cursor >= ctx.bytecode.len() {
            break;
        }
        let opcode = ctx.bytecode[cursor];
        if opcode == EX_JUMP && cursor + JUMP_INSTR_BYTES <= range_end {
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            if is_back_edge_target(target_mem, head_offset, ctx) {
                last = Some(BackEdge { jump_disk: cursor });
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }
    last
}

/// True when `target_mem` resolves to a disk offset at or before
/// `head_offset`. Blueprint loops can have setup code between the
/// back-edge target and the `EX_JUMP_IF_NOT`, so any backward jump is
/// a candidate. The real discriminator (skip target == resume) is
/// applied in `try_decode_loop` after the back-edge is found.
///
/// The `mem_to_disk` lookup is the preferred path because mem and disk
/// diverge in ubergraph bodies; the raw comparison is the fallback for
/// standalone function bodies where mem == disk.
fn is_back_edge_target(target_mem: usize, head_offset: usize, ctx: &DecodeCtx) -> bool {
    if let Some(mem_to_disk) = ctx.mem_to_disk {
        if let Some(&target_disk) = mem_to_disk.get(&target_mem) {
            return target_disk <= head_offset;
        }
    }
    target_mem <= head_offset
}

/// Disk-coordinate layout of a rotated-trampoline (do-while) ForEach whose
/// trampoline PUSH lives in the pre-header/increment block, OUTSIDE the
/// loop head's true-edge body slice. `absorb_displaced_body` cannot see it
/// (the PUSH isn't in `[body_disk, body_end_disk)`), so the canonical
/// ForEach absorption never engages and the body is hoisted out with a
/// detached `IntArray[0]`. This layout records the loop's structural
/// extents so the rotated emit can splice the element-index fetch, the
/// displaced user body (the sibling regions reached via the pre-header
/// trampoline), and the increment into one `While` the loop refiner lifts
/// to `ForEach`.
///
/// Shape (BP_DecoderTest `Latch_DoOnceInForEach`, head JIN `0xa1e`):
/// - `head_offset` JIN: false edge -> `exit_disk` (a POP block, the loop
///   exit), true edge -> body block (`[body_start, body_end)`, the
///   element-index fetch).
/// - body block ends in a back-edge `EX_JUMP` (`back_edge_disk`) whose
///   target is `preheader_disk` (`<= head_offset`).
/// - `preheader_disk` block STARTS with `EX_PUSH_EXECUTION_FLOW` whose
///   resume target (`increment_start`) is the increment, and whose pushed
///   continuation chains (through further trampoline jumps) to the
///   displaced user body. The increment falls through to the head.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RotatedTrampolineLayout {
    /// JIN loop-head disk offset. The cond expression is decoded from here
    /// and the increment range ends at this block's start.
    pub head_offset: usize,
    /// Disk offset of the body back-edge `EX_JUMP` opcode. The head's
    /// element-index fetch runs `[body_start, back_edge_disk)`.
    pub back_edge_disk: usize,
    /// Disk offset where the head's true-edge body (the element-index
    /// fetch) begins. Equals the disk position immediately after the loop
    /// head's condition expression.
    pub body_start: usize,
    /// Disk offset where the increment block begins (the pre-header PUSH's
    /// resume target). The increment runs to the loop-head block start.
    pub increment_start: usize,
}

/// Detect the rotated-trampoline (do-while) ForEach shape at a loop-head
/// `EX_JUMP_IF_NOT` whose entry block is `head_offset`. Returns the layout
/// when the positive discriminator holds, `None` otherwise.
///
/// Positive discriminator (every clause must hold; designed to fire ONLY
/// on the rotated shape and NEVER on an in-body-absorbed canonical ForEach,
/// whose PUSH sits inside the head's true-edge body slice):
/// 1. head terminator is `EX_JUMP_IF_NOT`; its false-edge skip target
///    resolves to a block that STARTS with `EX_POP_EXECUTION_FLOW` (the
///    loop exit reached by the trampoline pop).
/// 2. the head's true-edge body has a back-edge `EX_JUMP` whose target
///    block (`preheader`) starts at or before `head_offset` AND STARTS with
///    `EX_PUSH_EXECUTION_FLOW`.
/// 3. that pre-header PUSH's resume target re-enters the loop head region
///    (`<= head_offset`), i.e. the increment block that falls through to
///    the head.
/// 4. `absorb_displaced_body` finds NO in-body trampoline in the head's
///    true-edge body slice. This is the discriminating negative gate: a
///    canonical in-body ForEach has its PUSH inside the slice, so this
///    clause is false for all 18 working loops and they are never touched.
pub(crate) fn detect_rotated_trampoline(
    ctx: &DecodeCtx,
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    head_offset: usize,
    range_end: usize,
) -> Option<RotatedTrampolineLayout> {
    let mem_to_disk = ctx.mem_to_disk?;
    if ctx.bytecode.get(head_offset)? != &EX_JUMP_IF_NOT {
        return None;
    }

    // Resolve the JIN false-edge skip target and its block; it must start
    // with EX_POP_EXECUTION_FLOW (the loop exit, reached via the pop).
    let mut head_peek = head_offset + 1;
    let skip_target_mem = read_bc_u32(ctx.bytecode, &mut head_peek) as usize;
    let cond_expr_disk = head_peek;
    let exit_disk = mem_to_disk
        .get(&skip_target_mem)
        .copied()
        .unwrap_or(skip_target_mem);
    if block_start_opcode(cfg, ctx, exit_disk) != Some(EX_POP_EXECUTION_FLOW) {
        return None;
    }

    // The true-edge body starts after the condition expression.
    let mut cond_cursor = cond_expr_disk;
    let _ = decode_expr(&mut cond_cursor, ctx);
    let body_disk = cond_cursor;
    if body_disk >= range_end {
        return None;
    }

    // The body's back-edge EX_JUMP whose target is the PUSH-head pre-header.
    let back_edge = find_rotated_back_edge(ctx, cfg, body_disk, range_end, head_offset)?;
    let body_end = back_edge.jump_disk;
    if body_end <= body_disk {
        return None;
    }
    let mut be_peek = back_edge.jump_disk + 1;
    let preheader_mem = read_bc_u32(ctx.bytecode, &mut be_peek) as usize;
    let preheader_disk = mem_to_disk
        .get(&preheader_mem)
        .copied()
        .unwrap_or(preheader_mem);
    if preheader_disk > head_offset {
        return None;
    }
    // The pre-header block must START with EX_PUSH_EXECUTION_FLOW: the
    // trampoline that pushes the increment as the resume frame and chains
    // execution to the displaced user body. This is what places the PUSH
    // OUTSIDE the head's body slice and defeats `absorb_displaced_body`.
    if block_start_opcode(cfg, ctx, preheader_disk) != Some(EX_PUSH_EXECUTION_FLOW) {
        return None;
    }

    // The pre-header PUSH's resume target re-enters the loop head region.
    // The PUSH opcode is the first non-instrumentation opcode of the
    // pre-header block, which may be one byte past `preheader_disk` when the
    // block leads with a tracepoint.
    let push_addr = block_start_opcode_addr(cfg, ctx, preheader_disk)?;
    let mut push_peek = push_addr + 1;
    let resume_mem = read_bc_u32(ctx.bytecode, &mut push_peek) as usize;
    let resume_disk = mem_to_disk.get(&resume_mem).copied().unwrap_or(resume_mem);
    if resume_disk > head_offset {
        return None;
    }

    // Negative gate: the canonical in-body trampoline must be ABSENT inside
    // the head's true-edge body slice. The resume immediately after the
    // back-edge is the increment block; pass it as `back_edge_end`.
    let back_edge_end = back_edge.jump_disk + JUMP_INSTR_BYTES;
    if absorb_displaced_body(
        ctx,
        head_offset,
        body_disk,
        body_end,
        range_end,
        back_edge_end,
    )
    .is_some()
    {
        return None;
    }

    Some(RotatedTrampolineLayout {
        head_offset,
        back_edge_disk: back_edge.jump_disk,
        body_start: body_disk,
        increment_start: resume_disk,
    })
}

/// Decode the condition expression of a rotated-trampoline loop head. The
/// JIN at `head_offset` has the `counter < Array_Length(array)` condition
/// expression immediately after its 4-byte skip operand, mirroring the
/// canonical loop-head layout. Returns the decoded `Expr` for the `While`
/// the rotated emit produces (which `refine_loops` then lifts to ForEach).
pub(crate) fn rotated_loop_cond(ctx: &DecodeCtx, head_offset: usize) -> Option<Stmt> {
    if ctx.bytecode.get(head_offset)? != &EX_JUMP_IF_NOT {
        return None;
    }
    let cond_disk = head_offset + 1 + JUMP_TARGET_BYTES;
    let mut cursor = cond_disk;
    let cond = decode_expr(&mut cursor, ctx);
    Some(Stmt::Loop {
        kind: LoopKind::While,
        cond: Some(cond),
        body: Vec::new(),
        completion: None,
        offset: head_offset,
    })
}

/// Walk `[body_start, range_end)` for the rotated-shape body back-edge: the
/// FIRST `EX_JUMP` whose resolved target is at or before `head_offset` AND
/// whose target block STARTS with `EX_PUSH_EXECUTION_FLOW` (the pre-header
/// trampoline). Unlike `find_back_edge`, which takes the largest-disk
/// candidate, this targets the pre-header that closes the loop head's
/// true-edge body. The first such jump is the body terminator; later jumps
/// to PUSH-head blocks (`0xa74`, `0xacb` in `Latch_DoOnceInForEach`) belong
/// to the post-loop pre-header/exit trampoline chain, not the body.
fn find_rotated_back_edge(
    ctx: &DecodeCtx,
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    body_start: usize,
    range_end: usize,
    head_offset: usize,
) -> Option<BackEdge> {
    let mem_to_disk = ctx.mem_to_disk?;
    let mut cursor = body_start;
    while cursor < range_end {
        if cursor >= ctx.bytecode.len() {
            break;
        }
        if ctx.bytecode[cursor] == EX_JUMP && cursor + JUMP_INSTR_BYTES <= range_end {
            let mut peek = cursor + 1;
            let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
            let target_disk = mem_to_disk.get(&target_mem).copied().unwrap_or(target_mem);
            if target_disk <= head_offset
                && block_start_opcode(cfg, ctx, target_disk) == Some(EX_PUSH_EXECUTION_FLOW)
            {
                return Some(BackEdge { jump_disk: cursor });
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }
    None
}

/// Opcode byte that the block starting exactly at `start_disk` begins with,
/// skipping a leading instrumentation opcode (tracepoint/wire-tracepoint).
/// Returns `None` when no block starts there or the block is empty.
fn block_start_opcode(
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    ctx: &DecodeCtx,
    start_disk: usize,
) -> Option<u8> {
    let addr = block_start_opcode_addr(cfg, ctx, start_disk)?;
    ctx.bytecode.get(addr).copied()
}

/// Disk ADDRESS of the first non-instrumentation opcode in the block
/// starting exactly at `start_disk`. Differs from `block.start` when the
/// block leads with a tracepoint/wire-tracepoint. Returns `None` when no
/// block starts there or every opcode is instrumentation.
fn block_start_opcode_addr(
    cfg: &crate::bytecode::cfg::ControlFlowGraph,
    ctx: &DecodeCtx,
    start_disk: usize,
) -> Option<usize> {
    let block = cfg.blocks.iter().find(|block| block.start == start_disk)?;
    for &addr in &block.opcodes {
        let opcode = *ctx.bytecode.get(addr)?;
        if !is_instrumentation_opcode(opcode) {
            return Some(addr);
        }
    }
    None
}
