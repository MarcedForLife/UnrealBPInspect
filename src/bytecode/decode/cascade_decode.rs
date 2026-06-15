//! Decode-time recognizer for the Blueprint compiler's switch dispatch
//! table.
//!
//! The Blueprint compiler emits enum/integer switch nodes as a flat
//! sequence of `[temp = X != C; jump-if-not temp -> CASE_n]` pairs
//! followed by a single terminating `EX_JUMP` to the post-switch
//! convergence offset. Each case body lives past the terminating jump.
//!
//! `decode_branch`'s `OutOfRange` fallback can't model this shape, the
//! cascaded jump-if-not's then-bodies sit outside the outer's range and
//! collapse into a single block. This recognizer fires before
//! `decode_branch` whenever the head opcode is `EX_JUMP_IF_NOT` (or its
//! `EX_LET_BOOL`-prefixed pair) and produces `Stmt::Switch` directly with
//! each case body decoded from `[CASE_n, CASE_{n+1})`.
//!
//! Recognition is all-or-nothing: every step in the chain must match and
//! the terminating `EX_JUMP` must be present, otherwise `*pos` is left
//! untouched and the caller falls through to `decode_branch` /
//! `try_decode_loop`. Genuine if-elseif chains (no terminating jump)
//! still flow through `decode_branch` -> `lower_sentinel_cascade` ->
//! `fold_switch_cascades`.

use std::collections::BTreeSet;

use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;
use crate::bytecode::stmt::{Stmt, SwitchCase};

use super::block::decode_assignment;
use super::branch::decode_subrange;
use super::ctx::{mark_claimed, DecodeCtx, OwnerId};
use super::expr_decode::decode_expr;

/// Operand width for `EX_JUMP` / `EX_JUMP_IF_NOT` jump targets.
const JUMP_TARGET_BYTES: usize = 4;
/// Total instruction length (opcode + operand).
const JUMP_INSTR_BYTES: usize = 1 + JUMP_TARGET_BYTES;

/// Clip a case body's end to the nearest sibling-pin boundary that lies
/// strictly past `body_start`.
///
/// The boundary-aware region-walk descent installs the parent pin walk's
/// sibling-pin entry blocks on `ctx.arm_descent_stops` for the lifetime of
/// a dispatched region's decode (see `region_decode::dispatch_child_region_at`).
/// When a dispatched IfThen/IfThenElse region's entry block actually heads a
/// pop_flow-terminated `Switch` cascade, the cascade's last case body would
/// otherwise extend to the owned-range end and swallow those sibling pins,
/// emitting them once inside the case and again as the trailing sequence
/// (a `switch` on an enum inside a tick event, otherwise duplicated).
///
/// This mirrors the dominance-gated boundary that `reachable_blocks_in_arm`
/// applies to a dispatched IfThenElse arm: the cascade case body cannot run
/// into a sibling pin. Only forward stops (`block.start > body_start`)
/// participate, so sibling pins reached via backward/forward jumps at lower
/// addresses (legitimately below the cascade head) never truncate a body.
///
/// No-op when the stop-set is empty (the descent flag is off, or this is a
/// non-descent caller such as the linear sweep) or when no forward stop sits
/// before `body_end`: the original `body_end` is returned unchanged.
fn clip_body_end_to_forward_stop(body_start: usize, body_end: usize, ctx: &DecodeCtx) -> usize {
    let stops = ctx.arm_descent_stops.borrow();
    if stops.is_empty() {
        return body_end;
    }
    let Some(cfg) = ctx.cfg else {
        return body_end;
    };
    stops
        .iter()
        .filter_map(|&block_id| cfg.blocks.get(block_id).map(|block| block.start))
        .filter(|&stop_start| stop_start > body_start && stop_start < body_end)
        .min()
        .unwrap_or(body_end)
}

/// Try to decode a Blueprint switch dispatch table at `*pos`. Returns
/// `Some(Stmt::Switch)` when the bytes match the dispatch shape, with
/// `*pos` advanced to the terminating-jump's target (the convergence
/// offset). Returns `None` and leaves `*pos` unchanged otherwise.
///
/// Recognised shape:
/// ```text
///   pair_1: [EX_LET_BOOL t = NotEqual_*(X, C_1); EX_JUMP_IF_NOT t -> CASE_1]
///   pair_2: [EX_LET_BOOL t = NotEqual_*(X, C_2); EX_JUMP_IF_NOT t -> CASE_2]
///   ...
///   pair_N: [EX_LET_BOOL t = NotEqual_*(X, C_N); EX_JUMP_IF_NOT t -> CASE_N]
///   EX_JUMP T_default        <- terminating jump (post-switch convergence)
///   CASE_1: <case body 1>
///   CASE_2: <case body 2>
///   ...
///   CASE_N: <case body N>
///   T_default:                 <- decoded by the outer scope
/// ```
///
/// The simpler shape without the `EX_LET_BOOL` (where the JumpIfNot's
/// condition is the `NotEqual_*` call directly) is also recognised. The
/// production Blueprint compiler emits the assigned-temp form, the
/// inline form is supported so synthetic tests can exercise the
/// recognizer without constructing an `EX_LET_BOOL`.
pub(crate) fn try_decode_jumpifnot_cascade(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let head_offset = *pos;
    let pairs = collect_dispatch_pairs(head_offset, range_end, ctx)?;
    if pairs.len() < 2 {
        return None;
    }

    // `pairs.len() >= 2` here, so `last()` is Some; degrade to None defensively
    // on externally-derived data rather than panicking on a malformed asset.
    let last_pair = pairs.last()?;
    // Instrumentation can sit between the last pair's JumpIfNot and the
    // terminating EX_JUMP, mirroring the inter-pair case.
    let term_pos = skip_instrumentation(last_pair.after_jumpifnot, range_end, ctx)?;
    let terminating_jump = peek_terminating_jump(term_pos, range_end, ctx)?;

    // All case targets and the terminating jump's target must resolve
    // through the mem_to_disk map (identity when no map is present).
    let case_disks: Vec<usize> = pairs
        .iter()
        .map(|pair| resolve_target(pair.case_target_mem, ctx))
        .collect::<Option<_>>()?;
    let default_disk = resolve_target(terminating_jump.target_mem, ctx)?;

    // Every case target must be in-bounds and lie at or past the
    // terminating jump's end (i.e. past the dispatch table).
    let dispatch_end = terminating_jump.after_jump;
    for &case_disk in &case_disks {
        if case_disk < dispatch_end || case_disk > ctx.bytecode.len() {
            return None;
        }
        if case_disk > range_end {
            return None;
        }
    }
    if default_disk > range_end || default_disk > ctx.bytecode.len() {
        return None;
    }

    // Cases must be in monotonically increasing order so the body ranges
    // `[CASE_n, CASE_{n+1})` are well-formed. Anything else means the
    // shape isn't a dispatch table.
    for window in case_disks.windows(2) {
        if window[1] <= window[0] {
            return None;
        }
    }
    if let Some(&last_case) = case_disks.last() {
        if default_disk < last_case {
            return None;
        }
    }

    // Build the decoded case bodies via CFG-reachability so a case whose
    // forward in-body jumps land past a sibling case's entry keeps its own
    // bytes (the case-relocation shape). Fall back
    // to the contiguous `[CASE_n, CASE_{n+1})` slice when the CFG isn't
    // available (test contexts) or the case entry doesn't align to a block
    // leader. The canonical cascade has strictly increasing case targets,
    // so each case's values list holds exactly one entry.
    let canonical_stops = canonical_cascade_stop_disks(head_offset, &case_disks, default_disk);
    let mut cases: Vec<SwitchCase> = Vec::with_capacity(pairs.len());
    for (idx, pair) in pairs.iter().enumerate() {
        let body_start = case_disks[idx];
        let body_end = if idx + 1 < case_disks.len() {
            case_disks[idx + 1]
        } else {
            default_disk
        };
        let body = decode_cascade_case_body_via_reachability(
            body_start,
            &canonical_stops,
            default_disk,
            ctx,
        )
        .unwrap_or_else(|| decode_subrange(body_start, body_end, ctx));
        cases.push(SwitchCase {
            values: vec![pair.case_value.clone()],
            body,
        });
    }

    // Default body is left to the outer scope: advance pos to
    // `default_disk` so the post-switch code is decoded by the caller.
    *pos = default_disk;

    Some(Stmt::Switch {
        expr: pairs[0].switch_expr.clone(),
        cases,
        default: None,
        offset: head_offset,
    })
}

/// Try to decode a Blueprint switch dispatch where multiple enum values
/// converge to a shared body and the dispatch is terminated by
/// `EX_POP_EXECUTION_FLOW` rather than an `EX_JUMP`.
///
/// This is the shape the Blueprint compiler emits for a Switch on Enum
/// whose cases are wired through the same Sequence (multiple pin values
/// share the same downstream graph). The bytecode shape is:
/// ```text
///   pair_1: [EX_LET_BOOL t = NotEqual_*(X, V_1); EX_JUMP_IF_NOT t -> CASE_a]
///   pair_2: [EX_LET_BOOL t = NotEqual_*(X, V_2); EX_JUMP_IF_NOT t -> CASE_a]   // shared
///   pair_3: [EX_LET_BOOL t = NotEqual_*(X, V_3); EX_JUMP_IF_NOT t -> CASE_a]   // shared
///   pair_4: [EX_LET_BOOL t = NotEqual_*(X, V_4); EX_JUMP_IF_NOT t -> CASE_b]
///   EX_POP_EXECUTION_FLOW   <- 1-byte default body (returns to outer flow)
///   CASE_a: <shared body for V_1 / V_2 / V_3>
///   ...
///   CASE_b: <body for V_4>
/// ```
///
/// The recognizer emits one `SwitchCase` per UNIQUE target. Pairs whose
/// JumpIfNot targets converge group their case values into the resulting
/// case's `values` list, so a Walking+Running+Swimming -> one body shape
/// becomes a single `SwitchCase` carrying `values = [Walking, Running,
/// Swimming]`. Each unique body decodes exactly once. Case ordering is
/// preserved by the lowest source-position value within each group.
///
/// Falls through (returns `None` and leaves `*pos` untouched) when:
/// - fewer than 2 pairs match,
/// - the byte after the last pair isn't `EX_POP_EXECUTION_FLOW` (modulo
///   instrumentation),
/// - case targets aren't strictly past the dispatch table or can't be
///   resolved through `mem_to_disk`,
/// - the default body's range (between dispatch end and first case) isn't
///   exactly the 1-byte pop_flow.
pub(crate) fn try_decode_jumpifnot_cascade_shared(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let head_offset = *pos;
    let pairs = collect_dispatch_pairs(head_offset, range_end, ctx)?;
    if pairs.len() < 2 {
        return None;
    }

    // The byte after the last pair (modulo instrumentation) must be
    // `EX_POP_EXECUTION_FLOW`. The pop_flow is the entire default body:
    // when none of the cases match, control returns through the outer
    // flow stack.
    let last_pair = pairs.last()?;
    let term_pos = skip_instrumentation(last_pair.after_jumpifnot, range_end, ctx)?;
    let dispatch_end = cascade_pop_flow_dispatch_end(term_pos, range_end, ctx)?;

    // Resolve every case target via mem_to_disk. Targets must be in
    // bounds and lie at or past the dispatch end.
    let case_disks: Vec<usize> = pairs
        .iter()
        .map(|pair| resolve_target(pair.case_target_mem, ctx))
        .collect::<Option<_>>()?;
    for &case_disk in &case_disks {
        if case_disk < dispatch_end || case_disk > ctx.bytecode.len() {
            return None;
        }
        if case_disk > range_end {
            return None;
        }
    }

    // To recognise the canonical shape, at least one pair of consecutive
    // cases must share a target (otherwise it's a regular cascade that
    // should have been caught by the canonical recognizer's terminating-
    // EX_JUMP path; falling through here would silently change behaviour
    // for cascades that simply lack a terminating jump).
    let has_shared_target = case_disks.windows(2).any(|window| window[0] == window[1]);
    if !has_shared_target {
        return None;
    }

    // The first case must begin exactly at `dispatch_end`. The 1-byte
    // pop_flow IS the default body; nothing else should sit between it
    // and the first case body.
    let min_case_disk = *case_disks.iter().min()?;
    if min_case_disk != dispatch_end {
        return None;
    }

    // Compute body bounds per unique target. Sort the unique case
    // targets so each body's [start, end) range is well-formed.
    let mut sorted_targets: Vec<usize> = case_disks.clone();
    sorted_targets.sort_unstable();
    sorted_targets.dedup();

    // Group pairs by target offset, preserving the source-order of each
    // group (the lowest pair index targeting each disk position). The
    // resulting case list keeps original cascade order; each unique body
    // decodes exactly once and carries the merged values list.
    let mut group_order: Vec<usize> = Vec::new();
    let mut group_first_idx: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut group_values: std::collections::BTreeMap<usize, Vec<Expr>> =
        std::collections::BTreeMap::new();
    for (idx, pair) in pairs.iter().enumerate() {
        let target = case_disks[idx];
        if let std::collections::btree_map::Entry::Vacant(slot) = group_first_idx.entry(target) {
            slot.insert(idx);
            group_order.push(target);
        }
        group_values
            .entry(target)
            .or_default()
            .push(pair.case_value.clone());
    }
    group_order.sort_by_key(|target| group_first_idx[target]);

    // The last unique case body ends at `range_end` (the owned-range end).
    // Under the boundary-aware region-walk descent, clip it to the nearest
    // sibling-pin boundary so the body can't swallow the parent's trailing
    // pins. No-op when no descent stop-set is installed.
    let last_target = *sorted_targets.last()?;
    let last_body_end = clip_body_end_to_forward_stop(last_target, range_end, ctx);

    // Decode each unique case body via CFG-reachability, same as the
    // canonical arm. The shared cascade's stop-set is the dispatch head
    // plus every sibling unique target plus the pop_flow landing (modelled
    // by `last_body_end`, since pop_flow has no explicit jump target).
    let shared_stops = shared_cascade_stop_disks(head_offset, &sorted_targets, last_body_end);
    let mut cases: Vec<SwitchCase> = Vec::with_capacity(group_order.len());
    for target in &group_order {
        // `target` was sourced from `sorted_targets`, so `position` is Some;
        // bail the whole recognizer rather than emit a partial switch if a
        // malformed asset breaks that invariant.
        let target_idx = sorted_targets.iter().position(|value| value == target)?;
        let body_end = if target_idx + 1 < sorted_targets.len() {
            sorted_targets[target_idx + 1]
        } else {
            last_body_end
        };
        let body =
            decode_cascade_case_body_via_reachability(*target, &shared_stops, last_body_end, ctx)
                .unwrap_or_else(|| decode_subrange(*target, body_end, ctx));
        let values = group_values.remove(target)?;
        cases.push(SwitchCase { values, body });
    }

    // The 1-byte pop_flow is the default body; we model it as an empty
    // default (no statement) since pop_flow only signals "return to outer
    // flow", which is implicit at function/event tail.
    //
    // Advance *pos past the entire dispatch + case bodies. The case
    // bodies were just decoded inline, so resume past the last byte we
    // claimed. Clipped to the same sibling-pin boundary so a non-emitter
    // (linear-sweep) caller resumes at the pins rather than past them;
    // identical to `range_end` when no descent stop-set is installed.
    *pos = last_body_end;

    Some(Stmt::Switch {
        expr: pairs[0].switch_expr.clone(),
        cases,
        default: None,
        offset: head_offset,
    })
}

/// Try to decode a Blueprint switch dispatch where every case JumpIfNot
/// targets a shared backward trampoline whose own `EX_JUMP` forwards to
/// the actual case body. The dispatch is terminated by
/// `EX_POP_EXECUTION_FLOW`.
///
/// This is the shape Blueprint emits for a Switch on Enum whose cases
/// all wire to the same downstream graph but whose convergence body
/// lives in another (lower-disk) section of the event because the body
/// was reused across reachability paths. The bytecode shape is:
/// ```text
///   pair_1: [EX_LET_BOOL t = NotEqual_*(X, V_1); EX_JUMP_IF_NOT t -> TRAMP]
///   pair_2: [EX_LET_BOOL t = NotEqual_*(X, V_2); EX_JUMP_IF_NOT t -> TRAMP]
///   pair_N: [EX_LET_BOOL t = NotEqual_*(X, V_N); EX_JUMP_IF_NOT t -> TRAMP]
///   EX_POP_EXECUTION_FLOW
///   ...
///   TRAMP: <instrumentation*> EX_JUMP -> CONVERGENCE
///   ...
///   CONVERGENCE: <body> EX_POP_EXECUTION_FLOW
/// ```
///
/// On a match, the recognizer:
/// - Decodes the convergence body once, bounded by its terminating
///   `EX_POP_EXECUTION_FLOW`.
/// - Emits a single `SwitchCase` carrying the merged values list (V_1,
///   V_2, ..., V_N) and the decoded body.
/// - Marks both the trampoline span and the convergence body span as
///   claimed so the outer linear sweep doesn't re-emit them.
///
/// Falls through (returns `None` and leaves `*pos` untouched) when:
/// - fewer than 2 pairs match,
/// - the byte after the last pair isn't `EX_POP_EXECUTION_FLOW` (modulo
///   instrumentation),
/// - case targets aren't all identical (this arm only handles the
///   single-shared-trampoline shape; mixed targets fall through to the
///   canonical / forward-shared arms),
/// - the trampoline at the shared target doesn't decode as
///   `<instrumentation*> EX_JUMP <ultimate>`,
/// - the ultimate destination's chain doesn't terminate in
///   `EX_POP_EXECUTION_FLOW` within `MAX_CONVERGENCE_OPCODES`,
/// - the ultimate destination doesn't lie in the event's owned ranges
///   (would mis-claim bytes belonging to another event),
/// - the convergence body isn't single-source-reachable (predecessor
///   scan finds an inbound edge from outside the cascade).
pub(crate) fn try_decode_jumpifnot_cascade_shared_via_trampoline(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    let head_offset = *pos;
    let pairs = collect_dispatch_pairs(head_offset, range_end, ctx)?;
    if pairs.len() < 2 {
        return None;
    }

    let last_pair = pairs.last()?;
    let term_pos = skip_instrumentation(last_pair.after_jumpifnot, range_end, ctx)?;
    let dispatch_end = cascade_pop_flow_dispatch_end(term_pos, range_end, ctx)?;

    // Every pair must share the same target. Mixed-target cascades go
    // through the canonical or forward-shared arms.
    let trampoline_disk = resolve_target(pairs[0].case_target_mem, ctx)?;
    if !pairs
        .iter()
        .all(|pair| resolve_target(pair.case_target_mem, ctx) == Some(trampoline_disk))
    {
        return None;
    }
    if trampoline_disk >= ctx.bytecode.len() {
        return None;
    }

    // The trampoline must decode as <instrumentation*> EX_JUMP <ult>.
    let trampoline = peek_jump_trampoline(trampoline_disk, ctx)?;
    let ultimate_disk = resolve_target(trampoline.ultimate_mem, ctx)?;

    // The ultimate destination must lie inside one of the event's owned
    // disk ranges. Without this gate, the recognizer could claim bytes
    // belonging to a sibling event (the trampoline conceptually belongs
    // to whichever event's range encloses it; the convergence body might
    // belong to a different one).
    if !disk_in_owned_ranges(ultimate_disk, ctx) {
        return None;
    }

    // Walk the convergence chain to find its terminating
    // `EX_POP_EXECUTION_FLOW`. Bounded so a malformed body can't drive
    // an unbounded scan.
    let convergence_end = scan_pop_flow_terminator(ultimate_disk, ctx)?;

    // Predecessor verification: confirm the convergence body is reached
    // ONLY via the cascade's trampoline. Prevents claiming bytes that
    // another event's edge legitimately enters.
    if !convergence_is_single_source(ultimate_disk, trampoline_disk, ctx) {
        return None;
    }

    let owner = OwnerId::TrampolineCascade {
        merge_disk: ultimate_disk,
    };
    // Decode the convergence body under the convergence's CFG-region
    // owner so any prescan claim sitting inside that region's
    // transitive coverage is bypassed regardless of which prescan
    // installed it. Falls back to the cascade owner when no region
    // tree is available (synthetic contexts, standalone functions).
    let body_owner = ctx
        .region_id_for(ultimate_disk)
        .map(|region_id| OwnerId::CfgRegion { region_id })
        .unwrap_or(owner);
    let body = {
        let _guard = ctx.with_decoding_owner(body_owner);
        decode_subrange(ultimate_disk, convergence_end, ctx)
    };
    let merged_values: Vec<Expr> = pairs.iter().map(|pair| pair.case_value.clone()).collect();
    let cases = vec![SwitchCase {
        values: merged_values,
        body,
    }];

    // Claim the trampoline span and the convergence body span so the
    // outer linear sweep skips them. Trampoline is in someone else's
    // owned range so claiming is harmless there; the convergence body
    // is the bytes the IsValid pre-scan / linear sweep would otherwise
    // emit at top level.
    mark_claimed(ctx, trampoline_disk, trampoline.trampoline_end, owner);
    mark_claimed(ctx, ultimate_disk, convergence_end, owner);

    *pos = dispatch_end;

    Some(Stmt::Switch {
        expr: pairs[0].switch_expr.clone(),
        cases,
        default: None,
        offset: head_offset,
    })
}

/// Trampoline shape: `<instrumentation*> EX_JUMP <ultimate_mem>`.
///
/// `trampoline_end` is the disk index immediately past the EX_JUMP's
/// operand (the byte after the trampoline's last byte). `ultimate_mem`
/// is the mem-coordinate target encoded in the EX_JUMP operand;
/// callers translate it to disk via `resolve_target`.
struct JumpTrampoline {
    ultimate_mem: usize,
    trampoline_end: usize,
}

/// Peek the bytecode at `disk` for a trampoline shape: zero or more
/// instrumentation opcodes followed by an `EX_JUMP <target>`. Returns
/// `None` for any other shape (real opcodes between the start and the
/// jump, EOF, malformed length scan).
fn peek_jump_trampoline(disk: usize, ctx: &DecodeCtx) -> Option<JumpTrampoline> {
    let probe = skip_instrumentation(disk, ctx.bytecode.len(), ctx)?;
    if probe + JUMP_INSTR_BYTES > ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode[probe] != EX_JUMP {
        return None;
    }
    let mut peek = probe + 1;
    let ultimate_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
    Some(JumpTrampoline {
        ultimate_mem,
        trampoline_end: peek,
    })
}

/// Walk forward from `start` accumulating opcode lengths until the first
/// `EX_POP_EXECUTION_FLOW` at depth zero. Returns the disk index just
/// past the pop_flow byte. Aborts (returns `None`) on
/// `EX_END_OF_SCRIPT` or `EX_RETURN` (no pop terminator found),
/// zero-length opcodes (defensive), or after `MAX_CONVERGENCE_OPCODES`
/// steps.
///
/// Doesn't descend into nested constructs because IsValid-shaped bodies
/// are flat at the dispatch level: any inner `EX_JUMP_IF_NOT` is a
/// regular if-block whose terminator stays within its own bounds, and
/// the body's enclosing `EX_POP_EXECUTION_FLOW` always sits at the
/// outermost level.
fn scan_pop_flow_terminator(start: usize, ctx: &DecodeCtx) -> Option<usize> {
    /// Bound on chain walk so a malformed stream can't drive an
    /// unbounded scan. Observed convergence bodies terminate within a
    /// handful of opcodes; 64 is comfortably above that.
    const MAX_CONVERGENCE_OPCODES: usize = 64;
    let mut cursor = start;
    let mut visited = 0usize;
    while cursor < ctx.bytecode.len() && visited < MAX_CONVERGENCE_OPCODES {
        let opcode = ctx.bytecode[cursor];
        match opcode {
            EX_POP_EXECUTION_FLOW => return Some(cursor + 1),
            EX_END_OF_SCRIPT | EX_RETURN => return None,
            _ => {}
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return None;
        }
        cursor += length;
        visited += 1;
    }
    None
}

/// True when `disk` lies inside any of the current event's owned disk
/// ranges. False when the context has no `owned_ranges` slice (function
/// bodies, synthetic test contexts).
fn disk_in_owned_ranges(disk: usize, ctx: &DecodeCtx) -> bool {
    let Some(ranges) = ctx.owned_ranges else {
        return false;
    };
    ranges
        .iter()
        .any(|range| disk >= range.start && disk < range.end)
}

/// Predecessor-scan the bytecode for inbound edges to `convergence_disk`.
/// Returns `true` when the only inbound edge is from `trampoline_disk`'s
/// EX_JUMP (i.e. the convergence body is reached exclusively via the
/// trampoline). Returns `false` when any other opcode's target operand
/// resolves to `convergence_disk`, or when the context has no
/// `mem_to_disk` map (we can't safely verify without it).
///
/// Walks every opcode in the bytecode at depth zero (using the length
/// scanner). Only opcodes carrying a 4-byte mem-coord target operand are
/// inspected: `EX_JUMP`, `EX_JUMP_IF_NOT`, `EX_PUSH_EXECUTION_FLOW`. A
/// dropped check on `EX_POP_FLOW_IF_NOT` is intentional: its target is
/// the alternate path, not a direct branch into the convergence body.
fn convergence_is_single_source(
    convergence_disk: usize,
    trampoline_disk: usize,
    ctx: &DecodeCtx,
) -> bool {
    let Some(mem_to_disk) = ctx.mem_to_disk else {
        return false;
    };

    let mut cursor = 0usize;
    while cursor < ctx.bytecode.len() {
        let opcode = ctx.bytecode[cursor];
        // Opcodes carrying a 4-byte mem-coord target operand. Other
        // opcodes (assignments, calls, etc.) consume operands of various
        // sizes that may incidentally encode bytes matching a
        // mem-coordinate; relying on the length scanner keeps the walk
        // accurate.
        let target_at = match opcode {
            EX_JUMP | EX_JUMP_IF_NOT | EX_PUSH_EXECUTION_FLOW => Some(cursor + 1),
            _ => None,
        };
        if let Some(operand_pos) = target_at {
            if operand_pos + JUMP_TARGET_BYTES <= ctx.bytecode.len() {
                let mut peek = operand_pos;
                let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
                if let Some(&target_disk) = mem_to_disk.get(&target_mem) {
                    if target_disk == convergence_disk {
                        // The trampoline's EX_JUMP is the expected
                        // single source. Other inbound edges fail the
                        // check.
                        let trampoline_jump_disk = match peek_jump_trampoline(trampoline_disk, ctx)
                        {
                            Some(tramp) => tramp.trampoline_end - JUMP_INSTR_BYTES,
                            None => return false,
                        };
                        if cursor != trampoline_jump_disk {
                            return false;
                        }
                    }
                }
            }
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            return false;
        }
        cursor += length;
    }
    true
}

/// One pair in the dispatch chain: the `Status != C_n` test plus the
/// JumpIfNot whose target is the case body for `C_n`.
struct DispatchPair {
    /// The lhs of the `NotEqual_*` call: `X` in `X != C`.
    switch_expr: Expr,
    /// The rhs of the `NotEqual_*` call: `C_n` (the case value).
    case_value: Expr,
    /// Mem-coordinate target of the JumpIfNot, pointing at CASE_n.
    case_target_mem: usize,
    /// Disk position immediately after the JumpIfNot instruction (where
    /// the next pair, or the terminating jump, begins).
    after_jumpifnot: usize,
}

/// Walk forward from `start` collecting consecutive dispatch pairs.
/// Stops at the first opcode that doesn't match the `[Assign Ne; JumpIfNot]`
/// or `[JumpIfNot Ne]` shape and returns whatever pairs were collected
/// (caller decides whether the count is enough).
///
/// Returns `None` when no pair matches at all (so the caller can return
/// fast without re-checking).
fn collect_dispatch_pairs(
    start: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Vec<DispatchPair>> {
    let mut pairs: Vec<DispatchPair> = Vec::new();
    let mut cursor = start;
    let mut common_lhs: Option<Expr> = None;

    while cursor < range_end {
        // Step over any instrumentation between pairs. The editor emits
        // EX_TRACEPOINT / EX_WIRE_TRACEPOINT bookkeeping between every
        // pair of real statements; without skipping, the second pair's
        // peek would see the tracepoint as the new head opcode and bail.
        let probe_cursor = match skip_instrumentation(cursor, range_end, ctx) {
            Some(pos) => pos,
            None => break,
        };
        let pair = match peek_dispatch_pair(probe_cursor, range_end, ctx) {
            Some(pair) => pair,
            None => break,
        };

        // The lhs of every pair's NotEqual_* call must match the first
        // pair's lhs structurally. Otherwise this isn't a single-switch
        // dispatch, it's an unrelated chain.
        match &common_lhs {
            None => common_lhs = Some(pair.switch_expr.clone()),
            Some(expected) if *expected == pair.switch_expr => {}
            Some(_) => break,
        }

        cursor = pair.after_jumpifnot;
        pairs.push(pair);
    }

    if pairs.is_empty() {
        None
    } else {
        Some(pairs)
    }
}

/// Try to peek a single dispatch pair at `cursor`. Returns the parsed
/// pair without committing any state; on mismatch returns `None`.
fn peek_dispatch_pair(cursor: usize, range_end: usize, ctx: &DecodeCtx) -> Option<DispatchPair> {
    if cursor >= ctx.bytecode.len() || cursor >= range_end {
        return None;
    }

    // Two shapes accepted:
    // 1. `EX_LET_BOOL t = NotEqual_*(X, C); EX_JUMP_IF_NOT t -> CASE`
    // 2. `EX_JUMP_IF_NOT NotEqual_*(X, C) -> CASE`
    let opcode = ctx.bytecode[cursor];
    if opcode == EX_LET_BOOL {
        return peek_assigned_pair(cursor, range_end, ctx);
    }
    if opcode == EX_JUMP_IF_NOT {
        return peek_inline_pair(cursor, range_end, ctx);
    }
    None
}

/// Peek an `[EX_LET_BOOL t = NotEqual_*(X, C); EX_JUMP_IF_NOT t -> CASE]`
/// pair starting at `cursor`. Returns `None` if either half doesn't
/// match. Instrumentation opcodes between the assignment and the
/// JumpIfNot are skipped (the editor emits trace markers between every
/// real statement).
fn peek_assigned_pair(cursor: usize, range_end: usize, ctx: &DecodeCtx) -> Option<DispatchPair> {
    let mut probe = cursor;

    // Decode the assignment via the canonical helper. Bail if the
    // resulting Stmt isn't an Assignment with the recognized shape.
    let stmt = decode_assignment(&mut probe, ctx);
    if probe > range_end {
        return None;
    }
    let (temp_name, switch_expr, case_value) = match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name),
            rhs,
            ..
        } => match extract_ne_call(&rhs) {
            Some((lhs, rhs_lit)) => (name, lhs, rhs_lit),
            None => return None,
        },
        _ => return None,
    };

    // Skip any instrumentation opcodes the editor emits between the
    // assignment and the JumpIfNot. The next semantic opcode must be
    // `EX_JUMP_IF_NOT` with cond `Var(temp_name)`.
    let jumpifnot_pos = skip_instrumentation(probe, range_end, ctx)?;
    if jumpifnot_pos + JUMP_INSTR_BYTES > range_end {
        return None;
    }
    if ctx.bytecode[jumpifnot_pos] != EX_JUMP_IF_NOT {
        return None;
    }
    let mut peek = jumpifnot_pos + 1;
    let case_target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
    let cond_disk = peek;
    let mut cond_cursor = cond_disk;
    let cond = decode_expr(&mut cond_cursor, ctx);
    if cond_cursor > range_end {
        return None;
    }
    match cond {
        Expr::Var(name) if name == temp_name => {}
        _ => return None,
    }

    Some(DispatchPair {
        switch_expr,
        case_value,
        case_target_mem,
        after_jumpifnot: cond_cursor,
    })
}

/// Peek an `[EX_JUMP_IF_NOT NotEqual_*(X, C) -> CASE]` pair (no separate
/// assignment). Used by synthetic tests; the production compiler always
/// emits the assigned-temp shape.
fn peek_inline_pair(cursor: usize, range_end: usize, ctx: &DecodeCtx) -> Option<DispatchPair> {
    if cursor + JUMP_INSTR_BYTES > range_end {
        return None;
    }
    if ctx.bytecode[cursor] != EX_JUMP_IF_NOT {
        return None;
    }
    let mut peek = cursor + 1;
    let case_target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
    let cond_disk = peek;
    let mut cond_cursor = cond_disk;
    let cond = decode_expr(&mut cond_cursor, ctx);
    if cond_cursor > range_end {
        return None;
    }
    let (switch_expr, case_value) = extract_ne_call(&cond)?;
    Some(DispatchPair {
        switch_expr,
        case_value,
        case_target_mem,
        after_jumpifnot: cond_cursor,
    })
}

/// Match `Expr::Call { name: "NotEqual_*", args: [lhs, rhs] }` and pull
/// out (lhs, rhs). Returns `None` for any other expression shape, including
/// `Eq`-call (which would be the start of a `[Equal_; JumpIf]` cascade
/// that this recognizer deliberately doesn't handle).
pub(crate) fn extract_ne_call(expr: &Expr) -> Option<(Expr, Expr)> {
    let Expr::Call { name, args } = expr else {
        return None;
    };
    if !name.starts_with("NotEqual_") {
        return None;
    }
    if args.len() != 2 {
        return None;
    }
    Some((args[0].clone(), args[1].clone()))
}

/// Description of the dispatch table's terminating `EX_JUMP`.
pub(crate) struct TerminatingJump {
    pub(crate) target_mem: usize,
    pub(crate) after_jump: usize,
}

/// Peek the terminating `EX_JUMP` at `cursor`. Bails if the byte isn't
/// `EX_JUMP` or the operand would run past `range_end`.
pub(crate) fn peek_terminating_jump(
    cursor: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<TerminatingJump> {
    if cursor + JUMP_INSTR_BYTES > range_end {
        return None;
    }
    if cursor >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode[cursor] != EX_JUMP {
        return None;
    }
    let mut peek = cursor + 1;
    let target_mem = read_bc_u32(ctx.bytecode, &mut peek) as usize;
    Some(TerminatingJump {
        target_mem,
        after_jump: peek,
    })
}

/// Detect the pop_flow terminator after the last dispatch pair: bounds-check
/// `term_pos`, require EX_POP_EXECUTION_FLOW, return the dispatch-table end
/// (term_pos + 1). None when out of range or not a pop_flow.
fn cascade_pop_flow_dispatch_end(
    term_pos: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<usize> {
    if term_pos >= ctx.bytecode.len() || term_pos >= range_end {
        return None;
    }
    if ctx.bytecode[term_pos] != EX_POP_EXECUTION_FLOW {
        return None;
    }
    Some(term_pos + 1)
}

/// Translate a mem-coordinate jump target to a disk position via
/// `mem_to_disk`. With no map at all (test contexts) mem equals disk and
/// the raw coordinate passes through. With a map present, every opcode
/// boundary has an entry on a clean walk, so a miss means the target
/// doesn't land on any known opcode boundary (corrupt operand or drift
/// walker anomaly); resolution fails and the recognizer declines rather
/// than guessing a disk position that may pass bounds checks by luck.
pub(crate) fn resolve_target(target_mem: usize, ctx: &DecodeCtx) -> Option<usize> {
    match ctx.mem_to_disk {
        Some(map) => map.get(&target_mem).copied(),
        None => Some(target_mem),
    }
}

/// Walk past any instrumentation opcodes (`EX_WIRE_TRACEPOINT`,
/// `EX_TRACEPOINT`, `EX_INSTRUMENTATION_EVENT`) at `cursor` and return
/// the position of the next semantic opcode. Bounded by `range_end` so
/// the skip never runs past the slice. Returns `None` when the walk
/// would exit the range.
fn skip_instrumentation(mut cursor: usize, range_end: usize, ctx: &DecodeCtx) -> Option<usize> {
    while cursor < range_end && cursor < ctx.bytecode.len() {
        let opcode = ctx.bytecode[cursor];
        if !matches!(
            opcode,
            EX_WIRE_TRACEPOINT | EX_TRACEPOINT | EX_INSTRUMENTATION_EVENT
        ) {
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

/// Stop-set for the canonical (EX_JUMP-terminated) cascade's
/// reachability-bounded body decode. Combines the dispatch head, every
/// case body's start (so a sibling case's bytes terminate the breadth-
/// first walk before they get swept in), and the post-switch convergence
/// (the EX_JUMP default target).
fn canonical_cascade_stop_disks(
    head_disk: usize,
    case_disks: &[usize],
    default_disk: usize,
) -> BTreeSet<usize> {
    let mut stops: BTreeSet<usize> = BTreeSet::new();
    stops.insert(head_disk);
    stops.insert(default_disk);
    stops.extend(case_disks.iter().copied());
    stops
}

/// Stop-set for the EX_POP_EXECUTION_FLOW-terminated shared-cascade
/// reachability-bounded body decode. Same construction as the canonical
/// arm but without an explicit default target (pop_flow has no jump
/// operand); the `range_end` passed alongside the stop-set guards the
/// walk past the last unique target body.
fn shared_cascade_stop_disks(
    head_disk: usize,
    sorted_unique_targets: &[usize],
    range_end: usize,
) -> BTreeSet<usize> {
    let mut stops: BTreeSet<usize> = BTreeSet::new();
    stops.insert(head_disk);
    stops.insert(range_end);
    stops.extend(sorted_unique_targets.iter().copied());
    stops
}

/// Reachability-bounded analog of `decode_subrange(case_start_disk, _, ctx)`
/// for a switch cascade's per-case body.
///
/// The canonical contiguous decode treats every case body as the
/// half-open byte range `[case_start, next_case_start)` (or `range_end`
/// for the last case). That premise loses information when the Blueprint
/// compiler emits forward in-body branches (an `EX_JUMP_IF_NOT` whose
/// target sits past a sibling case's start) and the case_a body
/// physically extends past the case_b entry in disk order, while the
/// case_b body owns only its own block. The case_a bytes that compile
/// after case_b are still CFG-reachable from case_a alone, but the
/// contiguous slice truncates at case_b's entry, dropping them.
///
/// This helper instead walks the basic-block control-flow graph (CFG)
/// forward from the block whose `start == case_start_disk`, expanding
/// successors via breadth-first search. The walk stops at any block whose
/// `start` matches an entry in `stop_disks` (the dispatch head, every
/// sibling case's entry, and the post-switch convergence) or whose `start`
/// is at-or-past `range_end`. A successor is also skipped when its `start`
/// is below the block currently being expanded (a backward edge in disk
/// order). Excluding backward edges keeps the walk inside the case's own
/// forward region: a sibling case that jumps back into the first case's
/// shared tail (a shared broadcast block reached via a back-jump from
/// cases 1..N) does not pull that tail into every case body, while a
/// case's own forward in-body jumps past a sibling's entry (a case whose
/// body has a nested sub-tree past the next case entry) are still
/// followed. A loop back-edge targets a header already visited
/// on the forward path, so skipping it loses no content. Collected blocks'
/// byte ranges are sorted and merged on contiguity / overlap; each merged
/// range is decoded via `decode_subrange` and the results are concatenated
/// in disk order.
///
/// Returns `None` when the CFG isn't available, when no block starts at
/// `case_start_disk`, or when the walk visits no blocks. Callers fall
/// through to the contiguous decode when the helper returns `None`.
fn decode_cascade_case_body_via_reachability(
    case_start_disk: usize,
    stop_disks: &BTreeSet<usize>,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Vec<Stmt>> {
    let cfg = ctx.cfg?;
    let entry_block_id = cfg.block_at_start(case_start_disk)?;

    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
    visited.insert(entry_block_id);
    queue.push_back(entry_block_id);

    let mut visited_ranges: Vec<std::ops::Range<usize>> = Vec::new();
    while let Some(block_id) = queue.pop_front() {
        let block = cfg.blocks.get(block_id)?;
        // The synthetic sink block has an empty opcode list and a degenerate
        // byte range. Skipping it leaves a clean range list.
        if block.start < block.end {
            visited_ranges.push(block.start..block.end);
        }
        let Some(successors) = cfg.successors.get(&block_id) else {
            continue;
        };
        for &successor_id in successors {
            if visited.contains(&successor_id) {
                continue;
            }
            let Some(successor_block) = cfg.blocks.get(successor_id) else {
                continue;
            };
            let successor_start = successor_block.start;
            // Sink block has start == end == bytecode.len() (or similar
            // degenerate marker); treat it as out-of-range so the walk
            // doesn't spuriously expand through it.
            if successor_block.start >= successor_block.end {
                continue;
            }
            if stop_disks.contains(&successor_start) {
                continue;
            }
            if successor_start >= range_end {
                continue;
            }
            // Skip backward edges (a successor that sits below the block
            // being expanded in disk order). This excludes a sibling case's
            // back-jump into an earlier case's shared tail while still
            // following a case's own forward in-body jumps.
            if successor_start < block.start {
                continue;
            }
            visited.insert(successor_id);
            queue.push_back(successor_id);
        }
    }

    if visited_ranges.is_empty() {
        return None;
    }

    visited_ranges.sort_by_key(|range| range.start);
    let mut merged: Vec<std::ops::Range<usize>> = Vec::with_capacity(visited_ranges.len());
    for range in visited_ranges {
        match merged.last_mut() {
            Some(last) if range.start <= last.end => {
                if range.end > last.end {
                    last.end = range.end;
                }
            }
            _ => merged.push(range),
        }
    }

    let mut stmts: Vec<Stmt> = Vec::new();
    for range in merged {
        stmts.extend(decode_subrange(range.start, range.end, ctx));
    }
    Some(stmts)
}
