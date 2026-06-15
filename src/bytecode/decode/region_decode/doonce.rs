use super::*;
use crate::bytecode::transforms::latch_recognition::{DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX};

/// Region-driven emitter for `RegionKind::DoOnceGate`. Returns a
/// `Vec<Stmt>` containing the entry block's pre-JIN preamble stmts
/// followed by a `Stmt::Latch { kind: DoOnce { name, gate_var }, ... }`
/// wrapping the gate-open arm body. Returns `None` when the region's
/// entry block doesn't end with `EX_JUMP_IF_NOT` or when the JIN cond
/// isn't a recognisable gate variable Var.
///
/// CFG successor convention (mirrors `try_emit_ifthenelse_region`):
/// `successors[0]` is the JIN target (gate-open arm, body runs when
/// `IsClosed == false`); `successors[1]` is the fallthrough
/// (gate-closed arm, typically empty or instrumentation only). Both
/// arms get BFS-walked under dominance from their arm entry to capture
/// any stray fallthrough-arm content for the log.
///
/// Body filtering: the first stmt in the gate-open arm is usually a
/// `gate_var = true` Assignment that closes the gate. The latch wrapper
/// makes that assignment implicit so the emitter drops it from the
/// body before wrapping. Subsequent stmts are kept verbatim.
pub(super) fn try_emit_doonce_region(
    region: &Region,
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
    idom: &BTreeMap<BlockId, BlockId>,
) -> Option<Vec<Stmt>> {
    if region.kind != RegionKind::DoOnceGate {
        return None;
    }
    let entry_block = cfg.blocks.get(region.entry)?;
    let terminator_addr = *entry_block.opcodes.last()?;
    if *ctx.bytecode.get(terminator_addr)? != EX_JUMP_IF_NOT {
        return None;
    }

    let cond = decode_jin_cond(terminator_addr, ctx)?;
    let gate_var_name = match &cond {
        Expr::Var(name) if is_doonce_gate_var_name(name) => name.clone(),
        _ => return None,
    };

    let succs = cfg.successors.get(&region.entry)?;
    if succs.len() != 2 {
        return None;
    }
    let gate_open_arm = succs[0];
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    // Pre-JIN preamble: opcodes inside the entry block before the JIN
    // terminator. Reuses the same decoder dispatch as the IfThenElse
    // probe so multi-opcode constructs (Let, Call) consume their span
    // cleanly.
    let preamble = decode_entry_preamble(entry_block, terminator_addr, entry_block.end, ctx);

    let mut body = decode_arm_body(gate_open_arm, None, region, region_id, cfg, ctx, idom);
    // Drop the gate-self-set assignment so the Latch wrapper makes it
    // implicit. The Blueprint compiler emits `gate_var = true` somewhere
    // along the gate-open arm; disk order vs CFG-BFS order may place it
    // anywhere in the body, so search and remove the first matching
    // assignment rather than checking only position 0.
    if let Some(idx) = body
        .iter()
        .position(|stmt| is_gate_self_set(stmt, &gate_var_name))
    {
        body.remove(idx);
    }
    let derived_name = derive_doonce_name_from_body(&body, &gate_var_name, terminator_addr);

    // Latent gap: `try_emit_doonce_region` does NOT call the own-exit
    // dispatch triad (`is_own_exit_with_content` /
    // `decode_post_merge_continuation`) that `try_emit_ifthenelse_region`
    // and `try_emit_ifthen_region` invoke. If a DoOnceGate
    // region ever ends up owning a non-empty exit block,
    // `mark_region_consumed` will sweep it away the same way the IfThen
    // bug dropped an event's trailing statements. No fixture exhibits this
    // today, so the gap is documented rather than fixed (refusing to add
    // unused code per CLAUDE.md). If a future fixture shows a DoOnce
    // region with dropped trailing content, replicate the IfThen own-exit
    // pattern here.
    let mut out = preamble;
    out.push(Stmt::Latch {
        kind: LatchKind::DoOnce {
            name: derived_name,
            gate_var: gate_var_name,
        },
        init: vec![],
        body,
        offset: terminator_addr,
    });
    Some(out)
}

/// Naked-if-with-latent-call fallback used by `try_emit_ifthen_region`
/// and `try_emit_ifthenelse_region` when the entry block's terminator
/// isn't an `EX_JUMP_IF_NOT`. The Blueprint compiler emits this shape
/// when a latent (Delay / SetTimer / similar) call is gated by a
/// Branch:
///
/// ```text
/// EX_LET temp = !cond                              <- preamble
/// EX_POP_FLOW_IF_NOT cond                          <- the gate
/// EX_CALL_FINAL_FUNCTION Delay(args)               <- latent body
/// EX_POP_EXECUTION_FLOW                            <- close frame (in fallthrough block)
/// ... resume target ...                            <- continuation (in latent_resume successor)
/// ```
///
/// The latent call's `SkipOffset` operand wires a successor edge from
/// the call to the resume target, so the entry block has 2 CFG
/// successors and classifies as `IfThen` / `IfThenElse`. The gate
/// itself is the `pop_flow_if_not` mid-block, not the call. This
/// helper finds that opcode, decodes everything before it as the
/// preamble (temp assignments / instrumentation), and delegates body
/// recognition to `naked_if::try_decode_naked_if`, which walks for
/// the matching `EX_POP_EXECUTION_FLOW` across block boundaries.
///
/// Returns `None` when the entry block holds no `pop_flow_if_not`,
/// when the cond is a literal (DoOnce init-scaffold tail), when the
/// entry sits inside a sibling claim, or when the matching pop can't
/// be located. In any of these cases the caller falls through to the
/// `walk_region` Linear default, which re-decodes the block via
/// `decode_region_block_if_unclaimed`.
///
/// The widened range_end (full bytecode length) is safe because
/// `find_matching_pop_execution_flow` bounds its walk by depth-1 of
/// the flow stack and by a `MAX_BODY_OPCODES` cap, so the search
/// terminates at the correct `EX_POP_EXECUTION_FLOW` without sliding
/// into sibling regions.
pub(super) fn try_emit_pop_flow_if_not_branch_region(
    region: &Region,
    region_id: RegionId,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Option<Vec<Stmt>> {
    let entry_block = cfg.blocks.get(region.entry)?;
    let pop_flow_if_not_addr = entry_block
        .opcodes
        .iter()
        .copied()
        .find(|addr| ctx.bytecode.get(*addr).copied() == Some(EX_POP_FLOW_IF_NOT))?;

    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    // Bound the preamble decode at the pop_flow_if_not so a multi-opcode
    // recogniser (Call with a latent resume edge, nested Branch, etc.)
    // can't accidentally consume the gate we're about to wrap.
    let preamble =
        decode_entry_preamble(entry_block, pop_flow_if_not_addr, pop_flow_if_not_addr, ctx);

    let mut pos = pop_flow_if_not_addr;
    let body_start_pos = entry_block.start;
    let mut branch_stmt = try_decode_naked_if(&mut pos, ctx.bytecode.len(), ctx)?;
    let body_end_pos = pos;

    // Inner-else splice: when the naked-if body contains a nested Branch
    // whose JIN else-target lives in a region-owned block outside the
    // naked-if body span, route that block into the inner Branch's
    // else_body instead of letting `walk_extra_region_blocks` emit it as
    // a sibling. Without this the inner-else leaks out of the outer
    // if-block (a nested-inner-else shape).
    let splice_consumed = try_splice_inner_else(
        &mut branch_stmt,
        region_id,
        body_start_pos,
        body_end_pos,
        cfg,
        ctx,
    );

    let mut out = preamble;
    out.push(branch_stmt);
    walk_extra_region_blocks(
        region_id,
        body_start_pos,
        body_end_pos,
        cfg,
        ctx,
        &mut out,
        &splice_consumed,
    );
    Some(out)
}

/// Locate a nested `Stmt::Branch` with empty `else_body` whose inner JIN
/// targets a region-owned block sitting outside the naked-if body span,
/// then splice that block's content into the inner Branch's `else_body`.
///
/// Returns the disk byte range of the spliced block so the caller can
/// pass it to `walk_extra_region_blocks` as a pre-consumed span, keeping
/// the trailing-extras walk from re-emitting the same content.
///
/// Conservative: only fires when all three audit conditions hold (empty
/// inner else, JIN target resolves to a region-owned block via
/// `mem_to_disk`, target block is outside the naked-if body span and in
/// the parent region's coverage). Returns `None` in every other case so
/// the existing trailing-extras path is unaffected.
fn try_splice_inner_else(
    outer_branch: &mut Stmt,
    region_id: RegionId,
    body_start_pos: usize,
    body_end_pos: usize,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> Option<Range<usize>> {
    let region_ranges = ctx.region_byte_ranges.and_then(|map| map.get(&region_id))?;
    let mem_to_disk = ctx.mem_to_disk?;

    let outer_then = match outer_branch {
        Stmt::Branch { then_body, .. } => then_body,
        _ => return None,
    };

    // The naked-if itself always has an empty else_body (Form B never
    // synthesises one). Start the search INSIDE the naked-if's then-body
    // so we find the inner JIN's Branch, not the outer.
    let inner = find_inner_branch_with_empty_else(outer_then)?;
    let Stmt::Branch {
        offset: jin_disk,
        else_body: inner_else,
        ..
    } = inner
    else {
        return None;
    };

    let jin_disk = *jin_disk;
    // JIN layout: [opcode byte][4-byte mem target operand][cond expr...]
    const JIN_OPCODE_BYTES: usize = 1;
    const JIN_TARGET_BYTES: usize = 4;
    let target_operand_pos = jin_disk.checked_add(JIN_OPCODE_BYTES)?;
    if target_operand_pos + JIN_TARGET_BYTES > ctx.bytecode.len() {
        return None;
    }
    let mut peek = target_operand_pos;
    let target_mem = crate::bytecode::decode::branch::read_jump_target(ctx.bytecode, &mut peek);
    let target_disk = *mem_to_disk.get(&target_mem)?;

    // Target must point outside the naked-if body span (otherwise it's
    // an in-body branch that decode_naked_if_body already classified
    // correctly).
    if target_disk >= body_start_pos && target_disk < body_end_pos {
        return None;
    }

    // Find the CFG block whose start is exactly target_disk and whose
    // coverage intersects the parent region. The block must also live
    // outside the naked-if body span (defense in depth; matches the
    // target_disk gate above).
    let block = cfg.blocks.iter().find(|block| {
        block.start == target_disk
            && !block.opcodes.is_empty()
            && (block.end <= body_start_pos || block.start >= body_end_pos)
            && region_ranges
                .iter()
                .any(|range| block.start < range.end && range.start < block.end)
    })?;

    let mut spliced: Vec<Stmt> = Vec::new();
    let mut consumed: Vec<Range<usize>> = Vec::new();
    decode_block_opcodes(
        cfg,
        block.id,
        ctx,
        &mut spliced,
        &mut consumed,
        region_ranges,
    );
    if spliced.is_empty() {
        return None;
    }

    *inner_else = spliced;
    Some(block.start..block.end)
}

/// Descend into `stmts` looking for a `Stmt::Branch` with empty
/// `else_body`. Searches then-bodies first (the nested-inner-else shape
/// nests the candidate inside the outer naked-if's then-body), then
/// else-bodies as defense in depth. Returns the first match found in DFS order.
fn find_inner_branch_with_empty_else(stmts: &mut [Stmt]) -> Option<&mut Stmt> {
    for stmt in stmts {
        if !matches!(stmt, Stmt::Branch { .. }) {
            continue;
        }
        // Two-pass over each Branch: first check if THIS one matches;
        // if not, recurse into its bodies. The two checks can't borrow
        // the same Stmt mutably at the same time, so they're sequenced.
        let is_match = matches!(stmt, Stmt::Branch { else_body, .. } if else_body.is_empty());
        if is_match {
            return Some(stmt);
        }
        if let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = stmt
        {
            if let Some(found) = find_inner_branch_with_empty_else(then_body) {
                return Some(found);
            }
            if let Some(found) = find_inner_branch_with_empty_else(else_body) {
                return Some(found);
            }
        }
    }
    None
}

/// True when `name` matches one of the BP-emitted DoOnce gate prefixes.
/// Uses the shared `DOONCE_GATE_PREFIX` / `DOONCE_INIT_PREFIX` consts, the
/// same prefixes `cfg/region.rs::is_doonce_gate` checks.
fn is_doonce_gate_var_name(name: &str) -> bool {
    name.starts_with(DOONCE_GATE_PREFIX) || name.starts_with(DOONCE_INIT_PREFIX)
}

/// True when `stmt` is `gate_name = true` (the DoOnce gate self-close
/// scaffold). Mirrors `is_gate_self_assignment` in `latch_recognition`.
fn is_gate_self_set(stmt: &Stmt, gate_name: &str) -> bool {
    let Stmt::Assignment { lhs, rhs, .. } = stmt else {
        return false;
    };
    let Expr::Var(lhs_name) = lhs else {
        return false;
    };
    if lhs_name != gate_name {
        return false;
    }
    matches!(rhs, Expr::Literal(text) if text == "true")
}

/// Derive a DoOnce display name from the gate-open arm body. Picks the
/// first non-library call-target name AT OR AFTER `anchor_offset`,
/// reflecting the BP-emitted layout where the user body lives at or
/// past the JIN's disk address; displaced pre-anchor content (visible
/// in disk order because of push/pop resume edges) is ignored for
/// naming. Falls back to `pick_first_user_call` (any position) when no
/// post-anchor user call is found, and finally to a
/// `DoOnce_<suffix>` constructed from the gate-variable suffix.
fn derive_doonce_name_from_body(body: &[Stmt], gate_var: &str, anchor_offset: usize) -> String {
    if let Some(name) = pick_user_call_at_or_after(body, anchor_offset) {
        return name;
    }
    if let Some(name) = pick_first_user_call(body) {
        return name;
    }
    let suffix = gate_var
        .trim_start_matches(DOONCE_GATE_PREFIX)
        .trim_start_matches(DOONCE_INIT_PREFIX)
        .trim_start_matches('_');
    if suffix.is_empty() {
        "DoOnce".to_string()
    } else {
        format!("DoOnce_{}", suffix)
    }
}

/// Same as `pick_first_user_call` but only considers stmts whose
/// offset is at or after `anchor_offset`. Used by the DoOnce naming
/// path to skip displaced pre-JIN content the BFS reaches via
/// pop_flow resume edges.
fn pick_user_call_at_or_after(stmts: &[Stmt], anchor_offset: usize) -> Option<String> {
    for stmt in stmts {
        if stmt.offset() >= anchor_offset {
            let direct = stmt_user_call_name(stmt);
            if let Some(name) = direct.filter(|name| !is_library_prefix(name)) {
                return Some(name);
            }
        }
        for slice in stmt.child_bodies() {
            if let Some(name) = pick_user_call_at_or_after(slice, anchor_offset) {
                return Some(name);
            }
        }
    }
    None
}

fn pick_first_user_call(stmts: &[Stmt]) -> Option<String> {
    for stmt in stmts {
        let direct = stmt_user_call_name(stmt);
        if let Some(name) = direct.filter(|name| !is_library_prefix(name)) {
            return Some(name);
        }
        for slice in stmt.child_bodies() {
            if let Some(name) = pick_first_user_call(slice) {
                return Some(name);
            }
        }
    }
    None
}

/// Pick a user-call-name from a single statement. Mirrors the shape
/// rules in `latch_recognition::stmt_call_display_name`: `Stmt::Call` may
/// carry the callee as `Var`/`FieldAccess`/`Call`/`MethodCall`, but a
/// `Stmt::Assignment` rhs only qualifies when it is actually call-shaped
/// (`Call`/`MethodCall`). A bare `var = othervar` copy is not a call.
fn stmt_user_call_name(stmt: &Stmt) -> Option<String> {
    match stmt {
        Stmt::Call { func, .. } => call_target_name(func),
        Stmt::Assignment { rhs, .. } => call_target_name_for_assign_rhs(rhs),
        _ => None,
    }
}

/// Extract a display name from a call-shaped `Expr` (Call / MethodCall /
/// bare Var produced by `decode_call`'s function-name unwrap).
fn call_target_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call { name, .. } | Expr::MethodCall { name, .. } | Expr::Var(name) => {
            Some(name.clone())
        }
        _ => None,
    }
}

/// Variant of `call_target_name` for the rhs of `Stmt::Assignment`. Only
/// accepts `Call`/`MethodCall`; rejects bare `Var` (value copy from a
/// temp, not a call) and other shapes.
fn call_target_name_for_assign_rhs(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call { name, .. } | Expr::MethodCall { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// Compact library-prefix filter for DoOnce naming. Subset of the full
/// list in `transforms::latch_recognition::LIBRARY_FUNC_PREFIXES`.
fn is_library_prefix(name: &str) -> bool {
    const LIBRARY_PREFIXES: &[&str] = &[
        "Select",
        "Multiply_",
        "Add_",
        "Subtract_",
        "Divide_",
        "Abs",
        "FClamp",
        "MakeVector",
        "MakeRotator",
        "MakeTransform",
        "BreakVector",
        "BreakRotator",
        "ComposeRotators",
        "VSize",
        "Normalize",
        "GetPlayerController",
        "GetPlayerCameraManager",
        "GetWorldDeltaSeconds",
        "IsValid",
        "PrintString",
    ];
    LIBRARY_PREFIXES.iter().any(|p| name.starts_with(p))
}
