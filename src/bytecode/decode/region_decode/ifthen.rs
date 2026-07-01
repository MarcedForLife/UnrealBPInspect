use super::*;

/// Region-driven emitter for `RegionKind::IfThen`. Degenerate case of
/// `IfThenElse` where one arm bypasses to `region.exit`. Emits
/// `Stmt::Branch` with an empty `else_body`. Mirrors
/// `try_emit_ifthenelse_region`'s CFG-successor convention (succs[0] =
/// JIN target / cond false, succs[1] = fallthrough / cond true) and
/// wraps cond in `Expr::Unary { Not, .. }` when the body lives on the
/// JIN-taken arm so the rendered branch reads `if !cond { body }`.
pub(super) fn try_emit_ifthen_region(
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: Option<&RegionTree>,
) -> Option<Vec<Stmt>> {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    if region.kind != RegionKind::IfThen {
        return None;
    }
    // Dispatch-table probe: see `try_emit_ifthenelse_region` for the
    // rationale. A `K2Node_SwitchEnum` whose case 0 jumps directly to
    // the region exit lands here as IfThen rather than IfThenElse, so
    // the probe runs in both emitters.
    if let Some(stmt) = try_emit_jumpifnot_cascade_region(region, region_id, cfg, ctx) {
        return Some(vec![stmt]);
    }
    // The kind check stays above the cascade probe; the helper re-checks it
    // redundantly. A terminator miss here routes to the pop_flow fallback,
    // not a bail, so consume the Option instead of `?`.
    let Some((entry_block, terminator_addr)) =
        region_entry_terminator(region, RegionKind::IfThen, EX_JUMP_IF_NOT, cfg, ctx)
    else {
        // See try_emit_ifthenelse_region for the naked-if-with-latent-
        // call shape this fallback handles.
        return try_emit_pop_flow_if_not_branch_region(region, region_id, cfg, ctx);
    };

    // Nested-naked-if shape: see `try_emit_ifthenelse_region` for the
    // byte-layout. Same dispatch into the pop_flow_if_not helper so
    // the outer naked-if wraps the inner JIN-Branch as its body
    // rather than the inner Branch and outer pop_flow_if_not both
    // emitting at the region level (which produces a duplicated
    // inner Branch).
    if has_earlier_pop_flow_if_not(entry_block, terminator_addr, ctx) {
        return try_emit_pop_flow_if_not_branch_region(region, region_id, cfg, ctx);
    }

    let cond = decode_jin_cond(terminator_addr, ctx)?;

    let succs = cfg.successors.get(&region.entry)?;
    if succs.len() != 2 {
        return None;
    }
    let (body_arm_entry, negate) = if succs[1] == region.exit {
        // Fallthrough lands at exit; body runs on the JIN-taken arm
        // (cond false). Negate so the rendered Branch reads
        // `if !cond { body }`.
        (succs[0], true)
    } else if succs[0] == region.exit {
        // JIN target is exit; body lives on the fallthrough arm.
        (succs[1], false)
    } else {
        return None;
    };
    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    let preamble = decode_entry_preamble(entry_block, terminator_addr, entry_block.end, ctx);

    // Decode the body region-aware (dispatching descendant regions through
    // the walker, the same path IfThenElse arms use) so nested constructs
    // and shared-convergence jumps nest correctly. Fall back to the flat
    // byte-slice arm decode when the region tree is unavailable (synthetic
    // contexts) or the dispatch can't resolve the arm.
    let then_body = region_tree
        .and_then(|tree| {
            decode_arm_via_region_dispatch(
                body_arm_entry,
                None,
                region,
                region_id,
                walk,
                tree,
                None,
            )
        })
        .unwrap_or_else(|| decode_arm_body(body_arm_entry, None, region, region_id, walk));
    let final_cond = if negate {
        Expr::Unary {
            op: crate::bytecode::expr::UnaryOp::Not,
            operand: Box::new(cond),
        }
    } else {
        cond
    };

    // Own-exit-with-content dispatch: when the region's own exit
    // block carries user content, emit the IfThen as `Branch + tail`
    // siblings. For IfThen there is only a body arm, so both
    // reachability sub-cases of `try_emit_ifthenelse_region`'s
    // dispatch collapse to sibling-level: when the body reaches exit,
    // the tail is a shared join (the IfThenElse `(true, true)`
    // analog); when the body terminates, the tail is reachable only
    // on the cond-false bypass, which still emits sibling-level (no
    // synthetic else arm is fabricated).
    //
    // Gate guard: only fire when the region's parent doesn't already
    // absorb the same exit content via arm-body BFS. See
    // `parent_owns_or_absorbs_exit` for the discriminator. Without
    // the guard, an inner IfThen duplicates the trailing call already
    // absorbed by an outer IfThenElse's then-arm.
    let own_exit = region_tree
        .map(|tree| is_own_exit_with_content(region_id, tree, cfg))
        .unwrap_or(false);
    let parent_pulls_same_exit = region_tree
        .map(|tree| parent_owns_or_absorbs_exit(region_id, tree, cfg))
        .unwrap_or(false);
    // `own_exit` implies `region_tree` is Some (computed from it above), so
    // folding the match in here can't drop the path, just avoids an expect.
    if let (true, Some(tree)) = (own_exit && !parent_pulls_same_exit, region_tree) {
        let tail = decode_post_merge_continuation(region_id, tree, cfg, ctx);
        if !tail_is_droppable(&tail) {
            let mut out = preamble;
            out.push(Stmt::Branch {
                cond: final_cond,
                then_body,
                else_body: Vec::new(),
                offset: terminator_addr,
            });
            out.extend(tail);
            return Some(out);
        }
    }

    let mut out = preamble;
    out.push(Stmt::Branch {
        cond: final_cond,
        then_body,
        else_body: Vec::new(),
        offset: terminator_addr,
    });
    Some(out)
}

/// Discriminator for the IfThen own-exit dispatch: returns true
/// when one of `region_id`'s ancestors (via parent chain) is an
/// arm-body-decoding region kind (IfThenElse / IfThen / DoOnceGate /
/// Loop / Switch) whose decode_arm_body BFS from its arm root would
/// reach the inner IfThen's exit block before hitting the ancestor's
/// own exit. When true, the ancestor already absorbs the trailing
/// content via arm-body BFS and the IfThen must NOT pull it again
/// (which would duplicate content).
///
/// The check is conservative: any ancestor whose region transitively
/// contains the IfThen's exit block AND uses arm-body BFS counts as
/// "absorbs". Linear / Trivial / SequenceChain ancestors don't absorb
/// (they walk disk-order, bounded by region ranges), so IfThens
/// directly under those kinds correctly pull their own exit content.
pub(super) fn parent_owns_or_absorbs_exit(
    region_id: RegionId,
    region_tree: &RegionTree,
    cfg: &ControlFlowGraph,
) -> bool {
    let _ = cfg;
    let region = match region_tree.regions.get(region_id) {
        Some(region) => region,
        None => return false,
    };
    let inner_exit = region.exit;
    let mut current_id = region_id;
    let mut current_parent_id = region.parent;
    while let Some(parent_id) = current_parent_id {
        let parent = match region_tree.regions.get(parent_id) {
            Some(parent) => parent,
            None => break,
        };
        // Per-kind emitters that decode arm bodies via BFS bounded by
        // region.exit. Linear/Trivial/SequenceChain ancestors walk
        // disk-order and never absorb a descendant's exit block.
        let absorbs = matches!(
            parent.kind,
            RegionKind::IfThenElse
                | RegionKind::IfThen
                | RegionKind::DoOnceGate
                | RegionKind::Loop
                | RegionKind::Switch
        );
        if absorbs {
            // The walker defers the parent's per-kind emit when an
            // immediate child shares its entry (see `walk_region`'s
            // `defer_to_inner_sibling` gate). In
            // that case the parent's arm-body BFS never runs, so the
            // inner's exit content is NOT absorbed and the own-exit
            // dispatch should pull. Otherwise the parent's arm-body BFS,
            // bounded by parent.exit, transitively reaches inner_exit (which
            // sits in the parent's region coverage) and absorbs it;
            // the own-exit dispatch must not double-pull.
            let parent_defers_to_current = region_tree
                .regions
                .get(current_id)
                .map(|child| child.entry == parent.entry)
                .unwrap_or(false);
            if !parent_defers_to_current && parent.exit != inner_exit {
                if let Some(&owner_id) = region_tree.block_to_region.get(&inner_exit) {
                    if region_is_descendant_of(owner_id, parent_id, region_tree) {
                        return true;
                    }
                }
            }
        }
        current_id = parent_id;
        current_parent_id = parent.parent;
    }
    false
}
