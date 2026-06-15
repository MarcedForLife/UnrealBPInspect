use super::*;

/// Region-driven emitter for `RegionKind::SequenceChain`. Returns a
/// `Vec<Stmt>` containing the entry block's pre-PUSH preamble stmts
/// followed by a `Stmt::Sequence { pins }` carrying one body per
/// execution-ordered pin. Returns `None` when the region's entry block
/// doesn't end with `EX_PUSH_EXECUTION_FLOW` or when the chain head has
/// no skeleton entry (synthetic contexts).
///
/// Pin ordering: `try_decode_sequence` documents (and `PushChainNode`'s
/// docs confirm) that `pin_partitions[i]` is execution order, with
/// `pin_partitions[0]` being the inline body that starts at
/// `after_chain` (the fallthrough after the last push) and
/// `pin_partitions[1..]` being each pushed target in reverse push order
/// (last push runs first after the fallthrough completes its POP). The
/// skeleton has already normalized to this order, so the emitter walks
/// `pin_partitions` directly.
///
/// Per-pin body walk: BFS from the pin's first-segment entry block,
/// gated by strict dominance from that block (mirroring
/// `decode_arm_body`) and bounded by an exclusion set of every OTHER
/// pin's entry block plus the region exit. Walking under the existing
/// per-opcode decoder lets multi-opcode recognisers (Call, Let, nested
/// Branch, nested Sequence) consume their full span.
pub(super) fn try_emit_sequencechain_region(
    region: &Region,
    region_id: RegionId,
    walk: RegionWalkCtx,
    region_tree: &RegionTree,
) -> Option<Vec<Stmt>> {
    let RegionWalkCtx { cfg, ctx, idom: _ } = walk;
    if region.kind != RegionKind::SequenceChain {
        return None;
    }
    let entry_block = cfg.blocks.get(region.entry)?;
    let terminator_addr = *entry_block.opcodes.last()?;
    if *ctx.bytecode.get(terminator_addr)? != EX_PUSH_EXECUTION_FLOW {
        return None;
    }
    let skeleton = ctx.skeleton?;
    // Push-to-epilogue dedup: when the entry-block PUSH has no chain
    // node of its own, the skeleton keyed the chain at an INNER push whose
    // pin body the SESE tree carved as a SIBLING region of the inner chain's
    // pin-owner (because the outer push-to-epilogue dominates it). The
    // disk-order fallback then emits that pin body twice: once via the inner
    // chain's partition fallback, once as the standalone sibling region.
    // Aliasing this region's lookup to the inner chain makes THIS region's
    // emitter fire over the whole subtree, which the walker marks consumed,
    // so the fallback never double-emits.
    //
    // Two conditions, both load-bearing (each alone over-fires across the
    // SequenceChain corpus): the missed push's continuation is the function's
    // sole EX_RETURN / EX_END_OF_SCRIPT block, and an inner SequenceChain
    // child of this region has a pin body owned by a sibling outside the
    // inner chain's subtree (the mis-nesting, which also yields the alias
    // head).
    let chain_node = match skeleton.push_chains.get(&terminator_addr) {
        Some(node) => node,
        None => {
            let sole_return =
                push_continuation_is_sole_return(region.entry, terminator_addr, cfg, ctx);
            if !sole_return {
                return None;
            }
            let alias_head = sibling_pinbody_misnesting(region_id, skeleton, cfg, region_tree)?;
            skeleton.push_chains.get(&alias_head)?
        }
    };
    if chain_node.pin_partitions.is_empty() {
        return None;
    }

    let _owner_guard = ctx.with_decoding_owner(OwnerId::CfgRegion { region_id });

    // Pre-PUSH preamble: opcodes in the entry block before the terminating
    // push. Mirrors the IfThenElse / DoOnce preamble walk so multi-opcode
    // constructs (Let, Call) inside the entry block consume their span.
    let preamble = decode_entry_preamble(entry_block, terminator_addr, entry_block.end, ctx);

    // Identify each pin's entry block via its first partition segment's
    // start address. The CFG only marks an address as a block leader when
    // it has 2+ in-degree or its unique predecessor is a multi-successor
    // opcode / explicit terminator; an `EX_JUMP` target with a single
    // predecessor is not promoted, so the target chains into the previous
    // block as a fallthrough. Pin bodies reached via JUMP from a sibling
    // pin therefore land mid-block. Fall back to byte-range decode (via
    // the pin's own partition segments) for pins whose entry doesn't
    // align with a block leader; that matches `try_decode_sequence`'s
    // `decode_subrange` path semantically.
    let pin_entries: Vec<Option<BlockId>> = chain_node
        .pin_partitions
        .iter()
        .map(|segments| {
            let seg_block = segments
                .first()
                .and_then(|range| cfg.block_at_start(range.start));
            // Body-before-scaffold climb: when the pin's lowest-disk segment
            // block sits interior to a wrapper IfThenElse whose branch
            // scaffold precedes the pin body in disk order, re-target the pin
            // entry at the wrapper's entry so the per-block BFS dispatches the
            // wrapper (rendering its guard + else-arm) instead of starting
            // interior to it.
            if let Some(block) = seg_block {
                if let Some(wrapper_id) =
                    climb_to_wrapper_region_for_pin(block, region_id, segments, region_tree, ctx)
                {
                    return Some(region_tree.regions[wrapper_id].entry);
                }
            }
            seg_block
        })
        .collect();
    let other_pin_entry_set: BTreeSet<BlockId> = pin_entries.iter().filter_map(|id| *id).collect();

    let mut pins: Vec<Vec<Stmt>> = Vec::with_capacity(pin_entries.len());
    for (pin_idx, maybe_entry) in pin_entries.iter().enumerate() {
        let pin_body = match maybe_entry {
            // The pin entry block aligns with a CFG block leader AND the SESE
            // region tree assigns that block (or a descendant) to this
            // SequenceChain region. Run the dominance-bounded BFS.
            Some(pin_entry) if block_in_region_subtree(*pin_entry, region_id, region_tree) => {
                let mut other_pins: BTreeSet<BlockId> = other_pin_entry_set.clone();
                other_pins.remove(pin_entry);
                decode_pin_body(
                    *pin_entry,
                    region.exit,
                    &other_pins,
                    walk,
                    region_tree,
                    region_id,
                    &chain_node.pin_partitions[pin_idx],
                )
            }
            // Pin entry exists as a block leader but lives outside this
            // SequenceChain's region subtree. Happens for nested
            // SequenceChain regions whose PIN0 (the after-chain
            // fallthrough) is dominated by the inner region's exit and
            // therefore classified into an ancestor region by SESE
            // decomposition. The per-block BFS would call
            // `decode_block_opcodes`, which filters owned-claim bytes
            // outside the parent CfgRegion's `region_byte_ranges`,
            // leaving the pin empty. Fall back to the partition-based
            // byte-range decode (same path used when there is no block
            // leader at all) so the chain's pin bytes decode through
            // `decode_subrange`'s non-linear-sweep claim semantics.
            _ => decode_pin_body_via_partition(&chain_node.pin_partitions[pin_idx], ctx),
        };
        pins.push(pin_body);
    }

    let mut out = preamble;
    out.push(Stmt::Sequence {
        pins,
        offset: terminator_addr,
    });
    Some(out)
}

/// Discriminator: the `EX_PUSH_EXECUTION_FLOW` at `terminator_addr`
/// pushes a continuation that is the function's sole `EX_RETURN` /
/// `EX_END_OF_SCRIPT` block (the push-to-epilogue shape). The push's CFG
/// `successors[0]` is the pushed continuation (see `cfg/build.rs`).
fn push_continuation_is_sole_return(
    entry_block_id: BlockId,
    terminator_addr: usize,
    cfg: &ControlFlowGraph,
    ctx: &DecodeCtx,
) -> bool {
    if ctx.bytecode.get(terminator_addr).copied() != Some(EX_PUSH_EXECUTION_FLOW) {
        return false;
    }
    let Some(succs) = cfg.successors.get(&entry_block_id) else {
        return false;
    };
    let Some(&continuation_block) = succs.first() else {
        return false;
    };
    // The continuation must itself terminate in EX_RETURN / EX_END_OF_SCRIPT
    // and be the ONLY such block in the function (the unique epilogue).
    let mut return_blocks = cfg.blocks.iter().filter(|block| {
        block
            .opcodes
            .last()
            .and_then(|&addr| ctx.bytecode.get(addr))
            .map(|&byte| matches!(byte, EX_RETURN | EX_END_OF_SCRIPT))
            .unwrap_or(false)
    });
    match (return_blocks.next(), return_blocks.next()) {
        (Some(only_return), None) => only_return.id == continuation_block,
        _ => false,
    }
}

/// Mis-nesting discriminator + alias resolver. The missed-push region
/// `region_id` (r0) has an inner SequenceChain child (the chain owner) whose
/// pin body SESE carved as a sibling region of that child rather than nested
/// under it, so r0's disk-order walk emits the body standalone in addition
/// to the inner chain's partition fallback (the duplication).
///
/// Returns the inner chain's head address (to alias r0's lookup to) when the
/// mis-nesting is present, `None` otherwise so ordinary push-to-epilogue
/// chains (whose pin bodies nest correctly) are left untouched.
fn sibling_pinbody_misnesting(
    region_id: RegionId,
    skeleton: &crate::bytecode::structure::StructureSkeleton,
    cfg: &ControlFlowGraph,
    region_tree: &RegionTree,
) -> Option<usize> {
    // The chain head address is the PUSH opcode, which is its block's
    // TERMINATOR, not the block start (e.g. an inner push at
    // 0x8 sits inside block b1 = [0x5..0xd]). Resolve the block that
    // CONTAINS the head address, then its region owner.
    let block_containing = |addr: usize| -> Option<BlockId> {
        cfg.blocks
            .iter()
            .find(|block| block.start <= addr && addr < block.end && !block.opcodes.is_empty())
            .map(|block| block.id)
    };

    // Candidate inner chains: chain heads whose containing block is owned by
    // a STRICT descendant region of `region_id` (the inner chain owner r1 is
    // a child of r0, not r0 itself). Lowest address first (nearest).
    let mut candidate_heads: Vec<usize> = skeleton
        .push_chains
        .keys()
        .copied()
        .filter(|&head_addr| {
            let Some(head_block) = block_containing(head_addr) else {
                return false;
            };
            block_in_region_subtree(head_block, region_id, region_tree)
                && region_tree.block_to_region.get(&head_block).copied() != Some(region_id)
        })
        .collect();
    candidate_heads.sort_unstable();

    for inner_head in candidate_heads {
        let Some(inner_node) = skeleton.push_chains.get(&inner_head) else {
            continue;
        };
        let Some(inner_head_block) = block_containing(inner_head) else {
            continue;
        };
        let Some(&inner_owner) = region_tree.block_to_region.get(&inner_head_block) else {
            continue;
        };
        // The inner chain owner must be a direct child of r0; a deeper-nested
        // inner chain would over-claim across intervening regions when aliased
        // (an observed over-fire).
        if region_tree.regions[inner_owner].parent != Some(region_id) {
            continue;
        }
        // At least one pin body of the inner chain must live in a DIFFERENT
        // direct child of r0 than the inner owner (the displaced sibling that
        // r0's disk-order walk emits standalone, producing the second copy).
        // Deeper-nested displaced bodies are not standalone r0 children, so
        // they leave no duplicate to dedup and are excluded.
        let has_sibling_pinbody = inner_node.pin_partitions.iter().any(|segments| {
            segments.iter().any(|seg| {
                let Some(body_block) = cfg.block_at_start(seg.start) else {
                    return false;
                };
                let Some(&body_region) = region_tree.block_to_region.get(&body_block) else {
                    return false;
                };
                // The direct child of r0 containing this pin body, when it is
                // not the inner owner itself, is the displaced sibling.
                topmost_descendant_with_parent(body_region, region_id, region_tree)
                    .is_some_and(|direct_child| direct_child != inner_owner)
            })
        });
        if has_sibling_pinbody {
            return Some(inner_head);
        }
    }
    None
}

/// Climb from `region` toward the root and return the topmost ancestor
/// (including `region` itself) whose immediate parent is `parent`. `None`
/// when `parent` is not an ancestor of `region`.
fn topmost_descendant_with_parent(
    region: RegionId,
    parent: RegionId,
    region_tree: &RegionTree,
) -> Option<RegionId> {
    let mut cursor = region;
    loop {
        match region_tree.regions[cursor].parent {
            Some(p) if p == parent => return Some(cursor),
            Some(p) => cursor = p,
            None => return None,
        }
    }
}
