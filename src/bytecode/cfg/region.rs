//! Single-entry single-exit (SESE) region decomposition.
//!
//! Builds a nested tree of regions over a `ControlFlowGraph` using its
//! dominance and post-dominance maps. Each region is a pair `(entry,
//! exit)` such that `entry` dominates `exit`, `exit` post-dominates
//! `entry`, and every path from outside the region into it passes
//! through `entry` (and analogously for `exit`).
//!
//! The decomposition is the program structure tree (PST) of Johnson 1994
//! restricted to dominator/post-dominator-paired regions. Two regions are
//! always either nested or disjoint, never partially overlapping.
//!
//! The whole CFG sits inside an outermost region `(entry_block,
//! sink_block)` where `sink_block` is the unique block reached by every
//! event-exit path. When the CFG has multiple terminators (e.g. an
//! `EX_RETURN` plus an unreachable `EX_END_OF_SCRIPT`), no single real
//! post-dominator exists; the outermost region is then synthesised with
//! the entry's `ipostdom` if available, falling back to the entry alone.
//!
//! Each region carries a `RegionKind` derived from its entry block's
//! terminator opcode and successor shape: `IfThenElse`, `IfThen`,
//! `Switch`, `Loop`, `Linear`, `SequenceChain`, `DoOnceGate`, or `Trivial`.
//!
//! Linear-merge invariant.
//! `build_region_tree_with_linear_merges` runs after the SESE tree is built
//! and synthesises a Linear sibling for any merge block that would otherwise
//! sit under a byte-sliced descendant region. Without this pass, a merge
//! block owned (under innermost-wins) by an inner IfThen/IfThenElse whose
//! parent byte-slices it never gets walked as a region, so the merge
//! block's content is silently dropped by `mark_region_consumed`. The
//! synthesised Linear sibling guarantees every content-bearing block has
//! a region the walker visits directly, so the SESE walker has single-
//! owner coverage of all content. See `region_linear.rs` for the rule.

use std::collections::{BTreeMap, BTreeSet};

use crate::binary::NameTable;
use crate::bytecode::opcodes::{
    EX_INSTANCE_VARIABLE, EX_JUMP_IF_NOT, EX_LOCAL_VARIABLE, EX_PUSH_EXECUTION_FLOW,
    EX_SWITCH_VALUE,
};
use crate::bytecode::partition::OpcodeGraph;
use crate::bytecode::readers::{read_bc_fname, read_bc_i32};
use crate::bytecode::transforms::latch_recognition::{DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX};

use super::{reachable_bounded, BlockId, BoundedReach, ControlFlowGraph};

/// Names beginning with any of these prefixes are synthetic gate booleans
/// the BP compiler emits for `DoOnce` and similar single-shot latches.
/// `DOONCE_GATE_PREFIX` is the gate-close pattern; `DOONCE_INIT_PREFIX` is the
/// init-pin pattern emitted by the DoOnce macro.
const DOONCE_GATE_PREFIXES: &[&str] = &[DOONCE_GATE_PREFIX, DOONCE_INIT_PREFIX];

/// Optional bytecode-side context that lets the classifier inspect
/// operand bytes (jump targets, condition variable names). When `None`,
/// the classifier falls back to opcode-only patterns; synthetic unit
/// tests that have no real bytecode pass `None`.
///
/// `mem_to_disk` maps memory-coordinate jump targets (as written in the
/// bytecode stream) to disk-coordinate block starts (as used by
/// `ControlFlowGraph`). The map is used by `DoOnceGate` and branch-range
/// classifiers. Pass `None` when the translation map is unavailable
/// (e.g. synthetic unit tests).
#[derive(Clone, Copy)]
pub struct RegionContext<'a> {
    pub bytecode: &'a [u8],
    pub ue5: i32,
    pub name_table: &'a NameTable,
    pub mem_to_disk: Option<&'a BTreeMap<usize, usize>>,
}

/// Identifier for a region within one `RegionTree`. Indexes into
/// `RegionTree::regions`.
pub type RegionId = usize;

/// Classification of a region by its entry block's branching shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionKind {
    /// Straight-line sequence of nested regions, no branching at entry.
    Linear,
    /// Two-way branch where one arm bypasses the body and falls straight
    /// to the exit. The other arm is the then-body.
    IfThen,
    /// Two-way branch with both arms non-trivial.
    IfThenElse,
    /// Region whose entry is the head of a natural loop (a back-edge
    /// targets `entry` from a block dominated by `entry`).
    Loop,
    /// N-way branch driven by `EX_SWITCH_VALUE`. Not constructed on current
    /// Blueprint shapes; `EX_SWITCH_VALUE` is value-selecting rather than an
    /// exec branch, so a switch-on-exec never reaches the classifier. Kept so
    /// the classification space stays complete.
    #[allow(dead_code)]
    Switch,
    /// Single block, no internal structure. Not constructed on any committed
    /// fixture; kept as the classifier's degenerate-region fallback.
    #[allow(dead_code)]
    Trivial,
    /// Entry terminates with `EX_PUSH_EXECUTION_FLOW`. The children are
    /// the pinned sub-bodies of a Sequence chain.
    SequenceChain,
    /// `EX_JUMP_IF_NOT` whose condition is a single Var reference to one
    /// of the compiler-generated DoOnce gate booleans
    /// (`Temp_bool_IsClosed_Variable_*` or
    /// `Temp_bool_Has_Been_Initd_Variable_*`). Synthesises into a
    /// `DoOnce` body.
    DoOnceGate,
}

/// One SESE region. `entry` dominates `exit`; `exit` post-dominates
/// `entry`. Both endpoints belong to the parent CFG.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct Region {
    pub id: RegionId,
    pub entry: BlockId,
    pub exit: BlockId,
    pub parent: Option<RegionId>,
    pub children: Vec<RegionId>,
    pub kind: RegionKind,
}

/// Nested SESE region tree for one CFG.
///
/// `root` is the outermost region spanning the whole event. `regions`
/// is dense (every id from 0..regions.len() is occupied) and stored in
/// pre-order traversal. `block_to_region` maps each block to its
/// innermost enclosing region.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct RegionTree {
    pub regions: Vec<Region>,
    pub root: RegionId,
    pub block_to_region: BTreeMap<BlockId, RegionId>,
}

impl RegionTree {
    /// Maximum nesting depth (root region = depth 1).
    pub fn max_depth(&self) -> usize {
        fn walk(tree: &RegionTree, region_id: RegionId, depth: usize) -> usize {
            let region = &tree.regions[region_id];
            let mut deepest = depth;
            for &child in &region.children {
                deepest = deepest.max(walk(tree, child, depth + 1));
            }
            deepest
        }
        walk(self, self.root, 1)
    }

    /// Count of regions by kind. Used by probes for distribution stats.
    pub fn kind_counts(&self) -> BTreeMap<&'static str, usize> {
        let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
        for region in &self.regions {
            let key = region_kind_label(region.kind);
            *counts.entry(key).or_insert(0) += 1;
        }
        counts
    }
}

/// Stable string label for a `RegionKind`. Used by probes and diagnostic
/// dumps; keep in sync with the variant set.
pub fn region_kind_label(kind: RegionKind) -> &'static str {
    match kind {
        RegionKind::Linear => "Linear",
        RegionKind::IfThen => "IfThen",
        RegionKind::IfThenElse => "IfThenElse",
        RegionKind::Loop => "Loop",
        RegionKind::Switch => "Switch",
        RegionKind::Trivial => "Trivial",
        RegionKind::SequenceChain => "SequenceChain",
        RegionKind::DoOnceGate => "DoOnceGate",
    }
}

/// Build a SESE region tree for `cfg`.
///
/// `idom` is `cfg`'s immediate-dominator map (root excluded). `ipostdom`
/// is the immediate-post-dominator map (the synthetic sink is excluded).
/// `graph` provides the opcode byte at each address, used to classify
/// entry-block terminators (`EX_JUMP_IF_NOT` -> branch, `EX_SWITCH_VALUE`
/// -> switch).
pub fn build_region_tree(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ipostdom: &BTreeMap<BlockId, BlockId>,
    graph: &OpcodeGraph,
) -> RegionTree {
    build_region_tree_with(cfg, idom, ipostdom, graph, None)
}

/// Build the SESE region tree with optional bytecode-side context.
///
/// `region_ctx` lets the classifier inspect JIN operands and condition
/// variable names to recognise BP-specific kinds (`SequenceChain`,
/// `DoOnceGate`). Synthetic unit tests pass `None` to stick to
/// opcode-only classification.
pub fn build_region_tree_with(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ipostdom: &BTreeMap<BlockId, BlockId>,
    graph: &OpcodeGraph,
    region_ctx: Option<RegionContext<'_>>,
) -> RegionTree {
    let candidates = collect_candidate_regions(cfg, idom, ipostdom);
    let postdom_distance = compute_postdom_distance(cfg, ipostdom);
    let nesting = nest_regions(cfg, &candidates, idom, &postdom_distance);
    materialise(cfg, &candidates, &nesting, graph, region_ctx)
}

/// Variant of `build_region_tree_with` that additionally runs the
/// post-merge Linear-region extraction pass. See
/// `super::region_linear::extract_post_merge_linears` for the
/// implementation.
///
/// Wired into production decode: `decode/mod.rs` (event region trees) and
/// `k2node_byte_map.rs` both build their region trees through this entry.
/// Also exercised by a local-only integration test when present.
pub fn build_region_tree_with_linear_merges(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ipostdom: &BTreeMap<BlockId, BlockId>,
    graph: &OpcodeGraph,
    region_ctx: Option<RegionContext<'_>>,
) -> RegionTree {
    let mut tree = build_region_tree_with(cfg, idom, ipostdom, graph, region_ctx);
    super::region_linear::extract_post_merge_linears(&mut tree, cfg);
    tree
}

/// Distance from each block to the synthetic sink along the ipostdom
/// chain. The sink itself has distance 0; a block whose ipostdom is
/// the sink has distance 1, and so on. Blocks unreachable along the
/// chain (shouldn't happen post-sink-fix) get `usize::MAX`.
fn compute_postdom_distance(
    cfg: &ControlFlowGraph,
    ipostdom: &BTreeMap<BlockId, BlockId>,
) -> BTreeMap<BlockId, usize> {
    let mut distance: BTreeMap<BlockId, usize> = BTreeMap::new();
    for block in &cfg.blocks {
        let mut cursor = block.id;
        let mut steps = 0usize;
        let mut visited: BTreeSet<BlockId> = BTreeSet::new();
        loop {
            if cursor == cfg.sink {
                break;
            }
            if !visited.insert(cursor) {
                steps = usize::MAX;
                break;
            }
            match ipostdom.get(&cursor) {
                Some(&next) => {
                    cursor = next;
                    steps += 1;
                }
                None => {
                    steps = usize::MAX;
                    break;
                }
            }
        }
        distance.insert(block.id, steps);
    }
    distance
}

/// Candidate `(entry, exit)` pairs.
///
/// The root pair is `(cfg.entry, deepest_postdom)`, where
/// `deepest_postdom` walks the ipostdom chain down from `cfg.entry` to
/// the last block (typically the unique sink). Additional candidates:
/// - branching blocks (2+ successors) paired with their ipostdom,
/// - loop heads (blocks that are the target of a back-edge under the
///   dominator relation) paired with their ipostdom.
fn collect_candidate_regions(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ipostdom: &BTreeMap<BlockId, BlockId>,
) -> Vec<(BlockId, BlockId)> {
    let mut pairs: Vec<(BlockId, BlockId)> = Vec::new();
    let mut seen: BTreeSet<(BlockId, BlockId)> = BTreeSet::new();

    let root_exit = deepest_postdom(cfg.entry, ipostdom);
    pairs.push((cfg.entry, root_exit));
    seen.insert((cfg.entry, root_exit));

    for block in &cfg.blocks {
        let succs = cfg
            .successors
            .get(&block.id)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        let preds = cfg
            .predecessors
            .get(&block.id)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        let is_branching = succs.len() >= 2;
        let is_loop_head = preds
            .iter()
            .any(|&pred| dominates(cfg, idom, block.id, pred));
        if !is_branching && !is_loop_head {
            continue;
        }
        let Some(&exit) = ipostdom.get(&block.id) else {
            continue;
        };
        if exit == block.id {
            continue;
        }
        if seen.insert((block.id, exit)) {
            pairs.push((block.id, exit));
        }
    }

    pairs
}

/// True iff `ancestor` dominates `node` (either equals or is on the
/// idom chain from `node` to the root).
fn dominates(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ancestor: BlockId,
    node: BlockId,
) -> bool {
    if ancestor == node {
        return true;
    }
    strictly_dominates(cfg, idom, ancestor, node)
}

/// Walk down the ipostdom chain from `start` and return the deepest
/// (last) block on it. The chain terminates when a block has no
/// post-dominator entry. Returns `start` itself if no entry exists.
fn deepest_postdom(start: BlockId, ipostdom: &BTreeMap<BlockId, BlockId>) -> BlockId {
    let mut cursor = start;
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    visited.insert(cursor);
    while let Some(&next) = ipostdom.get(&cursor) {
        if !visited.insert(next) {
            break;
        }
        cursor = next;
    }
    cursor
}

/// Determine parent for each candidate region.
///
/// Region `r1 = (a1, e1)` strictly contains `r2 = (a2, e2)` iff `r1`'s
/// block slice is a superset of `r2`'s. Equivalently:
/// - `a1` strictly dominates `a2`, OR
/// - `a1 == a2` and `e2 != e1` and `e2` lies on the ipostdom chain
///   between `a2` and `e1` (i.e. `postdom_distance[e2] >
///   postdom_distance[e1]`).
///
/// Among all containing candidates, pick the innermost: greatest
/// dominator depth of `a1`, then smallest `postdom_distance[e1]`
/// (closest to the inner region's exit).
fn nest_regions(
    cfg: &ControlFlowGraph,
    candidates: &[(BlockId, BlockId)],
    idom: &BTreeMap<BlockId, BlockId>,
    postdom_distance: &BTreeMap<BlockId, usize>,
) -> BTreeMap<RegionId, Option<RegionId>> {
    let mut parents: BTreeMap<RegionId, Option<RegionId>> = BTreeMap::new();
    parents.insert(0, None);

    for (region_id, &(entry, exit)) in candidates.iter().enumerate().skip(1) {
        let exit_distance = postdom_distance.get(&exit).copied().unwrap_or(usize::MAX);
        let mut best: Option<(RegionId, usize, usize)> = None;
        for (candidate_id, &(c_entry, c_exit)) in candidates.iter().enumerate() {
            if candidate_id == region_id {
                continue;
            }
            let c_exit_distance = postdom_distance.get(&c_exit).copied().unwrap_or(usize::MAX);
            let contains = if strictly_dominates(cfg, idom, c_entry, entry) {
                // Different entries: candidate's exit must also enclose
                // ours. The candidate's exit lies on or past our exit
                // along the postdom chain, i.e. is post-dominated by
                // our exit or equals it. Approximated by
                // `c_exit_distance <= exit_distance`.
                c_exit_distance <= exit_distance
            } else if c_entry == entry {
                exit != c_exit && c_exit_distance < exit_distance
            } else {
                false
            };
            if !contains {
                continue;
            }
            let entry_depth = dom_depth(idom, c_entry);
            // Innermost enclosing parent = greatest entry depth
            // (closer to our entry down the dom tree); when entries
            // tie, greater post-dom distance from the sink (exit
            // closer to our entry along the post-dom chain).
            match best {
                None => best = Some((candidate_id, entry_depth, c_exit_distance)),
                Some((_, best_depth, best_exit_distance))
                    if entry_depth > best_depth
                        || (entry_depth == best_depth && c_exit_distance > best_exit_distance) =>
                {
                    best = Some((candidate_id, entry_depth, c_exit_distance));
                }
                _ => {}
            }
        }
        parents.insert(region_id, best.map(|(id, _, _)| id));
    }
    parents
}

/// True iff `ancestor` strictly dominates `node` (i.e. `ancestor` is on
/// the idom chain from `node` to the root, but `ancestor != node`).
fn strictly_dominates(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
    ancestor: BlockId,
    node: BlockId,
) -> bool {
    if ancestor == node {
        return false;
    }
    if ancestor == cfg.entry {
        return true;
    }
    let mut cursor = node;
    while let Some(&parent) = idom.get(&cursor) {
        if parent == ancestor {
            return true;
        }
        if parent == cursor {
            return false;
        }
        cursor = parent;
    }
    false
}

/// Distance from the entry block to `node` along the dominator chain.
/// Entry is depth 0.
fn dom_depth(idom: &BTreeMap<BlockId, BlockId>, node: BlockId) -> usize {
    let mut depth = 0usize;
    let mut cursor = node;
    while let Some(&parent) = idom.get(&cursor) {
        if parent == cursor {
            break;
        }
        depth += 1;
        cursor = parent;
    }
    depth
}

/// Construct the final `RegionTree` from candidates + nesting metadata,
/// assigning each block to its innermost enclosing region and classifying
/// every region by kind.
fn materialise(
    cfg: &ControlFlowGraph,
    candidates: &[(BlockId, BlockId)],
    parents: &BTreeMap<RegionId, Option<RegionId>>,
    graph: &OpcodeGraph,
    region_ctx: Option<RegionContext<'_>>,
) -> RegionTree {
    let mut regions: Vec<Region> = candidates
        .iter()
        .enumerate()
        .map(|(id, &(entry, exit))| Region {
            id,
            entry,
            exit,
            parent: *parents.get(&id).unwrap_or(&None),
            children: Vec::new(),
            kind: RegionKind::Trivial,
        })
        .collect();

    for region_id in 1..regions.len() {
        if let Some(parent_id) = regions[region_id].parent {
            regions[parent_id].children.push(region_id);
        }
    }

    let block_to_region = assign_blocks_to_regions(cfg, &regions);

    let kinds: Vec<RegionKind> = regions
        .iter()
        .map(|region| classify_region(cfg, region, graph, region_ctx))
        .collect();
    for (region, kind) in regions.iter_mut().zip(kinds) {
        region.kind = kind;
    }

    RegionTree {
        regions,
        root: 0,
        block_to_region,
    }
}

/// Each block belongs to the innermost region whose entry dominates it
/// AND whose exit either equals it or is reached only via the exit (i.e.
/// the block is in the entry->exit sub-CFG slice).
///
/// We approximate "in the slice" by: the block is reachable from `entry`
/// without passing through `exit`, OR the block IS `exit`. Then among
/// all regions that contain the block by this test, choose the one
/// whose `entry` has the greatest dominator-tree depth.
fn assign_blocks_to_regions(
    cfg: &ControlFlowGraph,
    regions: &[Region],
) -> BTreeMap<BlockId, RegionId> {
    let mut slices: Vec<BTreeSet<BlockId>> = Vec::with_capacity(regions.len());
    for (region_id, region) in regions.iter().enumerate() {
        let slice = if region_id == 0 {
            // Root region must contain every reachable block, even when
            // the CFG has multiple sinks and no single real post-dom.
            all_reachable_blocks(cfg)
        } else {
            reachable_in_slice(cfg, region.entry, region.exit)
        };
        slices.push(slice);
    }

    let mut block_to_region: BTreeMap<BlockId, RegionId> = BTreeMap::new();
    for block in &cfg.blocks {
        // The synthetic sink stays at the root; it represents the
        // event-exit junction and is not part of any user-visible
        // inner structure.
        if block.id == cfg.sink {
            block_to_region.insert(block.id, 0);
            continue;
        }
        let mut best: Option<(RegionId, usize)> = None;
        for (region_id, _region) in regions.iter().enumerate() {
            if !slices[region_id].contains(&block.id) {
                continue;
            }
            let mut depth = 0usize;
            let mut cursor = Some(region_id);
            while let Some(current) = cursor {
                depth += 1;
                cursor = regions[current].parent;
            }
            match best {
                None => best = Some((region_id, depth)),
                Some((_, best_depth)) if depth > best_depth => {
                    best = Some((region_id, depth));
                }
                _ => {}
            }
        }
        // Fall back to the root region when the block isn't covered by
        // any region's slice. This happens for blocks that aren't
        // forward-reachable from `cfg.entry` via basic-block successors
        // (e.g. PoP-only entry blocks whose body opens via push-target
        // edges originating elsewhere). The root region is a defined
        // catch-all and downstream consumers see every block accounted
        // for.
        let assigned = best.map(|(region_id, _)| region_id).unwrap_or(0);
        block_to_region.insert(block.id, assigned);
    }
    block_to_region
}

/// Set of every block reachable from `cfg.entry`. Used as the slice for
/// the root region so it always covers the whole event, even when the
/// CFG has multiple sinks (e.g. several `EX_RETURN` blocks).
fn all_reachable_blocks(cfg: &ControlFlowGraph) -> BTreeSet<BlockId> {
    let mut reached: BTreeSet<BlockId> = BTreeSet::new();
    let mut frontier: Vec<BlockId> = vec![cfg.entry];
    while let Some(node) = frontier.pop() {
        if !reached.insert(node) {
            continue;
        }
        let succs = cfg
            .successors
            .get(&node)
            .map(|edges| edges.as_slice())
            .unwrap_or(&[]);
        for &succ in succs {
            if !reached.contains(&succ) {
                frontier.push(succ);
            }
        }
    }
    reached
}

/// Set of blocks reachable from `entry` in `cfg` without crossing `exit`,
/// plus `exit` itself. Used to define the membership of a region.
fn reachable_in_slice(cfg: &ControlFlowGraph, entry: BlockId, exit: BlockId) -> BTreeSet<BlockId> {
    reachable_bounded(
        cfg,
        entry,
        exit,
        BoundedReach {
            skip_sink: false,
            include_boundary: true,
        },
    )
}

/// Classify a region by its entry block's terminator and successor
/// shape. The root region uses the same logic against its entry block.
///
/// BP-specific kinds are tested before the generic two-way fallthrough:
/// `SequenceChain` on `EX_PUSH_EXECUTION_FLOW` terminator, `DoOnceGate`
/// on a JIN whose cond is a `Temp_bool_IsClosed_Variable_*` Var.
fn classify_region(
    cfg: &ControlFlowGraph,
    region: &Region,
    graph: &OpcodeGraph,
    region_ctx: Option<RegionContext<'_>>,
) -> RegionKind {
    if has_loop_back_edge(cfg, region) {
        return RegionKind::Loop;
    }

    let entry_block = &cfg.blocks[region.entry];
    let succs = cfg
        .successors
        .get(&region.entry)
        .map(|edges| edges.as_slice())
        .unwrap_or(&[]);

    if entry_block.opcodes.is_empty() {
        return RegionKind::Trivial;
    }
    if succs.is_empty() && region.entry == region.exit {
        return RegionKind::Trivial;
    }

    let terminator_addr = *entry_block.opcodes.last().expect("non-empty block");
    let opcode = graph.opcodes.get(&terminator_addr).copied();

    if matches!(opcode, Some(EX_PUSH_EXECUTION_FLOW)) {
        return RegionKind::SequenceChain;
    }

    if let Some(ctx) = region_ctx {
        if matches!(opcode, Some(EX_JUMP_IF_NOT)) && is_doonce_gate(terminator_addr, ctx) {
            return RegionKind::DoOnceGate;
        }
    }

    match opcode {
        Some(EX_SWITCH_VALUE) if succs.len() >= 2 => RegionKind::Switch,
        Some(EX_JUMP_IF_NOT) if succs.len() == 2 => classify_two_way(cfg, region, succs),
        _ if succs.len() == 1 => RegionKind::Linear,
        _ if succs.len() >= 2 => classify_two_way(cfg, region, succs),
        _ => RegionKind::Trivial,
    }
}

/// True when the JIN at `jin_addr` has a condition of the form
/// `<Var>(<DoOnce gate>)`. The JIN layout is
/// `[opcode byte][4-byte target][cond expression]`; this checks the
/// cond opcode plus the first name on its field path against the
/// `DOONCE_GATE_PREFIXES` list.
fn is_doonce_gate(jin_addr: usize, ctx: RegionContext<'_>) -> bool {
    let cond_opcode_pos = jin_addr.saturating_add(1).saturating_add(4);
    if cond_opcode_pos >= ctx.bytecode.len() {
        return false;
    }
    let cond_opcode = ctx.bytecode[cond_opcode_pos];
    if !matches!(cond_opcode, EX_INSTANCE_VARIABLE | EX_LOCAL_VARIABLE) {
        return false;
    }
    let mut pos = cond_opcode_pos + 1;
    let Some(first_name) = peek_field_path_first_name(ctx.bytecode, &mut pos, ctx.name_table)
    else {
        return false;
    };
    DOONCE_GATE_PREFIXES
        .iter()
        .any(|prefix| first_name.starts_with(prefix))
}

/// Peek the first FName on a `FFieldPath` operand without allocating
/// any other path segments. Returns `None` if the operand is empty
/// (`path_num <= 0`) or the buffer is too short to hold the first name.
fn peek_field_path_first_name(
    bytecode: &[u8],
    pos: &mut usize,
    name_table: &NameTable,
) -> Option<String> {
    // FName on disk = int32 name index + int32 instance number.
    const FNAME_DISK_BYTES: usize = 8;
    let path_num = read_bc_i32(bytecode, pos);
    if path_num <= 0 {
        return None;
    }
    if *pos + FNAME_DISK_BYTES > bytecode.len() {
        return None;
    }
    Some(read_bc_fname(bytecode, pos, name_table))
}

/// Two-way branch: classify as `IfThen` when one successor is the exit
/// block (that arm is empty / falls through), otherwise `IfThenElse`.
fn classify_two_way(cfg: &ControlFlowGraph, region: &Region, succs: &[BlockId]) -> RegionKind {
    if succs.len() != 2 {
        return RegionKind::IfThenElse;
    }
    if region.entry == region.exit {
        return RegionKind::IfThenElse;
    }
    if succs[0] == region.exit || succs[1] == region.exit {
        // One arm is the exit itself: the body skips straight to join.
        return RegionKind::IfThen;
    }
    let _ = cfg;
    RegionKind::IfThenElse
}

/// True iff some block inside the region's slice has an edge targeting
/// `region.entry`. Equivalent to "natural loop with head `region.entry`"
/// because the slice covers exactly the blocks dominated by `entry` up
/// to and including `exit`.
fn has_loop_back_edge(cfg: &ControlFlowGraph, region: &Region) -> bool {
    let preds = cfg
        .predecessors
        .get(&region.entry)
        .map(|edges| edges.as_slice())
        .unwrap_or(&[]);
    if preds.is_empty() {
        return false;
    }
    let slice = reachable_in_slice(cfg, region.entry, region.exit);
    preds.iter().any(|pred| slice.contains(pred))
}
