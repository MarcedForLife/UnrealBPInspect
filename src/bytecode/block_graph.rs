//! Block-level control flow graph for bytecode linearization.
//!
//! Splits a flat [`BcStatement`] stream into basic blocks, wires control-flow
//! edges by parsing jump targets, and provides analysis helpers
//! (in-degree, predecessors, convergence detection). Used by
//! `flow::reorder_convergence` (linearizes post-latch streams with backward
//! jumps) and by the ubergraph event linearization pass (re-orders each
//! event's partition so the entry block's control flow, not physical
//! offsets, drives emission order).
//!
//! Post-latch artifacts are recognized during block construction: `}`
//! (body-end from `transform_latch_patterns`) ends a block and produces a
//! [`BlockExit::LatchTerminal`], and blocks opening with a `DoOnce(name)` /
//! `FlipFlop(name)` header are tagged with [`BlockMetadata::LatchBody`].
//! Sequence dispatch chains (grouped and interleaved `push_flow`/`jump`
//! layouts) are collapsed into opaque [`BlockMetadata::SequenceSuperBlock`]
//! blocks so the DFS linearization can walk past them without tearing the
//! Sequence pattern that downstream `reorder_flow_patterns` re-detects.
//!
//! # Terminology
//!
//! - **Basic block**: maximal statement run with a single entry and single exit.
//! - **In-degree**: number of CFG edges into a block.
//! - **Convergence**: the block both branches of a conditional eventually reach.
//!
//! A block boundary is placed before every jump target and after every
//! terminal / jump / conditional-jump / computed-jump statement.
//! See [`BlockCfg::build`] for the exact rules.
//!
//! ```text
//!     ┌──────────────┐
//!     │ entry block  │
//!     └──────┬───────┘
//!            │
//!            ▼
//!     ┌──────────────┐  CondJump { fall_through, target }
//!     │    guard     │
//!     └──┬────────┬──┘
//!        │        │
//!        ▼        ▼
//!     fall_through target
//!         │        │
//!         └───┬────┘
//!             ▼
//!         convergence
//! ```

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use super::decode::BcStatement;
use super::flow::{detect_sequence_spans, parse_if_jump, parse_jump, parse_jump_computed};
use super::{
    OffsetMap, BARE_RETURN, BLOCK_CLOSE, JUMP_OFFSET_TOLERANCE, POP_FLOW, RETURN_NOP,
    STRUCTURE_OFFSET_TOLERANCE,
};

pub(crate) type BlockId = usize;

/// Knobs that vary between `BlockCfg::build` and `BlockCfg::build_for_structurer`.
///
/// The linearization callers (`reorder_convergence`, ubergraph event
/// linearization) resolve jumps at [`JUMP_OFFSET_TOLERANCE`] (4) and rely on
/// Sequence super-block collapse to keep dispatch chains atomic during DFS.
/// The structurer runs after further mem_adj drift has accumulated and needs
/// [`STRUCTURE_OFFSET_TOLERANCE`] (8) plus the raw (uncollapsed) block layout
/// so it can see the `if !(cond) jump` exit of a block that would otherwise
/// be buried inside a sequence super-block.
#[derive(Debug, Clone, Copy)]
struct BlockCfgConfig {
    /// Fuzzy tolerance passed to `OffsetMap::find_fuzzy` when resolving
    /// jump/push_flow targets to statement indices.
    jump_tolerance: usize,
    /// Whether to fold detected Sequence dispatches into
    /// [`BlockMetadata::SequenceSuperBlock`] atoms.
    collapse_sequence_super_blocks: bool,
}

impl BlockCfgConfig {
    /// Configuration used by the shared linearization callers.
    fn linearization() -> Self {
        Self {
            jump_tolerance: JUMP_OFFSET_TOLERANCE,
            collapse_sequence_super_blocks: true,
        }
    }

    /// Configuration used by the structurer's else-branch CFG query.
    fn structurer() -> Self {
        Self {
            jump_tolerance: STRUCTURE_OFFSET_TOLERANCE,
            collapse_sequence_super_blocks: false,
        }
    }
}

/// Classification of a block for downstream linearization passes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) enum BlockMetadata {
    #[default]
    Normal,
    /// Block whose range starts with a `DoOnce(name) {` / `FlipFlop(name) {`
    /// header and ends with `}` (the body-end replacement emitted by
    /// `transform_latch_patterns`). The latch name is captured so later
    /// passes can reason about the DoOnce/FlipFlop instance without
    /// re-parsing the header line.
    LatchBody { latch_name: String },
    /// Block that stands in for an entire Sequence dispatch: the
    /// `push_flow`/`jump` dispatch chain, its inline body, and each pin body.
    /// Linearization emits the block's `stmt_range` verbatim so downstream
    /// `detect_grouped_sequences` / `detect_interleaved_sequences` can
    /// re-detect the pattern during `reorder_flow_patterns`.
    ///
    /// All three ranges are statement indices into the stream passed to
    /// [`BlockCfg::build`]. The super-block's `stmt_range` is the union
    /// `chain.start .. max(inline_body.end, pins[*].end)`.
    SequenceSuperBlock {
        chain: Range<usize>,
        inline_body: Range<usize>,
        pins: Vec<Range<usize>>,
    },
}

/// A basic block: a contiguous run of statements with a single entry and
/// a single exit edge (plus one fall-through).
#[derive(Debug, Clone)]
pub(crate) struct Block {
    /// Statement indices into the original `stmts` slice passed to [`BlockCfg::build`].
    pub stmt_range: Range<usize>,
    pub exit: BlockExit,
    /// Latch-body / super-block classification. Only consumed by tests today;
    /// populated in real CFGs so downstream passes can consume it later.
    #[allow(dead_code)]
    pub metadata: BlockMetadata,
    /// Linearization bookkeeping. Set true once this block's statements have
    /// been emitted into the output stream.
    pub emitted: bool,
}

/// Control-flow edge leaving a basic block.
#[derive(Debug, Clone)]
pub(crate) enum BlockExit {
    /// Implicit fall-through to the next block in original layout.
    FallThrough,
    /// Unconditional jump to another block.
    Jump(BlockId),
    /// Conditional branch: `fall_through` is the true-body, `target` is the false-body.
    CondJump {
        fall_through: BlockId,
        target: BlockId,
    },
    /// Block ends by exiting the function (return, pop_flow, jump_computed).
    /// No local convergence is possible because execution leaves the current
    /// scope entirely.
    ReturnTerminal,
    /// Block ends with `}` (the latch body-close emitted by
    /// `transform_latch_patterns`). Structurally a block end with no
    /// fall-through edge, but shared post-latch code CAN still be the
    /// convergence target of a sibling branch.
    LatchTerminal,
}

impl BlockExit {
    /// True for any non-fall-through, non-jump exit (return, pop_flow,
    /// jump_computed, latch `}`). Both terminal variants contribute no
    /// outgoing edges to the CFG.
    #[allow(dead_code)]
    fn is_terminal(&self) -> bool {
        matches!(self, BlockExit::ReturnTerminal | BlockExit::LatchTerminal)
    }

    /// True only for exits that leave the function. Used by
    /// `find_convergence_target` to distinguish true function-exits (no
    /// local convergence possible) from latch body-ends (convergence still
    /// possible via the sibling branch).
    fn is_return(&self) -> bool {
        matches!(self, BlockExit::ReturnTerminal)
    }
}

/// Block-level CFG built from a flat statement stream.
pub(crate) struct BlockCfg {
    pub blocks: Vec<Block>,
    /// Maps the first-statement index of each block to its block id.
    pub stmt_to_block: HashMap<usize, BlockId>,
}

impl BlockCfg {
    /// Build a block-level CFG over `stmts` for the linearization callers.
    ///
    /// Splits into basic blocks at jump boundaries, then wires exit edges by
    /// parsing each block's last statement. Jump targets are resolved at
    /// [`JUMP_OFFSET_TOLERANCE`] and detected Sequence dispatches are
    /// collapsed into opaque super-blocks.
    pub fn build(stmts: &[BcStatement], offset_map: &OffsetMap) -> Self {
        Self::build_with_config(stmts, offset_map, BlockCfgConfig::linearization())
    }

    /// Build a block-level CFG for the structurer's else-branch query.
    ///
    /// Uses [`STRUCTURE_OFFSET_TOLERANCE`] (instead of
    /// [`JUMP_OFFSET_TOLERANCE`]) so jump targets still resolve after the
    /// mem_adj drift accumulated by earlier passes, and skips Sequence
    /// super-block collapse so the `if !(cond) jump` exit of a block inside
    /// a Sequence stays visible to `detect_else_branch_via_cfg`.
    pub fn build_for_structurer(stmts: &[BcStatement], offset_map: &OffsetMap) -> Self {
        Self::build_with_config(stmts, offset_map, BlockCfgConfig::structurer())
    }

    fn build_with_config(
        stmts: &[BcStatement],
        offset_map: &OffsetMap,
        config: BlockCfgConfig,
    ) -> Self {
        let (blocks, stmt_to_block) = build_basic_blocks(stmts, offset_map, config.jump_tolerance);
        let mut cfg = BlockCfg {
            blocks,
            stmt_to_block,
        };
        wire_block_edges(
            &mut cfg.blocks,
            stmts,
            offset_map,
            &cfg.stmt_to_block,
            config.jump_tolerance,
        );
        annotate_latch_bodies(&mut cfg.blocks, stmts);
        if config.collapse_sequence_super_blocks {
            collapse_sequence_super_blocks(&mut cfg, stmts, offset_map);
        }
        cfg
    }

    /// Block whose `stmt_range` contains `stmt_idx`, or `None` when the index
    /// falls outside every block's range.
    pub fn block_of(&self, stmt_idx: usize) -> Option<BlockId> {
        if let Some(&bid) = self.stmt_to_block.get(&stmt_idx) {
            return Some(bid);
        }
        // Blocks are built in physical order, so starts are non-decreasing.
        // Find the rightmost block whose start is <= stmt_idx.
        let pos = self
            .blocks
            .partition_point(|b| b.stmt_range.start <= stmt_idx);
        if pos == 0 {
            return None;
        }
        let bid = pos - 1;
        let range = &self.blocks[bid].stmt_range;
        if stmt_idx < range.end {
            Some(bid)
        } else {
            None
        }
    }

    /// Incoming edge count for every block, indexed by `BlockId`.
    pub fn compute_in_degree(&self) -> Vec<usize> {
        compute_in_degree(&self.blocks)
    }

    /// Predecessor lists for every block, indexed by `BlockId`.
    pub fn compute_predecessors(&self) -> Vec<Vec<BlockId>> {
        compute_predecessors(&self.blocks)
    }
}

/// Pre-compute inclusive `[open, close]` ranges of latch-body atoms
/// (`DoOnce(X) {` through the matching `}`). Nested latch bodies would
/// double-match; skip them by walking the outer open-to-close span and
/// ignoring interior openers, and rely on the `}` after body-rewrite being
/// the only close that matches the outermost open.
fn compute_latch_body_ranges(stmts: &[BcStatement]) -> Vec<(usize, usize)> {
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if parse_latch_header(&stmts[i].text).is_some() {
            // Find the matching close-brace, allowing nested blocks.
            let mut depth = 1;
            let mut j = i + 1;
            while j < stmts.len() {
                let t = stmts[j].text.trim();
                if t.ends_with('{')
                    && (t == "A|B: {" || parse_latch_header(&stmts[j].text).is_some())
                {
                    depth += 1;
                } else if t == "}" {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                j += 1;
            }
            if j < stmts.len() {
                ranges.push((i, j));
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    ranges
}

/// Split statements into basic blocks at jump boundaries.
///
/// A block boundary is placed:
/// - After every jump, conditional jump, terminal, or jump_computed
/// - Before every statement whose mem_offset is a jump target
///
/// Latch bodies (`DoOnce(X) { ... }` / `FlipFlop(X) { A|B: { ... } }`) are
/// treated as atomic units. Internal block boundaries (jump targets, latch
/// statement termini) within the latch span are suppressed so the
/// linearization DFS emits the latch as a single block ending in `}`
/// (Terminal).
fn build_basic_blocks(
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
    jump_tolerance: usize,
) -> (Vec<Block>, HashMap<usize, BlockId>) {
    // Collect all jump target offsets and resolve to statement indices
    let mut target_indices: HashSet<usize> = HashSet::new();
    for stmt in stmts {
        if let Some((_, target)) = parse_if_jump(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
        if let Some(target) = parse_jump(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
        if let Some(target) = super::flow::parse_push_flow(&stmt.text) {
            if let Some(idx) = offset_map.find_fuzzy(target, jump_tolerance) {
                target_indices.insert(idx);
            }
        }
    }

    // Suppress block boundaries inside latch bodies so they stay atomic.
    // Interior indices are strictly between the opener and the closing `}`:
    // the opener itself starts the block, and the `}` (close) must still end
    // it so the trailing statement starts a new block.
    let latch_ranges = compute_latch_body_ranges(stmts);
    let inside_latch = |idx: usize| -> bool {
        latch_ranges
            .iter()
            .any(|&(open, close)| idx > open && idx < close)
    };

    let mut blocks: Vec<Block> = Vec::new();
    let mut current_start = 0;

    let is_block_end = |stmt: &BcStatement| -> bool {
        stmt.text == RETURN_NOP
            || stmt.text == BARE_RETURN
            || stmt.text == POP_FLOW
            || stmt.text.trim() == BLOCK_CLOSE
            || parse_jump(&stmt.text).is_some()
            || parse_if_jump(&stmt.text).is_some()
            || parse_jump_computed(&stmt.text)
    };

    for (i, stmt) in stmts.iter().enumerate() {
        // Start a new block if this statement is a jump target, unless it's
        // inside an atomic latch body.
        if target_indices.contains(&i) && i > current_start && !inside_latch(i) {
            blocks.push(Block {
                stmt_range: current_start..i,
                exit: BlockExit::FallThrough,
                metadata: BlockMetadata::Normal,
                emitted: false,
            });
            current_start = i;
        }

        // End the current block on a terminator, unless we're inside a latch
        // body (statements there are part of the latch atom; only the final
        // `}` is allowed to end the block).
        if is_block_end(stmt) && !inside_latch(i) {
            blocks.push(Block {
                stmt_range: current_start..i + 1,
                exit: BlockExit::FallThrough, // patched in wire_block_edges
                metadata: BlockMetadata::Normal,
                emitted: false,
            });
            current_start = i + 1;
        }
    }
    // Remaining statements form a final block
    if current_start < stmts.len() {
        blocks.push(Block {
            stmt_range: current_start..stmts.len(),
            exit: BlockExit::FallThrough,
            metadata: BlockMetadata::Normal,
            emitted: false,
        });
    }

    // Build stmt_index -> block_id map for each block's first statement
    let mut stmt_to_block: HashMap<usize, BlockId> = HashMap::new();
    for (bid, block) in blocks.iter().enumerate() {
        stmt_to_block.insert(block.stmt_range.start, bid);
    }

    (blocks, stmt_to_block)
}

/// Examine each block's last statement and set its exit edge.
fn wire_block_edges(
    blocks: &mut [Block],
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
    stmt_to_block: &HashMap<usize, BlockId>,
    jump_tolerance: usize,
) {
    let resolve_target = |target_offset: usize| -> Option<BlockId> {
        let stmt_idx = offset_map.find_fuzzy(target_offset, jump_tolerance)?;
        stmt_to_block.get(&stmt_idx).copied()
    };

    for bid in 0..blocks.len() {
        let range = &blocks[bid].stmt_range;
        if range.is_empty() {
            continue;
        }
        let last_idx = range.end - 1;
        let last_text = &stmts[last_idx].text;
        let next_block = bid + 1;

        if last_text == RETURN_NOP || last_text == BARE_RETURN || last_text == POP_FLOW {
            blocks[bid].exit = BlockExit::ReturnTerminal;
        } else if last_text.trim() == BLOCK_CLOSE {
            blocks[bid].exit = BlockExit::LatchTerminal;
        } else if let Some((_, target)) = parse_if_jump(last_text) {
            let ft = if next_block < blocks.len() {
                next_block
            } else {
                bid
            };
            blocks[bid].exit = match resolve_target(target) {
                Some(tbid) => BlockExit::CondJump {
                    fall_through: ft,
                    target: tbid,
                },
                None => BlockExit::FallThrough,
            };
        } else if let Some(target) = parse_jump(last_text) {
            blocks[bid].exit = match resolve_target(target) {
                Some(tbid) => BlockExit::Jump(tbid),
                None => BlockExit::FallThrough,
            };
        } else if parse_jump_computed(last_text) {
            blocks[bid].exit = BlockExit::ReturnTerminal;
        }
        // else: FallThrough (default)
    }
}

/// Parse a latch-header first line and return the latch name if the text
/// matches `DoOnce(<name>) {` or `FlipFlop(<name>) {`.
fn parse_latch_header(text: &str) -> Option<&str> {
    let trimmed = text.trim();
    let rest = trimmed
        .strip_prefix("DoOnce(")
        .or_else(|| trimmed.strip_prefix("FlipFlop("))?;
    let close_paren = rest.find(')')?;
    let after = rest[close_paren + 1..].trim_start();
    if after != "{" {
        return None;
    }
    Some(&rest[..close_paren])
}

/// Populate [`BlockMetadata::LatchBody`] for blocks whose first statement is a
/// DoOnce/FlipFlop header and whose last statement is `}` (the body-end
/// replacement emitted by `transform_latch_patterns`).
fn annotate_latch_bodies(blocks: &mut [Block], stmts: &[BcStatement]) {
    for block in blocks.iter_mut() {
        if block.stmt_range.is_empty() {
            continue;
        }
        let first = &stmts[block.stmt_range.start].text;
        let last = &stmts[block.stmt_range.end - 1].text;
        if last.trim() != "}" {
            continue;
        }
        let Some(name) = parse_latch_header(first) else {
            continue;
        };
        block.metadata = BlockMetadata::LatchBody {
            latch_name: name.to_string(),
        };
    }
}

/// Collapse each detected Sequence dispatch into a single opaque super-block.
///
/// After this pass, Sequences appear as one `BlockMetadata::SequenceSuperBlock`
/// block whose `stmt_range` covers the dispatch chain, inline body, and pin
/// bodies. Linearization emits the range verbatim, so the raw
/// `push_flow`/`jump` layout survives for `detect_grouped_sequences` /
/// `detect_interleaved_sequences` to re-detect during `reorder_flow_patterns`.
///
/// Block IDs in `exit` edges and `stmt_to_block` are renumbered so callers can
/// treat the CFG as if the super-blocks had always been there.
fn collapse_sequence_super_blocks(
    cfg: &mut BlockCfg,
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) {
    let spans = detect_sequence_spans(stmts, offset_map);
    if spans.is_empty() {
        return;
    }

    // Process spans outermost-first but skip any nested inside an already-consumed
    // range. detect_sequence_spans sorts by chain.start, so a parent comes before
    // its children when ranges nest — this simple check is enough.
    let mut consumed: Vec<Range<usize>> = Vec::new();
    let mut super_ranges: Vec<(Range<usize>, BlockMetadata)> = Vec::new();
    for span in &spans {
        let full = span.full_range();
        if consumed
            .iter()
            .any(|c| full.start >= c.start && full.end <= c.end)
        {
            continue;
        }
        consumed.push(full.clone());
        super_ranges.push((
            full,
            BlockMetadata::SequenceSuperBlock {
                chain: span.chain.clone(),
                inline_body: span.inline_body.clone(),
                pins: span.pins.clone(),
            },
        ));
    }

    if super_ranges.is_empty() {
        return;
    }

    apply_super_block_collapse(cfg, &super_ranges);
}

/// Rebuild `cfg.blocks` so every `(range, metadata)` in `super_ranges` becomes
/// a single block, with preserved surrounding blocks and remapped edges.
fn apply_super_block_collapse(cfg: &mut BlockCfg, super_ranges: &[(Range<usize>, BlockMetadata)]) {
    let old_blocks = std::mem::take(&mut cfg.blocks);

    // Map each old BlockId to (new_id, is_first_block_of_super).
    // Blocks that fall entirely inside a super-block range get collapsed onto
    // the super-block's new id. Blocks straddling a boundary shouldn't exist
    // because build_basic_blocks already splits at jump targets, but if one
    // does we conservatively leave it alone (the super-block collapse is a
    // no-op for that span).
    let mut old_to_new: Vec<Option<BlockId>> = vec![None; old_blocks.len()];
    let mut new_blocks: Vec<Block> = Vec::with_capacity(old_blocks.len());

    let super_for = |range: &Range<usize>| -> Option<&(Range<usize>, BlockMetadata)> {
        super_ranges
            .iter()
            .find(|(r, _)| range.start >= r.start && range.end <= r.end)
    };

    let mut consumed_super: Vec<bool> = vec![false; super_ranges.len()];

    for (old_id, block) in old_blocks.iter().enumerate() {
        if let Some((super_range, meta)) = super_for(&block.stmt_range) {
            let super_idx = super_ranges
                .iter()
                .position(|(r, _)| r.start == super_range.start && r.end == super_range.end)
                .expect("super_for returns a known range");
            if consumed_super[super_idx] {
                // Redirect subsequent blocks inside this super-block to the
                // same new id.
                old_to_new[old_id] = Some(new_blocks.len() - 1);
                continue;
            }
            consumed_super[super_idx] = true;
            let new_id = new_blocks.len();
            new_blocks.push(Block {
                stmt_range: super_range.clone(),
                exit: BlockExit::FallThrough, // patched below
                metadata: meta.clone(),
                emitted: false,
            });
            old_to_new[old_id] = Some(new_id);
            continue;
        }
        let new_id = new_blocks.len();
        new_blocks.push(block.clone());
        old_to_new[old_id] = Some(new_id);
    }

    // Patch edges: translate old BlockIds via old_to_new. If a super-block's
    // successor falls inside its own range (rare, defensive), treat as Terminal.
    let translate = |old: BlockId| -> Option<BlockId> { old_to_new.get(old).copied().flatten() };

    for (old_id, block) in old_blocks.iter().enumerate() {
        let Some(new_id) = old_to_new[old_id] else {
            continue;
        };
        // Each super-block is visited multiple times (once per swallowed old
        // block). Only set its exit from the LAST block in the super-block
        // range so fall-through goes to whatever follows the super-block.
        let super_range = &new_blocks[new_id].stmt_range;
        let is_super = matches!(
            new_blocks[new_id].metadata,
            BlockMetadata::SequenceSuperBlock { .. }
        );
        if is_super && block.stmt_range.end != super_range.end {
            continue;
        }

        let new_exit = match &block.exit {
            BlockExit::ReturnTerminal => BlockExit::ReturnTerminal,
            BlockExit::LatchTerminal => BlockExit::LatchTerminal,
            BlockExit::FallThrough => BlockExit::FallThrough,
            BlockExit::Jump(target) => match translate(*target) {
                Some(t) if t == new_id => BlockExit::ReturnTerminal,
                Some(t) => BlockExit::Jump(t),
                None => BlockExit::FallThrough,
            },
            BlockExit::CondJump {
                fall_through,
                target,
            } => {
                let ft = translate(*fall_through).unwrap_or(new_id);
                let tgt = translate(*target).unwrap_or(new_id);
                BlockExit::CondJump {
                    fall_through: ft,
                    target: tgt,
                }
            }
        };
        new_blocks[new_id].exit = new_exit;
    }

    let mut stmt_to_block: HashMap<usize, BlockId> = HashMap::new();
    for (new_id, block) in new_blocks.iter().enumerate() {
        stmt_to_block.insert(block.stmt_range.start, new_id);
    }

    cfg.blocks = new_blocks;
    cfg.stmt_to_block = stmt_to_block;
}

/// Compute incoming edge count for each block.
fn compute_in_degree(blocks: &[Block]) -> Vec<usize> {
    let mut deg = vec![0usize; blocks.len()];
    for (bid, block) in blocks.iter().enumerate() {
        match &block.exit {
            BlockExit::FallThrough => {
                if bid + 1 < blocks.len() {
                    deg[bid + 1] += 1;
                }
            }
            BlockExit::Jump(target) => {
                deg[*target] += 1;
            }
            BlockExit::CondJump {
                fall_through,
                target,
            } => {
                deg[*fall_through] += 1;
                deg[*target] += 1;
            }
            BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        }
    }
    deg
}

/// Build predecessor lists: for each block, which blocks have edges to it.
fn compute_predecessors(blocks: &[Block]) -> Vec<Vec<BlockId>> {
    let mut preds = vec![Vec::new(); blocks.len()];
    for (bid, block) in blocks.iter().enumerate() {
        match &block.exit {
            BlockExit::FallThrough => {
                if bid + 1 < blocks.len() {
                    preds[bid + 1].push(bid);
                }
            }
            BlockExit::Jump(target) => {
                preds[*target].push(bid);
            }
            BlockExit::CondJump {
                fall_through,
                target,
            } => {
                preds[*fall_through].push(bid);
                preds[*target].push(bid);
            }
            BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        }
    }
    preds
}

/// True if every block that jumps to `target` has been emitted already.
///
/// Used by the linearization pass to decide whether a convergence block
/// can be emitted inline (all paths have reached it) versus left for the
/// sweep pass.
pub(crate) fn all_predecessors_emitted(
    blocks: &[Block],
    predecessors: &[Vec<BlockId>],
    target: BlockId,
) -> bool {
    if target >= predecessors.len() {
        return true;
    }
    predecessors[target]
        .iter()
        .all(|&pred| blocks[pred].emitted)
}

/// Find the convergence target of two branches: the block that both paths
/// eventually reach via explicit Jump / CondJump edges.
///
/// Semantics match the prior shared-exit intersection (only blocks reached
/// by explicit jump edges are candidates), with one additional defensive
/// filter:
///
/// - **Return-branch guard.** If either branch's entry block is
///   immediately `ReturnTerminal` (the branch returns, pops flow, or runs
///   a computed jump without any non-terminal successor), there's no
///   local convergence to emit, return `None`. Prevents pulling
///   post-return code into a region where execution has already exited.
///   `LatchTerminal` (`}` body-close) is NOT guarded here: a latch body
///   ends the block structurally but shared post-latch code can still
///   be the convergence target of the sibling branch.
///
/// Among qualifying candidates, returns the one with the lowest block ID
/// (earliest in original layout -- matches the previous heuristic).
///
/// # Why not a broader predecessor-walk filter?
///
/// An "outside predecessor" filter (reject any candidate whose
/// predecessors lie outside `reachable_from_a ∪ reachable_from_b`) was
/// drafted earlier but regresses functions like `AttemptGrip` where a
/// legitimate convergence candidate has a backward predecessor from code
/// that emits later in the stream. The terminal-branch guard alone is
/// sufficient to prevent the `EvaluateClimbing` regression, the broader
/// filter over-rejects. Revisit when there's CFG-level data on exactly
/// which join points should be excluded.
pub(crate) fn find_convergence_target(
    blocks: &[Block],
    branch_a: BlockId,
    branch_b: BlockId,
) -> Option<BlockId> {
    if branch_a >= blocks.len() || branch_b >= blocks.len() {
        return None;
    }
    if blocks[branch_a].exit.is_return() || blocks[branch_b].exit.is_return() {
        return None;
    }

    let mut targets_a: HashSet<BlockId> = HashSet::new();
    let mut visited_a: HashSet<BlockId> = HashSet::new();
    collect_branch_exits(blocks, branch_a, &mut targets_a, &mut visited_a);

    let mut targets_b: HashSet<BlockId> = HashSet::new();
    let mut visited_b: HashSet<BlockId> = HashSet::new();
    collect_branch_exits(blocks, branch_b, &mut targets_b, &mut visited_b);

    targets_a.intersection(&targets_b).copied().min()
}

/// Recursively collect all Jump targets reachable from a block, following
/// all edge types transitively. The `visited` set prevents infinite loops
/// from backward edges.
fn collect_branch_exits(
    blocks: &[Block],
    bid: BlockId,
    targets: &mut HashSet<BlockId>,
    visited: &mut HashSet<BlockId>,
) {
    if bid >= blocks.len() || !visited.insert(bid) {
        return;
    }
    match &blocks[bid].exit {
        BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}
        BlockExit::Jump(target) => {
            targets.insert(*target);
            collect_branch_exits(blocks, *target, targets, visited);
        }
        BlockExit::FallThrough => {
            collect_branch_exits(blocks, bid + 1, targets, visited);
        }
        BlockExit::CondJump {
            fall_through,
            target,
        } => {
            collect_branch_exits(blocks, *fall_through, targets, visited);
            collect_branch_exits(blocks, *target, targets, visited);
        }
    }
}

/// Recursive DFS linearization using the block-level CFG.
///
/// Emits blocks in an order where conditional jumps always target forward positions:
/// - CondJump: emit fall-through (true body) first, then target (false body)
/// - Jump to single-entry block: follow inline
/// - Jump to multi-entry block: leave the jump in place (becomes goto label)
/// - FallThrough: follow next block, insert synthetic jump if already emitted
///
/// Shared by `flow::reorder_convergence` and
/// `output_summary::ubergraph::linearize_from_entry`. Seed blocks can be any
/// entry point in the CFG; callers typically seed with the event entry block
/// first, then sweep the remaining blocks so unreachable code is preserved.
pub(crate) fn linearize_blocks(
    blocks: &mut [Block],
    stmts: &[BcStatement],
    in_degree: &[usize],
    predecessors: &[Vec<BlockId>],
    bid: BlockId,
    output: &mut Vec<BcStatement>,
) {
    if bid >= blocks.len() || blocks[bid].emitted {
        return;
    }
    blocks[bid].emitted = true;

    // Emit this block's statements
    let range = blocks[bid].stmt_range.clone();
    for idx in range {
        output.push(stmts[idx].clone());
    }

    let exit = blocks[bid].exit.clone();
    match exit {
        BlockExit::ReturnTerminal | BlockExit::LatchTerminal => {}

        BlockExit::FallThrough => {
            let next = bid + 1;
            if next < blocks.len() {
                if !blocks[next].emitted && in_degree[next] <= 1 {
                    // Single-entry successor: follow inline
                    linearize_blocks(blocks, stmts, in_degree, predecessors, next, output);
                } else {
                    // Multi-entry or already emitted: insert a synthetic
                    // forward jump so the structurer's else-branch detector
                    // sees an explicit branch exit even when the successor
                    // is deferred.
                    let target_offset = stmts[blocks[next].stmt_range.start].mem_offset;
                    output.push(BcStatement::new(0, format!("jump 0x{target_offset:x}")));
                }
            }
        }

        BlockExit::Jump(target) => {
            // Follow single-entry targets inline; leave multi-entry convergence
            // blocks in place (their jump becomes a goto in structure_bytecode)
            if target < blocks.len() && in_degree[target] <= 1 && !blocks[target].emitted {
                linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
            }
        }

        BlockExit::CondJump {
            fall_through,
            target,
        } => {
            if fall_through < blocks.len()
                && in_degree[fall_through] > 1
                && target < blocks.len()
                && in_degree[target] <= 1
            {
                // Guard pattern: the fall-through is a multi-entry convergence
                // block and the target (else-body) is single-entry. Emit the
                // single-entry false body first, then the convergence. Produces
                // a guard: `if (cond) { false-body } convergence`.
                // Negate the if-jump so the structurer sees the correct
                // condition after the swap.
                negate_last_if_jump(stmts, &blocks[bid].stmt_range, output);
                linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                linearize_blocks(blocks, stmts, in_degree, predecessors, fall_through, output);
            } else {
                // Standard case: emit true body (fall-through) first, then
                // false body (target).
                linearize_blocks(blocks, stmts, in_degree, predecessors, fall_through, output);
                if target < blocks.len() && in_degree[target] <= 1 {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                }
                // If the target was deferred (in_degree > 1), try emitting it
                // now that the fall-through has been emitted. Handles the
                // common case where both branches of an inner if/else converge
                // to a block that should stay within the current scope.
                if target < blocks.len()
                    && !blocks[target].emitted
                    && all_predecessors_emitted(blocks, predecessors, target)
                {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, target, output);
                }
            }

            // After both branches, find their common convergence point and
            // emit it if all its predecessors have been emitted.
            if let Some(conv) = find_convergence_target(blocks, fall_through, target) {
                if !blocks[conv].emitted && all_predecessors_emitted(blocks, predecessors, conv) {
                    linearize_blocks(blocks, stmts, in_degree, predecessors, conv, output);
                }
            }
        }
    }
}

/// Negate the last if-jump in the output.
///
/// When the guard pattern swaps true/false body order, the if-jump condition
/// needs to be inverted. Wraps the condition in an extra `!()` so the
/// structurer (which strips the outer `!`) gets the negated condition.
/// Double-negation is cleaned up later.
fn negate_last_if_jump(
    stmts: &[BcStatement],
    block_range: &std::ops::Range<usize>,
    output: &mut [BcStatement],
) {
    if block_range.is_empty() {
        return;
    }
    let last_idx = block_range.end - 1;
    let last_text = &stmts[last_idx].text;
    if let Some((cond, target)) = super::flow::parse_if_jump(last_text) {
        if let Some(out_stmt) = output.last_mut() {
            if out_stmt.text == *last_text {
                out_stmt.text = format!("if !(!{cond}) jump 0x{target:x}");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build an [`OffsetMap`] + build a [`BlockCfg`] from a compact
    /// `(mem_offset, text)` description.
    fn cfg_from(items: &[(usize, &str)]) -> (Vec<BcStatement>, BlockCfg) {
        let stmts: Vec<BcStatement> = items
            .iter()
            .map(|(off, t)| BcStatement::new(*off, t.to_string()))
            .collect();
        let offset_map = OffsetMap::build(&stmts);
        let cfg = BlockCfg::build(&stmts, &offset_map);
        (stmts, cfg)
    }

    #[test]
    fn build_splits_at_jump_and_target() {
        // Three blocks: [before if-jump], [fall-through body], [jump target]
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "a = 1"),
            (0x14, "if !(cond) jump 0x20"),
            (0x18, "b = 2"),
            (0x20, "c = 3"),
        ]);
        assert_eq!(cfg.blocks.len(), 3);
        assert_eq!(cfg.blocks[0].stmt_range, 0..2);
        assert_eq!(cfg.blocks[1].stmt_range, 2..3);
        assert_eq!(cfg.blocks[2].stmt_range, 3..4);
        assert!(matches!(
            cfg.blocks[0].exit,
            BlockExit::CondJump {
                fall_through: 1,
                target: 2
            }
        ));
        assert!(matches!(cfg.blocks[1].exit, BlockExit::FallThrough));
        assert!(matches!(cfg.blocks[2].exit, BlockExit::FallThrough));
    }

    #[test]
    fn build_marks_return_as_terminal() {
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "a = 1"),
            (0x14, "return nop"),
            (0x18, "b = 2"), // unreachable but still a block
        ]);
        assert_eq!(cfg.blocks.len(), 2);
        assert!(matches!(cfg.blocks[0].exit, BlockExit::ReturnTerminal));
    }

    #[test]
    fn compute_in_degree_counts_all_edges() {
        // if !(cond) jump 0x20    -> ft=block1, target=block2
        //   block1: fall through  -> block2
        //   block2: convergence target (in_degree 2)
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(cond) jump 0x18"),
            (0x14, "a = 1"),
            (0x18, "b = 2"),
        ]);
        let deg = cfg.compute_in_degree();
        assert_eq!(deg.len(), 3);
        assert_eq!(deg[0], 0);
        assert_eq!(deg[1], 1); // fall-through from block 0
        assert_eq!(deg[2], 2); // both ft from block 1 and jump target from block 0
    }

    #[test]
    fn compute_predecessors_lists_all_sources() {
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(cond) jump 0x18"),
            (0x14, "a = 1"),
            (0x18, "b = 2"),
        ]);
        let preds = cfg.compute_predecessors();
        assert_eq!(preds[0], Vec::<BlockId>::new());
        assert_eq!(preds[1], vec![0]);
        // block 2 has two predecessors: block 0 (via CondJump target) and block 1 (fall-through)
        let mut p2 = preds[2].clone();
        p2.sort();
        assert_eq!(p2, vec![0, 1]);
    }

    #[test]
    fn find_convergence_target_returns_shared_exit() {
        // Both branches jump to a shared convergence block:
        //   block0: if !(cond) jump 0x18  (CondJump ft=1, target=2)
        //   block1: a = 1; jump 0x20
        //   block2: b = 2; jump 0x20
        //   block3: c = 3                 (convergence, in-degree 2)
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(cond) jump 0x18"),
            (0x14, "a = 1"),
            (0x15, "jump 0x20"),
            (0x18, "b = 2"),
            (0x19, "jump 0x20"),
            (0x20, "c = 3"),
        ]);
        assert!(matches!(
            cfg.blocks[0].exit,
            BlockExit::CondJump {
                fall_through: 1,
                target: 2
            }
        ));
        let conv = find_convergence_target(&cfg.blocks, 1, 2);
        assert_eq!(conv, Some(3));
    }

    #[test]
    fn find_convergence_target_none_when_branch_returns() {
        // One branch ends in `return nop` -- there is no local convergence
        // because that side of the if exits the function entirely. The
        // defensive filter must reject the trailing block even though it
        // appears reachable from the other branch.
        //   block0: if !(cond) jump 0x18  (CondJump ft=1, target=2)
        //   block1: a = 1; return nop    (Terminal)
        //   block2: b = 2; jump 0x20
        //   block3: c = 3
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(cond) jump 0x18"),
            (0x14, "a = 1"),
            (0x15, "return nop"),
            (0x18, "b = 2"),
            (0x19, "jump 0x20"),
            (0x20, "c = 3"),
        ]);
        let conv = find_convergence_target(&cfg.blocks, 1, 2);
        assert_eq!(
            conv, None,
            "branch that returns has no convergence with the other branch"
        );
    }

    #[test]
    fn find_convergence_target_none_when_both_branches_terminate() {
        // Both branches end in `return nop`. No convergence is possible
        // because execution exits the function from either side.
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(cond) jump 0x18"),
            (0x14, "a = 1"),
            (0x15, "return nop"),
            (0x18, "b = 2"),
            (0x19, "return nop"),
        ]);
        let conv = find_convergence_target(&cfg.blocks, 1, 2);
        assert_eq!(
            conv, None,
            "two terminal branches have no shared convergence"
        );
    }

    #[test]
    fn block_exit_helpers_distinguish_return_from_latch() {
        // The helpers underpin the terminal-branch guard split: both variants
        // contribute no outgoing edges, but only ReturnTerminal blocks the
        // find_convergence_target early-return.
        assert!(BlockExit::ReturnTerminal.is_terminal());
        assert!(BlockExit::LatchTerminal.is_terminal());
        assert!(!BlockExit::FallThrough.is_terminal());

        assert!(BlockExit::ReturnTerminal.is_return());
        assert!(!BlockExit::LatchTerminal.is_return());
        assert!(!BlockExit::FallThrough.is_return());
    }

    /// Build a minimal [`Block`] with explicit `exit`, stmt_range 0..0
    /// (unused by edge-only analyses), and default metadata.
    fn synthetic_block(exit: BlockExit) -> Block {
        Block {
            stmt_range: 0..0,
            exit,
            metadata: BlockMetadata::Normal,
            emitted: false,
        }
    }

    #[test]
    fn find_convergence_target_allows_latch_terminal_branches() {
        // Construct a CFG manually so one branch's entry block exits via
        // LatchTerminal while a sibling pathway still Jumps into a shared
        // block. Old code guarded both Terminal variants together and
        // returned `None` here; the split lets the convergence through.
        //
        //   block0: CondJump ft=1, target=2
        //   block1: Jump(3)              (non-terminal branch entry)
        //   block2: Jump(3)              (also reaches block3)
        //   block3: LatchTerminal        (shared convergence candidate)
        //
        // Both branches contribute block3 to their Jump-target sets, so
        // the intersection picks block3. A latch-body `}` ending the
        // convergence block itself is fine: downstream passes still emit
        // the body correctly.
        let blocks = vec![
            synthetic_block(BlockExit::CondJump {
                fall_through: 1,
                target: 2,
            }),
            synthetic_block(BlockExit::Jump(3)),
            synthetic_block(BlockExit::Jump(3)),
            synthetic_block(BlockExit::LatchTerminal),
        ];

        let conv = find_convergence_target(&blocks, 1, 2);
        assert_eq!(
            conv,
            Some(3),
            "LatchTerminal convergence target must be detected"
        );

        // Sanity check: if block3 were ReturnTerminal, that wouldn't change
        // the convergence outcome on its own (the guard checks the branch
        // entries, not the convergence block itself).
        let mut with_return_conv = blocks.clone();
        with_return_conv[3].exit = BlockExit::ReturnTerminal;
        let conv = find_convergence_target(&with_return_conv, 1, 2);
        assert_eq!(
            conv,
            Some(3),
            "convergence block's own exit variant doesn't affect the guard"
        );

        // But if one BRANCH ENTRY is ReturnTerminal, the guard fires and
        // returns None. The old code would also fire for LatchTerminal here.
        let mut with_return_branch = blocks.clone();
        with_return_branch[1].exit = BlockExit::ReturnTerminal;
        let conv = find_convergence_target(&with_return_branch, 1, 2);
        assert_eq!(
            conv, None,
            "ReturnTerminal branch entry blocks convergence detection"
        );

        // Swap in LatchTerminal on the branch entry and the guard no longer
        // fires. The entry has no outgoing edges so the intersection is
        // empty and we still get None, but for the different structural
        // reason (no reachable convergence, not a hard-coded guard).
        let mut with_latch_branch = blocks;
        with_latch_branch[1].exit = BlockExit::LatchTerminal;
        let conv = find_convergence_target(&with_latch_branch, 1, 2);
        assert_eq!(
            conv, None,
            "LatchTerminal branch contributes no successors so intersection is empty"
        );
    }

    #[test]
    fn find_convergence_target_handles_nested_convergence() {
        // Nested if/else whose branches both jump to a shared exit. The
        // non-terminal guard should NOT reject this case -- both branches
        // have non-terminal exits (Jump / CondJump) and the intersection
        // is well defined.
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "if !(x) jump 0x18"),
            (0x14, "a = 1"),
            (0x15, "jump 0x20"),
            (0x18, "if !(y) jump 0x1e"),
            (0x1a, "b = 2"),
            (0x1b, "jump 0x20"),
            (0x1e, "c = 3"),
            (0x1f, "jump 0x20"),
            (0x20, "conv()"),
        ]);
        let conv = find_convergence_target(&cfg.blocks, 1, 2);
        assert!(conv.is_some(), "should detect nested convergence");
    }

    #[test]
    fn doonce_body_is_terminal_and_tagged() {
        // DoOnce body produced by transform_latch_patterns:
        //   DoOnce(Foo) {
        //     MyCall()
        //   }
        // The trailing `}` is a Terminal (no fall-through to the next stmt).
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "DoOnce(Foo) {"),
            (0x14, "MyCall()"),
            (0x18, "}"),
            (0x1c, "after = 1"),
        ]);
        // Two blocks: the DoOnce body (0..3) and the trailing statement (3..4).
        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!(cfg.blocks[0].stmt_range, 0..3);
        assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
        assert_eq!(
            cfg.blocks[0].metadata,
            BlockMetadata::LatchBody {
                latch_name: "Foo".to_string(),
            }
        );
    }

    #[test]
    fn flipflop_body_is_terminal_and_tagged() {
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "FlipFlop(Toggle) {"),
            (0x14, "HandleA()"),
            (0x18, "}"),
        ]);
        assert_eq!(cfg.blocks.len(), 1);
        assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
        assert_eq!(
            cfg.blocks[0].metadata,
            BlockMetadata::LatchBody {
                latch_name: "Toggle".to_string(),
            }
        );
    }

    #[test]
    fn bare_brace_close_is_terminal_but_not_latch_body() {
        // Defensive: treat any `}` as LatchTerminal, even when not preceded by
        // a recognized DoOnce/FlipFlop header. Metadata stays Normal.
        let (_stmts, cfg) =
            cfg_from(&[(0x10, "do_something()"), (0x14, "}"), (0x18, "unrelated()")]);
        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!(cfg.blocks[0].stmt_range, 0..2);
        assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
        assert_eq!(cfg.blocks[0].metadata, BlockMetadata::Normal);
    }

    #[test]
    fn grouped_sequence_collapses_into_super_block() {
        // Grouped (regular-function) Sequence pattern:
        //   push_flow pin0_end; push_flow pin1_end; jump pin0_body;
        //   push_flow pin2_end; jump pin1_body;
        //   inline_body_stmt; pop_flow;
        //   pin2_body_stmt; pop_flow;
        //   pin1_body_stmt; pop_flow;
        //   pin0_body_stmt; pop_flow;
        //
        // `detect_grouped_sequences` needs at least 2 push_flow/jump pairs and
        // a pop_flow terminator for the inline body. Build a minimal example
        // with two pins and verify the CFG collapses into a single super-block.
        let (_stmts, cfg) = cfg_from(&[
            (0x10, "push_flow 0x40"), // end-marker for the pair chain
            (0x14, "push_flow 0x20"), // pin0 continuation
            (0x18, "jump 0x34"),      // jump to pin0 body
            (0x1c, "push_flow 0x28"), // pin1 continuation
            (0x20, "jump 0x38"),      // jump to pin1 body
            (0x24, "inline_stmt()"),  // inline body
            (0x28, "pop_flow"),       // inline body terminator
            (0x34, "pin0_stmt()"),    // pin0 body
            (0x36, "pop_flow"),       // pin0 terminator
            (0x38, "pin1_stmt()"),    // pin1 body
            (0x3c, "pop_flow"),       // pin1 terminator
        ]);

        let super_block = cfg
            .blocks
            .iter()
            .find(|b| matches!(b.metadata, BlockMetadata::SequenceSuperBlock { .. }));
        assert!(
            super_block.is_some(),
            "expected a SequenceSuperBlock in the collapsed CFG"
        );
        let super_block = super_block.unwrap();
        // The super-block should cover the entire Sequence: from the first
        // push_flow through the last pin's terminator.
        assert_eq!(super_block.stmt_range.start, 0);
        assert_eq!(super_block.stmt_range.end, 11);
        // Super-block ends with a pin terminator (pop_flow) so its exit is ReturnTerminal.
        assert!(matches!(super_block.exit, BlockExit::ReturnTerminal));
    }

    #[test]
    fn block_after_doonce_starts_after_close_brace() {
        // The block following a latch body must start AT the next statement,
        // not somewhere inside the DoOnce body.
        let (stmts, cfg) = cfg_from(&[
            (0x10, "DoOnce(Bar) {"),
            (0x14, "Inside()"),
            (0x18, "}"),
            (0x1c, "AfterCall()"),
            (0x20, "return nop"),
        ]);
        assert_eq!(cfg.blocks.len(), 2);
        assert_eq!(cfg.blocks[0].stmt_range, 0..3);
        assert_eq!(cfg.blocks[1].stmt_range, 3..5);
        // The next block starts on `AfterCall()`, confirming the `}` ended
        // its predecessor cleanly.
        assert_eq!(stmts[cfg.blocks[1].stmt_range.start].text, "AfterCall()");
        assert!(matches!(cfg.blocks[1].exit, BlockExit::ReturnTerminal));
        assert_eq!(
            cfg.blocks[0].metadata,
            BlockMetadata::LatchBody {
                latch_name: "Bar".to_string(),
            }
        );
    }
}
