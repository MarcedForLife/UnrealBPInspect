//! Latch-body annotation and Sequence super-block collapse.

use std::collections::HashMap;
use std::ops::Range;

use crate::bytecode::decode::BcStatement;
use crate::bytecode::flow::detect_sequence_spans;
use crate::bytecode::OffsetMap;

use super::types::{Block, BlockCfg, BlockExit, BlockId, BlockMetadata};

/// Parse `DoOnce(<name>) {` or `FlipFlop(<name>) {`, returning the name.
pub(super) fn parse_latch_header(text: &str) -> Option<&str> {
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

pub(super) fn annotate_latch_bodies(blocks: &mut [Block], stmts: &[BcStatement]) {
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

/// Collapse each detected Sequence dispatch into a single super-block whose
/// `stmt_range` covers chain + inline body + pin bodies. Linearization emits
/// it verbatim so `reorder_flow_patterns` can re-detect the pattern.
/// Edges and `stmt_to_block` are renumbered.
pub(super) fn collapse_sequence_super_blocks(
    cfg: &mut BlockCfg,
    stmts: &[BcStatement],
    offset_map: &OffsetMap,
) {
    let spans = detect_sequence_spans(stmts, offset_map);
    if spans.is_empty() {
        return;
    }

    // detect_sequence_spans sorts by chain.start, so a parent comes before
    // its children; skipping anything already inside `consumed` handles nesting.
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

fn apply_super_block_collapse(cfg: &mut BlockCfg, super_ranges: &[(Range<usize>, BlockMetadata)]) {
    let old_blocks = std::mem::take(&mut cfg.blocks);

    // Blocks entirely inside a super-block range collapse onto its new id.
    // Boundary-straddling blocks shouldn't exist (build_basic_blocks splits
    // at jump targets); if one does the super-block collapse is a no-op for
    // that span.
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
            let super_new_id = if consumed_super[super_idx] {
                new_blocks.len() - 1
            } else {
                consumed_super[super_idx] = true;
                let new_id = new_blocks.len();
                new_blocks.push(Block {
                    stmt_range: super_range.clone(),
                    exit: BlockExit::FallThrough, // patched below
                    metadata: meta.clone(),
                    emitted: false,
                    push_flow_count: 0,
                    return_kind: None,
                });
                new_id
            };
            // Aggregate flow-stack counts so the super-block mirrors the
            // text-level totals of its range.
            new_blocks[super_new_id].push_flow_count += block.push_flow_count;
            if block.stmt_range.end == super_range.end {
                new_blocks[super_new_id].return_kind = block.return_kind;
            }
            old_to_new[old_id] = Some(super_new_id);
            continue;
        }
        let new_id = new_blocks.len();
        new_blocks.push(block.clone());
        old_to_new[old_id] = Some(new_id);
    }

    // If a super-block's successor falls inside its own range (rare), treat
    // as Terminal.
    let translate = |old: BlockId| -> Option<BlockId> { old_to_new.get(old).copied().flatten() };

    for (old_id, block) in old_blocks.iter().enumerate() {
        let Some(new_id) = old_to_new[old_id] else {
            continue;
        };
        // Set the super-block exit from its LAST swallowed block so
        // fall-through goes to whatever follows the super-block.
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
