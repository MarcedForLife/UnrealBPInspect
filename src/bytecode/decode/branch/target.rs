//! Jump-target classification and instrumentation skipping for the branch decoder.
//!
//! Reads/peeks `EX_JUMP` targets, classifies a target as intra-event, the
//! event-end sentinel, or a cross-event entry, and skips instrumentation
//! opcodes the editor inserts ahead of real jumps.

use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::readers::read_bc_u32;

use super::super::ctx::DecodeCtx;

/// Operand width for `EX_JUMP` / `EX_JUMP_IF_NOT` jump targets. Both
/// opcodes encode a `CodeSkipSizeType` (u32) in mem coordinates.
pub(super) const JUMP_TARGET_BYTES: usize = 4;

/// Classification of a jump target relative to the current decode context.
#[derive(Debug, Clone)]
pub(crate) enum JumpTarget {
    /// Target lives within the current decode range. The `disk` field is
    /// a slice index suitable for further decoding.
    InRange { disk: usize, mem: usize },
    /// Target is the entry of another event. The decoder should emit a
    /// `Stmt::EventCall` rather than recursing.
    EventEntry { event_name: String, mem: usize },
    /// Target falls outside the current range and isn't an event entry.
    /// This typically means the construct extends beyond the current
    /// block, e.g. a tail-call style jump or unresolved offset.
    OutOfRange,
    /// Target couldn't be translated through `mem_to_disk` and isn't
    /// recognised as an event entry.
    Unresolved,
}

/// Classify a memory-coordinate jump target against the current context.
///
/// Resolution order:
/// 1. Event entry table (if present) -> `EventEntry`.
/// 2. `mem_to_disk` map -> `InRange` if the disk offset lies inside
///    `[range_start_disk, range_end_disk]` OR (when the partition has
///    given the event multiple disjoint ranges) inside any of the
///    event's owned ranges. Otherwise `OutOfRange`.
/// 3. Fallback -> `Unresolved`.
///
/// The `owned_ranges` extension is the cross-range classification fix:
/// after partitioning, an event's bytes can be split across several
/// non-contiguous disk ranges, and a Branch in one range may legitimately
/// jump to a body that lives in another range belonging to the same
/// event. Single-range classification incorrectly returned `OutOfRange`
/// for those targets, leaving displaced bodies empty and the bytes
/// emitting flat at top level when the next range was decoded.
pub(crate) fn classify_target(
    target_mem: usize,
    range_start_disk: usize,
    range_end_disk: usize,
    ctx: &DecodeCtx,
) -> JumpTarget {
    if let Some(entries) = ctx.event_entries {
        if let Some(name) = entries.get(&target_mem) {
            return JumpTarget::EventEntry {
                event_name: name.clone(),
                mem: target_mem,
            };
        }
    }

    if let Some(mem_to_disk) = ctx.mem_to_disk {
        if let Some(&disk) = mem_to_disk.get(&target_mem) {
            if disk >= range_start_disk && disk <= range_end_disk {
                return JumpTarget::InRange {
                    disk,
                    mem: target_mem,
                };
            }
            if disk_in_owned_ranges(disk, ctx) {
                return JumpTarget::InRange {
                    disk,
                    mem: target_mem,
                };
            }
            return JumpTarget::OutOfRange;
        }
    }

    JumpTarget::Unresolved
}

/// True when `disk` falls inside any of the event's owned disk ranges.
/// Returns `false` when the context has no `owned_ranges` slice (i.e.
/// standalone function or synthetic test).
fn disk_in_owned_ranges(disk: usize, ctx: &DecodeCtx) -> bool {
    let Some(ranges) = ctx.owned_ranges else {
        return false;
    };
    ranges
        .iter()
        .any(|range| disk >= range.start && disk < range.end)
}

/// Upper bound for forward scans that may need to cross owned-range gaps.
/// Returns the maximum `range.end` across all owned ranges when the
/// context has them, otherwise the caller-supplied `range_end`. Used by
/// terminator-jump scanners and convergence detection so they don't stop
/// at a single range's end when the construct's body extends past it.
pub(crate) fn event_scan_end(range_end: usize, ctx: &DecodeCtx) -> usize {
    match ctx.owned_ranges {
        Some(ranges) => ranges
            .iter()
            .map(|range| range.end)
            .max()
            .unwrap_or(range_end),
        None => range_end,
    }
}

/// Read the 4-byte mem-coord target operand for a jump opcode.
pub(crate) fn read_jump_target(bytecode: &[u8], pos: &mut usize) -> usize {
    read_bc_u32(bytecode, pos) as usize
}

/// Detect whether the byte at `pos` (within `[range_start, range_end)`)
/// is an `EX_JUMP` opcode. If so, peek its target without consuming.
///
/// Returns `Some((target_mem, jump_disk_pos, jump_end_disk_pos))` where
/// `jump_disk_pos` is `pos` and `jump_end_disk_pos` is the disk index
/// immediately after the operand.
pub(crate) fn peek_jump_at(
    bytecode: &[u8],
    pos: usize,
    range_end: usize,
) -> Option<(usize, usize, usize)> {
    let opcode_byte_count = 1;
    let total_jump_size = opcode_byte_count + JUMP_TARGET_BYTES;
    if pos + total_jump_size > range_end {
        return None;
    }
    if bytecode.get(pos)? != &EX_JUMP {
        return None;
    }
    let mut cursor = pos + opcode_byte_count;
    let target = read_bc_u32(bytecode, &mut cursor) as usize;
    Some((target, pos, cursor))
}

/// True for instrumentation opcodes that occupy one byte and carry no
/// semantic content. The recogniser walks past these when looking for
/// the first "real" opcode after a JIN.
fn is_instrumentation_opcode(opcode: u8) -> bool {
    matches!(
        opcode,
        EX_TRACEPOINT | EX_WIRE_TRACEPOINT | EX_INSTRUMENTATION_EVENT
    )
}

/// Skip past instrumentation opcodes starting at `pos`, returning the
/// disk position of the first non-instrumentation byte. Stops at
/// `range_end` if reached. The walk consumes opcodes via
/// `opcode_length_at` so an `EX_INSTRUMENTATION_EVENT` (which has a name
/// operand) advances correctly.
pub(super) fn skip_instrumentation(pos: usize, range_end: usize, ctx: &DecodeCtx) -> usize {
    let mut cursor = pos;
    while cursor < range_end {
        let Some(&opcode) = ctx.bytecode.get(cursor) else {
            break;
        };
        if !is_instrumentation_opcode(opcode) {
            break;
        }
        let length = opcode_length_at(cursor, ctx.bytecode, ctx.ue5, ctx.name_table);
        if length == 0 {
            break;
        }
        cursor += length;
    }
    cursor
}

/// Skip leading instrumentation opcodes (WIRE_TRACEPOINT / TRACEPOINT /
/// INSTRUMENTATION_EVENT) starting at `pos`, then run [`peek_jump_at`] on
/// the first non-instrumentation byte. The IsValid classifier and the
/// prescan use this to detect the displaced-arm `EX_JUMP` that compilers
/// emit immediately after the JIN body header, since non-debug builds
/// interpose 3+ bytes of tracepoint opcodes that would defeat a raw
/// `peek_jump_at` at the body's first byte.
pub(crate) fn peek_jump_after_instrumentation(
    pos: usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<(usize, usize, usize)> {
    let after_instrumentation = skip_instrumentation(pos, range_end, ctx);
    peek_jump_at(ctx.bytecode, after_instrumentation, range_end)
}

/// Find the owned segment of `ctx.owned_ranges` that contains `disk`.
/// Returns `None` when the context has no owned ranges or no segment
/// matches. Used by the IsValid recogniser to bound a displaced
/// valid-pin body whose extent is the contiguous segment partition
/// already assigned to the enclosing scope.
pub(super) fn owned_segment_containing(disk: usize, ctx: &DecodeCtx) -> Option<(usize, usize)> {
    let ranges = ctx.owned_ranges?;
    ranges
        .iter()
        .find(|range| range.start <= disk && disk < range.end)
        .map(|range| (range.start, range.end))
}
