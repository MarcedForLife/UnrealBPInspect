//! Shared decoder test helpers.
//!
//! Each `decode/*` test module previously redefined the same handful of
//! small builders (`empty_name_table`, `ue4_ctx`, `identity_map`,
//! `u32_le`, `stmt_kind`). Centralising them keeps one canonical shape;
//! a couple of file-specific signatures (`branch.rs` passes
//! `event_entries`) flow through the same builder via an `Option`
//! parameter.

use crate::binary::NameTable;
use crate::bytecode::stmt::Stmt;
use std::collections::BTreeMap;

use super::ctx::DecodeCtx;

/// Empty `NameTable`. Bytecode tests rarely exercise FName operands at
/// the statement level once expressions are pre-decoded, so most decode
/// tests can get away with no names at all.
pub(crate) fn empty_name_table() -> NameTable {
    NameTable::from_names(vec![])
}

/// `DecodeCtx` for UE4 (ue5 = 0) with no event entries. Suitable for
/// most decode unit tests where cross-event jump translation is out of
/// scope.
pub(crate) fn ue4_ctx<'a>(
    bytecode: &'a [u8],
    name_table: &'a NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
) -> DecodeCtx<'a> {
    ue4_ctx_with_events(bytecode, name_table, mem_to_disk, None)
}

/// `DecodeCtx` for UE4 (ue5 = 0) with a caller-supplied event-entry map.
/// Branch decoding tests need this variant to exercise the cross-event
/// jump path that emits `Stmt::EventCall`.
pub(crate) fn ue4_ctx_with_events<'a>(
    bytecode: &'a [u8],
    name_table: &'a NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
    event_entries: Option<&'a BTreeMap<usize, String>>,
) -> DecodeCtx<'a> {
    DecodeCtx {
        mem_to_disk: Some(mem_to_disk),
        event_entries,
        ..DecodeCtx::new(bytecode, name_table, &[], &[], 0)
    }
}

/// `DecodeCtx` for UE4 with a caller-supplied export-name table. The
/// dispatch-cascade tests need this variant so EX_CALL_MATH operands
/// resolve to a recognised function name (e.g. `NotEqual_IntInt`)
/// without having to construct a real import table fixture.
pub(crate) fn ue4_ctx_with_exports<'a>(
    bytecode: &'a [u8],
    name_table: &'a NameTable,
    mem_to_disk: &'a BTreeMap<usize, usize>,
    export_names: &'a [String],
) -> DecodeCtx<'a> {
    DecodeCtx {
        mem_to_disk: Some(mem_to_disk),
        ..DecodeCtx::new(bytecode, name_table, &[], export_names, 0)
    }
}

/// Identity mem-to-disk map for streams without FName-bearing operands.
/// Maps each opcode-boundary offset to itself.
pub(crate) fn identity_map(boundaries: &[usize]) -> BTreeMap<usize, usize> {
    boundaries.iter().map(|&off| (off, off)).collect()
}

/// Little-endian encoding of a `u32` jump target / count operand.
pub(crate) fn u32_le(value: u32) -> [u8; 4] {
    value.to_le_bytes()
}

/// Append a little-endian `u32` to `buffer`. Used by tests that build
/// synthetic bytecode streams imperatively.
pub(crate) fn put_u32(buffer: &mut Vec<u8>, value: u32) {
    buffer.extend_from_slice(&value.to_le_bytes());
}

/// Append a little-endian `i32` to `buffer`. Mirrors `put_u32` for the
/// signed operand widths the bytecode uses (name-table indices,
/// instance numbers, etc.).
pub(crate) fn put_i32(buffer: &mut Vec<u8>, value: i32) {
    buffer.extend_from_slice(&value.to_le_bytes());
}

/// Append an FName operand: name-table index plus instance-number `0`.
/// Matches the on-disk shape produced by the property serializer.
pub(crate) fn put_fname(buffer: &mut Vec<u8>, name_idx: i32) {
    put_i32(buffer, name_idx);
    put_i32(buffer, 0);
}

/// Append a field-path operand: count = 1, single FName entry, owner
/// index 0. Used wherever the bytecode encodes a property reference as
/// `EFieldPath`.
pub(crate) fn put_field_path(buffer: &mut Vec<u8>, name_idx: i32) {
    put_i32(buffer, 1);
    put_fname(buffer, name_idx);
    put_i32(buffer, 0);
}

/// Variant-name extractor for friendlier assertion failure output.
pub(crate) fn stmt_kind(stmt: &Stmt) -> &'static str {
    match stmt {
        Stmt::Assignment { .. } => "Assignment",
        Stmt::Call { .. } => "Call",
        Stmt::Branch { .. } => "Branch",
        Stmt::Sequence { .. } => "Sequence",
        Stmt::Loop { .. } => "Loop",
        Stmt::Switch { .. } => "Switch",
        Stmt::Latch { .. } => "Latch",
        Stmt::Return { .. } => "Return",
        Stmt::EventCall { .. } => "EventCall",
        Stmt::Break { .. } => "Break",
        Stmt::Unknown { .. } => "Unknown",
    }
}
