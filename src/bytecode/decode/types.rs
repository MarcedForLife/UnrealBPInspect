use super::super::readers::*;
use super::super::resolve::*;
use crate::binary::NameTable;
use crate::types::ImportEntry;

#[derive(Clone)]
pub struct BcStatement {
    /// In-memory bytecode offset (adjusted for FName size differences).
    pub mem_offset: usize,
    /// Absorbed offsets from removed statements, so `OffsetMap` can still
    /// resolve jump targets that pointed at them. Populated by transform
    /// passes. Empty for most statements.
    pub offset_aliases: Vec<usize>,
    pub text: String,
}

impl BcStatement {
    pub fn new(mem_offset: usize, text: impl Into<String>) -> Self {
        Self {
            mem_offset,
            text: text.into(),
            offset_aliases: Vec::new(),
        }
    }
}

/// Immutable context shared across recursive decode calls. Split from the
/// mutable `pos`/`mem_adj` state to avoid borrow conflicts.
pub struct DecodeCtx<'a> {
    pub(super) bytecode: &'a [u8],
    pub(super) name_table: &'a NameTable,
    pub(super) imports: &'a [ImportEntry],
    pub(super) export_names: &'a [String],
    pub(super) ue5: i32,
}

impl<'a> DecodeCtx<'a> {
    pub(super) fn read_obj_ref(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_obj_ref(self.bytecode, pos, self.imports, self.export_names, mem_adj)
    }

    pub(super) fn read_field_path(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_field_path(self.bytecode, pos, self.name_table, mem_adj)
    }

    pub(super) fn read_fname_with_adj(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_fname_with_adj(self.bytecode, pos, self.name_table, mem_adj)
    }
}
