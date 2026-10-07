//! Bytecode-level binary readers.
//!
//! Works on `&[u8]` + `&mut usize` (not `Cursor`). Returns defaults on
//! truncation, but retain the attempted cursor end so callers can diagnose
//! missing operands instead of accepting the fallback value as decoded data.

use std::collections::BTreeMap;

use crate::binary::NameTable;

/// Shared low-level read context for the partition and structure scanners.
///
/// Bundles the four inputs the opcode-length and successor scanners thread
/// together: the bytecode slice, the name table (for FName reads), the UE5
/// version gate (`0` for UE4, `1000+` for UE5), and the memory-to-disk jump
/// target translation. Passing one `&BytecodeView` collapses the repeated
/// `(bytecode, name_table, ue5, mem_to_disk)` quartet that the scanners would
/// otherwise forward individually through every layer.
///
/// Functions taking a subset of the four still accept the whole view and read
/// only the fields they need; the bundle stays homogeneous across the pipeline.
pub(crate) struct BytecodeView<'a> {
    pub bytecode: &'a [u8],
    pub name_table: &'a NameTable,
    pub ue5: i32,
    pub mem_to_disk: &'a BTreeMap<usize, usize>,
}

macro_rules! read_bc_num {
    ($name:ident, $ty:ty, $default:expr) => {
        pub fn $name(bytecode: &[u8], pos: &mut usize) -> $ty {
            const SIZE: usize = std::mem::size_of::<$ty>();
            let end = pos.saturating_add(SIZE);
            if end > bytecode.len() {
                *pos = end;
                return $default;
            }
            let val = <$ty>::from_le_bytes(bytecode[*pos..end].try_into().unwrap());
            *pos = end;
            val
        }
    };
}

read_bc_num!(read_bc_u8, u8, 0);
read_bc_num!(read_bc_i32, i32, 0);
read_bc_num!(read_bc_u32, u32, 0);
read_bc_num!(read_bc_i64, i64, 0);
read_bc_num!(read_bc_u16, u16, 0);
read_bc_num!(read_bc_u64, u64, 0);
read_bc_num!(read_bc_f32, f32, 0.0);
read_bc_num!(read_bc_f64, f64, 0.0);

pub fn read_bc_fname(bytecode: &[u8], pos: &mut usize, name_table: &NameTable) -> String {
    let index = read_bc_i32(bytecode, pos);
    let number = read_bc_i32(bytecode, pos);
    let base = name_table.get(index);
    if number > 0 {
        format!("{}_{}", base, number - 1)
    } else {
        base.to_string()
    }
}

/// Read 3 floats as f64 values. `lwc` = Large World Coordinates (UE5 >= 1004):
/// vectors/rotators are serialized as f64 instead of f32.
pub fn read_bc_xyz(bytecode: &[u8], pos: &mut usize, lwc: bool) -> (f64, f64, f64) {
    (
        read_bc_float(bytecode, pos, lwc),
        read_bc_float(bytecode, pos, lwc),
        read_bc_float(bytecode, pos, lwc),
    )
}

/// Read 4 floats (f32 or f64 depending on LWC) as f64 values.
pub fn read_bc_xyzw(bytecode: &[u8], pos: &mut usize, lwc: bool) -> (f64, f64, f64, f64) {
    (
        read_bc_float(bytecode, pos, lwc),
        read_bc_float(bytecode, pos, lwc),
        read_bc_float(bytecode, pos, lwc),
        read_bc_float(bytecode, pos, lwc),
    )
}

/// Read one float and widen to f64. With `lwc` (Large World Coordinates,
/// the UE5 1004+ double-vector format) the value is stored as f64; pre-LWC
/// it is f32, widened. Tuple elements evaluate left-to-right, so callers
/// reading several in sequence advance `pos` in component order.
fn read_bc_float(bytecode: &[u8], pos: &mut usize, lwc: bool) -> f64 {
    if lwc {
        read_bc_f64(bytecode, pos)
    } else {
        read_bc_f32(bytecode, pos) as f64
    }
}

/// Read an FName and apply the mem_adj correction.
/// FNames are 8 bytes on disk but 12 in memory (WITH_CASE_PRESERVING_NAME adds DisplayIndex).
pub fn read_bc_fname_with_adj(
    bytecode: &[u8],
    pos: &mut usize,
    name_table: &NameTable,
    mem_adj: &mut i32,
) -> String {
    let name = read_bc_fname(bytecode, pos, name_table);
    *mem_adj += 4;
    name
}

pub fn read_bc_string(bytecode: &[u8], pos: &mut usize) -> String {
    let mut bytes = Vec::new();
    while *pos < bytecode.len() {
        let byte = bytecode[*pos];
        *pos += 1;
        if byte == 0 {
            return String::from_utf8_lossy(&bytes).to_string();
        }
        bytes.push(byte);
    }
    // A terminator is part of the operand, so EOF is a failed read.
    *pos = pos.saturating_add(1);
    String::from_utf8_lossy(&bytes).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_reader_requires_a_terminator_and_stops_at_it() {
        for (bytes, expected, end) in [
            (&b"\0"[..], "", 1),
            (&b"abc\0tail"[..], "abc", 4),
            (&b""[..], "", 1),
            (&b"abc"[..], "abc", 4),
        ] {
            let mut position = 0;
            assert_eq!(read_bc_string(bytes, &mut position), expected);
            assert_eq!(position, end);
        }
        let mut position = usize::MAX;
        assert_eq!(read_bc_string(&[], &mut position), "");
        assert_eq!(position, usize::MAX);
    }

    #[test]
    fn truncated_numeric_reads_preserve_attempted_end_without_overflow() {
        let mut position = 1;
        assert_eq!(read_bc_i32(&[0, 1], &mut position), 0);
        assert_eq!(position, 5);
        assert_eq!(read_bc_u8(&[0, 1], &mut position), 0);
        assert_eq!(position, 6);
        position = usize::MAX - 1;
        assert_eq!(read_bc_f64(&[], &mut position), 0.0);
        assert_eq!(position, usize::MAX);
        assert_eq!(read_bc_u8(&[], &mut position), 0);
        assert_eq!(position, usize::MAX);
    }
}
