//! Bytecode-level binary readers.
//!
//! Works on `&[u8]` + `&mut usize` (not `Cursor`). Returns defaults on
//! truncation rather than erroring; bytecode parsing is best-effort.

use crate::binary::NameTable;

macro_rules! read_bc_num {
    ($name:ident, $ty:ty, $default:expr) => {
        pub fn $name(bytecode: &[u8], pos: &mut usize) -> $ty {
            const SIZE: usize = std::mem::size_of::<$ty>();
            if *pos + SIZE > bytecode.len() {
                *pos = bytecode.len();
                return $default;
            }
            let val = <$ty>::from_le_bytes(bytecode[*pos..*pos + SIZE].try_into().unwrap());
            *pos += SIZE;
            val
        }
    };
}

pub fn read_bc_u8(bytecode: &[u8], pos: &mut usize) -> u8 {
    if *pos >= bytecode.len() {
        *pos = bytecode.len();
        return 0;
    }
    let val = bytecode[*pos];
    *pos += 1;
    val
}

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
    if lwc {
        (
            read_bc_f64(bytecode, pos),
            read_bc_f64(bytecode, pos),
            read_bc_f64(bytecode, pos),
        )
    } else {
        (
            read_bc_f32(bytecode, pos) as f64,
            read_bc_f32(bytecode, pos) as f64,
            read_bc_f32(bytecode, pos) as f64,
        )
    }
}

/// Read 4 floats (f32 or f64 depending on LWC) as f64 values.
pub fn read_bc_xyzw(bytecode: &[u8], pos: &mut usize, lwc: bool) -> (f64, f64, f64, f64) {
    if lwc {
        (
            read_bc_f64(bytecode, pos),
            read_bc_f64(bytecode, pos),
            read_bc_f64(bytecode, pos),
            read_bc_f64(bytecode, pos),
        )
    } else {
        (
            read_bc_f32(bytecode, pos) as f64,
            read_bc_f32(bytecode, pos) as f64,
            read_bc_f32(bytecode, pos) as f64,
            read_bc_f32(bytecode, pos) as f64,
        )
    }
}

pub fn read_bc_string(bytecode: &[u8], pos: &mut usize) -> String {
    let mut s = Vec::new();
    while *pos < bytecode.len() {
        let byte = bytecode[*pos];
        *pos += 1;
        if byte == 0 {
            break;
        }
        s.push(byte);
    }
    String::from_utf8_lossy(&s).to_string()
}
