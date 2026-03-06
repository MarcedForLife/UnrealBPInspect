use crate::binary::NameTable;

pub fn read_bc_u8(bc: &[u8], pos: &mut usize) -> u8 {
    if *pos >= bc.len() { *pos = bc.len(); return 0; }
    let v = bc[*pos];
    *pos += 1;
    v
}

pub fn read_bc_i32(bc: &[u8], pos: &mut usize) -> i32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0; }
    let v = i32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

pub fn read_bc_u32(bc: &[u8], pos: &mut usize) -> u32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0; }
    let v = u32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

pub fn read_bc_i64(bc: &[u8], pos: &mut usize) -> i64 {
    if *pos + 8 > bc.len() { *pos = bc.len(); return 0; }
    let v = i64::from_le_bytes([
        bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3],
        bc[*pos+4], bc[*pos+5], bc[*pos+6], bc[*pos+7],
    ]);
    *pos += 8;
    v
}

pub fn read_bc_f32(bc: &[u8], pos: &mut usize) -> f32 {
    if *pos + 4 > bc.len() { *pos = bc.len(); return 0.0; }
    let v = f32::from_le_bytes([bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3]]);
    *pos += 4;
    v
}

pub fn read_bc_fname(bc: &[u8], pos: &mut usize, nt: &NameTable) -> String {
    let index = read_bc_i32(bc, pos);
    let number = read_bc_i32(bc, pos);
    let base = nt.get(index);
    if number > 0 { format!("{}_{}", base, number - 1) } else { base.to_string() }
}

pub fn read_bc_u16(bc: &[u8], pos: &mut usize) -> u16 {
    if *pos + 2 > bc.len() { *pos = bc.len(); return 0; }
    let v = u16::from_le_bytes([bc[*pos], bc[*pos+1]]);
    *pos += 2;
    v
}

pub fn read_bc_u64(bc: &[u8], pos: &mut usize) -> u64 {
    if *pos + 8 > bc.len() { *pos = bc.len(); return 0; }
    let v = u64::from_le_bytes([
        bc[*pos], bc[*pos+1], bc[*pos+2], bc[*pos+3],
        bc[*pos+4], bc[*pos+5], bc[*pos+6], bc[*pos+7],
    ]);
    *pos += 8;
    v
}

pub fn read_bc_string(bc: &[u8], pos: &mut usize) -> String {
    let mut s = Vec::new();
    while *pos < bc.len() {
        let b = bc[*pos];
        *pos += 1;
        if b == 0 { break; }
        s.push(b);
    }
    String::from_utf8_lossy(&s).to_string()
}
