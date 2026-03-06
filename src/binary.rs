use std::io::{Cursor, Read, Seek, SeekFrom};
use anyhow::Result;

pub type R<'a> = Cursor<&'a [u8]>;

pub fn read_i32(c: &mut R) -> Result<i32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(i32::from_le_bytes(b))
}

pub fn read_u32(c: &mut R) -> Result<u32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(u32::from_le_bytes(b))
}

pub fn read_i64(c: &mut R) -> Result<i64> {
    let mut b = [0u8; 8];
    c.read_exact(&mut b)?;
    Ok(i64::from_le_bytes(b))
}

pub fn read_u8(c: &mut R) -> Result<u8> {
    let mut b = [0u8; 1];
    c.read_exact(&mut b)?;
    Ok(b[0])
}

pub fn read_f32(c: &mut R) -> Result<f32> {
    let mut b = [0u8; 4];
    c.read_exact(&mut b)?;
    Ok(f32::from_le_bytes(b))
}

pub fn read_f64(c: &mut R) -> Result<f64> {
    let mut b = [0u8; 8];
    c.read_exact(&mut b)?;
    Ok(f64::from_le_bytes(b))
}

pub fn read_guid(c: &mut R) -> Result<[u8; 16]> {
    let mut g = [0u8; 16];
    c.read_exact(&mut g)?;
    Ok(g)
}

pub fn read_fstring(c: &mut R) -> Result<String> {
    let len = read_i32(c)?;
    if len == 0 {
        return Ok(String::new());
    }
    if len > 0 {
        let mut s = vec![0u8; len as usize];
        c.read_exact(&mut s)?;
        Ok(String::from_utf8_lossy(&s).trim_end_matches('\0').to_string())
    } else {
        let count = (-len) as usize;
        let mut s = vec![0u8; count * 2];
        c.read_exact(&mut s)?;
        let utf16: Vec<u16> = s.chunks_exact(2).map(|c| u16::from_le_bytes([c[0], c[1]])).collect();
        Ok(String::from_utf16_lossy(&utf16).trim_end_matches('\0').to_string())
    }
}

pub struct NameTable {
    names: Vec<String>,
}

impl NameTable {
    pub fn read(c: &mut R, count: i32, offset: i32) -> Result<Self> {
        c.seek(SeekFrom::Start(offset as u64))?;
        let mut names = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let name = read_fstring(c)?;
            let _hash = read_u32(c)?;
            names.push(name);
        }
        Ok(NameTable { names })
    }

    pub fn get(&self, index: i32) -> &str {
        self.names.get(index as usize).map(|s| s.as_str()).unwrap_or("?")
    }

    pub fn fname(&self, c: &mut R) -> Result<String> {
        let index = read_i32(c)?;
        let number = read_i32(c)?;
        let base = self.get(index);
        if number > 0 {
            Ok(format!("{}_{}", base, number - 1))
        } else {
            Ok(base.to_string())
        }
    }

    pub fn fname_is_none(&self, c: &mut R) -> Result<(String, bool)> {
        let index = read_i32(c)?;
        let number = read_i32(c)?;
        let base = self.get(index);
        let is_none = base == "None" && number == 0;
        let name = if number > 0 {
            format!("{}_{}", base, number - 1)
        } else {
            base.to_string()
        };
        Ok((name, is_none))
    }
}
