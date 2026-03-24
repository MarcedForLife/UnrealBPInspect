//! Low-level binary reading helpers for `.uasset` parsing.

use anyhow::Result;
use std::io::{Cursor, Read, Seek, SeekFrom};

pub type Reader<'a> = Cursor<&'a [u8]>;

macro_rules! read_le {
    ($name:ident, $ty:ty) => {
        pub fn $name(reader: &mut Reader) -> Result<$ty> {
            let mut b = [0u8; std::mem::size_of::<$ty>()];
            reader.read_exact(&mut b)?;
            Ok(<$ty>::from_le_bytes(b))
        }
    };
}

read_le!(read_i32, i32);
read_le!(read_u32, u32);
read_le!(read_i64, i64);
read_le!(read_u8, u8);
read_le!(read_f32, f32);
read_le!(read_f64, f64);

pub fn read_guid(reader: &mut Reader) -> Result<[u8; 16]> {
    let mut g = [0u8; 16];
    reader.read_exact(&mut g)?;
    Ok(g)
}

/// Read UE FString: len > 0 -> UTF-8 (len bytes), len < 0 -> UTF-16 (|len| code units).
pub fn read_fstring(reader: &mut Reader) -> Result<String> {
    let len = read_i32(reader)?;
    if len == 0 {
        return Ok(String::new());
    }
    if len > 0 {
        let mut s = vec![0u8; len as usize];
        reader.read_exact(&mut s)?;
        Ok(String::from_utf8_lossy(&s)
            .trim_end_matches('\0')
            .to_string())
    } else {
        let count = (-len) as usize;
        let mut s = vec![0u8; count * 2];
        reader.read_exact(&mut s)?;
        let utf16: Vec<u16> = s
            .chunks_exact(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect();
        Ok(String::from_utf16_lossy(&utf16)
            .trim_end_matches('\0')
            .to_string())
    }
}

pub struct NameTable {
    names: Vec<String>,
}

impl NameTable {
    pub fn read(reader: &mut Reader, count: i32, offset: i32) -> Result<Self> {
        reader.seek(SeekFrom::Start(offset as u64))?;
        let mut names = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let name = read_fstring(reader)?;
            let _hash = read_u32(reader)?;
            names.push(name);
        }
        Ok(NameTable { names })
    }

    pub fn get(&self, index: i32) -> &str {
        self.names
            .get(index as usize)
            .map(|s| s.as_str())
            .unwrap_or("?")
    }

    fn format_fname(base: &str, number: i32) -> String {
        if number > 0 {
            format!("{}_{}", base, number - 1)
        } else {
            base.to_string()
        }
    }

    /// Read an FName (8 bytes on disk): name table index + instance number.
    /// UE serializes instance number 1-based, so Number=1 displays as "_0".
    pub fn fname(&self, reader: &mut Reader) -> Result<String> {
        let index = read_i32(reader)?;
        let number = read_i32(reader)?;
        Ok(Self::format_fname(self.get(index), number))
    }

    #[cfg(test)]
    pub fn from_names(names: Vec<String>) -> Self {
        NameTable { names }
    }

    pub fn fname_is_none(&self, reader: &mut Reader) -> Result<(String, bool)> {
        let index = read_i32(reader)?;
        let number = read_i32(reader)?;
        let base = self.get(index);
        let is_none = base == "None" && number == 0;
        Ok((Self::format_fname(base, number), is_none))
    }

    /// Skip an FField metadata block: int32 gate (1 = present), then count + key/value entries.
    pub fn skip_metadata(&self, reader: &mut Reader) -> Result<()> {
        let has_meta = read_i32(reader)?;
        if has_meta != 0 {
            let meta_count = read_i32(reader)?;
            for _ in 0..meta_count {
                self.fname(reader)?;
                read_fstring(reader)?;
            }
        }
        Ok(())
    }

    /// Peek at the next FName without consuming it. Returns true if it resolves
    /// to a known FField property class name (ends with "Property").
    pub fn peek_is_ffield_class(&self, reader: &mut Reader) -> Result<bool> {
        let pos = reader.position();
        let index = read_i32(reader)?;
        let instance = read_i32(reader)?;
        reader.seek(SeekFrom::Start(pos))?;
        // FField class names always have instance number 0. Checking this
        // prevents false positives where bytecode data (e.g. bytecode_size
        // followed by storage_size) coincidentally maps to a "Property" name.
        if instance != 0 {
            return Ok(false);
        }
        let base = self.get(index);
        Ok(base.ends_with("Property"))
    }
}
