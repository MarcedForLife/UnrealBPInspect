pub fn strip_guid_suffix(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() < 36 { return name; }
    let hex_start = bytes.len() - 32;
    if !bytes[hex_start..].iter().all(|b| b.is_ascii_hexdigit()) { return name; }
    if bytes[hex_start - 1] != b'_' { return name; }
    let mut i = hex_start - 2;
    if !bytes[i].is_ascii_digit() { return name; }
    while i > 0 && bytes[i - 1].is_ascii_digit() { i -= 1; }
    if i == 0 || bytes[i - 1] != b'_' { return name; }
    &name[..i - 1]
}

pub fn clean_bc_name(name: &str) -> String {
    let name = strip_guid_suffix(name);
    if let Some(rest) = name.strip_prefix("CallFunc_") {
        let rest = rest.strip_suffix("_ReturnValue").unwrap_or(rest);
        return format!("${}", rest);
    }
    if let Some(rest) = name.strip_prefix("K2Node_DynamicCast_") {
        return format!("$Cast_{}", rest);
    }
    if let Some(rest) = name.strip_prefix("K2Node_") {
        return format!("${}", rest);
    }
    name.to_string()
}
