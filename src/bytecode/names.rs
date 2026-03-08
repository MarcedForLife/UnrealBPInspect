/// Strip UE compiler-generated GUID suffixes: `VarName_42_A1B2C3D4E5F6...` → `VarName`.
/// The compiler appends `_<digits>_<32 hex chars>` to disambiguate generated names.
pub fn strip_guid_suffix(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() < 36 {
        return name;
    }
    let hex_start = bytes.len() - 32;
    if !bytes[hex_start..].iter().all(|b| b.is_ascii_hexdigit()) {
        return name;
    }
    if bytes[hex_start - 1] != b'_' {
        return name;
    }
    let mut i = hex_start - 2;
    if !bytes[i].is_ascii_digit() {
        return name;
    }
    while i > 0 && bytes[i - 1].is_ascii_digit() {
        i -= 1;
    }
    if i == 0 || bytes[i - 1] != b'_' {
        return name;
    }
    &name[..i - 1]
}

pub fn clean_bc_name(name: &str) -> String {
    let name = strip_guid_suffix(name);
    if let Some(rest) = name.strip_prefix("CallFunc_") {
        let rest = rest.strip_suffix("_ReturnValue").unwrap_or(rest);
        // Strip K2_ from function-derived variable names
        let rest = rest.strip_prefix("K2_").unwrap_or(rest);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_guid_with_suffix() {
        // Format: NAME_DIGITS_32HEXCHARS
        assert_eq!(
            strip_guid_suffix("SomeVar_42_0123456789ABCDEF0123456789ABCDEF"),
            "SomeVar"
        );
    }

    #[test]
    fn strip_guid_short_name() {
        assert_eq!(strip_guid_suffix("Foo"), "Foo");
    }

    #[test]
    fn strip_guid_no_hex() {
        assert_eq!(
            strip_guid_suffix("Foo_42_notahexstring_notahex_pad_"),
            "Foo_42_notahexstring_notahex_pad_"
        );
    }

    #[test]
    fn clean_callfunc() {
        assert_eq!(clean_bc_name("CallFunc_Foo_ReturnValue"), "$Foo");
    }

    #[test]
    fn clean_callfunc_no_retval() {
        assert_eq!(clean_bc_name("CallFunc_Bar"), "$Bar");
    }

    #[test]
    fn clean_dynamic_cast() {
        assert_eq!(
            clean_bc_name("K2Node_DynamicCast_SomeClass"),
            "$Cast_SomeClass"
        );
    }

    #[test]
    fn clean_k2node() {
        assert_eq!(clean_bc_name("K2Node_SomeThing"), "$SomeThing");
    }

    #[test]
    fn clean_plain_name() {
        assert_eq!(clean_bc_name("MyVariable"), "MyVariable");
    }

    #[test]
    fn clean_k2_prefix_in_callfunc() {
        assert_eq!(
            clean_bc_name("CallFunc_K2_SetWorldLocationAndRotation_ReturnValue"),
            "$SetWorldLocationAndRotation"
        );
    }
}
