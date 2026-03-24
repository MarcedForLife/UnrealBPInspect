/// Strip UE compiler-generated GUID suffixes: `VarName_42_A1B2C3D4E5F6...` -> `VarName`.
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
    let name = normalize_lwc_name(name);
    if let Some(rest) = name.strip_prefix("CallFunc_") {
        let rest = rest.strip_suffix("_ReturnValue").unwrap_or(rest);
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

/// Normalize UE5 LWC (Large World Coordinates) name variants back to UE4 equivalents
/// for clean cross-version diffs.
fn normalize_lwc_name(name: &str) -> String {
    let mut s = name.to_string();
    // Binary math ops: _DoubleDouble -> _FloatFloat
    s = s.replace("_DoubleDouble", "_FloatFloat");
    // Standalone function renames
    s = s.replace("SelectDouble", "SelectFloat");
    // Strip UE5 implicit cast intermediary suffixes, these are transparent
    // pass-through assignments that clutter output and block temp inlining.
    if let Some(base) = s.strip_suffix("_ImplicitCast") {
        s = base.to_string();
    } else if let Some(pos) = s.rfind("_ImplicitCast_") {
        // _ImplicitCast_N suffix (numbered variant)
        let suffix = &s[pos + "_ImplicitCast_".len()..];
        if suffix.chars().all(|c| c.is_ascii_digit()) {
            // Keep the _N disambiguator but drop _ImplicitCast
            s = format!("{}_{}", &s[..pos], suffix);
        }
    }
    s
}

// Inline tests: strip_guid_suffix and clean_bytecode_name are private helpers.
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

    // LWC normalization

    #[test]
    fn lwc_double_double_to_float_float() {
        assert_eq!(
            clean_bc_name("CallFunc_Add_DoubleDouble_ReturnValue"),
            "$Add_FloatFloat"
        );
    }

    #[test]
    fn lwc_select_double_to_select_float() {
        assert_eq!(
            clean_bc_name("CallFunc_SelectDouble_ReturnValue"),
            "$SelectFloat"
        );
    }

    #[test]
    fn lwc_strip_implicit_cast_suffix() {
        assert_eq!(
            clean_bc_name("CallFunc_Subtract_DoubleDouble_A_ImplicitCast"),
            "$Subtract_FloatFloat_A"
        );
    }

    #[test]
    fn lwc_strip_implicit_cast_numbered() {
        assert_eq!(
            clean_bc_name("CallFunc_Subtract_DoubleDouble_B_ImplicitCast_1"),
            "$Subtract_FloatFloat_B_1"
        );
    }

    #[test]
    fn lwc_k2node_implicit_cast() {
        assert_eq!(
            clean_bc_name("K2Node_VariableSet_Health_ImplicitCast"),
            "$VariableSet_Health"
        );
    }

    #[test]
    fn lwc_plain_name_no_change() {
        assert_eq!(clean_bc_name("MyVariable"), "MyVariable");
    }
}
