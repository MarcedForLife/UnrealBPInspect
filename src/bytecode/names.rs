/// Object-name prefix of the compiler-generated ubergraph entry function.
pub(crate) const EXECUTE_UBERGRAPH_PREFIX: &str = "ExecuteUbergraph_";

/// Free-function names recognised as Blueprint latent UFUNCTIONs. Their
/// trailing `FLatentActionInfo` argument is editor-elided, and their Call
/// statement carries an interleaved resume continuation. The argument-strip
/// pass (`transforms::strip_latent_action_info`) and the emit-time
/// resume-body lookup (`emit::summary`) share this single list.
pub(crate) const LATENT_FUNCTIONS: &[&str] = &[
    "Delay",
    "DelayUntilNextTick",
    "RetriggerableDelay",
    "MoveComponentTo",
];

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

/// FName prefix shared by all K2Node Blueprint graph-node classes.
pub(crate) const K2NODE_PREFIX: &str = "K2Node_";
/// K2Node class name for an execution-sequence node.
pub(crate) const K2NODE_EXECUTION_SEQUENCE: &str = "K2Node_ExecutionSequence";
/// K2Node class name for a macro-instance node.
pub(crate) const K2NODE_MACRO_INSTANCE: &str = "K2Node_MacroInstance";

/// Classification of a Blueprint flow-stack / control macro, decided once
/// from its resolved macro short name (`build_macro_names`).
///
/// `from_name` maps any unrecognised name to `ExecutionSequence`,
/// reproducing the historical unknown-default the flow-stack region
/// classifier relied on. The variants distinguished by downstream passes
/// are `DoOnce` (the only one carrying a gate-LET the wrap synthesis keys
/// on) and `FlipFlop` (the only toggle the cross-event inliner re-synthesizes);
/// `IsValid` / `MultiGate` / `ExecutionSequence` are recognised but not
/// gate-attributed.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MacroKind {
    DoOnce,
    FlipFlop,
    IsValid,
    MultiGate,
    ExecutionSequence,
}

impl MacroKind {
    /// Classify a resolved macro short name. Any name outside the
    /// recognised set falls through to `ExecutionSequence`, the same
    /// default the flow-stack `has_push` fallback applied to a partition
    /// with no recognised kind.
    pub(crate) fn from_name(name: &str) -> MacroKind {
        match name {
            "DoOnce" => MacroKind::DoOnce,
            "FlipFlop" => MacroKind::FlipFlop,
            "IsValid" => MacroKind::IsValid,
            "MultiGate" => MacroKind::MultiGate,
            _ => MacroKind::ExecutionSequence,
        }
    }

    /// True for the macros whose scattered scaffold the attributor walks
    /// (`DoOnce` / `IsValid` / `FlipFlop`). Drives downstream
    /// pin-reachability attribution.
    pub(crate) fn is_recognised(self) -> bool {
        matches!(
            self,
            MacroKind::DoOnce | MacroKind::IsValid | MacroKind::FlipFlop
        )
    }

    /// True for the macros that emit a gate-LET / JIN / JUMP scaffold the
    /// `attribute_macro_scaffold_bytes` pass attributes (`DoOnce` /
    /// `FlipFlop`). Distinct from [`MacroKind::is_recognised`].
    pub(crate) fn has_gate_scaffold(self) -> bool {
        matches!(self, MacroKind::DoOnce | MacroKind::FlipFlop)
    }
}

pub fn clean_bc_name(name: &str) -> String {
    let name = strip_guid_suffix(name);
    let name = normalize_lwc_name(name);
    if let Some(rest) = name.strip_prefix("CallFunc_") {
        let rest = strip_return_value_suffix(rest);
        let rest = rest.strip_prefix("K2_").unwrap_or(&rest).to_string();
        return format!("${}", rest);
    }
    if let Some(rest) = name.strip_prefix("K2Node_DynamicCast_") {
        return format!("$Cast_{}", rest);
    }
    if let Some(rest) = name.strip_prefix(K2NODE_PREFIX) {
        return format!("${}", rest);
    }
    name.to_string()
}

/// Strip `_ReturnValue` or `_ReturnValue_<digits>` from the tail of `name`.
/// Preserves the numeric disambiguator so `Foo_ReturnValue_1` becomes
/// `Foo_1`, matching the decoder's `_<N>` suffix convention for
/// disambiguating duplicate out-params.
fn strip_return_value_suffix(name: &str) -> String {
    const RETURN_VALUE_MARKER: &str = "_ReturnValue";
    if let Some(base) = name.strip_suffix(RETURN_VALUE_MARKER) {
        return base.to_string();
    }
    if let Some(pos) = name.rfind(&format!("{}_", RETURN_VALUE_MARKER)) {
        let suffix = &name[pos + RETURN_VALUE_MARKER.len() + 1..];
        if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
            return format!("{}_{}", &name[..pos], suffix);
        }
    }
    name.to_string()
}

/// Normalize UE5 LWC (Large World Coordinates) name variants back to UE4 equivalents
/// for clean cross-version diffs.
pub fn normalize_lwc_name(name: &str) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip_guid_suffix_cases() {
        // Suffix stripped only for the exact NAME_DIGITS_32HEXCHARS shape.
        for (input, expected) in [
            ("SomeVar_42_0123456789ABCDEF0123456789ABCDEF", "SomeVar"),
            ("Foo", "Foo"), // no suffix
            (
                "Foo_42_notahexstring_notahex_pad_",
                "Foo_42_notahexstring_notahex_pad_",
            ), // trailing segment isn't 32 hex chars
        ] {
            assert_eq!(
                strip_guid_suffix(input),
                expected,
                "strip_guid_suffix({input:?})"
            );
        }
    }

    #[test]
    fn clean_bc_name_cases() {
        let cases = [
            // CallFunc_/K2Node_ prefix and _ReturnValue stripping.
            ("CallFunc_Foo_ReturnValue", "$Foo"),
            ("CallFunc_Bar", "$Bar"),
            ("K2Node_DynamicCast_SomeClass", "$Cast_SomeClass"),
            ("K2Node_SomeThing", "$SomeThing"),
            ("MyVariable", "MyVariable"), // plain name unchanged
            (
                "CallFunc_K2_SetWorldLocationAndRotation_ReturnValue",
                "$SetWorldLocationAndRotation",
            ),
            // `_ReturnValue_<N>` is the duplicate-out-param disambiguator: strip
            // `_ReturnValue`, keep the numeric `_<N>`. A non-digit suffix is not
            // the disambiguator shape and stays intact.
            ("CallFunc_IsValid_ReturnValue_1", "$IsValid_1"),
            ("CallFunc_IsValid_ReturnValue_42", "$IsValid_42"),
            (
                "CallFunc_IsValid_ReturnValue_Foo",
                "$IsValid_ReturnValue_Foo",
            ),
            // LWC (Large World Coordinates): double variants and implicit-cast
            // suffixes fold back to the UE4 float names.
            ("CallFunc_Add_DoubleDouble_ReturnValue", "$Add_FloatFloat"),
            ("CallFunc_SelectDouble_ReturnValue", "$SelectFloat"),
            (
                "CallFunc_Subtract_DoubleDouble_A_ImplicitCast",
                "$Subtract_FloatFloat_A",
            ),
            (
                "CallFunc_Subtract_DoubleDouble_B_ImplicitCast_1",
                "$Subtract_FloatFloat_B_1",
            ),
            (
                "K2Node_VariableSet_Health_ImplicitCast",
                "$VariableSet_Health",
            ),
        ];
        for (raw, expected) in cases {
            assert_eq!(clean_bc_name(raw), expected, "clean_bc_name({raw:?})");
        }
    }
}
