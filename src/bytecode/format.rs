//! Call formatting: operator inlining, array rewriting, name cleanup.
//!
//! Transforms decoded Kismet function calls into readable pseudocode.
//! `format_call_or_operator` is the main entry point, called from `decode.rs`.

use crate::helpers::expr_is_compound;

/// Binary operator table: (prefix_or_exact_name, operator_symbol).
/// Matched against the short name (after last `.`). Prefix entries use `starts_with`,
/// exact entries (no `_` suffix) use `==`.
const BINARY_OPS: &[(&str, &str)] = &[
    ("Add_", "+"),
    ("Subtract_", "-"),
    ("Multiply_", "*"),
    ("Divide_", "/"),
    ("Percent_", "%"),
    ("EqualEqual_", "=="),
    ("NotEqual_", "!="),
    ("LessEqual_", "<="),
    ("GreaterEqual_", ">="),
    ("Less_", "<"),
    ("Greater_", ">"),
    ("GreaterGreater_", ">>"),
    ("LessLess_", "<<"),
    ("BooleanAND", "&&"),
    ("BooleanOR", "||"),
    ("Concat_StrStr", "+"),
];

fn maybe_paren(expr: &str) -> String {
    if expr_is_compound(expr) {
        format!("({})", expr)
    } else {
        expr.to_string()
    }
}

/// Try to inline a Kismet math/logic function as an operator expression.
fn try_inline_operator(name: &str, args: &[String]) -> Option<String> {
    let short = name.rsplit('.').next().unwrap_or(name);
    // Unary prefix
    if short == "Not_PreBool" {
        return args.first().map(|a| format!("!{}", maybe_paren(a)));
    }
    // Binary operators
    let operator = BINARY_OPS.iter().find_map(|(prefix, op)| {
        if short.starts_with(prefix) || short == *prefix {
            Some(*op)
        } else {
            None
        }
    })?;
    if args.len() >= 2 {
        Some(format!(
            "{} {} {}",
            maybe_paren(&args[0]),
            operator,
            maybe_paren(&args[1])
        ))
    } else {
        None
    }
}

/// Rewrite KismetArrayLibrary function calls to idiomatic array syntax.
///
/// Method-style: `Array_Add(arr, item)` -> `arr.Add(item)`
/// Index-style:  `Array_Get(arr, idx, $out)` -> `$out = arr[idx]`
/// Property-style: `Array_Length(arr)` -> `arr.Num()`
pub(super) fn try_rewrite_array_call(name: &str, args: &[String]) -> Option<String> {
    let method = name.strip_prefix("Array_")?;
    let arr = args.first()?;
    let rest = &args[1..];

    // Index-access patterns
    match method {
        "Get" if args.len() == 3 => return Some(format!("{} = {}[{}]", args[2], arr, args[1])),
        "Set" if args.len() >= 3 && args.get(3).is_none_or(|v| v != "true") => {
            return Some(format!("{}[{}] = {}", arr, args[1], args[2]));
        }
        _ => {}
    }

    // Out-param patterns (last arg is the output)
    match method {
        "Last" if rest.len() == 1 => return Some(format!("{} = {}.Last()", rest[0], arr)),
        "Find" if rest.len() == 2 => {
            return Some(format!("{} = {}.Find({})", rest[1], arr, rest[0]));
        }
        _ => {}
    }

    // Default: arr.Method(remaining args)
    Some(format!("{}.{}({})", arr, method, rest.join(", ")))
}

fn strip_k2_prefix(name: &str) -> &str {
    name.strip_prefix("K2_")
        .or_else(|| name.strip_prefix("Conv_"))
        .unwrap_or(name)
}

fn strip_func_prefix(name: &str) -> String {
    let result = if let Some(dot_pos) = name.rfind('.') {
        let class_part = &name[..dot_pos];
        let func = strip_k2_prefix(&name[dot_pos + 1..]);
        if is_ue4_library_class(class_part) {
            func.to_string()
        } else {
            format!("{}.{}", class_part, func)
        }
    } else {
        strip_k2_prefix(name).to_string()
    };
    normalize_lwc_func(&result)
}

/// Normalize UE5 LWC (Large World Coordinates) function names back to UE4 equivalents.
fn normalize_lwc_func(name: &str) -> String {
    name.replace("_DoubleDouble", "_FloatFloat")
        .replace("SelectDouble", "SelectFloat")
}

pub(super) fn is_ue4_library_class(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    matches!(
        short,
        "KismetArrayLibrary"
            | "KismetMathLibrary"
            | "KismetSystemLibrary"
            | "KismetStringLibrary"
            | "KismetTextLibrary"
            | "KismetInputLibrary"
            | "KismetMaterialLibrary"
            | "KismetNodeHelperLibrary"
            | "KismetRenderingLibrary"
            | "KismetGuidLibrary"
            | "GameplayStatics"
            | "HeadMountedDisplayFunctionLibrary"
            | "BlueprintMapLibrary"
            | "BlueprintSetLibrary"
    )
}

/// Extract the resume offset from a LatentActionInfo struct literal.
///
/// The `skip_offset` field is where execution resumes after the latent action completes.
/// Used by summary output to match resume blocks to their Delay() calls.
fn extract_latent_resume_offset(lai: &str) -> Option<usize> {
    let inner = lai.strip_prefix("LatentActionInfo(")?.strip_suffix(')')?;
    let first = inner.split(',').next()?.trim();
    // skip_offset(0xHEX) format
    let hex = first.strip_prefix("skip_offset(0x")?.strip_suffix(')')?;
    usize::from_str_radix(hex, 16).ok()
}

pub(super) fn format_call_or_operator(name: &str, args: Vec<String>) -> String {
    if let Some(inlined) = try_inline_operator(name, &args) {
        return inlined;
    }
    // Extract resume offset from LatentActionInfo before stripping
    let resume_annotation = args
        .iter()
        .find(|a| a.starts_with("LatentActionInfo("))
        .and_then(|lai| extract_latent_resume_offset(lai));
    // Strip WorldContextObject (self as first arg of global functions) and LatentActionInfo
    let mut clean_args: Vec<String> = args
        .iter()
        .filter(|a| {
            // Drop WorldContextObject; "self" as first arg of non-method calls
            (a.as_str() != "self" || name.contains('.'))
            // Drop LatentActionInfo struct literals, internal plumbing
            && !a.starts_with("LatentActionInfo(")
        })
        .cloned()
        .collect();
    let clean_name = strip_func_prefix(name);
    crate::enums::resolve_enum_args(&clean_name, &mut clean_args);
    if let Some(rewritten) = try_rewrite_array_call(&clean_name, &clean_args) {
        return rewritten;
    }
    let call = format!(
        "{}({})",
        clean_name,
        clean_args
            .iter()
            .map(|a| a.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );
    if let Some(offset) = resume_annotation {
        format!("{} /*resume:0x{:04x}*/", call, offset)
    } else {
        call
    }
}
