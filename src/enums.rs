//! Resolve known UE enum integer values to their symbolic names.
//!
//! Two entry points: [`resolve_enum_args`] for function call arguments,
//! [`resolve_enum_comparison`] for an `==`/`!=` against a known
//! enum-returning getter.

/// Rewrite integer arguments of `func_name` in place to their enum names.
/// Indices are relative to the displayed argument list, after
/// WorldContextObject / LatentActionInfo filtering in
/// `format_call_or_operator`.
pub fn resolve_enum_args(func_name: &str, args: &mut [String]) {
    let name = canonical_name(func_name);
    for &(funcs, indices, values) in ARG_MAPPINGS {
        if !funcs.contains(&name) {
            continue;
        }
        for &index in indices {
            if let Some(arg) = args.get_mut(index) {
                resolve_literal(arg, values, "");
            }
        }
    }
}

/// Rewrite an `lhs <op> rhs` equality in place when one side refers to
/// a known enum-returning getter (call form `Receiver.Getter(...)` or
/// bytecode temp form `$Getter`/`$Getter_N`) and the other is an
/// integer literal.
pub fn resolve_enum_comparison(lhs: &mut String, rhs: &mut String) {
    if let Some((prefix, values)) = getter_enum(lhs) {
        resolve_literal(rhs, values, prefix);
    } else if let Some((prefix, values)) = getter_enum(rhs) {
        resolve_literal(lhs, values, prefix);
    }
}

fn getter_enum(expr: &str) -> Option<(&'static str, &'static [&'static str])> {
    let raw = match expr.strip_prefix('$') {
        Some(temp) => strip_numeric_suffix(temp),
        None => expr.rsplit_once('(')?.0,
    };
    let name = canonical_name(raw);
    COMPARISON_GETTERS
        .iter()
        .find(|(getter, ..)| *getter == name)
        .map(|(_, prefix, values)| (*prefix, *values))
}

/// Short, unprefixed function name for table lookup: drops any
/// `Class.` qualifier and the Kismet compiler's `K2_` / `Conv_` prefix.
fn canonical_name(name: &str) -> &str {
    let short = name.rsplit('.').next().unwrap_or(name);
    short
        .strip_prefix("K2_")
        .or_else(|| short.strip_prefix("Conv_"))
        .unwrap_or(short)
}

/// Bytecode temps get a `_<digits>` disambiguator when multiple instances
/// share a base name; strip it to match the underlying getter.
fn strip_numeric_suffix(name: &str) -> &str {
    match name.rsplit_once('_') {
        Some((head, tail)) if !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()) => head,
        _ => name,
    }
}

fn resolve_literal(operand: &mut String, values: &[&str], prefix: &str) {
    let Ok(index) = operand.trim().parse::<usize>() else {
        return;
    };
    if let Some(name) = values.get(index) {
        *operand = format!("{prefix}{name}");
    }
}

// (function_names, arg_indices, enum_values)
const ARG_MAPPINGS: &[(&[&str], &[usize], &[&str])] = &[
    (&["SetCollisionEnabled"], &[0], ECOLLISION_ENABLED),
    (
        &["SetCollisionObjectType", "SetCollisionResponseToChannel"],
        &[0],
        ECOLLISION_CHANNEL,
    ),
    (
        &["SetCollisionResponseToChannel"],
        &[1],
        ECOLLISION_RESPONSE,
    ),
    (
        &["SetCollisionResponseToAllChannels"],
        &[0],
        ECOLLISION_RESPONSE,
    ),
    (
        &[
            "AttachToComponent",
            "AttachRootComponentTo",
            "AttachToActor",
        ],
        &[2, 3, 4],
        EATTACHMENT_RULE,
    ),
    (
        &[
            "DetachFromComponent",
            "DetachRootComponentFromParent",
            "DetachFromActor",
        ],
        &[0, 1, 2],
        EDETACHMENT_RULE,
    ),
    (
        &["GetSocketTransform", "GetRelativeTransform"],
        &[1],
        ERELATIVE_TRANSFORM_SPACE,
    ),
    (&["SetTickGroup"], &[0], ETICKING_GROUP),
    (&["SetMobility"], &[0], ECOMPONENT_MOBILITY),
    (&["SetMovementMode"], &[0], EMOVEMENT_MODE),
    (
        &[
            "GetInputAxisKeyValue",
            "GetInputVectorKeyState",
            "GetKey",
            "InputKey",
            "InputAction",
        ],
        &[1],
        EINPUT_EVENT,
    ),
    // DrawDebugType is at displayed index 6 in all trace variants.
    (TRACE_FUNCS, &[6], EDRAW_DEBUG_TRACE),
];

const TRACE_FUNCS: &[&str] = &[
    "LineTraceSingle",
    "LineTraceSingleForObjects",
    "SphereTraceSingle",
    "SphereTraceSingleForObjects",
    "BoxTraceSingle",
    "BoxTraceSingleForObjects",
    "CapsuleTraceSingle",
    "CapsuleTraceSingleForObjects",
    "LineTraceMulti",
    "LineTraceMultiForObjects",
    "SphereTraceMulti",
    "SphereTraceMultiForObjects",
    "BoxTraceMulti",
    "BoxTraceMultiForObjects",
    "CapsuleTraceMulti",
    "CapsuleTraceMultiForObjects",
];

// (getter_name, value_prefix, enum_values)
// On `==`/`!=` against a getter listed here, the integer literal on the
// other side becomes `{prefix}{values[n]}`.
const COMPARISON_GETTERS: &[(&str, &str, &[&str])] =
    &[("GetCollisionObjectType", "ECC_", ECOLLISION_CHANNEL)];

// Enum value tables. Indices match the UE4 enum declaration order.

const ECOLLISION_ENABLED: &[&str] = &["NoCollision", "QueryOnly", "PhysicsOnly", "QueryAndPhysics"];

const ECOLLISION_CHANNEL: &[&str] = &[
    "WorldStatic",
    "WorldDynamic",
    "Pawn",
    "Visibility",
    "Camera",
    "PhysicsBody",
    "Vehicle",
    "Destructible",
];

const ECOLLISION_RESPONSE: &[&str] = &["Ignore", "Overlap", "Block"];

const EATTACHMENT_RULE: &[&str] = &["KeepRelative", "KeepWorld", "SnapToTarget"];

const EDETACHMENT_RULE: &[&str] = &["KeepRelative", "KeepWorld"];

const ERELATIVE_TRANSFORM_SPACE: &[&str] = &[
    "RTS_World",
    "RTS_Actor",
    "RTS_Component",
    "RTS_ParentBoneSpace",
];

const ETICKING_GROUP: &[&str] = &[
    "PrePhysics",
    "DuringPhysics",
    "PostPhysics",
    "PostUpdateWork",
];

const ECOMPONENT_MOBILITY: &[&str] = &["Static", "Stationary", "Movable"];

const EMOVEMENT_MODE: &[&str] = &[
    "None",
    "Walking",
    "NavWalking",
    "Falling",
    "Swimming",
    "Flying",
    "Custom",
];

const EINPUT_EVENT: &[&str] = &["Pressed", "Released", "Repeat", "DoubleClick", "Axis"];

const EDRAW_DEBUG_TRACE: &[&str] = &["None", "ForOneFrame", "ForDuration", "Persistent"];
