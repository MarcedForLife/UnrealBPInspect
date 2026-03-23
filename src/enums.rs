/// Resolve known UE enum integer arguments to their symbolic names.
///
/// Covers core engine enums whose integer values are ABI-stable. Indices are
/// relative to the displayed argument list (after WorldContextObject/LatentActionInfo
/// filtering in `format_call_or_operator`).
pub fn resolve_enum_args(func_name: &str, args: &mut [String]) {
    let short = func_name.rsplit('.').next().unwrap_or(func_name);
    let stripped = short
        .strip_prefix("K2_")
        .or_else(|| short.strip_prefix("Conv_"))
        .unwrap_or(short);

    for &(func, indices, values) in MAPPINGS {
        if stripped == func {
            for &index in indices {
                resolve(args, index, values);
            }
        }
    }
}

fn resolve(args: &mut [String], index: usize, values: &[&str]) {
    if let Some(arg) = args.get(index) {
        if let Ok(val) = arg.trim().parse::<usize>() {
            if let Some(name) = values.get(val) {
                args[index] = name.to_string();
            }
        }
    }
}

// (function_name, arg_indices, enum_values)
// Enum values are indexed by position (first element = 0).
// To add coverage: add a row with the function name, which arguments to resolve, and the enum.
const MAPPINGS: &[(&str, &[usize], &[&str])] = &[
    // Collision
    ("SetCollisionEnabled", &[0], ECOLLISION_ENABLED),
    ("SetCollisionResponseToChannel", &[0], ECOLLISION_CHANNEL),
    ("SetCollisionResponseToChannel", &[1], ECOLLISION_RESPONSE),
    (
        "SetCollisionResponseToAllChannels",
        &[0],
        ECOLLISION_RESPONSE,
    ),
    ("SetCollisionObjectType", &[0], ECOLLISION_CHANNEL),
    // Attachment
    ("AttachToComponent", &[2, 3, 4], EATTACHMENT_RULE),
    ("AttachRootComponentTo", &[2, 3, 4], EATTACHMENT_RULE),
    ("AttachToActor", &[2, 3, 4], EATTACHMENT_RULE),
    ("DetachFromComponent", &[0, 1, 2], EDETACHMENT_RULE),
    (
        "DetachRootComponentFromParent",
        &[0, 1, 2],
        EDETACHMENT_RULE,
    ),
    ("DetachFromActor", &[0, 1, 2], EDETACHMENT_RULE),
    // Transform
    ("GetSocketTransform", &[1], ERELATIVE_TRANSFORM_SPACE),
    ("GetRelativeTransform", &[1], ERELATIVE_TRANSFORM_SPACE),
    // Component/movement
    ("SetTickGroup", &[0], ETICKING_GROUP),
    ("SetMobility", &[0], ECOMPONENT_MOBILITY),
    ("SetMovementMode", &[0], EMOVEMENT_MODE),
    // Input
    ("GetInputAxisKeyValue", &[1], EINPUT_EVENT),
    ("GetInputVectorKeyState", &[1], EINPUT_EVENT),
    ("GetKey", &[1], EINPUT_EVENT),
    ("InputKey", &[1], EINPUT_EVENT),
    ("InputAction", &[1], EINPUT_EVENT),
    // Trace functions (DrawDebugType at display index 6)
    ("LineTraceSingle", &[6], EDRAW_DEBUG_TRACE),
    ("LineTraceSingleForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("SphereTraceSingle", &[6], EDRAW_DEBUG_TRACE),
    ("SphereTraceSingleForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("BoxTraceSingle", &[6], EDRAW_DEBUG_TRACE),
    ("BoxTraceSingleForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("CapsuleTraceSingle", &[6], EDRAW_DEBUG_TRACE),
    ("CapsuleTraceSingleForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("LineTraceMulti", &[6], EDRAW_DEBUG_TRACE),
    ("LineTraceMultiForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("SphereTraceMulti", &[6], EDRAW_DEBUG_TRACE),
    ("SphereTraceMultiForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("BoxTraceMulti", &[6], EDRAW_DEBUG_TRACE),
    ("BoxTraceMultiForObjects", &[6], EDRAW_DEBUG_TRACE),
    ("CapsuleTraceMulti", &[6], EDRAW_DEBUG_TRACE),
    ("CapsuleTraceMultiForObjects", &[6], EDRAW_DEBUG_TRACE),
];

const ECOLLISION_ENABLED: &[&str] = &["NoCollision", "QueryOnly", "PhysicsOnly", "QueryAndPhysics"];

const ECOLLISION_CHANNEL: &[&str] = &[
    "WorldStatic",
    "WorldDynamic",
    "Pawn",
    "Visibility",
    "Camera",
    "PhysicsBody",
];

const EATTACHMENT_RULE: &[&str] = &["KeepRelative", "KeepWorld", "SnapToTarget"];

const EDETACHMENT_RULE: &[&str] = &["KeepRelative", "KeepWorld"];

const ERELATIVE_TRANSFORM_SPACE: &[&str] = &[
    "RTS_World",
    "RTS_Actor",
    "RTS_Component",
    "RTS_ParentBoneSpace",
];

const EDRAW_DEBUG_TRACE: &[&str] = &["None", "ForOneFrame", "ForDuration", "Persistent"];

const ETICKING_GROUP: &[&str] = &[
    "PrePhysics",
    "DuringPhysics",
    "PostPhysics",
    "PostUpdateWork",
];

const ECOLLISION_RESPONSE: &[&str] = &["Ignore", "Overlap", "Block"];

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
