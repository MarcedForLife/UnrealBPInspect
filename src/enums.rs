/// Resolve known UE4 enum integer arguments to their symbolic names.
///
/// Only touches plain integer literal args — variables, expressions, bools are left alone.
/// Indices are relative to the displayed argument list (after WorldContextObject/LatentActionInfo
/// filtering in `format_call_or_operator`).
pub fn resolve_enum_args(func_name: &str, args: &mut [String]) {
    let short = func_name.rsplit('.').next().unwrap_or(func_name);
    let stripped = short
        .strip_prefix("K2_")
        .or_else(|| short.strip_prefix("Conv_"))
        .unwrap_or(short);

    let mappings: &[(usize, &[&str])] = match stripped {
        "SetCollisionEnabled" => &[(0, ECOLLISION_ENABLED)],
        "SetCollisionResponseToChannel" => &[(0, ECOLLISION_CHANNEL)],
        "AttachToComponent" | "AttachRootComponentTo" | "AttachToActor" => {
            &[(2, EATTACHMENT_RULE), (3, EATTACHMENT_RULE), (4, EATTACHMENT_RULE)]
        }
        "DetachFromComponent" | "DetachRootComponentFromParent" | "DetachFromActor" => {
            &[(0, EDETACHMENT_RULE), (1, EDETACHMENT_RULE), (2, EDETACHMENT_RULE)]
        }
        "GetSocketTransform" | "GetRelativeTransform" => &[(1, ERELATIVE_TRANSFORM_SPACE)],
        "SetTickGroup" => &[(0, ETICKING_GROUP)],
        _ => {
            // Trace functions: SphereTraceSingle, LineTraceSingleForObjects, etc.
            if is_trace_function(stripped) {
                // DrawDebugType is typically at display index 6
                static TRACE_MAP: [(usize, &[&str]); 1] = [(6, EDRAW_DEBUG_TRACE)];
                &TRACE_MAP
            } else {
                return;
            }
        }
    };

    for &(idx, values) in mappings {
        if idx < args.len() {
            if let Ok(v) = args[idx].trim().parse::<i32>() {
                if let Some(name) = values.get(v as usize) {
                    args[idx] = name.to_string();
                }
            }
        }
    }
}

fn is_trace_function(name: &str) -> bool {
    // Matches SphereTrace*, LineTrace*, BoxTrace*, CapsuleTrace*
    for prefix in &["SphereTrace", "LineTrace", "BoxTrace", "CapsuleTrace"] {
        if name.starts_with(prefix) { return true; }
    }
    false
}

const ECOLLISION_ENABLED: &[&str] = &[
    "NoCollision",      // 0
    "QueryOnly",        // 1
    "PhysicsOnly",      // 2
    "QueryAndPhysics",  // 3
];

const ECOLLISION_CHANNEL: &[&str] = &[
    "WorldStatic",      // 0
    "WorldDynamic",     // 1
    "Pawn",             // 2
    "Visibility",       // 3
    "Camera",           // 4
    "PhysicsBody",      // 5
];

const EATTACHMENT_RULE: &[&str] = &[
    "KeepRelative",     // 0
    "KeepWorld",        // 1
    "SnapToTarget",     // 2
];

const EDETACHMENT_RULE: &[&str] = &[
    "KeepRelative",     // 0
    "KeepWorld",        // 1
];

const ERELATIVE_TRANSFORM_SPACE: &[&str] = &[
    "RTS_World",                // 0
    "RTS_Actor",                // 1
    "RTS_Component",            // 2
    "RTS_ParentBoneSpace",      // 3
];

const EDRAW_DEBUG_TRACE: &[&str] = &[
    "None",             // 0
    "ForOneFrame",      // 1
    "ForDuration",      // 2
    "Persistent",       // 3
];

const ETICKING_GROUP: &[&str] = &[
    "PrePhysics",       // 0
    "DuringPhysics",    // 1
    "PostPhysics",      // 2
    "PostUpdateWork",   // 3
];
