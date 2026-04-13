//! Expression decoder: raw Kismet bytecode into [`BcStatement`]s.
//!
//! `mem_adj` tracks the cumulative on-disk vs in-memory FName size difference
//! so jump targets resolve correctly.

use super::format::{format_call_or_operator, is_ue4_library_class};
use super::readers::*;
use super::resolve::*;
use crate::binary::NameTable;
use crate::types::{ImportEntry, VER_UE5_LARGE_WORLD_COORDINATES};

use super::opcodes::*;

#[derive(Clone)]
pub struct BcStatement {
    /// In-memory bytecode offset (adjusted for FName size differences).
    /// Used by structure/flow passes to resolve jump targets.
    pub mem_offset: usize,
    /// Additional offsets absorbed when temp inlining merges statements.
    /// Jump targets pointing to these offsets resolve to this statement.
    pub offset_aliases: Vec<usize>,
    pub text: String,
}

impl BcStatement {
    pub fn new(mem_offset: usize, text: impl Into<String>) -> Self {
        Self {
            mem_offset,
            text: text.into(),
            offset_aliases: Vec::new(),
        }
    }
}

/// Immutable context shared across recursive decode calls.
///
/// Separated from the mutable `pos`/`mem_adj` state to avoid borrow conflicts.
pub struct DecodeCtx<'a> {
    bytecode: &'a [u8],
    name_table: &'a NameTable,
    imports: &'a [ImportEntry],
    export_names: &'a [String],
    ue5: i32,
}

impl<'a> DecodeCtx<'a> {
    fn read_obj_ref(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_obj_ref(self.bytecode, pos, self.imports, self.export_names, mem_adj)
    }

    fn read_field_path(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_field_path(self.bytecode, pos, self.name_table, mem_adj)
    }

    fn read_fname_with_adj(&self, pos: &mut usize, mem_adj: &mut i32) -> String {
        read_bc_fname_with_adj(self.bytecode, pos, self.name_table, mem_adj)
    }
}

/// Opcodes that read a field path and format with a prefix string.
/// Dispatched before the main match in `decode_expr`.
const FIELD_PATH_OPS: &[(u8, &str)] = &[
    (EX_LOCAL_VARIABLE, ""),
    (EX_INSTANCE_VARIABLE, "self."),
    (EX_DEFAULT_VARIABLE, "default."),
    (EX_LOCAL_OUT_VARIABLE, "out "),
    (EX_CLASS_SPARSE_DATA_VARIABLE, "sparse."),
];

/// Opcodes that read an obj_ref + decode a sub-expression, formatting as `prefix<Class>(expr)`.
const CAST_OPS: &[(u8, &str)] = &[
    (EX_META_CAST, "cast"),
    (EX_DYNAMIC_CAST, "cast"),
    (EX_OBJ_TO_IFACE_CAST, "icast"),
    (EX_CROSS_IFACE_CAST, "icast"),
    (EX_IFACE_TO_OBJ_CAST, "obj_cast"),
];

/// Constant opcodes that return a fixed string with no byte reads.
const LITERAL_CONSTANTS: &[(u8, &str)] = &[
    (EX_INT_ZERO, "0"),
    (EX_INT_ONE, "1"),
    (EX_TRUE, "true"),
    (EX_FALSE, "false"),
    (EX_NO_OBJECT, "null"),
    (EX_NO_INTERFACE, "null_iface"),
];

/// End-marker opcodes that terminate a constant list (return None).
const END_MARKERS: &[u8] = &[
    EX_END_STRUCT_CONST,
    EX_END_ARRAY_CONST,
    EX_END_SET_CONST,
    EX_END_MAP_CONST,
];

/// Constant opcodes that read 3 components via `read_bc_xyz` and format with a prefix.
const XYZ_CONST_OPS: &[(u8, &str)] = &[(EX_ROTATION_CONST, "Rot"), (EX_VECTOR_CONST, "Vec")];

/// Decode EX_CONTEXT / EX_CLASS_CONTEXT / EX_CONTEXT_FAIL_SILENT.
/// Reads object + rvalue info + member expression, formats as `obj.member`.
fn decode_context(
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
    sep: &str,
    elide_library: bool,
) -> Option<String> {
    macro_rules! decode_next {
        () => {
            decode_expr(ctx, pos, mem_adj).unwrap_or_default()
        };
    }
    let obj = decode_next!();
    read_bc_context_rvalue(ctx.bytecode, pos, ctx.name_table, mem_adj);
    let expr = decode_next!();
    let expr = expr.strip_prefix("self.").unwrap_or(&expr);
    if elide_library && is_ue4_library_class(&obj) {
        Some(expr.to_string())
    } else {
        Some(format!("{}{}{}", obj, sep, expr))
    }
}

/// Decode expressions until a terminator opcode is reached, returning them as a list.
fn decode_expr_list(
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
    terminator: u8,
) -> Vec<String> {
    let mut items = Vec::new();
    loop {
        if *pos >= ctx.bytecode.len() {
            break;
        }
        if ctx.bytecode[*pos] == terminator {
            *pos += 1;
            break;
        }
        match decode_expr(ctx, pos, mem_adj) {
            Some(item) => items.push(item),
            None => break,
        }
    }
    items
}

/// Decode constant/literal opcodes (int, float, string, name, vector, struct, text, containers).
fn decode_constant(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<String> {
    let bytecode = ctx.bytecode;
    macro_rules! decode_next {
        () => {
            decode_expr(ctx, pos, mem_adj).unwrap_or_default()
        };
    }

    match opcode {
        EX_INT_CONST => Some(format!("{}", read_bc_i32(bytecode, pos))),
        EX_FLOAT_CONST => Some(format!("{:.4}", read_bc_f32(bytecode, pos))),
        EX_STRING_CONST => Some(format!("\"{}\"", read_bc_string(bytecode, pos))),
        EX_OBJECT_CONST => {
            let obj = ctx.read_obj_ref(pos, mem_adj);
            Some(obj)
        }
        EX_NAME_CONST => {
            let name = ctx.read_fname_with_adj(pos, mem_adj);
            Some(format!("'{}'", name))
        }
        EX_BYTE_CONST => Some(format!("{}", read_bc_u8(bytecode, pos))),
        EX_TEXT_CONST => {
            let text_type = read_bc_u8(bytecode, pos);
            match text_type {
                0 => Some("\"\"".into()),
                1 => {
                    let _ns = decode_next!();
                    let _key = decode_next!();
                    let val = decode_next!();
                    Some(format!("LOCTEXT({})", val))
                }
                2 | 3 => {
                    let val = decode_next!();
                    Some(val)
                }
                4 => {
                    let _table = ctx.read_obj_ref(pos, mem_adj);
                    let key = decode_next!();
                    Some(format!("STRTABLE({})", key))
                }
                0xFF => Some("\"\"".into()),
                _ => Some(format!("text(type={})", text_type)),
            }
        }
        EX_TRANSFORM_CONST => {
            let lwc = ctx.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES;
            let (rx, ry, rz, rw) = read_bc_xyzw(bytecode, pos, lwc);
            let (tx, ty, tz) = read_bc_xyz(bytecode, pos, lwc);
            let (sx, sy, sz) = read_bc_xyz(bytecode, pos, lwc);
            Some(format!("Transform(Rot({:.1},{:.1},{:.1},{:.1}),Pos({:.1},{:.1},{:.1}),Scale({:.1},{:.1},{:.1}))",
                rx, ry, rz, rw, tx, ty, tz, sx, sy, sz))
        }
        EX_INT_CONST_BYTE => Some(format!("{}", read_bc_u8(bytecode, pos))),
        EX_STRUCT_CONST => {
            let struct_ref = ctx.read_obj_ref(pos, mem_adj);
            let _serial_size = read_bc_i32(bytecode, pos);
            let fields = decode_expr_list(ctx, pos, mem_adj, EX_END_STRUCT_CONST);
            Some(format!("{}({})", struct_ref, fields.join(", ")))
        }
        EX_UNICODE_STRING_CONST => {
            let mut s = Vec::new();
            while *pos + 1 < bytecode.len() {
                let low = bytecode[*pos];
                let high = bytecode[*pos + 1];
                *pos += 2;
                if low == 0 && high == 0 {
                    break;
                }
                s.push(u16::from_le_bytes([low, high]));
            }
            Some(format!("\"{}\"", String::from_utf16_lossy(&s)))
        }
        EX_INT64_CONST => Some(format!("{}L", read_bc_i64(bytecode, pos))),
        EX_UINT64_CONST => Some(format!("{}UL", read_bc_u64(bytecode, pos))),
        EX_DOUBLE_CONST => Some(format!("{:.4}", read_bc_f64(bytecode, pos))),
        EX_PROPERTY_CONST => {
            let path = ctx.read_field_path(pos, mem_adj);
            Some(format!("prop({})", path))
        }
        EX_SOFT_OBJECT_CONST => {
            let path = decode_next!();
            Some(format!("soft({})", path))
        }
        EX_VECTOR3F_CONST if ctx.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES => {
            let x = read_bc_f32(bytecode, pos);
            let y = read_bc_f32(bytecode, pos);
            let z = read_bc_f32(bytecode, pos);
            Some(format!("Vec3f({:.1},{:.1},{:.1})", x, y, z))
        }
        EX_ARRAY_CONST => {
            let _inner = ctx.read_obj_ref(pos, mem_adj);
            let _count = read_bc_i32(bytecode, pos);
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_ARRAY_CONST);
            Some(format!("[{}]", items.join(", ")))
        }
        EX_SET_CONST => {
            let _inner = ctx.read_obj_ref(pos, mem_adj);
            let _count = read_bc_i32(bytecode, pos);
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_SET_CONST);
            Some(format!("set{{{}}}", items.join(", ")))
        }
        EX_MAP_CONST => {
            let _key_prop = ctx.read_obj_ref(pos, mem_adj);
            let _val_prop = ctx.read_obj_ref(pos, mem_adj);
            let _count = read_bc_i32(bytecode, pos);
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_MAP_CONST);
            Some(format!("map{{{}}}", items.join(", ")))
        }
        _ => None,
    }
}

/// Decode delegate opcodes (instance, bind, add/remove/clear/call multicast).
fn decode_delegate(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<String> {
    macro_rules! decode_next {
        () => {
            decode_expr(ctx, pos, mem_adj).unwrap_or_default()
        };
    }
    match opcode {
        EX_INSTANCE_DELEGATE => {
            let name = ctx.read_fname_with_adj(pos, mem_adj);
            Some(format!("delegate({})", name))
        }
        EX_BIND_DELEGATE => {
            let name = ctx.read_fname_with_adj(pos, mem_adj);
            let delegate = decode_next!();
            let obj = decode_next!();
            Some(format!("bind({}, {}, {})", name, delegate, obj))
        }
        EX_ADD_MULTICAST_DELEGATE => {
            let delegate = decode_next!();
            let func = decode_next!();
            Some(format!("{} += {}", delegate, func))
        }
        EX_CLEAR_MULTICAST_DELEGATE => {
            let delegate = decode_next!();
            Some(format!("{}.Clear()", delegate))
        }
        EX_REMOVE_MULTICAST_DELEGATE => {
            let delegate = decode_next!();
            let func = decode_next!();
            Some(format!("{} -= {}", delegate, func))
        }
        EX_CALL_MULTICAST_DELEGATE => {
            let func = ctx.read_obj_ref(pos, mem_adj);
            let args = decode_func_args(ctx, pos, mem_adj);
            Some(format!("{}.Broadcast({})", func, args.join(", ")))
        }
        _ => None,
    }
}

/// Decode container set/mutation opcodes (set array, set, map and their terminators).
fn decode_container_mutation(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<String> {
    macro_rules! decode_next {
        () => {
            decode_expr(ctx, pos, mem_adj).unwrap_or_default()
        };
    }
    match opcode {
        EX_SET_ARRAY => {
            let target = decode_next!();
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_ARRAY);
            Some(format!("{} = [{}]", target, items.join(", ")))
        }
        EX_END_ARRAY => None,
        EX_SET_SET => {
            let target = decode_next!();
            let _count = read_bc_i32(ctx.bytecode, pos);
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_SET);
            Some(format!("{} = set{{{}}}", target, items.join(", ")))
        }
        EX_END_SET => None,
        EX_SET_MAP => {
            let target = decode_next!();
            let _count = read_bc_i32(ctx.bytecode, pos);
            let items = decode_expr_list(ctx, pos, mem_adj, EX_END_MAP);
            Some(format!("{} = map{{{}}}", target, items.join(", ")))
        }
        EX_END_MAP => None,
        _ => None,
    }
}

/// Table-driven opcode dispatch for uniform opcode families (field-path prefixes,
/// casts, literal constants, xyz vectors). Returns `None` for unrecognized opcodes.
fn decode_table_op(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<Option<String>> {
    // Field-path prefix: read field path, prepend prefix
    if let Some(prefix) = FIELD_PATH_OPS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, pfx)| *pfx)
    {
        let prop = ctx.read_field_path(pos, mem_adj);
        return Some(Some(format!("{}{}", prefix, prop)));
    }

    // Cast: read obj_ref + sub-expression, format as prefix<Class>(expr)
    if let Some(cast_kind) = CAST_OPS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, pfx)| *pfx)
    {
        let class = ctx.read_obj_ref(pos, mem_adj);
        let expr = decode_expr(ctx, pos, mem_adj).unwrap_or_default();
        return Some(Some(format!("{}<{}>({})", cast_kind, class, expr)));
    }

    // Literal constants: fixed string, no byte reads
    if let Some(val) = LITERAL_CONSTANTS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, v)| *v)
    {
        return Some(Some(val.to_string()));
    }

    // End markers: terminate a constant list
    if END_MARKERS.contains(&opcode) {
        return Some(None);
    }

    // 3-component vector/rotator constants
    if let Some(prefix) = XYZ_CONST_OPS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, pfx)| *pfx)
    {
        let (x, y, z) = read_bc_xyz(
            ctx.bytecode,
            pos,
            ctx.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES,
        );
        return Some(Some(format!("{}({:.1},{:.1},{:.1})", prefix, x, y, z)));
    }

    None
}

/// Decode a single Kismet expression. Tries `decode_table_op` first (uniform
/// opcode families), then falls through to `decode_match_op` (unique opcodes).
pub fn decode_expr(ctx: &DecodeCtx, pos: &mut usize, mem_adj: &mut i32) -> Option<String> {
    if *pos >= ctx.bytecode.len() {
        return None;
    }
    let opcode = read_bc_u8(ctx.bytecode, pos);

    // Table-driven opcodes: field-path prefixes, casts, literal constants, xyz vectors
    if let Some(result) = decode_table_op(opcode, ctx, pos, mem_adj) {
        return result;
    }

    // Remaining opcodes: explicit match arms
    decode_match_op(opcode, ctx, pos, mem_adj)
}

/// Explicit match dispatch for opcodes that don't fit a uniform table pattern:
/// control flow, assignments, function calls, context, delegates, containers, switches.
fn decode_match_op(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<String> {
    let bytecode = ctx.bytecode;
    // Shorthand for recursive decode calls. A closure can't work because pos and
    // mem_adj are &mut (multiple borrows), but ctx is shared immutably.
    macro_rules! decode_next {
        () => {
            decode_expr(ctx, pos, mem_adj).unwrap_or_default()
        };
        (opt) => {
            decode_expr(ctx, pos, mem_adj)
        };
    }

    match opcode {
        // Control flow
        EX_RETURN => {
            let expr = decode_next!();
            Some(format!("return {}", expr))
        }
        EX_JUMP => {
            let offset = read_bc_u32(bytecode, pos);
            Some(format!("jump 0x{:x}", offset))
        }
        EX_JUMP_IF_NOT => {
            let offset = read_bc_u32(bytecode, pos);
            let cond = decode_next!();
            Some(format!("if !({}) jump 0x{:x}", cond, offset))
        }
        EX_ASSERT => {
            let _line = read_bc_u16(bytecode, pos);
            let _debug_only = read_bc_u8(bytecode, pos);
            let expr = decode_next!();
            Some(format!("assert({})", expr))
        }
        EX_NOTHING => Some("nop".into()),
        EX_NOTHING_INT32 => {
            let _ = read_bc_i32(bytecode, pos);
            Some("nop".into())
        }

        // Assignment
        EX_LET | EX_LET_MULTICAST_DELEGATE | EX_LET_DELEGATE => {
            let _prop = ctx.read_field_path(pos, mem_adj);
            let var = decode_next!();
            let val = decode_next!();
            Some(format!("{} = {}", var, val))
        }
        EX_LET_BOOL | EX_LET_OBJ => {
            let var = decode_next!();
            let val = decode_next!();
            Some(format!("{} = {}", var, val))
        }
        EX_LET_WEAK_OBJ_PTR => {
            let var = decode_next!();
            let val = decode_next!();
            Some(format!("{} = weak({})", var, val))
        }
        EX_LET_VALUE_ON_PERSISTENT_FRAME => {
            // Persistent frame vars live on the ubergraph's persistent stack frame, surviving
            // across latent action resumes (e.g. Delay). The [persistent] marker prevents
            // inlining since their value must persist across event boundaries.
            let prop = ctx.read_field_path(pos, mem_adj);
            let val = decode_next!();
            Some(format!("{} = {} [persistent]", prop, val))
        }

        // Context / member access
        EX_CLASS_CONTEXT => decode_context(ctx, pos, mem_adj, ".", false),
        EX_CONTEXT => decode_context(ctx, pos, mem_adj, ".", true),
        EX_CONTEXT_FAIL_SILENT => decode_context(ctx, pos, mem_adj, "?.", true),
        EX_STRUCT_MEMBER_CONTEXT => {
            let prop = ctx.read_field_path(pos, mem_adj);
            let struct_expr = decode_next!();
            Some(format!("{}.{}", struct_expr, prop))
        }

        // Function calls
        EX_VIRTUAL_FUNCTION | EX_LOCAL_VIRTUAL_FUNCTION => {
            let name = ctx.read_fname_with_adj(pos, mem_adj);
            let args = decode_func_args(ctx, pos, mem_adj);
            Some(format_call_or_operator(&name, args))
        }
        EX_FINAL_FUNCTION | EX_LOCAL_FINAL_FUNCTION => {
            let func = ctx.read_obj_ref(pos, mem_adj);
            let args = decode_func_args(ctx, pos, mem_adj);
            Some(format_call_or_operator(&func, args))
        }
        EX_CALL_MATH => {
            let func = ctx.read_obj_ref(pos, mem_adj);
            let args = decode_func_args(ctx, pos, mem_adj);
            Some(format_call_or_operator(&func, args))
        }

        // Constants (literal/end-marker/xyz handled by decode_table_op)
        EX_INT_CONST
        | EX_FLOAT_CONST
        | EX_STRING_CONST
        | EX_OBJECT_CONST
        | EX_NAME_CONST
        | EX_BYTE_CONST
        | EX_TEXT_CONST
        | EX_TRANSFORM_CONST
        | EX_INT_CONST_BYTE
        | EX_STRUCT_CONST
        | EX_UNICODE_STRING_CONST
        | EX_INT64_CONST
        | EX_UINT64_CONST
        | EX_DOUBLE_CONST
        | EX_PROPERTY_CONST
        | EX_SOFT_OBJECT_CONST
        | EX_ARRAY_CONST
        | EX_SET_CONST
        | EX_MAP_CONST => decode_constant(opcode, ctx, pos, mem_adj),
        EX_VECTOR3F_CONST if ctx.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES => {
            decode_constant(opcode, ctx, pos, mem_adj)
        }
        EX_VECTOR3F_CONST => {
            // UE4: unused opcode, treat as StructMemberContext fallback
            let prop = ctx.read_field_path(pos, mem_adj);
            let struct_expr = decode_next!();
            Some(format!("{}.{}", struct_expr, prop))
        }
        EX_BITFIELD_CONST => {
            let _path = ctx.read_field_path(pos, mem_adj);
            let value = read_bc_u8(bytecode, pos) != 0;
            Some(format!("{}", value))
        }

        // Containers
        EX_SET_ARRAY | EX_END_ARRAY | EX_SET_SET | EX_END_SET | EX_SET_MAP | EX_END_MAP => {
            decode_container_mutation(opcode, ctx, pos, mem_adj)
        }

        // Delegates
        EX_INSTANCE_DELEGATE
        | EX_BIND_DELEGATE
        | EX_ADD_MULTICAST_DELEGATE
        | EX_CLEAR_MULTICAST_DELEGATE
        | EX_REMOVE_MULTICAST_DELEGATE
        | EX_CALL_MULTICAST_DELEGATE => decode_delegate(opcode, ctx, pos, mem_adj),

        // Casts
        EX_PRIMITIVE_CAST => {
            let cast_type = read_bc_u8(bytecode, pos);
            let expr = decode_next!();
            let name = primitive_cast_name(cast_type, ctx.ue5);
            if name.is_empty() {
                Some(expr) // transparent cast (LWC float/double, obj-to-iface)
            } else {
                Some(format!("{}({})", name, expr))
            }
        }

        // Interface
        EX_INTERFACE_CONTEXT => {
            let expr = decode_next!();
            // Collapse nested iface: iface(iface(X)) -> iface(X)
            if let Some(inner) = expr
                .strip_prefix("iface(")
                .and_then(|s| s.strip_suffix(')'))
            {
                Some(format!("iface({})", inner))
            } else if expr == "null_iface" || expr.is_empty() {
                Some("null_iface".into())
            } else {
                Some(format!("iface({})", expr))
            }
        }

        // Flow stack (push/pop used for structured if/loop detection)
        EX_PUSH_EXECUTION_FLOW => {
            let offset = read_bc_u32(bytecode, pos);
            Some(format!("push_flow 0x{:x}", offset))
        }
        EX_POP_EXECUTION_FLOW => Some("pop_flow".into()),
        EX_COMPUTED_JUMP => {
            let expr = decode_next!();
            Some(format!("jump_computed({})", expr))
        }
        EX_POP_FLOW_IF_NOT => {
            let cond = decode_next!();
            Some(format!("pop_flow_if_not({})", cond))
        }

        // Switch
        EX_SWITCH_VALUE => {
            let num_cases = read_bc_u16(bytecode, pos);
            let _end_offset = read_bc_u32(bytecode, pos);
            let index = decode_next!();
            let mut cases = Vec::new();
            for _ in 0..num_cases {
                let case_val = decode_next!();
                let _next_offset = read_bc_u32(bytecode, pos);
                let result = decode_next!();
                cases.push(format!("{}: {}", case_val, result));
            }
            let default = decode_next!();
            if default.starts_with("$Select_Default") {
                Some(format!("switch({}) {{ {} }}", index, cases.join(", ")))
            } else {
                Some(format!(
                    "switch({}) {{ {}, default: {} }}",
                    index,
                    cases.join(", "),
                    default
                ))
            }
        }

        // Misc
        EX_SELF => Some("self".into()),
        EX_SKIP => {
            let _skip = read_bc_u32(bytecode, pos);
            decode_next!(opt)
        }
        EX_END_PARM_VALUE => Some("end_param".into()),
        EX_END_FUNCTION_PARMS | EX_END_OF_SCRIPT => None,
        EX_BREAKPOINT => Some("breakpoint".into()),
        EX_WIRE_TRACEPOINT => Some("wire_trace".into()),
        EX_TRACEPOINT => Some("tracepoint".into()),
        EX_SKIP_OFFSET_CONST => {
            let offset = read_bc_u32(bytecode, pos);
            Some(format!("skip_offset(0x{:x})", offset))
        }
        EX_INSTRUMENTATION_EVENT => {
            let event_type = read_bc_u8(bytecode, pos);
            if event_type == 4 {
                let _name = ctx.read_fname_with_adj(pos, mem_adj);
            }
            Some("instrumentation".into())
        }
        EX_ARRAY_GET_BY_REF => {
            let array = decode_next!();
            let index = decode_next!();
            Some(format!("{}[{}]", array, index))
        }
        EX_FIELD_PATH_CONST => {
            let path = ctx.read_field_path(pos, mem_adj);
            Some(format!("fieldpath({})", path))
        }
        EX_AUTO_RTFM_TRANSACT => {
            let expr = decode_next!();
            Some(format!("rtfm_transact({})", expr))
        }
        EX_AUTO_RTFM_STOP_TRANSACT => {
            let _mode = read_bc_u8(bytecode, pos);
            Some("rtfm_stop".into())
        }
        EX_AUTO_RTFM_ABORT_IF_NOT => {
            let expr = decode_next!();
            Some(format!("rtfm_abort_if_not({})", expr))
        }
        _ => Some(format!("???(0x{:02x})", opcode)),
    }
}

fn decode_func_args(ctx: &DecodeCtx, pos: &mut usize, mem_adj: &mut i32) -> Vec<String> {
    let mut args = Vec::new();
    loop {
        if *pos >= ctx.bytecode.len() {
            break;
        }
        if ctx.bytecode[*pos] == EX_END_FUNCTION_PARMS {
            *pos += 1;
            break;
        }
        if let Some(expr) = decode_expr(ctx, pos, mem_adj) {
            args.push(expr);
        } else {
            break;
        }
    }
    args
}

fn primitive_cast_name(cast_type: u8, ue5: i32) -> String {
    if ue5 >= VER_UE5_LARGE_WORLD_COORDINATES {
        // UE5 renumbered cast types and added LWC float↔double conversions.
        match cast_type {
            0x00 => String::new(), // CST_ObjectToInterface, transparent
            0x01 => "bool".into(), // CST_ObjectToBool
            0x02 => "bool".into(), // CST_InterfaceToBool
            0x03 => String::new(), // CST_DoubleToFloat, implicit narrowing
            0x04 => String::new(), // CST_FloatToDouble, implicit widening
            _ => format!("cast_{}", cast_type),
        }
    } else {
        match cast_type {
            0x41 => "iface_to_obj".into(), // CST_InterfaceToObject
            0x46 => "obj_to_iface".into(), // CST_ObjectToInterface
            0x47 => "bool".into(),         // CST_ObjectToBool
            0x49 => "bool".into(),         // CST_InterfaceToBool
            _ => format!("cast_{}", cast_type),
        }
    }
}

/// Decode a raw bytecode slice into statements, skipping instrumentation opcodes.
///
/// Returns `(statements, final_mem_adj)` for optional drift validation via `--debug`.
pub fn decode_bytecode(
    bytecode: &[u8],
    name_table: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    ue5: i32,
) -> (Vec<BcStatement>, i32) {
    let ctx = DecodeCtx {
        bytecode,
        name_table,
        imports,
        export_names,
        ue5,
    };
    let mut pos = 0;
    let mut mem_adj: i32 = 0;
    let mut stmts = Vec::new();
    while pos < bytecode.len() {
        let mem_start = (pos as i32 + mem_adj) as usize;
        let start = pos;
        match decode_expr(&ctx, &mut pos, &mut mem_adj) {
            Some(s) => match s.as_str() {
                "nop" | "wire_trace" | "tracepoint" | "instrumentation" => continue,
                _ => {
                    stmts.push(BcStatement::new(mem_start, s));
                }
            },
            None => break,
        }
        if pos == start {
            break;
        }
    }
    (stmts, mem_adj)
}

// Inline tests: these test private functions (try_rewrite_array_call, decode_expr, etc.)
// that aren't accessible from tests/. Integration tests cover the public API end-to-end.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::NameTable;
    use crate::bytecode::format::try_rewrite_array_call;

    // Helper: build a NameTable with given names (index 0 = first name)
    fn name_table(names: &[&str]) -> NameTable {
        NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
    }

    // Helper: append little-endian i32
    fn push_i32(bytecode: &mut Vec<u8>, v: i32) {
        bytecode.extend_from_slice(&v.to_le_bytes());
    }
    fn push_f32(bytecode: &mut Vec<u8>, v: f32) {
        bytecode.extend_from_slice(&v.to_le_bytes());
    }
    fn push_f64(bytecode: &mut Vec<u8>, v: f64) {
        bytecode.extend_from_slice(&v.to_le_bytes());
    }

    // Helper: append a single-name FFieldPath (16 bytes)
    // FName = name_index(i32) + instance_number(i32), then owner(i32)
    fn push_field_path(bytecode: &mut Vec<u8>, name_idx: i32) {
        push_i32(bytecode, 1); // path_num = 1
        push_i32(bytecode, name_idx); // FName index
        push_i32(bytecode, 0); // FName instance number
        push_i32(bytecode, 0); // owner
    }

    // Helper: decode a single expression from bytes
    fn expr(bytecode: &[u8], ue5: i32) -> (Option<String>, i32) {
        let names = name_table(&["TestVar", "TestFunc", "None"]);
        let imports = vec![];
        let export_names = vec![];
        let ctx = DecodeCtx {
            bytecode,
            name_table: &names,
            imports: &imports,
            export_names: &export_names,
            ue5,
        };
        let mut pos = 0;
        let mut mem_adj = 0;
        let result = decode_expr(&ctx, &mut pos, &mut mem_adj);
        (result, mem_adj)
    }

    // Helper: decode with custom name table
    fn expr_with_names(bytecode: &[u8], names: &NameTable, ue5: i32) -> Option<String> {
        let imports = vec![];
        let export_names = vec![];
        let ctx = DecodeCtx {
            bytecode,
            name_table: names,
            imports: &imports,
            export_names: &export_names,
            ue5,
        };
        let mut pos = 0;
        let mut mem_adj = 0;
        decode_expr(&ctx, &mut pos, &mut mem_adj)
    }

    // LWC opcodes: float vs double branching

    #[test]
    fn rotation_const_ue4_reads_floats() {
        let mut bytecode = vec![0x22];
        push_f32(&mut bytecode, 1.0);
        push_f32(&mut bytecode, 2.0);
        push_f32(&mut bytecode, 3.0);
        let (result, _) = expr(&bytecode, 0);
        assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
    }

    #[test]
    fn rotation_const_ue5_lwc_reads_doubles() {
        let mut bytecode = vec![0x22];
        push_f64(&mut bytecode, 1.0);
        push_f64(&mut bytecode, 2.0);
        push_f64(&mut bytecode, 3.0);
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
    }

    #[test]
    fn vector_const_ue4_reads_floats() {
        let mut bytecode = vec![0x23];
        push_f32(&mut bytecode, 10.0);
        push_f32(&mut bytecode, 20.0);
        push_f32(&mut bytecode, 30.0);
        let (result, _) = expr(&bytecode, 0);
        assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
    }

    #[test]
    fn vector_const_ue5_lwc_reads_doubles() {
        let mut bytecode = vec![0x23];
        push_f64(&mut bytecode, 10.0);
        push_f64(&mut bytecode, 20.0);
        push_f64(&mut bytecode, 30.0);
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
    }

    #[test]
    fn transform_const_ue4_reads_floats() {
        let mut bytecode = vec![0x2B];
        for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
            push_f32(&mut bytecode, v);
        }
        let (result, _) = expr(&bytecode, 0);
        assert!(result.unwrap().starts_with("Transform("));
    }

    #[test]
    fn transform_const_ue5_lwc_reads_doubles() {
        let mut bytecode = vec![0x2B];
        for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
            push_f64(&mut bytecode, v);
        }
        let (result, _) = expr(&bytecode, 1004);
        assert!(result.unwrap().starts_with("Transform("));
    }

    // 0x41: UE5 = Vector3fConst, UE4 = StructMemberContext fallback

    #[test]
    fn vector3f_const_ue5() {
        let mut bytecode = vec![0x41];
        push_f32(&mut bytecode, 1.0);
        push_f32(&mut bytecode, 2.0);
        push_f32(&mut bytecode, 3.0);
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "Vec3f(1.0,2.0,3.0)");
    }

    // 0x37: EX_DoubleConst

    #[test]
    fn double_const() {
        let mut bytecode = vec![0x37];
        push_f64(&mut bytecode, 1.2345);
        let (result, _) = expr(&bytecode, 0);
        assert_eq!(result.unwrap(), "1.2345");
    }

    // 0x0C: EX_NothingInt32

    #[test]
    fn nothing_int32_returns_nop() {
        let mut bytecode = vec![0x0C];
        push_i32(&mut bytecode, 42);
        let (result, _) = expr(&bytecode, 0);
        assert_eq!(result.unwrap(), "nop");
    }

    // 0x11: EX_BitFieldConst

    #[test]
    fn bitfield_const() {
        let mut bytecode = vec![0x11];
        push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
        bytecode.push(0x01); // uint8 value = true
        let names = name_table(&["TestVar"]);
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "true");
    }

    // 0x33: EX_PropertyConst

    #[test]
    fn property_const() {
        let mut bytecode = vec![0x33];
        push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
        let names = name_table(&["TestVar"]);
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "prop(TestVar)");
    }

    // 0x6C: EX_ClassSparseDataVariable

    #[test]
    fn class_sparse_data_variable() {
        let mut bytecode = vec![0x6C];
        push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
        let names = name_table(&["TestVar"]);
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "sparse.TestVar");
    }

    // 0x70-0x72: RTFM opcodes

    #[test]
    fn rtfm_transact() {
        let mut bytecode = vec![0x70];
        bytecode.push(0x27); // EX_True as inner expression
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "rtfm_transact(true)");
    }

    #[test]
    fn rtfm_stop_transact() {
        let bytecode = vec![0x71, 0x01]; // opcode + mode byte
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "rtfm_stop");
    }

    #[test]
    fn rtfm_abort_if_not() {
        let mut bytecode = vec![0x72];
        bytecode.push(0x28); // EX_False as condition
        let (result, _) = expr(&bytecode, 1004);
        assert_eq!(result.unwrap(), "rtfm_abort_if_not(false)");
    }

    // 0x43/0x44: EX_LetMulticastDelegate/EX_LetDelegate (with FFieldPath)

    #[test]
    fn let_multicast_delegate() {
        let names = name_table(&["MyDelegate", "Target", "Value"]);
        let mut bytecode = vec![0x43];
        push_field_path(&mut bytecode, 0); // FFieldPath ->"MyDelegate"
                                           // var: EX_LocalVariable with FFieldPath -> "Target"
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 1);
        // val: EX_LocalVariable with FFieldPath -> "Value"
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 2);
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "Target = Value");
    }

    #[test]
    fn let_delegate() {
        let names = name_table(&["MyDelegate", "Target", "Value"]);
        let mut bytecode = vec![0x44];
        push_field_path(&mut bytecode, 0); // FFieldPath ->"MyDelegate"
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 1); // var
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 2); // val
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "Target = Value");
    }

    // 0x39/0x3B: EX_SetSet/EX_SetMap (with element count)

    #[test]
    fn set_set_reads_element_count() {
        let names = name_table(&["MySet"]);
        let mut bytecode = vec![0x39];
        // target: EX_LocalVariable
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 0);
        // element count (int32)
        push_i32(&mut bytecode, 2);
        // two elements: EX_IntConst(1), EX_IntConst(2), then EX_EndSet
        bytecode.push(0x1D);
        push_i32(&mut bytecode, 1);
        bytecode.push(0x1D);
        push_i32(&mut bytecode, 2);
        bytecode.push(0x3A); // EX_EndSet
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "MySet = set{1, 2}");
    }

    #[test]
    fn set_map_reads_element_count() {
        let names = name_table(&["MyMap"]);
        let mut bytecode = vec![0x3B];
        bytecode.push(0x00);
        push_field_path(&mut bytecode, 0); // target
        push_i32(&mut bytecode, 1); // element count
        bytecode.push(0x1D);
        push_i32(&mut bytecode, 10); // key
        bytecode.push(0x1D);
        push_i32(&mut bytecode, 20); // value
        bytecode.push(0x3C); // EX_EndMap
        let result = expr_with_names(&bytecode, &names, 0);
        assert_eq!(result.unwrap(), "MyMap = map{10, 20}");
    }

    // LWC pre-1004: still uses floats

    #[test]
    fn vector_const_ue5_pre_lwc_reads_floats() {
        let mut bytecode = vec![0x23];
        push_f32(&mut bytecode, 1.0);
        push_f32(&mut bytecode, 2.0);
        push_f32(&mut bytecode, 3.0);
        let (result, _) = expr(&bytecode, 1003); // pre-LWC UE5
        assert_eq!(result.unwrap(), "Vec(1.0,2.0,3.0)");
    }

    // decode_bytecode filters nop

    #[test]
    fn decode_bytecode_filters_nothing_int32() {
        let names = name_table(&["None"]);
        let imports = vec![];
        let export_names = vec![];
        let mut bytecode = vec![0x0C]; // EX_NothingInt32
        push_i32(&mut bytecode, 0);
        bytecode.push(0x53); // EX_EndOfScript
        let (stmts, _) = decode_bytecode(&bytecode, &names, &imports, &export_names, 0);
        assert!(stmts.is_empty(), "NothingInt32 should be filtered as nop");
    }

    // Array rewrite tests

    fn owned(val: &str) -> String {
        val.to_string()
    }

    #[test]
    fn array_get_rewrite() {
        let result =
            try_rewrite_array_call("Array_Get", &[owned("arr"), owned("0"), owned("$item")]);
        assert_eq!(result.unwrap(), "$item = arr[0]");
    }

    #[test]
    fn array_set_rewrite() {
        let result = try_rewrite_array_call(
            "Array_Set",
            &[owned("arr"), owned("0"), owned("val"), owned("false")],
        );
        assert_eq!(result.unwrap(), "arr[0] = val");
    }

    #[test]
    fn array_set_size_to_fit_keeps_method_call() {
        let result = try_rewrite_array_call(
            "Array_Set",
            &[owned("arr"), owned("0"), owned("val"), owned("true")],
        );
        assert_eq!(result.unwrap(), "arr.Set(0, val, true)");
    }

    #[test]
    fn array_length_rewrite() {
        let result = try_rewrite_array_call("Array_Length", &[owned("arr")]);
        assert_eq!(result.unwrap(), "arr.Length()");
    }

    #[test]
    fn array_add_rewrite() {
        let result = try_rewrite_array_call("Array_Add", &[owned("arr"), owned("item")]);
        assert_eq!(result.unwrap(), "arr.Add(item)");
    }

    #[test]
    fn array_contains_rewrite() {
        let result = try_rewrite_array_call("Array_Contains", &[owned("arr"), owned("item")]);
        assert_eq!(result.unwrap(), "arr.Contains(item)");
    }

    #[test]
    fn array_remove_rewrite() {
        let result = try_rewrite_array_call("Array_Remove", &[owned("arr"), owned("2")]);
        assert_eq!(result.unwrap(), "arr.Remove(2)");
    }

    #[test]
    fn array_remove_item_rewrite() {
        let result = try_rewrite_array_call("Array_RemoveItem", &[owned("arr"), owned("item")]);
        assert_eq!(result.unwrap(), "arr.RemoveItem(item)");
    }

    #[test]
    fn array_find_rewrite() {
        let result =
            try_rewrite_array_call("Array_Find", &[owned("arr"), owned("item"), owned("$idx")]);
        assert_eq!(result.unwrap(), "$idx = arr.Find(item)");
    }

    #[test]
    fn array_last_rewrite() {
        let result = try_rewrite_array_call("Array_Last", &[owned("arr"), owned("$item")]);
        assert_eq!(result.unwrap(), "$item = arr.Last()");
    }

    #[test]
    fn array_clear_rewrite() {
        let result = try_rewrite_array_call("Array_Clear", &[owned("arr")]);
        assert_eq!(result.unwrap(), "arr.Clear()");
    }

    #[test]
    fn array_insert_rewrite() {
        let result =
            try_rewrite_array_call("Array_Insert", &[owned("arr"), owned("item"), owned("2")]);
        assert_eq!(result.unwrap(), "arr.Insert(item, 2)");
    }

    #[test]
    fn non_array_passthrough() {
        let result = try_rewrite_array_call("SomeFunc", &[owned("a"), owned("b")]);
        assert!(result.is_none());
    }
}
