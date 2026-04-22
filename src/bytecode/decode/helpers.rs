use super::super::format::is_ue4_library_class;
use super::super::opcodes::*;
use super::super::readers::*;
use super::super::resolve::*;
use super::expr::decode_expr;
use super::types::DecodeCtx;
use crate::types::VER_UE5_LARGE_WORLD_COORDINATES;

/// Opcodes that read a field path and format with a prefix string.
const FIELD_PATH_OPS: &[(u8, &str)] = &[
    (EX_LOCAL_VARIABLE, ""),
    (EX_INSTANCE_VARIABLE, "self."),
    (EX_DEFAULT_VARIABLE, "default."),
    (EX_LOCAL_OUT_VARIABLE, "out "),
    (EX_CLASS_SPARSE_DATA_VARIABLE, "sparse."),
];

/// Opcodes that read obj_ref + sub-expression, format as `prefix<Class>(expr)`.
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

/// End-marker opcodes that terminate a constant list.
const END_MARKERS: &[u8] = &[
    EX_END_STRUCT_CONST,
    EX_END_ARRAY_CONST,
    EX_END_SET_CONST,
    EX_END_MAP_CONST,
];

/// 3-component vector/rotator constants.
const XYZ_CONST_OPS: &[(u8, &str)] = &[(EX_ROTATION_CONST, "Rot"), (EX_VECTOR_CONST, "Vec")];

/// Decode EX_CONTEXT / EX_CLASS_CONTEXT / EX_CONTEXT_FAIL_SILENT as `obj.member`.
pub(super) fn decode_context(
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

/// Decode expressions until `terminator` opcode, returning them as a list.
pub(super) fn decode_expr_list(
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
pub(super) fn decode_constant(
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
pub(super) fn decode_delegate(
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
            let args = super::funcs::decode_func_args(ctx, pos, mem_adj);
            Some(format!("{}.Broadcast({})", func, args.join(", ")))
        }
        _ => None,
    }
}

/// Decode container set/mutation opcodes (set array, set, map and their terminators).
pub(super) fn decode_container_mutation(
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

/// Table-driven dispatch for uniform opcode families: field-path prefixes,
/// casts, literal constants, xyz vectors. `None` for unrecognized opcodes.
pub(super) fn decode_table_op(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<Option<String>> {
    if let Some(prefix) = FIELD_PATH_OPS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, pfx)| *pfx)
    {
        let prop = ctx.read_field_path(pos, mem_adj);
        return Some(Some(format!("{}{}", prefix, prop)));
    }

    if let Some(cast_kind) = CAST_OPS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, pfx)| *pfx)
    {
        let class = ctx.read_obj_ref(pos, mem_adj);
        let expr = decode_expr(ctx, pos, mem_adj).unwrap_or_default();
        return Some(Some(format!("{}<{}>({})", cast_kind, class, expr)));
    }

    if let Some(val) = LITERAL_CONSTANTS
        .iter()
        .find(|(op, _)| *op == opcode)
        .map(|(_, v)| *v)
    {
        return Some(Some(val.to_string()));
    }

    if END_MARKERS.contains(&opcode) {
        return Some(None);
    }

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
