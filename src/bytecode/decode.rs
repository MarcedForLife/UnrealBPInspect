use super::readers::*;
use super::resolve::*;
use crate::binary::NameTable;
use crate::types::ImportEntry;

use super::opcodes::*;

#[derive(Clone)]
pub struct BcStatement {
    pub mem_offset: usize,
    pub text: String,
}

/// Check if an expression contains an infix operator and needs parenthesization.
fn needs_parens(expr: &str) -> bool {
    const TOKENS: &[&str] = &[
        " && ", " || ", " + ", " - ", " * ", " / ", " % ", " < ", " <= ", " > ", " >= ", " == ",
        " != ", " >> ", " << ",
    ];
    TOKENS.iter().any(|tok| expr.contains(tok)) || expr.starts_with('!')
}

fn maybe_paren(expr: &str) -> String {
    if needs_parens(expr) {
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
        if let Some(a) = args.first() {
            return Some(format!("!{}", maybe_paren(a)));
        }
    }
    // Binary operators — prefix matching covers all type combinations
    let op = if short.starts_with("Add_") || short == "Concat_StrStr" {
        "+"
    } else if short.starts_with("Subtract_") {
        "-"
    } else if short.starts_with("Multiply_") {
        "*"
    } else if short.starts_with("Divide_") {
        "/"
    } else if short.starts_with("Percent_") {
        "%"
    } else if short.starts_with("EqualEqual_") {
        "=="
    } else if short.starts_with("NotEqual_") {
        "!="
    } else if short.starts_with("LessEqual_") {
        "<="
    } else if short.starts_with("GreaterEqual_") {
        ">="
    } else if short.starts_with("Less_") {
        "<"
    } else if short.starts_with("Greater_") {
        ">"
    } else if short == "BooleanAND" {
        "&&"
    } else if short == "BooleanOR" {
        "||"
    } else if short.starts_with("GreaterGreater_") {
        ">>"
    } else if short.starts_with("LessLess_") {
        "<<"
    } else {
        return None;
    };
    if args.len() >= 2 {
        let lhs = maybe_paren(&args[0]);
        let rhs = maybe_paren(&args[1]);
        Some(format!("{} {} {}", lhs, op, rhs))
    } else {
        None
    }
}

fn strip_func_prefix(name: &str) -> String {
    if let Some(dot_pos) = name.rfind('.') {
        let class_part = &name[..dot_pos];
        let func = &name[dot_pos + 1..];
        let stripped = func
            .strip_prefix("K2_")
            .or_else(|| func.strip_prefix("Conv_"))
            .unwrap_or(func);
        if is_ue4_library_class(class_part) {
            stripped.to_string()
        } else {
            format!("{}.{}", class_part, stripped)
        }
    } else {
        let stripped = name
            .strip_prefix("K2_")
            .or_else(|| name.strip_prefix("Conv_"))
            .unwrap_or(name);
        stripped.to_string()
    }
}

fn is_ue4_library_class(name: &str) -> bool {
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

/// Extract the resume offset (Linkage field) from a LatentActionInfo struct literal.
/// Format: `LatentActionInfo(skip_offset(0xHEX), uuid, exec_func, callback_target)`
/// The first field is a skip_offset containing the resume entry point in the ubergraph.
fn extract_latent_resume_offset(lai: &str) -> Option<usize> {
    let inner = lai.strip_prefix("LatentActionInfo(")?.strip_suffix(')')?;
    let first = inner.split(',').next()?.trim();
    // skip_offset(0xHEX) format
    let hex = first.strip_prefix("skip_offset(0x")?.strip_suffix(')')?;
    usize::from_str_radix(hex, 16).ok()
}

fn format_call_or_operator(name: &str, args: Vec<String>) -> String {
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
            // Drop WorldContextObject — "self" as first arg of non-method calls
            (a.as_str() != "self" || name.contains('.'))
            // Drop LatentActionInfo struct literals — internal plumbing
            && !a.starts_with("LatentActionInfo(")
        })
        .cloned()
        .collect();
    let clean_name = strip_func_prefix(name);
    crate::enums::resolve_enum_args(&clean_name, &mut clean_args);
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

/// Decode expressions until a terminator opcode is reached, returning them as a list.
#[allow(clippy::too_many_arguments)]
fn decode_expr_list(
    bc: &[u8],
    pos: &mut usize,
    nt: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    mem_adj: &mut i32,
    ue5: i32,
    terminator: u8,
) -> Vec<String> {
    let mut items = Vec::new();
    loop {
        if *pos >= bc.len() {
            break;
        }
        if bc[*pos] == terminator {
            *pos += 1;
            break;
        }
        match decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5) {
            Some(item) => items.push(item),
            None => break,
        }
    }
    items
}

/// Decode a single Kismet expression, returning a string representation.
/// Returns None if at end of script or unknown opcode.
pub fn decode_expr(
    bc: &[u8],
    pos: &mut usize,
    nt: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    mem_adj: &mut i32,
    ue5: i32,
) -> Option<String> {
    if *pos >= bc.len() {
        return None;
    }
    let opcode = read_bc_u8(bc, pos);
    match opcode {
        // --- Variables (local, instance, default, out) ---
        EX_LOCAL_VARIABLE => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(prop)
        }
        EX_INSTANCE_VARIABLE => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("self.{}", prop))
        }
        EX_DEFAULT_VARIABLE => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("default.{}", prop))
        }
        // --- Control flow (return, jump, assert, switch, flow stack) ---
        EX_RETURN => {
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("return {}", expr))
        }
        EX_JUMP => {
            let offset = read_bc_u32(bc, pos);
            Some(format!("jump 0x{:x}", offset))
        }
        EX_JUMP_IF_NOT => {
            let offset = read_bc_u32(bc, pos);
            let cond =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("if !({}) jump 0x{:x}", cond, offset))
        }
        EX_ASSERT => {
            let _line = read_bc_u16(bc, pos);
            let _debug_only = read_bc_u8(bc, pos);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("assert({})", expr))
        }
        EX_NOTHING => Some("nop".into()),
        EX_NOTHING_INT32 => {
            let _ = read_bc_i32(bc, pos);
            Some("nop".into())
        }
        // --- Assignment (Let variants) ---
        EX_LET | EX_LET_MULTICAST_DELEGATE | EX_LET_DELEGATE => {
            let _prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let var =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let val =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        EX_BITFIELD_CONST => {
            let path = read_bc_field_path(bc, pos, nt, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("bitfield({}, {})", path, expr))
        }
        // --- Context / member access ---
        EX_CLASS_CONTEXT => {
            let obj =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}.{}", obj, expr))
        }
        // --- Casts ---
        EX_META_CAST | EX_DYNAMIC_CAST => {
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("cast<{}>({})", class, expr))
        }
        EX_LET_BOOL | EX_LET_OBJ => {
            let var =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let val =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        EX_END_PARM_VALUE => Some("end_param".into()),
        EX_END_FUNCTION_PARMS => None,
        EX_SELF => Some("self".into()),
        EX_SKIP => {
            let _skip = read_bc_u32(bc, pos);
            decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
        }
        EX_CONTEXT => {
            let obj =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            if is_ue4_library_class(&obj) {
                Some(expr.to_string())
            } else {
                Some(format!("{}.{}", obj, expr))
            }
        }
        EX_CONTEXT_FAIL_SILENT => {
            let obj =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            if is_ue4_library_class(&obj) {
                Some(expr.to_string())
            } else {
                Some(format!("{}?.{}", obj, expr))
            }
        }
        // --- Function calls ---
        EX_VIRTUAL_FUNCTION | EX_LOCAL_VIRTUAL_FUNCTION => {
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4; // disk: FName (8 bytes), mem: UFunction* resolved pointer (8+4 alignment)
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj, ue5);
            Some(format_call_or_operator(&name, args))
        }
        EX_FINAL_FUNCTION | EX_LOCAL_FINAL_FUNCTION => {
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj, ue5);
            Some(format_call_or_operator(&func, args))
        }
        // --- Constants (int, float, string, name, vector, struct, text, containers) ---
        EX_INT_CONST => Some(format!("{}", read_bc_i32(bc, pos))),
        EX_FLOAT_CONST => Some(format!("{:.4}", read_bc_f32(bc, pos))),
        EX_STRING_CONST => Some(format!("\"{}\"", read_bc_string(bc, pos))),
        EX_OBJECT_CONST => {
            let obj = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            Some(obj)
        }
        EX_NAME_CONST => {
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4; // disk: FName (8 bytes), mem: FName (12 bytes with DisplayIndex)
            Some(format!("'{}'", name))
        }
        EX_ROTATION_CONST => {
            let (p, y, r) = read_bc_xyz(bc, pos, ue5 >= 1004);
            Some(format!("Rot({:.1},{:.1},{:.1})", p, y, r))
        }
        EX_VECTOR_CONST => {
            let (x, y, z) = read_bc_xyz(bc, pos, ue5 >= 1004);
            Some(format!("Vec({:.1},{:.1},{:.1})", x, y, z))
        }
        EX_BYTE_CONST => Some(format!("{}", read_bc_u8(bc, pos))),
        EX_INT_ZERO => Some("0".into()),
        EX_INT_ONE => Some("1".into()),
        EX_TRUE => Some("true".into()),
        EX_FALSE => Some("false".into()),
        EX_TEXT_CONST => {
            let text_type = read_bc_u8(bc, pos);
            match text_type {
                0 => Some("\"\"".into()),
                1 => {
                    let _ns = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                        .unwrap_or_default();
                    let _key = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                        .unwrap_or_default();
                    let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                        .unwrap_or_default();
                    Some(format!("LOCTEXT({})", val))
                }
                2 | 3 => {
                    let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                        .unwrap_or_default();
                    Some(val)
                }
                4 => {
                    let _table = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
                    let key = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                        .unwrap_or_default();
                    Some(format!("STRTABLE({})", key))
                }
                0xFF => Some("\"\"".into()),
                _ => Some(format!("text(type={})", text_type)),
            }
        }
        EX_NO_OBJECT => Some("null".into()),
        EX_TRANSFORM_CONST => {
            let lwc = ue5 >= 1004;
            let (rx, ry, rz, rw) = read_bc_xyzw(bc, pos, lwc);
            let (tx, ty, tz) = read_bc_xyz(bc, pos, lwc);
            let (sx, sy, sz) = read_bc_xyz(bc, pos, lwc);
            Some(format!("Transform(Rot({:.1},{:.1},{:.1},{:.1}),Pos({:.1},{:.1},{:.1}),Scale({:.1},{:.1},{:.1}))",
                rx, ry, rz, rw, tx, ty, tz, sx, sy, sz))
        }
        EX_INT_CONST_BYTE => Some(format!("{}", read_bc_u8(bc, pos))),
        EX_NO_INTERFACE => Some("null_iface".into()),
        EX_STRUCT_CONST => {
            let struct_ref = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _serial_size = read_bc_i32(bc, pos);
            let fields = decode_expr_list(
                bc,
                pos,
                nt,
                imports,
                export_names,
                mem_adj,
                ue5,
                EX_END_STRUCT_CONST,
            );
            Some(format!("{}({})", struct_ref, fields.join(", ")))
        }
        EX_END_STRUCT_CONST => None,
        EX_SET_ARRAY => {
            let target =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let items = decode_expr_list(
                bc,
                pos,
                nt,
                imports,
                export_names,
                mem_adj,
                ue5,
                EX_END_ARRAY,
            );
            Some(format!("{} = [{}]", target, items.join(", ")))
        }
        EX_END_ARRAY => None,
        EX_PROPERTY_CONST => {
            let path = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("prop({})", path))
        }
        EX_UNICODE_STRING_CONST => {
            let mut s = Vec::new();
            while *pos + 1 < bc.len() {
                let lo = bc[*pos];
                let hi = bc[*pos + 1];
                *pos += 2;
                if lo == 0 && hi == 0 {
                    break;
                }
                s.push(u16::from_le_bytes([lo, hi]));
            }
            Some(format!("\"{}\"", String::from_utf16_lossy(&s)))
        }
        EX_INT64_CONST => Some(format!("{}L", read_bc_i64(bc, pos))),
        EX_UINT64_CONST => Some(format!("{}UL", read_bc_u64(bc, pos))),
        EX_DOUBLE_CONST => Some(format!("{:.4}", read_bc_f64(bc, pos))),
        EX_PRIMITIVE_CAST => {
            let cast_type = read_bc_u8(bc, pos);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let name = primitive_cast_name(cast_type);
            Some(format!("{}({})", name, expr))
        }
        EX_SET_SET => {
            let target =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let _count = read_bc_i32(bc, pos);
            let items =
                decode_expr_list(bc, pos, nt, imports, export_names, mem_adj, ue5, EX_END_SET);
            Some(format!("{} = set{{{}}}", target, items.join(", ")))
        }
        EX_END_SET => None,
        EX_SET_MAP => {
            let target =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let _count = read_bc_i32(bc, pos);
            let items =
                decode_expr_list(bc, pos, nt, imports, export_names, mem_adj, ue5, EX_END_MAP);
            Some(format!("{} = map{{{}}}", target, items.join(", ")))
        }
        EX_END_MAP => None,
        EX_SET_CONST => {
            let _inner = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let items = decode_expr_list(
                bc,
                pos,
                nt,
                imports,
                export_names,
                mem_adj,
                ue5,
                EX_END_SET_CONST,
            );
            Some(format!("set{{{}}}", items.join(", ")))
        }
        EX_END_SET_CONST => None,
        EX_MAP_CONST => {
            let _key_prop = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _val_prop = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let items = decode_expr_list(
                bc,
                pos,
                nt,
                imports,
                export_names,
                mem_adj,
                ue5,
                EX_END_MAP_CONST,
            );
            Some(format!("map{{{}}}", items.join(", ")))
        }
        EX_END_MAP_CONST => None,
        EX_VECTOR3F_CONST => {
            if ue5 > 0 {
                // UE5: explicit float vector
                let x = read_bc_f32(bc, pos);
                let y = read_bc_f32(bc, pos);
                let z = read_bc_f32(bc, pos);
                Some(format!("Vec3f({:.1},{:.1},{:.1})", x, y, z))
            } else {
                // UE4: unused opcode, treat as StructMemberContext fallback
                let prop = read_bc_field_path(bc, pos, nt, mem_adj);
                let struct_expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                    .unwrap_or_default();
                Some(format!("{}.{}", struct_expr, prop))
            }
        }
        EX_STRUCT_MEMBER_CONTEXT => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let struct_expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{}.{}", struct_expr, prop))
        }
        EX_LOCAL_OUT_VARIABLE => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("out {}", prop))
        }
        // --- Delegates ---
        EX_INSTANCE_DELEGATE => {
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            Some(format!("delegate({})", name))
        }
        EX_PUSH_EXECUTION_FLOW => {
            let offset = read_bc_u32(bc, pos);
            Some(format!("push_flow 0x{:x}", offset))
        }
        EX_POP_EXECUTION_FLOW => Some("pop_flow".into()),
        EX_COMPUTED_JUMP => {
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("jump_computed({})", expr))
        }
        EX_POP_FLOW_IF_NOT => {
            let cond =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("pop_flow_if_not({})", cond))
        }
        EX_BREAKPOINT => Some("breakpoint".into()),
        EX_INTERFACE_CONTEXT => {
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("iface({})", expr))
        }
        EX_OBJ_TO_IFACE_CAST | EX_CROSS_IFACE_CAST => {
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("icast<{}>({})", class, expr))
        }
        EX_END_OF_SCRIPT => None,
        EX_IFACE_TO_OBJ_CAST => {
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("obj_cast<{}>({})", class, expr))
        }
        EX_WIRE_TRACEPOINT => Some("wire_trace".into()),
        EX_SKIP_OFFSET_CONST => {
            let offset = read_bc_u32(bc, pos);
            Some(format!("skip_offset(0x{:x})", offset))
        }
        EX_ADD_MULTICAST_DELEGATE => {
            let delegate =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let func =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} += {}", delegate, func))
        }
        EX_CLEAR_MULTICAST_DELEGATE => {
            let delegate =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{}.Clear()", delegate))
        }
        EX_TRACEPOINT => Some("tracepoint".into()),
        EX_LET_WEAK_OBJ_PTR => {
            let var =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let val =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} = weak({})", var, val))
        }
        EX_BIND_DELEGATE => {
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            let delegate =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let obj =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("bind({}, {}, {})", name, delegate, obj))
        }
        EX_REMOVE_MULTICAST_DELEGATE => {
            let delegate =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let func =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} -= {}", delegate, func))
        }
        EX_CALL_MULTICAST_DELEGATE => {
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj, ue5);
            Some(format!("{}.Broadcast({})", func, args.join(", ")))
        }
        EX_LET_VALUE_ON_PERSISTENT_FRAME => {
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let val =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{} = {} [persistent]", prop, val))
        }
        EX_ARRAY_CONST => {
            let _inner = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let items = decode_expr_list(
                bc,
                pos,
                nt,
                imports,
                export_names,
                mem_adj,
                ue5,
                EX_END_ARRAY_CONST,
            );
            Some(format!("[{}]", items.join(", ")))
        }
        EX_END_ARRAY_CONST => None,
        EX_SOFT_OBJECT_CONST => {
            let path =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("soft({})", path))
        }
        EX_CALL_MATH => {
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj, ue5);
            Some(format_call_or_operator(&func, args))
        }
        EX_SWITCH_VALUE => {
            let num_cases = read_bc_u16(bc, pos);
            let _end_offset = read_bc_u32(bc, pos);
            let index =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let mut cases = Vec::new();
            for _ in 0..num_cases {
                let case_val = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                    .unwrap_or_default();
                let _next_offset = read_bc_u32(bc, pos);
                let result = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5)
                    .unwrap_or_default();
                cases.push(format!("{}: {}", case_val, result));
            }
            let default =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
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
        EX_INSTRUMENTATION_EVENT => {
            let event_type = read_bc_u8(bc, pos);
            if event_type == 4 {
                let _name = read_bc_fname(bc, pos, nt);
                *mem_adj += 4;
            }
            Some("instrumentation".into())
        }
        EX_ARRAY_GET_BY_REF => {
            let array =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            let index =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("{}[{}]", array, index))
        }
        EX_CLASS_SPARSE_DATA_VARIABLE => {
            let path = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("sparse.{}", path))
        }
        EX_FIELD_PATH_CONST => {
            let path = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("fieldpath({})", path))
        }
        EX_AUTO_RTFM_TRANSACT => {
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("rtfm_transact({})", expr))
        }
        EX_AUTO_RTFM_STOP_TRANSACT => {
            let _mode = read_bc_u8(bc, pos);
            Some("rtfm_stop".into())
        }
        EX_AUTO_RTFM_ABORT_IF_NOT => {
            let expr =
                decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5).unwrap_or_default();
            Some(format!("rtfm_abort_if_not({})", expr))
        }
        _ => Some(format!("???(0x{:02x})", opcode)),
    }
}

fn decode_func_args(
    bc: &[u8],
    pos: &mut usize,
    nt: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    mem_adj: &mut i32,
    ue5: i32,
) -> Vec<String> {
    let mut args = Vec::new();
    loop {
        if *pos >= bc.len() {
            break;
        }
        if bc[*pos] == EX_END_FUNCTION_PARMS {
            *pos += 1;
            break;
        }
        if let Some(expr) = decode_expr(bc, pos, nt, imports, export_names, mem_adj, ue5) {
            args.push(expr);
        } else {
            break;
        }
    }
    args
}

fn primitive_cast_name(cast_type: u8) -> String {
    match cast_type {
        0x41 => "iface_to_obj".into(), // CST_InterfaceToObject
        0x46 => "obj_to_iface".into(), // CST_ObjectToInterface
        0x47 => "bool".into(),         // CST_ObjectToBool
        _ => format!("cast_{}", cast_type),
    }
}

pub fn decode_bytecode(
    bc: &[u8],
    nt: &NameTable,
    imports: &[ImportEntry],
    export_names: &[String],
    ue5: i32,
) -> (Vec<BcStatement>, i32) {
    let mut pos = 0;
    let mut mem_adj: i32 = 0;
    let mut stmts = Vec::new();
    while pos < bc.len() {
        let mem_start = (pos as i32 + mem_adj) as usize;
        let start = pos;
        match decode_expr(bc, &mut pos, nt, imports, export_names, &mut mem_adj, ue5) {
            Some(s) => match s.as_str() {
                "nop" | "wire_trace" | "tracepoint" | "instrumentation" => continue,
                _ => {
                    stmts.push(BcStatement {
                        mem_offset: mem_start,
                        text: s,
                    });
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::NameTable;

    // Helper: build a NameTable with given names (index 0 = first name)
    fn nt(names: &[&str]) -> NameTable {
        NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
    }

    // Helper: append little-endian i32
    fn push_i32(bc: &mut Vec<u8>, v: i32) {
        bc.extend_from_slice(&v.to_le_bytes());
    }
    fn push_f32(bc: &mut Vec<u8>, v: f32) {
        bc.extend_from_slice(&v.to_le_bytes());
    }
    fn push_f64(bc: &mut Vec<u8>, v: f64) {
        bc.extend_from_slice(&v.to_le_bytes());
    }

    // Helper: append a single-name FFieldPath — 16 bytes
    // FName = name_index(i32) + instance_number(i32), then owner(i32)
    fn push_field_path(bc: &mut Vec<u8>, name_idx: i32) {
        push_i32(bc, 1); // path_num = 1
        push_i32(bc, name_idx); // FName index
        push_i32(bc, 0); // FName instance number
        push_i32(bc, 0); // owner
    }

    // Helper: decode a single expression from bytes
    fn expr(bc: &[u8], ue5: i32) -> (Option<String>, i32) {
        let names = nt(&["TestVar", "TestFunc", "None"]);
        let imports = vec![];
        let export_names = vec![];
        let mut pos = 0;
        let mut mem_adj = 0;
        let result = decode_expr(
            bc,
            &mut pos,
            &names,
            &imports,
            &export_names,
            &mut mem_adj,
            ue5,
        );
        (result, mem_adj)
    }

    // Helper: decode with custom name table
    fn expr_with_nt(bc: &[u8], names: &NameTable, ue5: i32) -> Option<String> {
        let imports = vec![];
        let export_names = vec![];
        let mut pos = 0;
        let mut mem_adj = 0;
        decode_expr(
            bc,
            &mut pos,
            names,
            &imports,
            &export_names,
            &mut mem_adj,
            ue5,
        )
    }

    // --- LWC opcodes: float vs double branching ---

    #[test]
    fn rotation_const_ue4_reads_floats() {
        let mut bc = vec![0x22];
        push_f32(&mut bc, 1.0);
        push_f32(&mut bc, 2.0);
        push_f32(&mut bc, 3.0);
        let (result, _) = expr(&bc, 0);
        assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
    }

    #[test]
    fn rotation_const_ue5_lwc_reads_doubles() {
        let mut bc = vec![0x22];
        push_f64(&mut bc, 1.0);
        push_f64(&mut bc, 2.0);
        push_f64(&mut bc, 3.0);
        let (result, _) = expr(&bc, 1004);
        assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
    }

    #[test]
    fn vector_const_ue4_reads_floats() {
        let mut bc = vec![0x23];
        push_f32(&mut bc, 10.0);
        push_f32(&mut bc, 20.0);
        push_f32(&mut bc, 30.0);
        let (result, _) = expr(&bc, 0);
        assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
    }

    #[test]
    fn vector_const_ue5_lwc_reads_doubles() {
        let mut bc = vec![0x23];
        push_f64(&mut bc, 10.0);
        push_f64(&mut bc, 20.0);
        push_f64(&mut bc, 30.0);
        let (result, _) = expr(&bc, 1004);
        assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
    }

    #[test]
    fn transform_const_ue4_reads_floats() {
        let mut bc = vec![0x2B];
        for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
            push_f32(&mut bc, v);
        }
        let (result, _) = expr(&bc, 0);
        assert!(result.unwrap().starts_with("Transform("));
    }

    #[test]
    fn transform_const_ue5_lwc_reads_doubles() {
        let mut bc = vec![0x2B];
        for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
            push_f64(&mut bc, v);
        }
        let (result, _) = expr(&bc, 1004);
        assert!(result.unwrap().starts_with("Transform("));
    }

    // --- 0x41: UE5 = Vector3fConst, UE4 = StructMemberContext fallback ---

    #[test]
    fn vector3f_const_ue5() {
        let mut bc = vec![0x41];
        push_f32(&mut bc, 1.0);
        push_f32(&mut bc, 2.0);
        push_f32(&mut bc, 3.0);
        let (result, _) = expr(&bc, 1000);
        assert_eq!(result.unwrap(), "Vec3f(1.0,2.0,3.0)");
    }

    // --- 0x37: EX_DoubleConst ---

    #[test]
    fn double_const() {
        let mut bc = vec![0x37];
        push_f64(&mut bc, 1.2345);
        let (result, _) = expr(&bc, 0);
        assert_eq!(result.unwrap(), "1.2345");
    }

    // --- 0x0C: EX_NothingInt32 ---

    #[test]
    fn nothing_int32_returns_nop() {
        let mut bc = vec![0x0C];
        push_i32(&mut bc, 42);
        let (result, _) = expr(&bc, 0);
        assert_eq!(result.unwrap(), "nop");
    }

    // --- 0x11: EX_BitFieldConst ---

    #[test]
    fn bitfield_const() {
        let mut bc = vec![0x11];
        push_field_path(&mut bc, 0); // FFieldPath → "TestVar"
        bc.push(0x27); // EX_True
        let names = nt(&["TestVar"]);
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "bitfield(TestVar, true)");
    }

    // --- 0x33: EX_PropertyConst ---

    #[test]
    fn property_const() {
        let mut bc = vec![0x33];
        push_field_path(&mut bc, 0); // FFieldPath → "TestVar"
        let names = nt(&["TestVar"]);
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "prop(TestVar)");
    }

    // --- 0x6C: EX_ClassSparseDataVariable ---

    #[test]
    fn class_sparse_data_variable() {
        let mut bc = vec![0x6C];
        push_field_path(&mut bc, 0); // FFieldPath → "TestVar"
        let names = nt(&["TestVar"]);
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "sparse.TestVar");
    }

    // --- 0x70-0x72: RTFM opcodes ---

    #[test]
    fn rtfm_transact() {
        let mut bc = vec![0x70];
        bc.push(0x27); // EX_True as inner expression
        let (result, _) = expr(&bc, 1004);
        assert_eq!(result.unwrap(), "rtfm_transact(true)");
    }

    #[test]
    fn rtfm_stop_transact() {
        let bc = vec![0x71, 0x01]; // opcode + mode byte
        let (result, _) = expr(&bc, 1004);
        assert_eq!(result.unwrap(), "rtfm_stop");
    }

    #[test]
    fn rtfm_abort_if_not() {
        let mut bc = vec![0x72];
        bc.push(0x28); // EX_False as condition
        let (result, _) = expr(&bc, 1004);
        assert_eq!(result.unwrap(), "rtfm_abort_if_not(false)");
    }

    // --- 0x43/0x44: EX_LetMulticastDelegate/EX_LetDelegate (with FFieldPath) ---

    #[test]
    fn let_multicast_delegate() {
        let names = nt(&["MyDelegate", "Target", "Value"]);
        let mut bc = vec![0x43];
        push_field_path(&mut bc, 0); // FFieldPath → "MyDelegate"
                                     // var: EX_LocalVariable with FFieldPath → "Target"
        bc.push(0x00);
        push_field_path(&mut bc, 1);
        // val: EX_LocalVariable with FFieldPath → "Value"
        bc.push(0x00);
        push_field_path(&mut bc, 2);
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "Target = Value");
    }

    #[test]
    fn let_delegate() {
        let names = nt(&["MyDelegate", "Target", "Value"]);
        let mut bc = vec![0x44];
        push_field_path(&mut bc, 0); // FFieldPath → "MyDelegate"
        bc.push(0x00);
        push_field_path(&mut bc, 1); // var
        bc.push(0x00);
        push_field_path(&mut bc, 2); // val
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "Target = Value");
    }

    // --- 0x39/0x3B: EX_SetSet/EX_SetMap (with element count) ---

    #[test]
    fn set_set_reads_element_count() {
        let names = nt(&["MySet"]);
        let mut bc = vec![0x39];
        // target: EX_LocalVariable
        bc.push(0x00);
        push_field_path(&mut bc, 0);
        // element count (int32)
        push_i32(&mut bc, 2);
        // two elements: EX_IntConst(1), EX_IntConst(2), then EX_EndSet
        bc.push(0x1D);
        push_i32(&mut bc, 1);
        bc.push(0x1D);
        push_i32(&mut bc, 2);
        bc.push(0x3A); // EX_EndSet
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "MySet = set{1, 2}");
    }

    #[test]
    fn set_map_reads_element_count() {
        let names = nt(&["MyMap"]);
        let mut bc = vec![0x3B];
        bc.push(0x00);
        push_field_path(&mut bc, 0); // target
        push_i32(&mut bc, 1); // element count
        bc.push(0x1D);
        push_i32(&mut bc, 10); // key
        bc.push(0x1D);
        push_i32(&mut bc, 20); // value
        bc.push(0x3C); // EX_EndMap
        let result = expr_with_nt(&bc, &names, 0);
        assert_eq!(result.unwrap(), "MyMap = map{10, 20}");
    }

    // --- LWC pre-1004: still uses floats ---

    #[test]
    fn vector_const_ue5_pre_lwc_reads_floats() {
        let mut bc = vec![0x23];
        push_f32(&mut bc, 1.0);
        push_f32(&mut bc, 2.0);
        push_f32(&mut bc, 3.0);
        let (result, _) = expr(&bc, 1003); // pre-LWC UE5
        assert_eq!(result.unwrap(), "Vec(1.0,2.0,3.0)");
    }

    // --- decode_bytecode filters nop ---

    #[test]
    fn decode_bytecode_filters_nothing_int32() {
        let names = nt(&["None"]);
        let imports = vec![];
        let export_names = vec![];
        let mut bc = vec![0x0C]; // EX_NothingInt32
        push_i32(&mut bc, 0);
        bc.push(0x53); // EX_EndOfScript
        let (stmts, _) = decode_bytecode(&bc, &names, &imports, &export_names, 0);
        assert!(stmts.is_empty(), "NothingInt32 should be filtered as nop");
    }
}
