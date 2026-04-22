use super::super::opcodes::*;
use super::expr::decode_expr;
use super::types::DecodeCtx;
use crate::types::VER_UE5_LARGE_WORLD_COORDINATES;

pub(super) fn decode_func_args(ctx: &DecodeCtx, pos: &mut usize, mem_adj: &mut i32) -> Vec<String> {
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

pub(super) fn primitive_cast_name(cast_type: u8, ue5: i32) -> String {
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
