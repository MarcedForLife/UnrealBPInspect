use super::super::format::format_call_or_operator;
use super::super::opcodes::*;
use super::super::readers::*;
use super::expr::decode_expr;
use super::funcs::{decode_func_args, primitive_cast_name};
use super::helpers::{decode_constant, decode_container_mutation, decode_context, decode_delegate};
use super::types::DecodeCtx;
use crate::types::VER_UE5_LARGE_WORLD_COORDINATES;

/// Explicit match for opcodes that don't fit a uniform table pattern:
/// control flow, assignments, function calls, context, delegates, containers, switches.
pub(super) fn decode_match_op(
    opcode: u8,
    ctx: &DecodeCtx,
    pos: &mut usize,
    mem_adj: &mut i32,
) -> Option<String> {
    let bytecode = ctx.bytecode;
    // Macro (not closure) because `pos` and `mem_adj` are &mut while `ctx` is shared.
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
            // Persistent-frame vars survive latent resumes (e.g. Delay); the
            // [persistent] marker blocks inlining across event boundaries.
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
