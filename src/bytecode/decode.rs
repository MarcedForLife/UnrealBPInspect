use crate::binary::NameTable;
use crate::types::ImportEntry;
use super::readers::*;
use super::resolve::*;

#[derive(Clone)]
pub struct BcStatement {
    pub mem_offset: usize,
    pub text: String,
}

/// Decode a single Kismet expression, returning a string representation.
/// Returns None if at end of script or unknown opcode.
pub fn decode_expr(bc: &[u8], pos: &mut usize, nt: &NameTable,
               imports: &[ImportEntry], export_names: &[String], mem_adj: &mut i32) -> Option<String> {
    if *pos >= bc.len() { return None; }
    let opcode = read_bc_u8(bc, pos);
    match opcode {
        0x00 => { // EX_LocalVariable
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(prop)
        }
        0x01 => { // EX_InstanceVariable
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("self.{}", prop))
        }
        0x02 => { // EX_DefaultVariable
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("default.{}", prop))
        }
        0x04 => { // EX_Return
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("return {}", expr))
        }
        0x06 => { // EX_Jump
            let offset = read_bc_u32(bc, pos);
            Some(format!("jump 0x{:x}", offset))
        }
        0x07 => { // EX_JumpIfNot
            let offset = read_bc_u32(bc, pos);
            let cond = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("if !({}) jump 0x{:x}", cond, offset))
        }
        0x09 => { // EX_Assert
            let _line = read_bc_u16(bc, pos);
            let _debug_only = read_bc_u8(bc, pos);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("assert({})", expr))
        }
        0x0B => Some("nop".into()), // EX_Nothing
        0x0F => { // EX_Let
            let _prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let var = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x12 => { // EX_ClassContext
            let obj = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}.{}", obj, expr))
        }
        0x13 => { // EX_MetaCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("cast<{}>({})", class, expr))
        }
        0x14 => { // EX_LetBool
            let var = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x15 => Some("end_param".into()), // EX_EndParmValue
        0x16 => None, // EX_EndFunctionParms
        0x17 => Some("self".into()), // EX_Self
        0x18 => { // EX_Skip
            let _skip = read_bc_u32(bc, pos);
            decode_expr(bc, pos, nt, imports, export_names, mem_adj)
        }
        0x19 => { // EX_Context
            let obj = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}.{}", obj, expr))
        }
        0x1A => { // EX_Context_FailSilent
            let obj = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            read_bc_context_rvalue(bc, pos, nt, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let expr = expr.strip_prefix("self.").unwrap_or(&expr);
            Some(format!("{}?.{}", obj, expr))
        }
        0x1B => { // EX_VirtualFunction
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4; // disk: FName (8 bytes), mem: UFunction* resolved pointer (8+4 alignment)
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", name, args.join(", ")))
        }
        0x1C => { // EX_FinalFunction
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x1D => Some(format!("{}", read_bc_i32(bc, pos))),    // EX_IntConst
        0x1E => Some(format!("{:.4}", read_bc_f32(bc, pos))), // EX_FloatConst
        0x1F => Some(format!("\"{}\"", read_bc_string(bc, pos))), // EX_StringConst
        0x20 => { // EX_ObjectConst
            let obj = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            Some(obj)
        }
        0x21 => { // EX_NameConst
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4; // disk: FName (8 bytes), mem: FName (12 bytes with DisplayIndex)
            Some(format!("'{}'", name))
        }
        0x22 => { // EX_RotationConst
            let p = read_bc_f32(bc, pos);
            let y = read_bc_f32(bc, pos);
            let r = read_bc_f32(bc, pos);
            Some(format!("Rot({:.1},{:.1},{:.1})", p, y, r))
        }
        0x23 => { // EX_VectorConst
            let x = read_bc_f32(bc, pos);
            let y = read_bc_f32(bc, pos);
            let z = read_bc_f32(bc, pos);
            Some(format!("Vec({:.1},{:.1},{:.1})", x, y, z))
        }
        0x24 => Some(format!("{}", read_bc_u8(bc, pos))), // EX_ByteConst
        0x25 => Some("0".into()),    // EX_IntZero
        0x26 => Some("1".into()),    // EX_IntOne
        0x27 => Some("true".into()), // EX_True
        0x28 => Some("false".into()),// EX_False
        0x29 => { // EX_TextConst
            let text_type = read_bc_u8(bc, pos);
            match text_type {
                0 => Some("\"\"".into()),
                1 => {
                    let _ns = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                    let _key = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                    let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                    Some(format!("LOCTEXT({})", val))
                }
                2 | 3 => {
                    let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                    Some(val)
                }
                4 => {
                    let _table = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
                    let key = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                    Some(format!("STRTABLE({})", key))
                }
                0xFF => Some("\"\"".into()),
                _ => Some(format!("text(type={})", text_type))
            }
        }
        0x2A => Some("null".into()),  // EX_NoObject
        0x2B => { // EX_TransformConst
            let rx = read_bc_f32(bc, pos); let ry = read_bc_f32(bc, pos);
            let rz = read_bc_f32(bc, pos); let rw = read_bc_f32(bc, pos);
            let tx = read_bc_f32(bc, pos); let ty = read_bc_f32(bc, pos);
            let tz = read_bc_f32(bc, pos);
            let sx = read_bc_f32(bc, pos); let sy = read_bc_f32(bc, pos);
            let sz = read_bc_f32(bc, pos);
            Some(format!("Transform(Rot({:.1},{:.1},{:.1},{:.1}),Pos({:.1},{:.1},{:.1}),Scale({:.1},{:.1},{:.1}))",
                rx, ry, rz, rw, tx, ty, tz, sx, sy, sz))
        }
        0x2C => Some(format!("{}", read_bc_u8(bc, pos))), // EX_IntConstByte
        0x2D => Some("null_iface".into()), // EX_NoInterface
        0x2E => { // EX_DynamicCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("cast<{}>({})", class, expr))
        }
        0x2F => { // EX_StructConst
            let struct_ref = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _serial_size = read_bc_i32(bc, pos);
            let mut fields = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x30 { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(f) => fields.push(f),
                    None => break,
                }
            }
            Some(format!("{}({})", struct_ref, fields.join(", ")))
        }
        0x30 => None, // EX_EndStructConst
        0x31 => { // EX_SetArray
            let target = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x32 { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("{} = [{}]", target, items.join(", ")))
        }
        0x32 => None, // EX_EndArray
        0x34 => { // EX_UnicodeStringConst
            let mut s = Vec::new();
            while *pos + 1 < bc.len() {
                let lo = bc[*pos]; let hi = bc[*pos + 1];
                *pos += 2;
                if lo == 0 && hi == 0 { break; }
                s.push(u16::from_le_bytes([lo, hi]));
            }
            Some(format!("\"{}\"", String::from_utf16_lossy(&s)))
        }
        0x35 => Some(format!("{}L", read_bc_i64(bc, pos))), // EX_Int64Const
        0x36 => Some(format!("{}UL", read_bc_u64(bc, pos))), // EX_UInt64Const
        0x38 => { // EX_PrimitiveCast
            let cast_type = read_bc_u8(bc, pos);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("cast_{}({})", cast_type, expr))
        }
        0x39 => { // EX_SetSet
            let target = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x3A { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("{} = set{{{}}}", target, items.join(", ")))
        }
        0x3A => None, // EX_EndSet
        0x3B => { // EX_SetMap
            let target = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x3C { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("{} = map{{{}}}", target, items.join(", ")))
        }
        0x3C => None, // EX_EndMap
        0x3D => { // EX_SetConst
            let _inner = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x3E { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("set{{{}}}", items.join(", ")))
        }
        0x3E => None, // EX_EndSetConst
        0x3F => { // EX_MapConst
            let _key_prop = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _val_prop = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x40 { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("map{{{}}}", items.join(", ")))
        }
        0x40 => None, // EX_EndMapConst
        0x41 => { // EX_StructMemberContext
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let struct_expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{}.{}", struct_expr, prop))
        }
        0x42 => { // EX_StructMemberContext variant
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let struct_expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{}.{}", struct_expr, prop))
        }
        0x43 => { // EX_LetDelegate
            let var = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x44 => { // EX_LocalVirtualFunction
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", name, args.join(", ")))
        }
        0x45 => { // EX_LocalFinalFunction
            let func = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x46 => { // EX_FinalFunction variant (ubergraph dispatch)
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x48 => { // EX_LocalOutVariable
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("out {}", prop))
        }
        0x4B => { // EX_InstanceDelegate
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            Some(format!("delegate({})", name))
        }
        0x4C => { // EX_PushExecutionFlow
            let offset = read_bc_u32(bc, pos);
            Some(format!("push_flow 0x{:x}", offset))
        }
        0x4D => Some("pop_flow".into()), // EX_PopExecutionFlow
        0x4E => { // EX_ComputedJump
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("jump_computed({})", expr))
        }
        0x4F => { // EX_PopExecutionFlowIfNot
            let cond = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("pop_flow_if_not({})", cond))
        }
        0x50 => Some("breakpoint".into()), // EX_Breakpoint
        0x51 => { // EX_InterfaceContext
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("iface({})", expr))
        }
        0x52 => { // EX_ObjToInterfaceCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("icast<{}>({})", class, expr))
        }
        0x53 => None, // EX_EndOfScript
        0x54 => { // EX_CrossInterfaceCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("icast<{}>({})", class, expr))
        }
        0x55 => { // EX_InterfaceToObjCast
            let class = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let expr = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("obj_cast<{}>({})", class, expr))
        }
        0x5A => Some("wire_trace".into()), // EX_WireTracepoint
        0x5B => { // EX_SkipOffsetConst
            let offset = read_bc_u32(bc, pos);
            Some(format!("skip_offset(0x{:x})", offset))
        }
        0x5C => { // EX_AddMulticastDelegate
            let delegate = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let func = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} += {}", delegate, func))
        }
        0x5D => { // EX_ClearMulticastDelegate
            let delegate = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{}.Clear()", delegate))
        }
        0x5E => Some("tracepoint".into()), // EX_Tracepoint
        0x5F => { // EX_LetObj
            let var = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = {}", var, val))
        }
        0x60 => { // EX_LetWeakObjPtr
            let var = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = weak({})", var, val))
        }
        0x61 => { // EX_BindDelegate
            let name = read_bc_fname(bc, pos, nt);
            *mem_adj += 4;
            let delegate = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let obj = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("bind({}, {}, {})", name, delegate, obj))
        }
        0x62 => { // EX_RemoveMulticastDelegate
            let delegate = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let func = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} -= {}", delegate, func))
        }
        0x63 => { // EX_CallMulticastDelegate
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}.Broadcast({})", func, args.join(", ")))
        }
        0x64 => { // EX_LetValueOnPersistentFrame
            let prop = read_bc_field_path(bc, pos, nt, mem_adj);
            let val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{} = {} [persistent]", prop, val))
        }
        0x65 => { // EX_ArrayConst
            let _inner = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let _count = read_bc_i32(bc, pos);
            let mut items = Vec::new();
            loop {
                if *pos >= bc.len() { break; }
                if bc[*pos] == 0x66 { *pos += 1; break; }
                match decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
                    Some(item) => items.push(item),
                    None => break,
                }
            }
            Some(format!("[{}]", items.join(", ")))
        }
        0x66 => None, // EX_EndArrayConst
        0x67 => { // EX_SoftObjectConst
            let path = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("soft({})", path))
        }
        0x68 => { // EX_CallMath
            let func = read_bc_obj_ref(bc, pos, imports, export_names, mem_adj);
            let args = decode_func_args(bc, pos, nt, imports, export_names, mem_adj);
            Some(format!("{}({})", func, args.join(", ")))
        }
        0x69 => { // EX_SwitchValue
            let num_cases = read_bc_u16(bc, pos);
            let _end_offset = read_bc_u32(bc, pos);
            let index = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let mut cases = Vec::new();
            for _ in 0..num_cases {
                let case_val = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                let _next_offset = read_bc_u32(bc, pos);
                let result = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
                cases.push(format!("{}: {}", case_val, result));
            }
            let default = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("switch({}) {{ {}, default: {} }}", index, cases.join(", "), default))
        }
        0x6A => { // EX_InstrumentationEvent
            let event_type = read_bc_u8(bc, pos);
            if event_type == 4 {
                let _name = read_bc_fname(bc, pos, nt);
                *mem_adj += 4;
            }
            Some("instrumentation".into())
        }
        0x6B => { // EX_ArrayGetByRef
            let array = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            let index = decode_expr(bc, pos, nt, imports, export_names, mem_adj).unwrap_or_default();
            Some(format!("{}[{}]", array, index))
        }
        0x6D => { // EX_FieldPathConst
            let path = read_bc_field_path(bc, pos, nt, mem_adj);
            Some(format!("fieldpath({})", path))
        }
        _ => {
            Some(format!("???(0x{:02x})", opcode))
        }
    }
}

fn decode_func_args(bc: &[u8], pos: &mut usize, nt: &NameTable,
                    imports: &[ImportEntry], export_names: &[String], mem_adj: &mut i32) -> Vec<String> {
    let mut args = Vec::new();
    loop {
        if *pos >= bc.len() { break; }
        if bc[*pos] == 0x16 {
            *pos += 1;
            break;
        }
        if let Some(expr) = decode_expr(bc, pos, nt, imports, export_names, mem_adj) {
            args.push(expr);
        } else {
            break;
        }
    }
    args
}

pub fn decode_bytecode(bc: &[u8], nt: &NameTable,
                   imports: &[ImportEntry], export_names: &[String]) -> (Vec<BcStatement>, i32) {
    let mut pos = 0;
    let mut mem_adj: i32 = 0;
    let mut stmts = Vec::new();
    while pos < bc.len() {
        let mem_start = (pos as i32 + mem_adj) as usize;
        let start = pos;
        match decode_expr(bc, &mut pos, nt, imports, export_names, &mut mem_adj) {
            Some(s) => {
                match s.as_str() {
                    "nop" | "wire_trace" | "tracepoint" | "instrumentation" => continue,
                    _ => {
                        stmts.push(BcStatement { mem_offset: mem_start, text: s });
                    }
                }
            }
            None => break,
        }
        if pos == start { break; }
    }
    (stmts, mem_adj)
}
