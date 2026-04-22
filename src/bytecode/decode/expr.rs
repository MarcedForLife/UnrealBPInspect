use super::super::readers::*;
use super::helpers::decode_table_op;
use super::match_op::decode_match_op;
use super::types::DecodeCtx;

/// Decode a single Kismet expression. Table-driven opcode families first,
/// then explicit match for the rest.
pub fn decode_expr(ctx: &DecodeCtx, pos: &mut usize, mem_adj: &mut i32) -> Option<String> {
    if *pos >= ctx.bytecode.len() {
        return None;
    }
    let opcode = read_bc_u8(ctx.bytecode, pos);
    if let Some(result) = decode_table_op(opcode, ctx, pos, mem_adj) {
        return result;
    }
    decode_match_op(opcode, ctx, pos, mem_adj)
}
