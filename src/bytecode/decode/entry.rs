use super::expr::decode_expr;
use super::types::{BcStatement, DecodeCtx};
use crate::binary::NameTable;
use crate::types::ImportEntry;

/// Decode a raw bytecode slice into statements, skipping instrumentation opcodes.
/// Returns `(statements, final_mem_adj)` for drift validation via `--debug`.
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
