//! Switch recognition for the bytecode decoder.
//!
//! Recognises the `EX_SwitchValue` opcode and produces `Stmt::Switch`.
//!
//! Bytecode layout:
//! ```text
//! EX_SWITCH_VALUE
//!   u16 num_cases
//!   u32 end_offset                 // mem offset where execution resumes
//!   <index_expr>                   // value being switched on
//!   for each case:
//!     <case_value_expr>
//!     u32 next_offset              // mem offset of the next case header
//!     <case_body_expr>
//!   <default_expr>
//! ```
//!
//! In Blueprint, `EX_SwitchValue` actually appears as an *expression*
//! (each case body is itself a sub-expression that evaluates to the
//! resulting value). The decoder still produces `Stmt::Switch` for it
//! because that's the cleanest way to surface multi-arm dispatch in
//! the typed IR. Each case body becomes a single `Stmt::Assignment`
//! synthesised from the case-value expression where appropriate, or
//! a degenerate one-statement body containing the case-result expr.
//!
//! Decodes the explicit `EX_SwitchValue` shape only.

use crate::bytecode::expr::Expr;
use crate::bytecode::opcodes::EX_SWITCH_VALUE;
use crate::bytecode::readers::{read_bc_u16, read_bc_u32};
use crate::bytecode::stmt::{Stmt, SwitchCase};

use super::ctx::DecodeCtx;
use super::expr_decode::decode_expr;

/// Try to decode an `EX_SwitchValue` at `*pos`. Returns `Some(Stmt::Switch)`
/// when the bytes form a recognisable switch, with `*pos` advanced past
/// the entire instruction. Returns `None` and leaves `*pos` unchanged
/// when the current opcode isn't `EX_SwitchValue`.
pub(crate) fn try_decode_switch(
    pos: &mut usize,
    range_end: usize,
    ctx: &DecodeCtx,
) -> Option<Stmt> {
    if *pos >= ctx.bytecode.len() {
        return None;
    }
    if ctx.bytecode[*pos] != EX_SWITCH_VALUE {
        return None;
    }

    let offset = *pos;
    let mut cursor = offset + 1;

    let num_cases = read_bc_u16(ctx.bytecode, &mut cursor) as usize;
    let _end_offset = read_bc_u32(ctx.bytecode, &mut cursor);

    // Index expression must decode cleanly. If it bottoms out as Unknown,
    // bail so the caller can fall back to a generic Unknown statement.
    let index_expr = decode_expr(&mut cursor, ctx);
    if matches!(index_expr, Expr::Unknown { .. }) {
        return None;
    }
    if cursor > range_end {
        return None;
    }

    let mut cases = Vec::with_capacity(num_cases);
    for _ in 0..num_cases {
        let case_value = decode_expr(&mut cursor, ctx);
        if cursor > range_end {
            return None;
        }
        // Per-case next_offset: we don't recurse into separate body
        // ranges because the case-result is itself a single
        // sub-expression in the EX_SwitchValue stream.
        let _next_offset = read_bc_u32(ctx.bytecode, &mut cursor);
        let case_result = decode_expr(&mut cursor, ctx);
        if cursor > range_end {
            return None;
        }
        cases.push(SwitchCase {
            values: vec![case_value],
            body: vec![Stmt::Assignment {
                lhs: Expr::Var("$switch_result".into()),
                rhs: case_result,
                offset,
            }],
        });
    }

    let default_expr = decode_expr(&mut cursor, ctx);
    if cursor > range_end {
        return None;
    }

    let default = match &default_expr {
        Expr::Var(name) if name.starts_with("$Select_Default") => None,
        Expr::Unknown { .. } => None,
        _ => Some(vec![Stmt::Assignment {
            lhs: Expr::Var("$switch_result".into()),
            rhs: default_expr,
            offset,
        }]),
    };

    *pos = cursor;
    Some(Stmt::Switch {
        expr: index_expr,
        cases,
        default,
        offset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::decode::test_fixtures::{
        empty_name_table, identity_map, stmt_kind, u32_le, ue4_ctx,
    };
    use crate::bytecode::opcodes::{
        EX_BYTE_CONST, EX_END_FUNCTION_PARMS, EX_INT_CONST, EX_NOTHING,
    };
    use crate::bytecode::stmt::Stmt;

    fn u16_le(value: u16) -> [u8; 2] {
        value.to_le_bytes()
    }

    /// Append an `EX_INT_CONST <value>` (5 bytes total) to `stream`.
    fn push_int_const(stream: &mut Vec<u8>, value: i32) {
        stream.push(EX_INT_CONST);
        stream.extend_from_slice(&value.to_le_bytes());
    }

    /// Append an `EX_BYTE_CONST <value>` (2 bytes total).
    fn push_byte_const(stream: &mut Vec<u8>, value: u8) {
        stream.push(EX_BYTE_CONST);
        stream.push(value);
    }

    /// Build a synthetic EX_SwitchValue stream:
    ///   EX_SWITCH_VALUE u16=num_cases u32=end_offset
    ///   <index_expr> [for each case: <case_value> u32=next <case_result>] <default>
    /// Returns (stream, end_offset_used).
    fn switch_stream(num_cases: u16, default: Option<i32>) -> Vec<u8> {
        let mut stream = vec![EX_SWITCH_VALUE];
        stream.extend_from_slice(&u16_le(num_cases));
        // Placeholder end_offset; we don't recurse into ranges so any
        // value works for these tests.
        stream.extend_from_slice(&u32_le(0xFFFF_FFFF));
        // Index expression: a byte literal so the test fixtures stay tiny.
        push_byte_const(&mut stream, 0xAB);
        for case_idx in 0..num_cases {
            // Case value: int literal (case index + 1).
            push_int_const(&mut stream, case_idx as i32 + 1);
            // Per-case next_offset placeholder.
            stream.extend_from_slice(&u32_le(0));
            // Case result: int literal (case index * 100 + 1).
            push_int_const(&mut stream, (case_idx as i32) * 100 + 1);
        }
        match default {
            Some(value) => push_int_const(&mut stream, value),
            None => stream.push(EX_NOTHING),
        }
        // Trailer so the stream isn't truncated when decode_expr peeks.
        stream.push(EX_END_FUNCTION_PARMS);
        stream
    }

    #[test]
    fn single_case_switch_with_default_decodes() {
        let stream = switch_stream(1, Some(999));
        let names = empty_name_table();
        let map = identity_map(&[0]);
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_switch(&mut pos, stream.len(), &ctx).expect("expected Stmt::Switch");

        match stmt {
            Stmt::Switch {
                expr,
                cases,
                default,
                offset,
            } => {
                assert_eq!(offset, 0);
                assert!(matches!(expr, Expr::Literal(_)));
                assert_eq!(cases.len(), 1);
                assert!(default.is_some());
                let default_body = default.unwrap();
                assert_eq!(default_body.len(), 1);
            }
            other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
        }
    }

    #[test]
    fn two_case_switch_decodes_both_cases() {
        let stream = switch_stream(2, Some(7));
        let names = empty_name_table();
        let map = identity_map(&[0]);
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_switch(&mut pos, stream.len(), &ctx).expect("expected Switch");
        match stmt {
            Stmt::Switch { cases, default, .. } => {
                assert_eq!(cases.len(), 2);
                assert!(default.is_some());
            }
            other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
        }
    }

    #[test]
    fn switch_with_select_default_omits_default() {
        // A default expression that resolves to "$Select_Default..." should
        // produce default = None. Using EX_NOTHING as the default for now,
        // which decodes as Unknown and also yields default = None.
        let stream = switch_stream(1, None);
        let names = empty_name_table();
        let map = identity_map(&[0]);
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let stmt = try_decode_switch(&mut pos, stream.len(), &ctx).expect("expected Switch");
        match stmt {
            Stmt::Switch { cases, default, .. } => {
                assert_eq!(cases.len(), 1);
                assert!(default.is_none());
            }
            other => panic!("expected Stmt::Switch, got {:?}", stmt_kind(&other)),
        }
    }

    #[test]
    fn non_switch_opcode_returns_none() {
        let stream = vec![EX_INT_CONST, 0x01, 0x00, 0x00, 0x00];
        let names = empty_name_table();
        let map = identity_map(&[0]);
        let ctx = ue4_ctx(&stream, &names, &map);

        let mut pos = 0;
        let result = try_decode_switch(&mut pos, stream.len(), &ctx);
        assert!(result.is_none());
        assert_eq!(pos, 0, "pos must not advance when the opcode mismatches");
    }
}
