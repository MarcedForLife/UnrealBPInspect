//! Verbose dump emitter for the decoded statement tree.
//!
//! Walks the decoded statement tree and renders a structured debug
//! representation showing each statement with its bytecode offset and
//! nested operands. Mirrors the spirit of the `output_text.rs` dump
//! but operates on the typed IR rather than raw export properties.

use std::fmt::Write;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::expr::{binary_op_symbol, unary_op_symbol, Expr};
use crate::bytecode::stmt::{LatchKind, LoopKind, Stmt, SwitchCase};

/// Emit a verbose debug dump of a decoded Blueprint (Unreal Blueprint) asset.
///
/// Each statement is printed with its bytecode offset, variant name, and
/// indented child nodes. Nested control-flow bodies are printed at a deeper
/// indent level so the tree structure is visually apparent.
pub fn emit_dump(asset: &DecodedAsset) -> String {
    let mut buf = String::new();
    writeln!(buf, "=== Blueprint Dump ===\n").unwrap();

    for function in &asset.functions {
        writeln!(buf, "function {} {{", function.name).unwrap();
        dump_stmts(&mut buf, &function.body, 1);
        writeln!(buf, "}}").unwrap();
        writeln!(buf).unwrap();
    }

    for event in &asset.events {
        writeln!(buf, "event {} {{", event.name).unwrap();
        dump_stmts(&mut buf, &event.body, 1);
        writeln!(buf, "}}").unwrap();
        writeln!(buf).unwrap();
    }

    // Trim trailing blank line after last block.
    if buf.ends_with("\n\n") {
        buf.truncate(buf.len() - 1);
    }

    buf
}

fn pad(indent_level: usize) -> String {
    "  ".repeat(indent_level)
}

fn dump_stmts(buf: &mut String, stmts: &[Stmt], indent_level: usize) {
    for stmt in stmts {
        dump_stmt(buf, stmt, indent_level);
    }
}

fn dump_stmt(buf: &mut String, stmt: &Stmt, indent_level: usize) {
    let prefix = pad(indent_level);
    match stmt {
        Stmt::Assignment { lhs, rhs, offset } => {
            writeln!(buf, "{}stmt 0x{:04x}: Assignment", prefix, offset).unwrap();
            writeln!(buf, "{}  lhs: {}", prefix, dump_expr(lhs)).unwrap();
            writeln!(buf, "{}  rhs: {}", prefix, dump_expr(rhs)).unwrap();
        }
        Stmt::Call { func, args, offset } => {
            writeln!(buf, "{}stmt 0x{:04x}: Call", prefix, offset).unwrap();
            writeln!(buf, "{}  func: {}", prefix, dump_expr(func)).unwrap();
            if args.is_empty() {
                writeln!(buf, "{}  args: (none)", prefix).unwrap();
            } else {
                writeln!(buf, "{}  args:", prefix).unwrap();
                for arg in args {
                    writeln!(buf, "{}    {}", prefix, dump_expr(arg)).unwrap();
                }
            }
        }
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            offset,
        } => {
            writeln!(buf, "{}stmt 0x{:04x}: Branch", prefix, offset).unwrap();
            writeln!(buf, "{}  cond: {}", prefix, dump_expr(cond)).unwrap();
            writeln!(buf, "{}  then:", prefix).unwrap();
            dump_stmts(buf, then_body, indent_level + 2);
            if !else_body.is_empty() {
                writeln!(buf, "{}  else:", prefix).unwrap();
                dump_stmts(buf, else_body, indent_level + 2);
            }
        }
        Stmt::Sequence { pins, offset } => {
            writeln!(
                buf,
                "{}stmt 0x{:04x}: Sequence ({} pins)",
                prefix,
                offset,
                pins.len()
            )
            .unwrap();
            for (pin_idx, pin_body) in pins.iter().enumerate() {
                writeln!(buf, "{}  pin {}:", prefix, pin_idx).unwrap();
                dump_stmts(buf, pin_body, indent_level + 2);
            }
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            offset,
        } => {
            let kind_label = loop_kind_label(kind);
            writeln!(
                buf,
                "{}stmt 0x{:04x}: Loop ({})",
                prefix, offset, kind_label
            )
            .unwrap();
            if let Some(cond_expr) = cond {
                writeln!(buf, "{}  cond: {}", prefix, dump_expr(cond_expr)).unwrap();
            }
            if let LoopKind::ForC { init, increment } = kind {
                if !init.is_empty() {
                    writeln!(buf, "{}  init:", prefix).unwrap();
                    dump_stmts(buf, init, indent_level + 2);
                }
                writeln!(buf, "{}  increment:", prefix).unwrap();
                dump_stmts(buf, increment, indent_level + 2);
            }
            if let LoopKind::ForEach { item, array } = kind {
                writeln!(buf, "{}  item: {}", prefix, item).unwrap();
                writeln!(buf, "{}  array: {}", prefix, dump_expr(array)).unwrap();
            }
            writeln!(buf, "{}  body:", prefix).unwrap();
            dump_stmts(buf, body, indent_level + 2);
            if let Some(completion_stmts) = completion {
                writeln!(buf, "{}  completion:", prefix).unwrap();
                dump_stmts(buf, completion_stmts, indent_level + 2);
            }
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            offset,
        } => {
            writeln!(
                buf,
                "{}stmt 0x{:04x}: Switch ({} cases)",
                prefix,
                offset,
                cases.len()
            )
            .unwrap();
            writeln!(buf, "{}  expr: {}", prefix, dump_expr(expr)).unwrap();
            dump_switch_cases(buf, cases, indent_level);
            if let Some(default_stmts) = default {
                writeln!(buf, "{}  default:", prefix).unwrap();
                dump_stmts(buf, default_stmts, indent_level + 2);
            }
        }
        Stmt::Latch {
            kind,
            init,
            body,
            offset,
        } => {
            let latch_label = latch_kind_label(kind);
            writeln!(
                buf,
                "{}stmt 0x{:04x}: Latch ({})",
                prefix, offset, latch_label
            )
            .unwrap();
            if !init.is_empty() {
                writeln!(buf, "{}  init:", prefix).unwrap();
                dump_stmts(buf, init, indent_level + 2);
            }
            writeln!(buf, "{}  body:", prefix).unwrap();
            dump_stmts(buf, body, indent_level + 2);
        }
        Stmt::Return { value, offset } => {
            writeln!(buf, "{}stmt 0x{:04x}: Return", prefix, offset).unwrap();
            if let Some(ret_expr) = value {
                writeln!(buf, "{}  value: {}", prefix, dump_expr(ret_expr)).unwrap();
            }
        }
        Stmt::EventCall { event_name, offset } => {
            writeln!(
                buf,
                "{}stmt 0x{:04x}: EventCall({})",
                prefix, offset, event_name
            )
            .unwrap();
        }
        Stmt::Break { offset } => {
            writeln!(buf, "{}stmt 0x{:04x}: Break", prefix, offset).unwrap();
        }
        Stmt::Unknown {
            reason,
            raw_bytes,
            offset,
            length,
        } => {
            writeln!(
                buf,
                "{}stmt 0x{:04x}: Unknown ({} bytes, reason: {})",
                prefix, offset, length, reason
            )
            .unwrap();
            if !raw_bytes.is_empty() {
                let hex: Vec<String> = raw_bytes
                    .iter()
                    .map(|byte| format!("{:02x}", byte))
                    .collect();
                writeln!(buf, "{}  bytes: {}", prefix, hex.join(" ")).unwrap();
            }
        }
    }
}

fn dump_switch_cases(buf: &mut String, cases: &[SwitchCase], indent_level: usize) {
    let prefix = pad(indent_level);
    for case in cases {
        let rendered_values: Vec<String> = case.values.iter().map(dump_expr).collect();
        writeln!(buf, "{}  case {}:", prefix, rendered_values.join(", ")).unwrap();
        dump_stmts(buf, &case.body, indent_level + 2);
    }
}

/// Render an expression as a compact single-line string for dump output.
///
/// Handles all Expr variants: literals, variables, calls, operators, casts,
/// containers, struct construction, and diagnostic escapes.
fn dump_expr(expr: &Expr) -> String {
    match expr {
        Expr::Literal(text) => format!("Literal({:?})", text),
        Expr::Var(name) => format!("Var({:?})", name),
        Expr::Call { name, args } => {
            let rendered_args = args_to_string(args);
            format!("Call({:?}, [{}])", name, rendered_args)
        }
        Expr::MethodCall { recv, name, args } => {
            let rendered_args = args_to_string(args);
            format!(
                "MethodCall({}.{:?}, [{}])",
                dump_expr(recv),
                name,
                rendered_args
            )
        }
        Expr::FieldAccess { recv, field } => {
            format!("FieldAccess({}.{:?})", dump_expr(recv), field)
        }
        Expr::Index { recv, idx } => {
            format!("Index({}[{}])", dump_expr(recv), dump_expr(idx))
        }
        Expr::Binary { op, lhs, rhs } => {
            format!(
                "Binary({} {} {})",
                dump_expr(lhs),
                binary_op_symbol(*op),
                dump_expr(rhs)
            )
        }
        Expr::Unary { op, operand } => {
            format!("Unary({} {})", unary_op_symbol(*op), dump_expr(operand))
        }
        Expr::Cast { kind, inner } => {
            format!("Cast({:?}, {})", kind, dump_expr(inner))
        }
        Expr::ArrayLit(items) => {
            let rendered_items = items.iter().map(dump_expr).collect::<Vec<_>>().join(", ");
            format!("ArrayLit([{}])", rendered_items)
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            format!(
                "Ternary({} ? {} : {})",
                dump_expr(cond),
                dump_expr(then_expr),
                dump_expr(else_expr)
            )
        }
        Expr::Switch {
            index,
            cases,
            default,
        } => {
            let case_strs: Vec<String> = cases
                .iter()
                .map(|case| {
                    format!(
                        "Case({}, {})",
                        dump_expr(&case.value),
                        dump_expr(&case.body)
                    )
                })
                .collect();
            format!(
                "Switch({}, [{}], default={})",
                dump_expr(index),
                case_strs.join(", "),
                dump_expr(default)
            )
        }
        Expr::Out(inner) => format!("Out({})", dump_expr(inner)),
        Expr::Interface(inner) => format!("Interface({})", dump_expr(inner)),
        Expr::Persistent(inner) => format!("Persistent({})", dump_expr(inner)),
        Expr::Resume { inner, target } => {
            format!("Resume({}, 0x{:x})", dump_expr(inner), target)
        }
        Expr::StructConstruct { type_name, fields } => {
            let rendered_fields = fields
                .iter()
                .map(|(field_name, field_val)| format!("{}={}", field_name, dump_expr(field_val)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("StructConstruct({:?}, {{{}}})", type_name, rendered_fields)
        }
        Expr::Unknown { reason, offset, .. } => {
            format!("Unknown({:?} @ 0x{:04x})", reason, offset)
        }
    }
}

fn args_to_string(args: &[Expr]) -> String {
    args.iter().map(dump_expr).collect::<Vec<_>>().join(", ")
}

fn loop_kind_label(kind: &LoopKind) -> &'static str {
    match kind {
        LoopKind::While => "while",
        LoopKind::ForC { .. } => "for-c",
        LoopKind::ForEach { .. } => "foreach",
    }
}

fn latch_kind_label(kind: &LatchKind) -> String {
    match kind {
        LatchKind::DoOnce { name, .. } => format!("DoOnce({})", name),
        LatchKind::FlipFlop { gate_var, .. } => format!("FlipFlop({})", gate_var),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::asset::{DecodedAsset, Event, Function};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    fn empty_asset() -> DecodedAsset {
        DecodedAsset {
            functions: vec![],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        }
    }

    #[test]
    fn empty_asset_emits_header_only() {
        let output = emit_dump(&empty_asset());
        assert!(output.contains("=== Blueprint Dump ==="));
        // No function or event blocks should appear.
        assert!(!output.contains("function"));
        assert!(!output.contains("event"));
    }

    #[test]
    fn single_function_with_assignment() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "TestFunc".into(),
                export_index: None,
                body: vec![Stmt::Assignment {
                    lhs: Expr::Var("x".into()),
                    rhs: Expr::Literal("5".into()),
                    offset: 0x0010,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let output = emit_dump(&asset);
        assert!(output.contains("function TestFunc {"));
        assert!(output.contains("stmt 0x0010: Assignment"));
        assert!(output.contains("lhs: Var(\"x\")"));
        assert!(output.contains("rhs: Literal(\"5\")"));
    }

    #[test]
    fn nested_branch_indents_correctly() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "BranchFunc".into(),
                export_index: None,
                body: vec![Stmt::Branch {
                    cond: Expr::Var("flag".into()),
                    then_body: vec![Stmt::Return {
                        value: None,
                        offset: 0x0030,
                    }],
                    else_body: vec![],
                    offset: 0x0020,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let output = emit_dump(&asset);
        assert!(output.contains("stmt 0x0020: Branch"));
        assert!(output.contains("cond: Var(\"flag\")"));
        assert!(output.contains("then:"));
        assert!(output.contains("stmt 0x0030: Return"));
        // then body is at deeper indent than the branch itself
        let branch_line = output
            .lines()
            .find(|line| line.contains("stmt 0x0020"))
            .unwrap();
        let return_line = output
            .lines()
            .find(|line| line.contains("stmt 0x0030"))
            .unwrap();
        let branch_indent = branch_line.len() - branch_line.trim_start().len();
        let return_indent = return_line.len() - return_line.trim_start().len();
        assert!(
            return_indent > branch_indent,
            "return should be indented more than branch"
        );
    }

    #[test]
    fn call_with_no_args_shows_none() {
        let asset = DecodedAsset {
            functions: vec![Function {
                name: "CallFunc".into(),
                export_index: None,
                body: vec![Stmt::Call {
                    func: Expr::Var("DoSomething".into()),
                    args: vec![],
                    offset: 0x0000,
                }],
            }],
            events: vec![],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let output = emit_dump(&asset);
        assert!(output.contains("stmt 0x0000: Call"));
        assert!(output.contains("func: Var(\"DoSomething\")"));
        assert!(output.contains("args: (none)"));
    }

    #[test]
    fn event_block_emits_correctly() {
        let asset = DecodedAsset {
            functions: vec![],
            events: vec![Event {
                name: "OnBeginPlay".into(),
                export_index: None,
                body: vec![Stmt::Return {
                    value: None,
                    offset: 0x0000,
                }],
            }],
            resume_bodies: std::collections::BTreeMap::new(),
        };
        let output = emit_dump(&asset);
        assert!(output.contains("event OnBeginPlay {"));
        assert!(output.contains("stmt 0x0000: Return"));
    }
}
