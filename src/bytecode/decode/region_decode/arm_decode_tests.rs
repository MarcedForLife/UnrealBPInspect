//! Compare structured traces with bytecode execution for acyclic flow.

use super::*;
use crate::binary::NameTable;
use crate::bytecode::decode::test_fixtures::put_field_path;
use crate::bytecode::expr::{BinaryOp, LiteralValue, UnaryOp};
use crate::bytecode::opcodes::*;

fn names() -> NameTable {
    NameTable::from_names(
        [
            "Path",
            "Near",
            "Ready",
            "Mode",
            "Valid",
            "Cue",
            "Counter",
            "InnerCounter",
            "Limit",
            "InnerLimit",
            "Temp_bool_IsClosed_Variable_1",
            "Temp_bool_IsClosed_Variable_2",
            "Temp_bool_Variable_7",
            "Temp_bool_Has_Been_Initd_Variable_1",
            "Temp_bool_Has_Been_Initd_Variable_2",
        ]
        .map(String::from)
        .to_vec(),
    )
}

fn exports() -> Vec<String> {
    [
        "Prepare",
        "Update",
        "Commit",
        "Notify",
        "Accumulate",
        "Primary",
        "Secondary",
        "Missing",
        "EqualEqual_IntInt",
        "Less_IntInt",
        "Add_IntInt",
        "Not_PreBool",
        "Visit",
        "InnerComplete",
        "OuterComplete",
    ]
    .map(String::from)
    .to_vec()
}

fn call(stream: &mut Vec<u8>, export_index: i32) {
    stream.push(EX_CALL_MATH);
    stream.extend(export_index.to_le_bytes());
    stream.push(EX_END_FUNCTION_PARMS);
}

fn jump(stream: &mut Vec<u8>, opcode: u8) -> usize {
    let offset = stream.len();
    stream.push(opcode);
    stream.extend([0; 4]);
    offset
}

fn branch(stream: &mut Vec<u8>, name_index: i32) -> usize {
    let offset = jump(stream, EX_JUMP_IF_NOT);
    stream.push(EX_LOCAL_VARIABLE);
    put_field_path(stream, name_index);
    offset
}

fn patch(stream: &mut [u8], offset: usize, target: usize) {
    stream[offset + 1..offset + 5].copy_from_slice(&(target as u32).to_le_bytes());
}

fn finish(stream: &mut Vec<u8>) -> usize {
    let offset = stream.len();
    stream.extend([EX_RETURN, EX_NOTHING, EX_END_OF_SCRIPT]);
    offset
}

fn evaluate(expr: &Expr, values: &BTreeMap<String, i64>) -> i64 {
    match expr {
        Expr::Var(name) => *values
            .get(name)
            .unwrap_or_else(|| panic!("undefined {name}")),
        Expr::Literal(LiteralValue::Text(value)) => match value.as_str() {
            "true" => 1,
            "false" => 0,
            _ => value.parse().unwrap(),
        },
        Expr::Call { name, args } => match name.as_str() {
            "EqualEqual_IntInt" => {
                i64::from(evaluate(&args[0], values) == evaluate(&args[1], values))
            }
            "Less_IntInt" => i64::from(evaluate(&args[0], values) < evaluate(&args[1], values)),
            "Add_IntInt" => evaluate(&args[0], values) + evaluate(&args[1], values),
            "Not_PreBool" => i64::from(evaluate(&args[0], values) == 0),
            "Array_Length" => evaluate(&args[0], values),
            _ => panic!("unsupported test expression {expr:?}"),
        },
        Expr::Binary { op, lhs, rhs } => match op {
            BinaryOp::Eq => i64::from(evaluate(lhs, values) == evaluate(rhs, values)),
            BinaryOp::Lt => i64::from(evaluate(lhs, values) < evaluate(rhs, values)),
            BinaryOp::Add => evaluate(lhs, values) + evaluate(rhs, values),
            BinaryOp::And => i64::from(evaluate(lhs, values) != 0 && evaluate(rhs, values) != 0),
            _ => panic!("unsupported test operator {op:?}"),
        },
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
        } => i64::from(evaluate(operand, values) == 0),
        Expr::Index { recv, idx } => {
            let index = evaluate(idx, values);
            assert!((0..evaluate(recv, values)).contains(&index));
            index
        }
        _ => panic!("unsupported test expression {expr:?}"),
    }
}

/// Some(true) returns from the function, Some(false) breaks the current loop.
fn execute(
    body: &[Stmt],
    values: &mut BTreeMap<String, i64>,
    trace: &mut Vec<String>,
) -> Option<bool> {
    for stmt in body {
        let control = match stmt {
            Stmt::Assignment {
                lhs: Expr::Var(name),
                rhs,
                ..
            } => {
                values.insert(name.clone(), evaluate(rhs, values));
                None
            }
            Stmt::Call {
                func: Expr::Var(name),
                args,
                ..
            } if name == "ResetDoOnce" => {
                let Expr::Var(target) = &args[0] else {
                    panic!("expected gate identifier")
                };
                let suffix = target
                    .strip_prefix("DoOnce_")
                    .expect("canonical reset gate");
                values.insert(format!("Temp_bool_IsClosed_Variable_{suffix}"), 0);
                None
            }
            Stmt::Call {
                func: Expr::Var(name),
                args,
                ..
            } => {
                let arguments: Vec<_> = args.iter().map(|arg| evaluate(arg, values)).collect();
                trace.push(if args.is_empty() {
                    name.clone()
                } else {
                    format!("{name}{arguments:?}")
                });
                None
            }
            Stmt::Branch {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let selected = if evaluate(cond, values) != 0 {
                    then_body
                } else {
                    else_body
                };
                execute(selected, values, trace)
            }
            Stmt::Switch {
                expr,
                cases,
                default,
                ..
            } => {
                let selected = evaluate(expr, values);
                let body = cases
                    .iter()
                    .find(|case| {
                        case.values
                            .iter()
                            .any(|value| evaluate(value, values) == selected)
                    })
                    .map(|case| case.body.as_slice())
                    .or(default.as_deref())
                    .unwrap_or(&[]);
                execute(body, values, trace)
            }
            Stmt::Sequence { pins, .. } => {
                let mut control = None;
                for pin in pins {
                    control = execute(pin, values, trace);
                    if control.is_some() {
                        break;
                    }
                }
                control
            }
            Stmt::Loop {
                kind,
                cond,
                body,
                completion,
                ..
            } => execute_loop(
                kind,
                cond.as_ref(),
                body,
                completion.as_deref(),
                values,
                trace,
            ),
            Stmt::Latch {
                kind, init, body, ..
            } => {
                if let Some(control) = execute(init, values, trace) {
                    return Some(control);
                }
                match kind {
                    crate::bytecode::stmt::LatchKind::DoOnce { gate_var, .. } => {
                        if values.get(gate_var).copied().unwrap_or(0) == 0 {
                            values.insert(gate_var.clone(), 1);
                            execute(body, values, trace)
                        } else {
                            None
                        }
                    }
                    crate::bytecode::stmt::LatchKind::FlipFlop { gate_var, .. } => {
                        let toggled = i64::from(values.get(gate_var).copied().unwrap_or(0) == 0);
                        values.insert(gate_var.clone(), toggled);
                        execute(body, values, trace)
                    }
                }
            }
            Stmt::Return { .. } => Some(true),
            Stmt::Break { .. } => Some(false),
            _ => panic!(
                "unsupported test statement {}",
                serde_json::to_string(stmt).unwrap()
            ),
        };
        if control.is_some() {
            return control;
        }
    }
    None
}

fn execute_loop(
    kind: &crate::bytecode::stmt::LoopKind,
    cond: Option<&Expr>,
    body: &[Stmt],
    completion: Option<&[Stmt]>,
    values: &mut BTreeMap<String, i64>,
    trace: &mut Vec<String>,
) -> Option<bool> {
    use crate::bytecode::stmt::LoopKind;
    if let LoopKind::ForC { init, .. } = kind {
        if let Some(control) = execute(init, values, trace) {
            return Some(control);
        }
    }
    let count = if let LoopKind::ForEach { array, .. } = kind {
        evaluate(array, values)
    } else {
        100
    };
    for iteration in 0..=100 {
        assert!(iteration < 100, "structured loop did not terminate");
        if matches!(kind, LoopKind::ForEach { .. }) && iteration >= count {
            break;
        }
        if cond.is_some_and(|cond| evaluate(cond, values) == 0) {
            break;
        }
        if let LoopKind::ForEach { item, .. } = kind {
            values.insert(item.clone(), iteration);
        }
        match execute(body, values, trace) {
            Some(true) => return Some(true),
            Some(false) => break,
            None => {}
        }
        if let LoopKind::ForC { increment, .. } = kind {
            if let Some(control) = execute(increment, values, trace) {
                return Some(control);
            }
        }
    }
    completion.and_then(|body| execute(body, values, trace))
}

fn bytecode_trace(ctx: &DecodeCtx, values: &mut BTreeMap<String, i64>) -> Vec<String> {
    let mut cursor = 0;
    let mut stack = Vec::new();
    let mut trace = Vec::new();
    for _ in 0..1000 {
        let opcode = ctx.bytecode[cursor];
        match opcode {
            EX_RETURN | EX_END_OF_SCRIPT => return trace,
            EX_JUMP | EX_PUSH_EXECUTION_FLOW | EX_JUMP_IF_NOT => {
                let target =
                    u32::from_le_bytes(ctx.bytecode[cursor + 1..cursor + 5].try_into().unwrap())
                        as usize;
                cursor += 5;
                match opcode {
                    EX_JUMP => cursor = target,
                    EX_PUSH_EXECUTION_FLOW => stack.push(target),
                    _ => {
                        let cond = decode_expr(&mut cursor, ctx);
                        if evaluate(&cond, values) == 0 {
                            cursor = target;
                        }
                    }
                }
            }
            EX_POP_EXECUTION_FLOW => match stack.pop() {
                Some(target) => cursor = target,
                None => return trace,
            },
            EX_POP_FLOW_IF_NOT => {
                cursor += 1;
                let cond = decode_expr(&mut cursor, ctx);
                if evaluate(&cond, values) == 0 {
                    match stack.pop() {
                        Some(target) => cursor = target,
                        None => return trace,
                    }
                }
            }
            _ => {
                let stmt = crate::bytecode::decode::block::decode_one(&mut cursor, ctx)
                    .ok()
                    .flatten()
                    .unwrap();
                assert!(execute(&[stmt], values, &mut trace).is_none());
            }
        }
    }
    panic!("test bytecode did not terminate")
}

fn decode_program(
    stream: &[u8],
    values: &mut BTreeMap<String, i64>,
    acyclic: bool,
) -> (Vec<Stmt>, Vec<String>) {
    let names = names();
    let exports = exports();
    let mapping = (0..stream.len()).map(|offset| (offset, offset)).collect();
    let graph = crate::bytecode::partition::build_opcode_graph(stream, 0, &names, &mapping);
    let (cfg, regions, ranges) =
        crate::bytecode::decode::orchestrate::build_event_cfg_and_region_tree(
            0,
            std::slice::from_ref(&(0..stream.len())),
            &graph,
            stream,
            0,
            &names,
            &mapping,
        );
    let ctx = DecodeCtx {
        mem_to_disk: Some(&mapping),
        graph: Some(&graph),
        cfg: Some(&cfg),
        region_tree: Some(&regions),
        region_byte_ranges: Some(&ranges),
        ..DecodeCtx::new(stream, &names, &[], &exports, 0)
    };
    let skeleton = crate::bytecode::structure::build_skeleton(
        stream,
        0,
        &names,
        &mapping,
        0..stream.len(),
        &[],
        Some(&graph),
    );
    let ctx = DecodeCtx {
        skeleton: Some(&skeleton),
        ..ctx
    };
    let reference = bytecode_trace(&ctx, values);
    if acyclic {
        assert!(
            decode_acyclic_body(&cfg, &ctx).is_some(),
            "expected acyclic decoder"
        );
    }
    (decode_region_tree(&regions, &cfg, &ctx), reference)
}

fn assert_traces(stream: &[u8], values: &[(&str, i64)], expected: &[&str]) -> Vec<Stmt> {
    let values: BTreeMap<_, _> = values
        .iter()
        .map(|(name, value)| (name.to_string(), *value))
        .collect();
    let (decoded, reference) = decode_program(stream, &mut values.clone(), true);
    assert_eq!(reference, expected);
    for transform in [false, true] {
        let mut body = decoded.clone();
        if transform {
            crate::bytecode::decode::apply_transform_stack_to_body(&mut body);
        }
        let mut trace = Vec::new();
        execute(&body, &mut values.clone(), &mut trace);
        assert_eq!(
            trace,
            reference,
            "structured body {}",
            serde_json::to_string(&body).unwrap()
        );
    }
    decoded
}

#[test]
fn partial_convergence_keeps_commit_inside_both_range_gates() {
    let mut stream = Vec::new();
    let choose = branch(&mut stream, 0);
    let near_first = branch(&mut stream, 1);
    let commit_first = jump(&mut stream, EX_JUMP);
    let alternate = stream.len();
    let ready = branch(&mut stream, 2);
    let update = stream.len();
    call(&mut stream, 2);
    let near_second = branch(&mut stream, 1);
    let commit_second = jump(&mut stream, EX_JUMP);
    let prepare = stream.len();
    call(&mut stream, 1);
    let prepared = jump(&mut stream, EX_JUMP);
    let commit = stream.len();
    call(&mut stream, 3);
    let exit = finish(&mut stream);
    for (offset, target) in [
        (choose, alternate),
        (near_first, exit),
        (commit_first, commit),
        (ready, prepare),
        (near_second, exit),
        (commit_second, commit),
        (prepared, update),
    ] {
        patch(&mut stream, offset, target);
    }
    for path in [0, 1] {
        for near in [0, 1] {
            for ready in [0, 1] {
                let mut expected = Vec::new();
                if path == 0 {
                    if ready == 0 {
                        expected.push("Prepare");
                    }
                    expected.push("Update");
                }
                if near != 0 {
                    expected.push("Commit");
                }
                assert_traces(
                    &stream,
                    &[("Path", path), ("Near", near), ("Ready", ready)],
                    &expected,
                );
            }
        }
    }
}

#[test]
fn optional_cleanup_does_not_guard_its_shared_continuation() {
    let mut stream = Vec::new();
    let gate = branch(&mut stream, 2);
    call(&mut stream, 1);
    let continuation = stream.len();
    call(&mut stream, 3);
    finish(&mut stream);
    patch(&mut stream, gate, continuation);
    assert_traces(&stream, &[("Ready", 0)], &["Commit"]);
    assert_traces(&stream, &[("Ready", 1)], &["Prepare", "Commit"]);
}

#[test]
fn switch_arms_keep_their_shared_notification() {
    let mut stream = Vec::new();
    let mut conditions = Vec::new();
    for value in 0i32..3 {
        let offset = jump(&mut stream, EX_JUMP_IF_NOT);
        stream.push(EX_CALL_MATH);
        stream.extend(9i32.to_le_bytes());
        stream.push(EX_LOCAL_VARIABLE);
        put_field_path(&mut stream, 3);
        stream.push(EX_INT_CONST);
        stream.extend(value.to_le_bytes());
        stream.push(EX_END_FUNCTION_PARMS);
        call(&mut stream, value + 1);
        conditions.push((offset, jump(&mut stream, EX_JUMP)));
    }
    let no_match = jump(&mut stream, EX_JUMP);
    let notify = stream.len();
    call(&mut stream, 4);
    let exit = finish(&mut stream);
    for (index, (condition, matched)) in conditions.iter().enumerate() {
        let next = conditions.get(index + 1).map_or(no_match, |pair| pair.0);
        patch(&mut stream, *condition, next);
        patch(&mut stream, *matched, notify);
    }
    patch(&mut stream, no_match, exit);
    for (mode, expected) in [
        (0, vec!["Prepare", "Notify"]),
        (1, vec!["Update", "Notify"]),
        (2, vec!["Commit", "Notify"]),
        (3, vec![]),
    ] {
        assert_traces(&stream, &[("Mode", mode)], &expected);
    }
}

#[test]
fn stack_sequence_preserves_order_and_nested_failure_scopes() {
    let mut stream = Vec::new();
    let sequence = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let displaced = jump(&mut stream, EX_JUMP);
    let select = stream.len();
    stream.push(EX_POP_FLOW_IF_NOT);
    stream.push(EX_LOCAL_VARIABLE);
    put_field_path(&mut stream, 1);
    let valid = branch(&mut stream, 4);
    let cue = branch(&mut stream, 5);
    call(&mut stream, 6);
    stream.push(EX_POP_EXECUTION_FLOW);
    let alternative = stream.len();
    call(&mut stream, 7);
    stream.push(EX_POP_EXECUTION_FLOW);
    let missing = stream.len();
    call(&mut stream, 8);
    stream.push(EX_POP_EXECUTION_FLOW);
    let accumulation = stream.len();
    call(&mut stream, 5);
    stream.push(EX_POP_EXECUTION_FLOW);
    stream.push(EX_END_OF_SCRIPT);
    for (offset, target) in [
        (sequence, select),
        (displaced, accumulation),
        (valid, missing),
        (cue, alternative),
    ] {
        patch(&mut stream, offset, target);
    }
    for near in [0, 1] {
        for valid in [0, 1] {
            for cue in [0, 1] {
                let mut expected = vec!["Accumulate"];
                if near != 0 {
                    expected.push(if valid == 0 {
                        "Missing"
                    } else if cue == 0 {
                        "Secondary"
                    } else {
                        "Primary"
                    });
                }
                assert_traces(
                    &stream,
                    &[("Near", near), ("Valid", valid), ("Cue", cue)],
                    &expected,
                );
            }
        }
    }
}

fn assert_declines_without_claims(stream: &[u8]) {
    let names = names();
    let exports = exports();
    let mapping = (0..stream.len()).map(|offset| (offset, offset)).collect();
    let graph = crate::bytecode::partition::build_opcode_graph(stream, 0, &names, &mapping);
    let cfg =
        crate::bytecode::cfg::build::build_cfg(&graph, 0, std::slice::from_ref(&(0..stream.len())));
    let claims = std::cell::RefCell::new(BTreeMap::new());
    let ctx = DecodeCtx {
        mem_to_disk: Some(&mapping),
        graph: Some(&graph),
        cfg: Some(&cfg),
        claimed: Some(&claims),
        ..DecodeCtx::new(stream, &names, &[], &exports, 0)
    };
    assert!(decode_acyclic_body(&cfg, &ctx).is_none());
    assert!(claims.borrow().is_empty());
    assert!(ctx.dispatched_loop_regions.borrow().is_empty());
    assert!(ctx.arm_descent_stops.borrow().is_empty());
}

#[test]
fn cyclic_and_unbounded_flow_stack_paths_decline_without_claims() {
    let mut cycle = Vec::new();
    let condition = branch(&mut cycle, 0);
    call(&mut cycle, 1);
    let back_edge = jump(&mut cycle, EX_JUMP);
    let exit = finish(&mut cycle);
    patch(&mut cycle, condition, exit);
    patch(&mut cycle, back_edge, 0);
    assert_declines_without_claims(&cycle);

    let mut growing_stack = Vec::new();
    let pushed = jump(&mut growing_stack, EX_PUSH_EXECUTION_FLOW);
    let condition = branch(&mut growing_stack, 0);
    let back_edge = jump(&mut growing_stack, EX_JUMP);
    let exit = finish(&mut growing_stack);
    patch(&mut growing_stack, pushed, exit);
    patch(&mut growing_stack, condition, exit);
    patch(&mut growing_stack, back_edge, 0);
    assert_declines_without_claims(&growing_stack);
}

#[test]
fn deep_branch_nesting_declines_before_exhausting_the_native_stack() {
    let mut stream = Vec::new();
    let conditions: Vec<_> = (0..130).map(|_| branch(&mut stream, 0)).collect();
    call(&mut stream, 1);
    let exit = finish(&mut stream);
    for offset in conditions {
        patch(&mut stream, offset, exit);
    }
    assert_declines_without_claims(&stream);
}

#[test]
fn conditional_with_missing_target_declines_without_claims() {
    let mut stream = Vec::new();
    let condition = branch(&mut stream, 0);
    call(&mut stream, 1);
    finish(&mut stream);
    patch(&mut stream, condition, usize::from(u16::MAX));
    assert_declines_without_claims(&stream);
}

#[test]
fn mixed_three_pin_sequence_keeps_identity_and_restores_empty_editor_slot() {
    let mut stream = Vec::new();
    let first_push = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let first_jump = jump(&mut stream, EX_JUMP);
    let second_push = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let second_jump = jump(&mut stream, EX_JUMP);
    let last = stream.len();
    call(&mut stream, 4);
    stream.push(EX_POP_EXECUTION_FLOW);
    let first = stream.len();
    let conditional = branch(&mut stream, 4);
    call(&mut stream, 6);
    let first_end = stream.len();
    stream.push(EX_POP_EXECUTION_FLOW);
    let middle = stream.len();
    call(&mut stream, 7);
    stream.extend([EX_POP_EXECUTION_FLOW, EX_END_OF_SCRIPT]);
    for (offset, target) in [
        (first_push, second_push),
        (first_jump, first),
        (second_push, last),
        (second_jump, middle),
        (conditional, first_end),
    ] {
        patch(&mut stream, offset, target);
    }
    let mut body = assert_traces(
        &stream,
        &[("Valid", 1)],
        &["Primary", "Secondary", "Notify"],
    );
    assert_traces(&stream, &[("Valid", 0)], &["Secondary", "Notify"]);
    crate::bytecode::decode::apply_transform_stack_to_body(&mut body);
    let [Stmt::Sequence { pins, offset }] = body.as_slice() else {
        panic!("expected one sequence")
    };
    assert_eq!(*offset, first_push);
    assert_eq!(pins.len(), 3);
    assert!(matches!(pins[0].as_slice(), [Stmt::Branch { .. }]));
    crate::bytecode::decode::orchestrate::restore_sequence_pins(
        &mut body,
        &[true, false, true, true],
    );
    let [Stmt::Sequence { pins, offset }] = body.as_slice() else {
        panic!("expected retained sequence")
    };
    assert_eq!(*offset, first_push);
    assert_eq!(pins.len(), 4);
    assert!(pins[1].is_empty());
    let mut trace = Vec::new();
    execute(
        &body,
        &mut BTreeMap::from([("Valid".into(), 1)]),
        &mut trace,
    );
    assert_eq!(trace, ["Primary", "Secondary", "Notify"]);
}

#[test]
fn early_return_inside_first_pin_does_not_execute_later_pins() {
    let mut stream = Vec::new();
    let next_pin = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let gate = branch(&mut stream, 4);
    stream.extend([EX_RETURN, EX_NOTHING]);
    let active = stream.len();
    call(&mut stream, 1);
    stream.push(EX_POP_EXECUTION_FLOW);
    let later = stream.len();
    call(&mut stream, 2);
    stream.extend([EX_POP_EXECUTION_FLOW, EX_END_OF_SCRIPT]);
    patch(&mut stream, next_pin, later);
    patch(&mut stream, gate, active);
    assert_traces(&stream, &[("Valid", 1)], &[]);
    assert_traces(&stream, &[("Valid", 0)], &["Prepare", "Update"]);
}

fn local(name_index: i32) -> Vec<u8> {
    let mut bytes = vec![EX_LOCAL_VARIABLE];
    put_field_path(&mut bytes, name_index);
    bytes
}

fn integer(value: i32) -> Vec<u8> {
    let mut bytes = vec![EX_INT_CONST];
    bytes.extend(value.to_le_bytes());
    bytes
}

fn math(export_index: i32, arguments: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = vec![EX_CALL_MATH];
    bytes.extend(export_index.to_le_bytes());
    for argument in arguments {
        bytes.extend(argument);
    }
    bytes.push(EX_END_FUNCTION_PARMS);
    bytes
}

fn assignment(stream: &mut Vec<u8>, name_index: i32, value: Vec<u8>) {
    if name_index >= 10 {
        stream.push(EX_LET_BOOL);
    } else {
        stream.push(EX_LET);
        put_field_path(stream, name_index);
    }
    stream.extend(local(name_index));
    stream.extend(value);
}

fn doonce_program(gates: &[i32]) -> Vec<u8> {
    let mut stream = Vec::new();
    let mut exits = Vec::new();
    for gate in gates {
        exits.push(jump(&mut stream, EX_JUMP_IF_NOT));
        stream.extend(math(12, &[local(*gate)]));
        assignment(&mut stream, *gate, vec![EX_TRUE]);
    }
    call(&mut stream, 6);
    let exit = finish(&mut stream);
    for conditional in exits {
        patch(&mut stream, conditional, exit);
    }
    stream
}

fn reset_program(gate: i32, initialized: i32) -> Vec<u8> {
    let mut stream = Vec::new();
    assignment(&mut stream, gate, vec![EX_FALSE]);
    assignment(&mut stream, initialized, vec![EX_TRUE]);
    finish(&mut stream);
    stream
}

fn initial_state() -> BTreeMap<String, i64> {
    [
        "Counter",
        "InnerCounter",
        "Limit",
        "InnerLimit",
        "Temp_bool_IsClosed_Variable_1",
        "Temp_bool_IsClosed_Variable_2",
        "Temp_bool_Variable_7",
        "Temp_bool_Has_Been_Initd_Variable_1",
        "Temp_bool_Has_Been_Initd_Variable_2",
    ]
    .map(|name| (name.to_string(), 0))
    .into_iter()
    .collect()
}

fn assert_invocations(
    programs: &[Vec<u8>],
    invocations: &[usize],
    initial: BTreeMap<String, i64>,
    expected: &[&str],
    acyclic: bool,
) -> Vec<Vec<Stmt>> {
    let mut reference_state = initial.clone();
    let mut decoded_state = initial.clone();
    let mut transformed_state = initial;
    let mut reference_trace = Vec::new();
    let mut decoded_trace = Vec::new();
    let mut transformed_trace = Vec::new();
    let mut transformed = Vec::new();
    for program in programs {
        let (mut body, _) = decode_program(program, &mut reference_state.clone(), acyclic);
        crate::bytecode::decode::apply_transform_stack_to_body(&mut body);
        transformed.push(body);
    }
    for invocation in invocations {
        let (decoded, trace) =
            decode_program(&programs[*invocation], &mut reference_state, acyclic);
        reference_trace.extend(trace);
        execute(&decoded, &mut decoded_state, &mut decoded_trace);
        execute(
            &transformed[*invocation],
            &mut transformed_state,
            &mut transformed_trace,
        );
        assert_eq!(
            decoded_trace,
            reference_trace,
            "decoded event {invocation}: {}",
            serde_json::to_string(&decoded).unwrap()
        );
        assert_eq!(
            transformed_trace,
            reference_trace,
            "transformed event {invocation}: {}",
            serde_json::to_string(&transformed[*invocation]).unwrap()
        );
        for name in [
            "Counter",
            "InnerCounter",
            "Temp_bool_IsClosed_Variable_1",
            "Temp_bool_IsClosed_Variable_2",
            "Temp_bool_Variable_7",
        ] {
            assert_eq!(
                transformed_state[name], reference_state[name],
                "state {name} after event {invocation}"
            );
        }
    }
    assert_eq!(reference_trace, expected);
    transformed
}

#[test]
fn shared_doonce_entries_and_independent_resets_preserve_state_across_invocations() {
    let programs = [
        doonce_program(&[10]),
        doonce_program(&[10]),
        doonce_program(&[11]),
        reset_program(10, 13),
        reset_program(11, 14),
    ];
    for first_closed in [0, 1] {
        for second_closed in [0, 1] {
            let mut initial = initial_state();
            initial.insert("Temp_bool_IsClosed_Variable_1".into(), first_closed);
            initial.insert("Temp_bool_IsClosed_Variable_2".into(), second_closed);
            let expected = vec!["Primary"; (4 - first_closed - second_closed) as usize];
            let bodies = assert_invocations(
                &programs,
                &[0, 1, 2, 0, 3, 1, 2, 4, 2],
                initial,
                &expected,
                true,
            );
            assert!(bodies[0].iter().any(|stmt| matches!(
                stmt,
                Stmt::Latch {
                    kind: LatchKind::DoOnce { .. },
                    ..
                }
            )));
            assert!(bodies[3].iter().any(|stmt| matches!(stmt, Stmt::Call { func: Expr::Var(name), .. } if name == "ResetDoOnce")));
        }
    }
}

#[test]
fn nested_doonce_gates_require_both_resets_before_the_body_runs_again() {
    let programs = [
        doonce_program(&[10, 11]),
        reset_program(10, 13),
        reset_program(11, 14),
    ];
    assert_invocations(
        &programs,
        &[0, 0, 1, 0, 2, 0, 1, 0],
        initial_state(),
        &["Primary", "Primary"],
        true,
    );
}

#[test]
fn flipflop_alternates_across_repeated_entries_and_restores_initial_phase() {
    let mut flip = Vec::new();
    assignment(&mut flip, 12, math(12, &[local(12)]));
    let conditional = branch(&mut flip, 12);
    call(&mut flip, 6);
    let done = jump(&mut flip, EX_JUMP);
    let alternate = flip.len();
    call(&mut flip, 7);
    let exit = finish(&mut flip);
    patch(&mut flip, conditional, alternate);
    patch(&mut flip, done, exit);
    for (phase, expected) in [
        (0, vec!["Primary", "Secondary", "Primary", "Secondary"]),
        (1, vec!["Secondary", "Primary", "Secondary", "Primary"]),
    ] {
        let mut initial = initial_state();
        initial.insert("Temp_bool_Variable_7".into(), phase);
        let bodies = assert_invocations(
            std::slice::from_ref(&flip),
            &[0, 0, 0, 0],
            initial,
            &expected,
            true,
        );
        assert!(bodies[0].iter().any(|stmt| matches!(
            stmt,
            Stmt::Latch {
                kind: LatchKind::FlipFlop { .. },
                ..
            }
        )));
    }
}

#[test]
fn nested_counter_loops_preserve_zero_iterations_and_completion_order() {
    let mut stream = Vec::new();
    assignment(&mut stream, 6, integer(0));
    let outer = jump(&mut stream, EX_JUMP_IF_NOT);
    stream.extend(math(10, &[local(6), local(8)]));
    assignment(&mut stream, 7, integer(0));
    let inner = jump(&mut stream, EX_JUMP_IF_NOT);
    stream.extend(math(10, &[local(7), local(9)]));
    stream.extend(math(13, &[local(6), local(7)]));
    assignment(&mut stream, 7, math(11, &[local(7), integer(1)]));
    let inner_back = jump(&mut stream, EX_JUMP);
    let inner_complete = stream.len();
    call(&mut stream, 14);
    assignment(&mut stream, 6, math(11, &[local(6), integer(1)]));
    let outer_back = jump(&mut stream, EX_JUMP);
    let outer_complete = stream.len();
    call(&mut stream, 15);
    finish(&mut stream);
    for (offset, target) in [
        (outer, outer_complete),
        (inner, inner_complete),
        (inner_back, inner),
        (outer_back, outer),
    ] {
        patch(&mut stream, offset, target);
    }
    for (outer_limit, inner_limit, expected) in [
        (0, 2, vec!["OuterComplete"]),
        (
            2,
            0,
            vec!["InnerComplete", "InnerComplete", "OuterComplete"],
        ),
        (
            2,
            2,
            vec![
                "Visit[0, 0]",
                "Visit[0, 1]",
                "InnerComplete",
                "Visit[1, 0]",
                "Visit[1, 1]",
                "InnerComplete",
                "OuterComplete",
            ],
        ),
    ] {
        let mut initial = initial_state();
        initial.insert("Limit".into(), outer_limit);
        initial.insert("InnerLimit".into(), inner_limit);
        assert_invocations(
            std::slice::from_ref(&stream),
            &[0],
            initial,
            &expected,
            false,
        );
    }
}

#[test]
fn nested_loop_exit_flags_and_completion_calls_match_unrefined_execution() {
    use crate::bytecode::stmt::LoopKind;
    use crate::bytecode::transforms::test_fixtures::{assign, call, lit, var};
    fn guarded_loop(
        counter: &str,
        items: &str,
        item: &str,
        stop: &str,
        mut body: Vec<Stmt>,
        completion: &str,
    ) -> Stmt {
        body.insert(
            0,
            assign(
                item,
                Expr::Index {
                    recv: Box::new(var(items)),
                    idx: Box::new(var(counter)),
                },
            ),
        );
        body.push(assign(
            counter,
            Expr::Binary {
                op: BinaryOp::Add,
                lhs: Box::new(var(counter)),
                rhs: Box::new(lit("1")),
            },
        ));
        Stmt::Loop {
            kind: LoopKind::While,
            cond: Some(Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(Expr::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(var(stop)),
                }),
                rhs: Box::new(Expr::Binary {
                    op: BinaryOp::Lt,
                    lhs: Box::new(var(counter)),
                    rhs: Box::new(Expr::Call {
                        name: "Array_Length".into(),
                        args: vec![var(items)],
                    }),
                }),
            }),
            body,
            completion: Some(vec![call(completion, vec![])]),
            offset: 0,
        }
    }
    let inner = guarded_loop(
        "InnerIndex",
        "InnerItems",
        "InnerItem",
        "InnerStop",
        vec![
            call("Visit", vec![var("OuterItem"), var("InnerItem")]),
            Stmt::Branch {
                cond: var("Found"),
                then_body: vec![
                    assign("InnerStop", lit("true")),
                    assign("OuterStop", lit("true")),
                    Stmt::Break { offset: 1 },
                ],
                else_body: vec![],
                offset: 2,
            },
        ],
        "InnerComplete",
    );
    let body = vec![
        assign("OuterIndex", lit("0")),
        assign("OuterStop", lit("false")),
        guarded_loop(
            "OuterIndex",
            "OuterItems",
            "OuterItem",
            "OuterStop",
            vec![
                assign("InnerIndex", lit("0")),
                assign("InnerStop", lit("false")),
                inner,
                call("AfterInner", vec![]),
            ],
            "OuterComplete",
        ),
        call("Notify", vec![]),
    ];
    let mut transformed = body.clone();
    crate::bytecode::decode::apply_transform_stack_to_body(&mut transformed);
    for (found, expected) in [
        (
            0,
            vec![
                "Visit[0, 0]",
                "Visit[0, 1]",
                "InnerComplete",
                "AfterInner",
                "Visit[1, 0]",
                "Visit[1, 1]",
                "InnerComplete",
                "AfterInner",
                "OuterComplete",
                "Notify",
            ],
        ),
        (
            1,
            vec![
                "Visit[0, 0]",
                "InnerComplete",
                "AfterInner",
                "OuterComplete",
                "Notify",
            ],
        ),
    ] {
        let mut original_state = BTreeMap::from([
            ("Found".into(), found),
            ("OuterItems".into(), 2),
            ("InnerItems".into(), 2),
        ]);
        let mut transformed_state = original_state.clone();
        let mut reference = Vec::new();
        let mut actual = Vec::new();
        execute(&body, &mut original_state, &mut reference);
        execute(&transformed, &mut transformed_state, &mut actual);
        assert_eq!(reference, expected);
        assert_eq!(
            actual,
            reference,
            "transformed loops {}",
            serde_json::to_string(&transformed).unwrap()
        );
        for flag in ["InnerStop", "OuterStop"] {
            assert_eq!(transformed_state[flag], original_state[flag]);
        }
    }
    let mut loop_kinds = Vec::new();
    crate::bytecode::transforms::visit::rewrite_stmts_preorder(&mut transformed, &mut |stmt| {
        if let Stmt::Loop { kind, .. } = stmt {
            loop_kinds.push(matches!(kind, LoopKind::ForEach { .. }));
        }
    });
    assert_eq!(loop_kinds, [true, true]);
}

#[test]
fn displaced_loop_return_tails_preserve_branch_paths_and_skip_completion() {
    for shared_tail in [false, true] {
        let mut stream = Vec::new();
        assignment(&mut stream, 6, integer(0));
        let head = jump(&mut stream, EX_JUMP_IF_NOT);
        stream.extend(math(10, &[local(6), local(8)]));
        let push = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
        let enter_body = jump(&mut stream, EX_JUMP);
        let increment = stream.len();
        assignment(&mut stream, 6, math(11, &[local(6), integer(1)]));
        let back = jump(&mut stream, EX_JUMP);
        let completed = stream.len();
        call(&mut stream, 15);
        let completion_return = jump(&mut stream, EX_JUMP);
        let body_start = stream.len();
        call(&mut stream, 13);
        let outer = branch(&mut stream, 0);
        let inner = branch(&mut stream, 1);
        stream.push(EX_POP_EXECUTION_FLOW);
        let first_tail = stream.len();
        call(&mut stream, 3);
        let first_return = finish(&mut stream);
        let second_tail = if shared_tail {
            first_tail
        } else {
            let offset = stream.len();
            call(&mut stream, 4);
            finish(&mut stream);
            offset
        };
        for (offset, target) in [
            (head, completed),
            (push, increment),
            (enter_body, body_start),
            (back, head),
            (completion_return, first_return),
            (outer, second_tail),
            (inner, first_tail),
        ] {
            patch(&mut stream, offset, target);
        }
        for (limit, path, near, expected) in [
            (0, 0, 0, vec!["OuterComplete"]),
            (
                2,
                0,
                1,
                vec!["Visit", if shared_tail { "Commit" } else { "Notify" }],
            ),
            (2, 1, 0, vec!["Visit", "Commit"]),
            (2, 1, 1, vec!["Visit", "Visit", "OuterComplete"]),
        ] {
            let mut initial = initial_state();
            initial.insert("Limit".into(), limit);
            initial.insert("Path".into(), path);
            initial.insert("Near".into(), near);
            assert_invocations(
                std::slice::from_ref(&stream),
                &[0],
                initial,
                &expected,
                false,
            );
        }
    }
}

#[test]
fn loop_flow_guard_returns_without_incrementing_or_visiting_later_items() {
    let mut stream = Vec::new();
    let exit_frame = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    assignment(&mut stream, 6, integer(0));
    let head = jump(&mut stream, EX_JUMP_IF_NOT);
    stream.extend(math(10, &[local(6), local(8)]));
    let body_frame = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let enter_body = jump(&mut stream, EX_JUMP);
    let increment = stream.len();
    assignment(&mut stream, 6, math(11, &[local(6), integer(1)]));
    let back = jump(&mut stream, EX_JUMP);
    let completed = stream.len();
    call(&mut stream, 15);
    stream.push(EX_POP_EXECUTION_FLOW);
    let body_start = stream.len();
    stream.extend(math(13, &[local(6)]));
    stream.push(EX_POP_FLOW_IF_NOT);
    stream.extend(math(9, &[local(6), local(1)]));
    call(&mut stream, 3);
    let exit = finish(&mut stream);
    for (offset, target) in [
        (exit_frame, exit),
        (head, completed),
        (body_frame, increment),
        (enter_body, body_start),
        (back, head),
    ] {
        patch(&mut stream, offset, target);
    }
    for (limit, near, expected) in [
        (0, 0, vec!["OuterComplete"]),
        (3, 0, vec!["Visit[0]", "Commit"]),
        (3, 1, vec!["Visit[0]", "Visit[1]", "Commit"]),
        (2, 3, vec!["Visit[0]", "Visit[1]", "OuterComplete"]),
    ] {
        let mut initial = initial_state();
        initial.insert("Limit".into(), limit);
        initial.insert("Near".into(), near);
        assert_invocations(
            std::slice::from_ref(&stream),
            &[0],
            initial,
            &expected,
            false,
        );
    }
}

#[test]
fn displaced_else_rejoins_loop_return_guard_instead_of_breaking() {
    let mut stream = Vec::new();
    let exit_frame = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    assignment(&mut stream, 6, integer(0));
    let head = jump(&mut stream, EX_JUMP_IF_NOT);
    stream.extend(math(10, &[local(6), local(8)]));
    let body_frame = jump(&mut stream, EX_PUSH_EXECUTION_FLOW);
    let enter_body = jump(&mut stream, EX_JUMP);
    let increment = stream.len();
    assignment(&mut stream, 6, math(11, &[local(6), integer(1)]));
    let back = jump(&mut stream, EX_JUMP);
    let completed = stream.len();
    call(&mut stream, 15);
    let complete_return = jump(&mut stream, EX_JUMP);
    let body_start = stream.len();
    stream.extend(math(13, &[local(6)]));
    let condition = branch(&mut stream, 0);
    assignment(&mut stream, 2, math(9, &[local(6), local(1)]));
    let shared = stream.len();
    stream.push(EX_POP_FLOW_IF_NOT);
    stream.extend(local(2));
    call(&mut stream, 3);
    let early_return = jump(&mut stream, EX_JUMP);
    let else_start = stream.len();
    assignment(&mut stream, 2, integer(0));
    let rejoin = jump(&mut stream, EX_JUMP);
    let exit = finish(&mut stream);
    for (offset, target) in [
        (exit_frame, exit),
        (head, completed),
        (body_frame, increment),
        (enter_body, body_start),
        (back, head),
        (complete_return, exit),
        (condition, else_start),
        (early_return, exit),
        (rejoin, shared),
    ] {
        patch(&mut stream, offset, target);
    }
    for (limit, path, near, expected) in [
        (0, 1, 0, vec!["OuterComplete"]),
        (3, 1, 0, vec!["Visit[0]", "Commit"]),
        (3, 1, 1, vec!["Visit[0]", "Visit[1]", "Commit"]),
        (2, 0, 0, vec!["Visit[0]", "Visit[1]", "OuterComplete"]),
        (2, 1, 3, vec!["Visit[0]", "Visit[1]", "OuterComplete"]),
    ] {
        let mut initial = initial_state();
        initial.insert("Limit".into(), limit);
        initial.insert("Path".into(), path);
        initial.insert("Near".into(), near);
        assert_invocations(
            std::slice::from_ref(&stream),
            &[0],
            initial,
            &expected,
            false,
        );
    }
}
