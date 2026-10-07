//! Match graph calls and branches to decoded statements for comment placement.

use crate::bytecode::expr::{CastKind, Expr, LiteralValue};
use crate::bytecode::stmt::Stmt;
use crate::types::{EdGraphPin, LinkedPin, ParsedAsset, PIN_DIRECTION_INPUT};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Both graph arms must reach proven statements in distinct arms of the
/// same decoded branch. This uses ancestry, without assuming true/false
/// polarity survives branch inversion during normalization.
pub(super) fn branch_statement_for_node<'a>(
    node: usize,
    body: &'a [Stmt],
    parsed: &ParsedAsset,
) -> Option<&'a Stmt> {
    let (header, _) = parsed.exports.get(node.checked_sub(1)?)?;
    let names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let class = crate::resolve::class_of(&parsed.imports, &names, header);
    if class.rsplit('.').next()? != "K2Node_IfThenElse" {
        return None;
    }
    if let Some(stmt) = branch_with_unique_condition(node, body, parsed, &names) {
        return Some(stmt);
    }
    let outputs: Vec<&EdGraphPin> = parsed
        .pin_data
        .get(&node)?
        .pins
        .iter()
        .filter(|pin| pin.is_exec_output())
        .collect();
    if outputs.len() != 2 || outputs.iter().any(|pin| pin.linked_to.len() != 1) {
        return None;
    }
    let first = first_mapped_exec_statement(outputs[0].linked_to[0].node, body, parsed)?;
    let second = first_mapped_exec_statement(outputs[1].linked_to[0].node, body, parsed)?;
    common_statement_branch(body, first, second)
}

fn branch_with_unique_condition<'a>(
    node: usize,
    body: &'a [Stmt],
    parsed: &ParsedAsset,
    names: &[String],
) -> Option<&'a Stmt> {
    let condition_path = |node| {
        let condition = parsed
            .pin_data
            .get(&node)?
            .pins
            .iter()
            .find(|pin| pin.name == "Condition" && pin.direction == PIN_DIRECTION_INPUT)?;
        graph_input_expression(node, condition, parsed, names, &mut BTreeSet::new())
    };
    let expected = condition_path(node)?;
    let header = &parsed.exports.get(node.checked_sub(1)?)?.0;
    let duplicates = parsed
        .exports
        .iter()
        .enumerate()
        .filter(|(index, (other, _))| {
            other.outer_index == header.outer_index
                && crate::resolve::short_class(&crate::resolve::class_of(
                    &parsed.imports,
                    names,
                    other,
                )) == "K2Node_IfThenElse"
                && condition_path(index + 1)
                    .is_some_and(|other| branch_conditions_match(&other, &expected, None))
        })
        .count();
    if duplicates != 1 {
        return None;
    }
    let mut matches = Vec::new();
    collect_branches_with_condition(body, &expected, &mut matches);
    match matches.as_slice() {
        [stmt] => Some(*stmt),
        _ => None,
    }
}

fn collect_branches_with_condition<'a>(
    body: &'a [Stmt],
    expected: &Expr,
    matches: &mut Vec<&'a Stmt>,
) {
    for (index, stmt) in body.iter().enumerate() {
        if let Stmt::Branch { cond, .. } = stmt {
            let condition = match cond {
                Expr::Unary {
                    op: crate::bytecode::expr::UnaryOp::Not,
                    operand,
                } => operand,
                other => other,
            };
            if branch_conditions_match(
                condition,
                expected,
                index.checked_sub(1).map(|previous| &body[previous]),
            ) {
                matches.push(stmt);
            }
        }
        for child in stmt.child_bodies_all() {
            collect_branches_with_condition(child, expected, matches);
        }
    }
}

fn first_mapped_exec_statement<'a>(
    start: usize,
    body: &'a [Stmt],
    parsed: &ParsedAsset,
) -> Option<&'a Stmt> {
    use crate::prop_query::find_struct_field_str;
    let mut queue = VecDeque::from([start]);
    let mut visited = BTreeSet::new();
    while let Some(node) = queue.pop_front() {
        if !visited.insert(node) {
            continue;
        }
        if let Some(mapping) = call_statements_by_node(node, &[body], parsed) {
            if let Some(stmt) = mapping.get(&node) {
                return Some(*stmt);
            }
        } else if let Some((_, properties)) = node
            .checked_sub(1)
            .and_then(|index| parsed.exports.get(index))
        {
            if let Some(member) =
                find_struct_field_str(properties, "FunctionReference", "MemberName")
            {
                let mut candidates = Vec::new();
                collect_call_statements(body, &member, &mut candidates);
                if candidates.len() == 1 {
                    return Some(candidates[0].0);
                }
            }
        }
        if let Some(data) = parsed.pin_data.get(&node) {
            // Crossing another fork can make an inner branch look like the
            // source branch. Only a linear continuation preserves this proof.
            let successors: Vec<usize> = data
                .pins
                .iter()
                .filter(|pin| pin.is_exec_output())
                .flat_map(|pin| pin.linked_to.iter().map(|link| link.node))
                .collect();
            if let [successor] = successors[..] {
                queue.push_back(successor);
            }
        }
    }
    None
}

fn common_statement_branch<'a>(body: &'a [Stmt], first: &Stmt, second: &Stmt) -> Option<&'a Stmt> {
    for stmt in body {
        for child in stmt.child_bodies_all() {
            if let Some(branch) = common_statement_branch(child, first, second) {
                return Some(branch);
            }
        }
        if let Stmt::Branch {
            then_body,
            else_body,
            ..
        } = stmt
        {
            let separate_arms = (contains_statement(then_body, first)
                && contains_statement(else_body, second))
                || (contains_statement(then_body, second) && contains_statement(else_body, first));
            if separate_arms {
                return Some(stmt);
            }
        }
    }
    None
}

pub(super) fn contains_statement(body: &[Stmt], target: &Stmt) -> bool {
    body.iter().any(|stmt| {
        std::ptr::eq(stmt, target)
            || stmt
                .child_bodies_all()
                .iter()
                .any(|child| contains_statement(child, target))
    })
}

/// Correlate a repeated executable call group using recoverable input paths.
/// An empty map means the group exists but its correspondence is ambiguous.
pub(super) fn call_statements_by_node<'a>(
    node: usize,
    bodies: &[&'a [Stmt]],
    parsed: &ParsedAsset,
) -> Option<BTreeMap<usize, &'a Stmt>> {
    use crate::prop_query::find_struct_field_str;
    let (header, properties) = parsed.exports.get(node.checked_sub(1)?)?;
    let member = find_struct_field_str(properties, "FunctionReference", "MemberName")?;
    let nodes: Vec<usize> = parsed
        .exports
        .iter()
        .enumerate()
        .filter_map(|(index, (other, props))| {
            (other.outer_index == header.outer_index
                && find_struct_field_str(props, "FunctionReference", "MemberName").as_deref()
                    == Some(member.as_str())
                && parsed
                    .pin_data
                    .get(&(index + 1))
                    .is_some_and(|pins| pins.pins.iter().any(EdGraphPin::is_exec_input)))
            .then_some(index + 1)
        })
        .collect();
    if nodes.len() < 2 || !nodes.contains(&node) {
        return None;
    }
    let mut statements = Vec::new();
    for body in bodies {
        collect_call_statements(body, &member, &mut statements);
    }
    if statements.len() != nodes.len() {
        return Some(BTreeMap::new());
    }
    let export_names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let candidates: BTreeMap<usize, Vec<usize>> = nodes
        .into_iter()
        .map(|node| {
            let choices = statements
                .iter()
                .enumerate()
                .filter_map(|(index, (stmt, previous))| {
                    call_inputs_match(node, stmt, *previous, parsed, &export_names).then_some(index)
                })
                .collect();
            (node, choices)
        })
        .collect();
    let Some(matching) = complete_matching(&candidates, None) else {
        return Some(BTreeMap::new());
    };
    // A pair is proven only if removing it makes every complete assignment
    // impossible. Ambiguous neighbors need not invalidate an independent pair.
    Some(
        matching
            .into_iter()
            .filter(|&(node, index)| complete_matching(&candidates, Some((node, index))).is_none())
            .map(|(node, index)| (node, statements[index].0))
            .collect(),
    )
}

fn complete_matching(
    candidates: &BTreeMap<usize, Vec<usize>>,
    forbidden: Option<(usize, usize)>,
) -> Option<BTreeMap<usize, usize>> {
    fn assign(
        node: usize,
        candidates: &BTreeMap<usize, Vec<usize>>,
        forbidden: Option<(usize, usize)>,
        visited: &mut BTreeSet<usize>,
        owners: &mut BTreeMap<usize, usize>,
    ) -> bool {
        for &index in &candidates[&node] {
            if forbidden == Some((node, index)) || !visited.insert(index) {
                continue;
            }
            if owners
                .get(&index)
                .copied()
                .is_none_or(|previous| assign(previous, candidates, forbidden, visited, owners))
            {
                owners.insert(index, node);
                return true;
            }
        }
        false
    }
    let mut owners = BTreeMap::new();
    for &node in candidates.keys() {
        if !assign(
            node,
            candidates,
            forbidden,
            &mut BTreeSet::new(),
            &mut owners,
        ) {
            return None;
        }
    }
    Some(
        owners
            .into_iter()
            .map(|(index, node)| (node, index))
            .collect(),
    )
}

fn collect_call_statements<'a>(
    body: &'a [Stmt],
    member: &str,
    statements: &mut Vec<(&'a Stmt, Option<&'a Stmt>)>,
) {
    for (index, stmt) in body.iter().enumerate() {
        if call_parts(stmt).is_some_and(|(name, _, _)| {
            crate::bytecode::names::clean_bc_name(name.strip_prefix("K2_").unwrap_or(name))
                == crate::bytecode::names::clean_bc_name(
                    member.strip_prefix("K2_").unwrap_or(member),
                )
        }) {
            statements.push((stmt, index.checked_sub(1).map(|previous| &body[previous])));
        }
        for child in stmt.child_bodies_all() {
            collect_call_statements(child, member, statements);
        }
    }
}

fn call_parts(stmt: &Stmt) -> Option<(&str, Option<&Expr>, &[Expr])> {
    match stmt {
        Stmt::Call {
            func: Expr::FieldAccess { recv, field },
            args,
            ..
        } => Some((field, Some(recv), args)),
        Stmt::Call {
            func: Expr::Var(name),
            args,
            ..
        } => Some((name, None, args)),
        Stmt::Assignment {
            rhs: Expr::MethodCall { recv, name, args },
            ..
        } => Some((name, Some(recv), args)),
        Stmt::Assignment {
            rhs: Expr::Call { name, args },
            ..
        } => Some((name, None, args)),
        _ => None,
    }
}

fn call_inputs_match(
    node: usize,
    stmt: &Stmt,
    previous: Option<&Stmt>,
    parsed: &ParsedAsset,
    export_names: &[String],
) -> bool {
    let Some((_, receiver, args)) = call_parts(stmt) else {
        return false;
    };
    let Some(data) = parsed.pin_data.get(&node) else {
        return false;
    };
    let mut argument_index = 0;
    for pin in data
        .pins
        .iter()
        .filter(|pin| pin.pin_type != "exec" && pin.name != "ReturnValue")
    {
        if pin
            .metadata
            .as_ref()
            .is_some_and(|metadata| metadata.parent_pin.is_some())
        {
            continue;
        }
        let actual = if pin.name == "self" {
            receiver
        } else {
            let argument = args.get(argument_index);
            argument_index += 1;
            argument
        };
        if !pin.is_data_input() {
            continue;
        }
        let Some(expected) =
            graph_input_expression(node, pin, parsed, export_names, &mut BTreeSet::new())
        else {
            continue;
        };
        if pin.name == "self" && receiver.is_none() {
            if crate::bytecode::transforms::lower_static_library_calls::is_static_library_class_literal(&expected) {
                continue;
            }
            if expression_matches(&Expr::Literal("self".into()), &expected, previous) == Some(false)
            {
                return false;
            }
        } else if actual
            .is_none_or(|expr| expression_matches(expr, &expected, previous) == Some(false))
        {
            return false;
        }
    }
    argument_index == args.len()
}

fn expression_path(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Var(name) => Some(name.split('.').map(str::to_string).collect()),
        Expr::Literal(LiteralValue::Text(name)) if name == "self" => Some(vec![name.clone()]),
        Expr::FieldAccess { recv, field } => {
            let mut path = expression_path(recv)?;
            path.push(field.clone());
            Some(path)
        }
        Expr::Out(inner) | Expr::Persistent(inner) => expression_path(inner),
        _ => None,
    }
}

fn normalized_expression(expr: &Expr) -> Expr {
    let mut statements = vec![Stmt::Assignment {
        lhs: Expr::Var(String::new()),
        rhs: expr.clone(),
        offset: 0,
    }];
    crate::bytecode::transforms::lower_static_library_calls::lower_static_library_calls(
        &mut statements,
    );
    crate::bytecode::transforms::lower_binary_ops::lower_binary_ops(&mut statements);
    let Stmt::Assignment { rhs, .. } = statements.remove(0) else {
        unreachable!()
    };
    rhs
}

fn expression_matches(actual: &Expr, expected: &Expr, previous: Option<&Stmt>) -> Option<bool> {
    structural_expression_matches(
        &normalized_expression(actual),
        &normalized_expression(expected),
        previous,
    )
}

fn structural_expression_matches(
    actual: &Expr,
    expected: &Expr,
    previous: Option<&Stmt>,
) -> Option<bool> {
    if let Expr::Out(inner) | Expr::Persistent(inner) = actual {
        return structural_expression_matches(inner, expected, previous);
    }
    if let Expr::Var(name) = actual {
        if name.starts_with('$') || name.starts_with("Temp_") {
            if let Some(Stmt::Assignment { lhs, rhs, .. }) = previous {
                if lhs == actual {
                    return expression_matches(rhs, expected, None);
                }
            }
            return None;
        }
    }
    if matches!(actual, Expr::Unknown { .. }) {
        return None;
    }
    if let (Some(actual), Some(expected)) = (expression_path(actual), expression_path(expected)) {
        return Some(actual == expected);
    }
    let pairs: Vec<(&Expr, &Expr)> = match (actual, expected) {
        (
            Expr::Call {
                name: actual_name,
                args: actual_args,
            },
            Expr::Call {
                name: expected_name,
                args: expected_args,
            },
        ) if actual_name == expected_name && actual_args.len() == expected_args.len() => {
            actual_args.iter().zip(expected_args).collect()
        }
        (
            Expr::MethodCall {
                recv: actual_recv,
                name: actual_name,
                args: actual_args,
            },
            Expr::MethodCall {
                recv: expected_recv,
                name: expected_name,
                args: expected_args,
            },
        ) if actual_name == expected_name && actual_args.len() == expected_args.len() => {
            std::iter::once((actual_recv.as_ref(), expected_recv.as_ref()))
                .chain(actual_args.iter().zip(expected_args))
                .collect()
        }
        (
            Expr::FieldAccess {
                recv: actual_recv,
                field: actual_field,
            },
            Expr::FieldAccess {
                recv: expected_recv,
                field: expected_field,
            },
        ) if actual_field == expected_field => vec![(actual_recv, expected_recv)],
        (
            Expr::Index {
                recv: actual_recv,
                idx: actual_idx,
            },
            Expr::Index {
                recv: expected_recv,
                idx: expected_idx,
            },
        ) => vec![(actual_recv, expected_recv), (actual_idx, expected_idx)],
        (
            Expr::Binary {
                op: actual_op,
                lhs: actual_lhs,
                rhs: actual_rhs,
            },
            Expr::Binary {
                op: expected_op,
                lhs: expected_lhs,
                rhs: expected_rhs,
            },
        ) if actual_op == expected_op => {
            vec![(actual_lhs, expected_lhs), (actual_rhs, expected_rhs)]
        }
        (
            Expr::Unary {
                op: actual_op,
                operand: actual_operand,
            },
            Expr::Unary {
                op: expected_op,
                operand: expected_operand,
            },
        ) if actual_op == expected_op => vec![(actual_operand, expected_operand)],
        (
            Expr::Cast {
                kind: actual_kind,
                inner: actual_inner,
            },
            Expr::Cast {
                kind: expected_kind,
                inner: expected_inner,
            },
        ) if actual_kind == expected_kind => vec![(actual_inner, expected_inner)],
        _ => return Some(actual == expected),
    };
    let mut complete = true;
    for (actual, expected) in pairs {
        match structural_expression_matches(actual, expected, previous) {
            Some(false) => return Some(false),
            None => complete = false,
            Some(true) => {}
        }
    }
    complete.then_some(true)
}

fn branch_conditions_match(actual: &Expr, expected: &Expr, previous: Option<&Stmt>) -> bool {
    let peel_not = |expr: &Expr| match expr {
        Expr::Unary {
            op: crate::bytecode::expr::UnaryOp::Not,
            operand,
        } => operand.as_ref().clone(),
        other => other.clone(),
    };
    expression_matches(&peel_not(actual), &peel_not(expected), previous) == Some(true)
}

fn graph_default_expression(
    pin: &EdGraphPin,
    parsed: &ParsedAsset,
    export_names: &[String],
) -> Option<Expr> {
    use crate::prop_query::{find_prop, find_prop_str};
    let metadata = pin.metadata.as_ref()?;
    if find_prop(&metadata.type_details, "ContainerType").is_some_and(|field| !matches!(&field.value, crate::types::PropValue::Enum { value, .. } if value == "None")) { return None; }
    let value = if metadata.default_value.is_empty()
        && !matches!(pin.pin_type.as_str(), "string" | "text" | "name")
    {
        &metadata.autogenerated_default_value
    } else {
        &metadata.default_value
    };
    let literal = match pin.pin_type.as_str() {
        "bool" => match value.to_ascii_lowercase().as_str() {
            "true" => "true".into(),
            "false" => "false".into(),
            _ => return None,
        },
        "int" => value.parse::<i32>().ok()?.to_string().into(),
        "int64" => format!("{}L", value.parse::<i64>().ok()?).into(),
        "byte" => value.parse::<u8>().ok()?.to_string().into(),
        "float" | "double" | "real" => {
            let subtype = find_prop_str(&metadata.type_details, "PinSubCategory");
            let double = pin.pin_type == "double"
                || (pin.pin_type == "real" && subtype.as_deref() == Some("double"));
            if pin.pin_type == "real" && !matches!(subtype.as_deref(), Some("float" | "double")) {
                return None;
            }
            if double {
                let number = value.parse::<f64>().ok()?;
                if !number.is_finite() {
                    return None;
                }
                LiteralValue::Float64(number.to_bits())
            } else {
                let number = value.parse::<f32>().ok()?;
                if !number.is_finite() {
                    return None;
                }
                LiteralValue::Float32(number.to_bits())
            }
        }
        "string" => format!("\"{value}\"").into(),
        "name" => format!("'{}'", if value.is_empty() { "None" } else { value }).into(),
        "text" => {
            let source = metadata.default_text_source.as_ref()?;
            match metadata.default_text_payload.get(4).copied()? as i8 {
                -1 => format!("\"{source}\"").into(),
                0 => format!("LOCTEXT(\"{source}\")").into(),
                _ => return None,
            }
        }
        "object" | "class" | "interface" => {
            if pin.name == "self" && metadata.default_object == 0 {
                return None;
            }
            if metadata.default_object == 0 {
                // Empty object defaults may be supplied through DefaultToSelf.
                if value != "None" {
                    return None;
                }
                "None".into()
            } else {
                let index = metadata.default_object;
                if (index < 0 && i64::from(index).unsigned_abs() > parsed.imports.len() as u64)
                    || (index > 0 && index as usize > export_names.len())
                {
                    return None;
                }
                let resolved =
                    crate::bytecode::resolve::resolve_bc_obj(index, &parsed.imports, export_names);
                if resolved == "?" || resolved.starts_with("export[") {
                    return None;
                }
                resolved.into()
            }
        }
        _ => return None,
    };
    Some(Expr::Literal(literal))
}

fn graph_input_expression(
    node: usize,
    pin: &EdGraphPin,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    match pin.linked_to.as_slice() {
        [source] => graph_pin_expression(source, parsed, names, visited),
        [] => {
            if let Some(source) = pin
                .metadata
                .as_ref()
                .and_then(|metadata| metadata.reference_pass_through.as_ref())
            {
                graph_pin_expression(source, parsed, names, visited)
            } else if pin
                .metadata
                .as_ref()
                .is_some_and(|metadata| metadata.parent_pin.is_some())
            {
                split_pin_expression(node, pin, parsed, names, visited)
            } else {
                graph_default_expression(pin, parsed, names)
            }
        }
        _ => None,
    }
}

fn split_pin_expression(
    node: usize,
    pin: &EdGraphPin,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    use crate::bytecode::names::strip_guid_suffix;
    let parent = pin.metadata.as_ref()?.parent_pin.as_ref()?;
    if parent.node != node {
        return None;
    }
    let parent_pin = parsed
        .pin_data
        .get(&node)?
        .pins
        .iter()
        .find(|candidate| candidate.pin_id == parent.pin_id)?;
    if !parent_pin
        .metadata
        .as_ref()?
        .sub_pins
        .iter()
        .any(|child| child.node == node && child.pin_id == pin.pin_id)
    {
        return None;
    }
    let prefix = format!("{}_", strip_guid_suffix(&parent_pin.name));
    let field = strip_guid_suffix(&pin.name)
        .strip_prefix(&prefix)?
        .to_string();
    let recv = graph_pin_expression(parent, parsed, names, visited)?;
    Some(Expr::FieldAccess {
        recv: Box::new(recv),
        field,
    })
}

fn graph_pin_expression(
    link: &LinkedPin,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    if visited.len() >= 64 || !visited.insert((link.node, link.pin_id)) {
        return None;
    }
    let result = graph_pin_expression_inner(link, parsed, names, visited);
    visited.remove(&(link.node, link.pin_id));
    result
}

fn graph_pin_expression_inner(
    link: &LinkedPin,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    use crate::prop_query::{find_prop, find_struct_field_str};
    use crate::types::PropValue;
    let (header, properties) = parsed.exports.get(link.node.checked_sub(1)?)?;
    let pins = &parsed.pin_data.get(&link.node)?.pins;
    let output = pins.iter().find(|pin| pin.pin_id == link.pin_id)?;
    if output.is_data_input() {
        return graph_input_expression(link.node, output, parsed, names, visited);
    }
    if !output.is_data_output() {
        return None;
    }
    if output
        .metadata
        .as_ref()
        .is_some_and(|metadata| metadata.parent_pin.is_some())
    {
        return split_pin_expression(link.node, output, parsed, names, visited);
    }
    if let Some(source) = output
        .metadata
        .as_ref()
        .and_then(|metadata| metadata.reference_pass_through.as_ref())
    {
        return graph_pin_expression(source, parsed, names, visited);
    }
    let class = crate::resolve::class_of(&parsed.imports, names, header);
    let input = |name: &str| {
        pins.iter()
            .find(|pin| pin.is_data_input() && pin.name == name)
    };
    match class.rsplit('.').next()? {
        "K2Node_Knot" => {
            let mut inputs = pins.iter().filter(|pin| pin.is_data_input());
            let input = inputs.next()?;
            if inputs.next().is_some() {
                return None;
            }
            graph_input_expression(link.node, input, parsed, names, visited)
        }
        "K2Node_FunctionEntry" => Some(Expr::Var(crate::bytecode::names::clean_bc_name(
            &output.name,
        ))),
        "K2Node_VariableGet" => {
            let member = find_struct_field_str(properties, "VariableReference", "MemberName")?;
            if crate::bytecode::names::clean_bc_name(&output.name)
                != crate::bytecode::names::clean_bc_name(&member)
            {
                return None;
            }
            graph_variable_target(link.node, parsed, names, visited)
        }
        "K2Node_GetArrayItem" => {
            let array = input("Array").or_else(|| input("TargetArray"))?;
            let index = input("Dimension1").or_else(|| input("Index"))?;
            Some(Expr::Index {
                recv: Box::new(graph_input_expression(
                    link.node, array, parsed, names, visited,
                )?),
                idx: Box::new(graph_input_expression(
                    link.node, index, parsed, names, visited,
                )?),
            })
        }
        "K2Node_DynamicCast" | "K2Node_ClassDynamicCast" if output.name.starts_with("As") => {
            let PropValue::Object(target) = &find_prop(properties, "TargetType")?.value else {
                return None;
            };
            let target = crate::bytecode::resolve::resolve_bc_obj(*target, &parsed.imports, names);
            if target == "?" {
                return None;
            }
            let source = input("Object").or_else(|| input("Class"))?;
            Some(Expr::Cast {
                kind: CastKind::Class { target },
                inner: Box::new(graph_input_expression(
                    link.node, source, parsed, names, visited,
                )?),
            })
        }
        "K2Node_CallFunction"
        | "K2Node_CommutativeAssociativeBinaryOperator"
        | "K2Node_PromotableOperator" => graph_call_expression(link.node, parsed, names, visited),
        _ => None,
    }
}

fn has_explicit_input_source(pin: &EdGraphPin) -> bool {
    !pin.linked_to.is_empty()
        || pin.metadata.as_ref().is_some_and(|metadata| {
            metadata.default_object != 0
                || metadata.reference_pass_through.is_some()
                || metadata.parent_pin.is_some()
        })
}

fn graph_call_expression(
    node: usize,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    use crate::prop_query::{find_prop_bool, find_struct_field_str};
    let properties = &parsed.exports.get(node.checked_sub(1)?)?.1;
    let pins = &parsed.pin_data.get(&node)?.pins;
    if pins.iter().any(EdGraphPin::is_exec_input)
        || find_prop_bool(properties, "bIsPureFunc") == Some(false)
    {
        return None;
    }
    if pins
        .iter()
        .filter(|pin| {
            pin.is_data_output()
                && pin
                    .metadata
                    .as_ref()
                    .is_none_or(|metadata| metadata.parent_pin.is_none())
        })
        .count()
        != 1
    {
        return None;
    }
    let member = find_struct_field_str(properties, "FunctionReference", "MemberName")?;
    let name = crate::bytecode::names::clean_bc_name(&member);
    let mut args = Vec::new();
    for pin in pins.iter().filter(|pin| {
        pin.is_data_input()
            && pin.name != "self"
            && pin
                .metadata
                .as_ref()
                .is_none_or(|metadata| metadata.parent_pin.is_none())
    }) {
        args.push(graph_input_expression(node, pin, parsed, names, visited)?);
    }
    let receiver = pins
        .iter()
        .find(|pin| pin.is_data_input() && pin.name == "self")
        .filter(|pin| has_explicit_input_source(pin));
    Some(if let Some(receiver) = receiver {
        Expr::MethodCall {
            recv: Box::new(graph_input_expression(
                node, receiver, parsed, names, visited,
            )?),
            name,
            args,
        }
    } else {
        Expr::Call { name, args }
    })
}

fn graph_variable_target(
    node: usize,
    parsed: &ParsedAsset,
    names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Expr> {
    use crate::prop_query::find_struct_field_str;
    let properties = &parsed.exports.get(node.checked_sub(1)?)?.1;
    let pins = &parsed.pin_data.get(&node)?.pins;
    let member = find_struct_field_str(properties, "VariableReference", "MemberName")?;
    let receiver = pins
        .iter()
        .find(|pin| pin.is_data_input() && pin.name == "self")
        .filter(|pin| has_explicit_input_source(pin));
    let field = crate::bytecode::names::clean_bc_name(&member);
    if let Some(receiver) = receiver {
        return Some(Expr::FieldAccess {
            recv: Box::new(graph_input_expression(
                node, receiver, parsed, names, visited,
            )?),
            field,
        });
    }
    let local = find_struct_field_str(properties, "VariableReference", "MemberScope")
        .is_some_and(|scope| !scope.is_empty() && scope != "None");
    Some(Expr::Var(if local {
        field
    } else {
        format!("self.{field}")
    }))
}

fn graph_assignment(node: usize, parsed: &ParsedAsset, names: &[String]) -> Option<(Expr, Expr)> {
    let properties = &parsed.exports.get(node.checked_sub(1)?)?.1;
    let member =
        crate::prop_query::find_struct_field_str(properties, "VariableReference", "MemberName")?;
    let input = parsed
        .pin_data
        .get(&node)?
        .pins
        .iter()
        .find(|pin| pin.is_data_input() && pin.name == member)?;
    Some((
        graph_variable_target(node, parsed, names, &mut BTreeSet::new())?,
        graph_input_expression(node, input, parsed, names, &mut BTreeSet::new())?,
    ))
}

fn assignment_statements_for_node<'a>(
    node: usize,
    body: &'a [Stmt],
    parsed: &ParsedAsset,
    names: &[String],
) -> Vec<&'a Stmt> {
    let Some((target, expected)) = graph_assignment(node, parsed, names) else {
        return Vec::new();
    };
    let header = &parsed.exports[node - 1].0;
    let ambiguous = parsed
        .exports
        .iter()
        .enumerate()
        .any(|(index, (other, _))| {
            if index + 1 == node
                || other.outer_index != header.outer_index
                || !crate::resolve::class_of(&parsed.imports, names, other)
                    .ends_with("K2Node_VariableSet")
            {
                return false;
            }
            if graph_variable_target(index + 1, parsed, names, &mut BTreeSet::new()).is_some_and(
                |other_target| expression_matches(&other_target, &target, None) == Some(false),
            ) {
                return false;
            }
            graph_assignment(index + 1, parsed, names).is_none_or(|(other_target, other_value)| {
                expression_matches(&other_target, &target, None) != Some(false)
                    && expression_matches(&other_value, &expected, None) != Some(false)
            })
        });
    if ambiguous {
        return Vec::new();
    }
    let mut matches = Vec::new();
    collect_matching_assignments(body, &target, &expected, &mut matches);
    matches
}

fn collect_matching_assignments<'a>(
    body: &'a [Stmt],
    target: &Expr,
    expected: &Expr,
    matches: &mut Vec<&'a Stmt>,
) {
    for (index, stmt) in body.iter().enumerate() {
        if let Stmt::Assignment { lhs, rhs, .. } = stmt {
            if expression_matches(lhs, target, None) == Some(true)
                && expression_matches(
                    rhs,
                    expected,
                    index.checked_sub(1).map(|previous| &body[previous]),
                ) == Some(true)
            {
                matches.push(stmt);
            }
        }
        for child in stmt.child_bodies_all() {
            collect_matching_assignments(child, target, expected, matches);
        }
    }
}

/// Preserve all distinct compiled occurrences only when graph evidence identifies the node.
pub(super) fn statement_for_node<'a>(
    node: usize,
    body: &'a [Stmt],
    parsed: &ParsedAsset,
) -> Vec<&'a Stmt> {
    use crate::prop_query::find_struct_field_str;
    let Some((header, properties)) = node
        .checked_sub(1)
        .and_then(|index| parsed.exports.get(index))
    else {
        return Vec::new();
    };
    let names: Vec<String> = parsed
        .exports
        .iter()
        .map(|(header, _)| header.object_name.clone())
        .collect();
    let class = crate::resolve::class_of(&parsed.imports, &names, header);
    if class.ends_with("K2Node_IfThenElse") {
        return branch_statement_for_node(node, body, parsed)
            .into_iter()
            .collect();
    }
    if let Some(member) = find_struct_field_str(properties, "FunctionReference", "MemberName") {
        if let Some(mapping) = call_statements_by_node(node, &[body], parsed) {
            return mapping.get(&node).copied().into_iter().collect();
        }
        let peers = parsed
            .exports
            .iter()
            .filter(|(other, props)| {
                other.outer_index == header.outer_index
                    && find_struct_field_str(props, "FunctionReference", "MemberName").as_ref()
                        == Some(&member)
            })
            .count();
        if peers != 1 {
            return Vec::new();
        }
        let mut calls = Vec::new();
        collect_call_statements(body, &member, &mut calls);
        return calls
            .into_iter()
            .filter(|(stmt, previous)| call_inputs_match(node, stmt, *previous, parsed, &names))
            .map(|(stmt, _)| stmt)
            .collect();
    }
    if !class.ends_with("K2Node_VariableSet") {
        return Vec::new();
    }
    assignment_statements_for_node(node, body, parsed, &names)
}

#[cfg(test)]
#[path = "call_attribution_tests.rs"]
mod tests;
