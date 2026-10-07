//! Match graph calls and branches to decoded statements for comment placement.

use crate::bytecode::expr::Expr;
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
        let [source] = condition.linked_to.as_slice() else {
            return None;
        };
        graph_pin_path(source, parsed, names, &mut BTreeSet::new())
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
                && condition_path(index + 1).as_ref() == Some(&expected)
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
    expected: &[String],
    matches: &mut Vec<&'a Stmt>,
) {
    for stmt in body {
        if let Stmt::Branch { cond, .. } = stmt {
            let condition = match cond {
                Expr::Unary {
                    op: crate::bytecode::expr::UnaryOp::Not,
                    operand,
                } => operand,
                other => other,
            };
            if expression_path(condition).as_deref() == Some(expected) {
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
    let mut candidates: BTreeMap<usize, Vec<usize>> = nodes
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
    let mut matched = BTreeMap::new();
    while !candidates.is_empty() {
        let singles: Vec<(usize, usize)> = candidates
            .iter()
            .filter(|(_, choices)| choices.len() == 1)
            .map(|(&node, choices)| (node, choices[0]))
            .collect();
        let selected: BTreeSet<usize> = singles.iter().map(|(_, index)| *index).collect();
        if singles.is_empty() || selected.len() != singles.len() {
            return Some(BTreeMap::new());
        }
        for (node, index) in singles {
            matched.insert(node, statements[index].0);
            candidates.remove(&node);
        }
        for choices in candidates.values_mut() {
            choices.retain(|index| !selected.contains(index));
        }
    }
    Some(matched)
}

fn collect_call_statements<'a>(
    body: &'a [Stmt],
    member: &str,
    statements: &mut Vec<(&'a Stmt, Option<&'a Stmt>)>,
) {
    for (index, stmt) in body.iter().enumerate() {
        if call_parts(stmt).is_some_and(|(name, _, _)| {
            name.strip_prefix("K2_").unwrap_or(name) == member.strip_prefix("K2_").unwrap_or(member)
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
        let actual = if pin.name == "self" {
            receiver
        } else {
            let argument = args.get(argument_index);
            argument_index += 1;
            argument
        };
        if pin.direction != PIN_DIRECTION_INPUT || pin.linked_to.len() != 1 {
            continue;
        }
        let Some(expected) = graph_pin_path(
            &pin.linked_to[0],
            parsed,
            export_names,
            &mut BTreeSet::new(),
        ) else {
            continue;
        };
        if actual.is_none_or(|expr| argument_path_matches(expr, &expected, previous) == Some(false))
        {
            return false;
        }
    }
    argument_index == args.len()
}

/// A temporary only identifies its input when its immediately preceding
/// assignment proves the alias. Otherwise it is compatible with any path.
fn argument_path_matches(
    expr: &Expr,
    expected: &[String],
    previous: Option<&Stmt>,
) -> Option<bool> {
    if let Expr::Out(inner) | Expr::Persistent(inner) = expr {
        return argument_path_matches(inner, expected, previous);
    }
    if let Expr::Var(name) = expr {
        if name.starts_with('$') || name.starts_with("Temp_") {
            if let Some(Stmt::Assignment { lhs, rhs, .. }) = previous {
                if lhs == expr {
                    return argument_path_matches(rhs, expected, None);
                }
            }
            return None;
        }
    }
    Some(expression_path(expr).as_deref() == Some(expected))
}

fn expression_path(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Var(name) => Some(name.split('.').map(str::to_string).collect()),
        Expr::FieldAccess { recv, field } => {
            let mut path = expression_path(recv)?;
            path.push(field.clone());
            Some(path)
        }
        Expr::Out(inner) | Expr::Persistent(inner) => expression_path(inner),
        _ => None,
    }
}

/// Only recover direct data references. Calls, collection indexing and
/// ambiguous links remain unknown, rather than inventing expression identity.
fn graph_pin_path(
    link: &LinkedPin,
    parsed: &ParsedAsset,
    export_names: &[String],
    visited: &mut BTreeSet<(usize, [u8; 16])>,
) -> Option<Vec<String>> {
    use crate::bytecode::names::strip_guid_suffix;
    use crate::prop_query::find_struct_field_str;
    if !visited.insert((link.node, link.pin_id)) {
        return None;
    }
    let (header, properties) = parsed.exports.get(link.node.checked_sub(1)?)?;
    let pins = &parsed.pin_data.get(&link.node)?.pins;
    let output = pins
        .iter()
        .find(|pin| pin.pin_id == link.pin_id && pin.is_data_output())?;
    let class = crate::resolve::class_of(&parsed.imports, export_names, header);
    match class.rsplit('.').next()? {
        "K2Node_Knot" => {
            let input = pins
                .iter()
                .find(|pin| pin.direction == PIN_DIRECTION_INPUT && pin.pin_type != "exec")?;
            if input.linked_to.len() != 1 {
                return None;
            }
            graph_pin_path(&input.linked_to[0], parsed, export_names, visited)
        }
        "K2Node_FunctionEntry" => {
            let name = strip_guid_suffix(&output.name);
            let parent = pins
                .iter()
                .filter(|pin| pin.is_data_output() && pin.pin_id != output.pin_id)
                .filter(|pin| name.starts_with(&format!("{}_", pin.name)))
                .max_by_key(|pin| pin.name.len());
            match parent {
                Some(parent) => Some(vec![
                    parent.name.clone(),
                    name[parent.name.len() + 1..].to_string(),
                ]),
                None => Some(vec![name.to_string()]),
            }
        }
        "K2Node_VariableGet" => {
            let member = find_struct_field_str(properties, "VariableReference", "MemberName")?;
            let receiver = pins
                .iter()
                .find(|pin| pin.name == "self" && pin.direction == PIN_DIRECTION_INPUT);
            let mut path = if let Some(receiver) = receiver.filter(|pin| !pin.linked_to.is_empty())
            {
                if receiver.linked_to.len() != 1 {
                    return None;
                }
                graph_pin_path(&receiver.linked_to[0], parsed, export_names, visited)?
            } else if find_struct_field_str(properties, "VariableReference", "MemberScope")
                .is_some()
            {
                Vec::new()
            } else {
                vec!["self".to_string()]
            };
            path.push(member.clone());
            if let Some(field) = strip_guid_suffix(&output.name).strip_prefix(&format!("{member}_"))
            {
                path.push(field.to_string());
            }
            Some(path)
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "call_attribution_tests.rs"]
mod tests;
