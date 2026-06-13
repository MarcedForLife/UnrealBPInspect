//! Call graph builder for the decoded asset.
//!
//! Walks the typed statement/expression tree and builds caller-to-callee
//! and callee-to-caller indexes from the decoded calls directly, rather
//! than by matching rendered text.
//!
//! The output uses `BTreeMap`/`BTreeSet` so iteration order is
//! deterministic across runs and platforms.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::emit::summary::is_latent_function;
use crate::bytecode::expr::Expr;
use crate::bytecode::stmt::Stmt;

/// Latent-call resume continuations keyed by the originating call's disk
/// offset, threaded through the statement walk so a latent call's resume
/// body is attributed to the function that issued the call (mirroring the
/// emitter's inline interleave).
type ResumeBodies = BTreeMap<usize, Vec<Stmt>>;

/// Maps each caller name to the set of callees it invokes.
pub type CalleesMap = BTreeMap<String, BTreeSet<String>>;

/// Maps each callee name to the set of callers that invoke it.
pub type CallersMap = BTreeMap<String, BTreeSet<String>>;

/// Build a call graph from a decoded Blueprint asset.
///
/// Visits every `Stmt::Call` and `Stmt::EventCall` in every function and
/// event body, including nested positions inside Branch/Sequence/Loop/Switch/
/// Latch and the resume continuation of a latent call (`Delay`,
/// `MoveComponentTo`, etc.). Also descends into `Expr::Call` and
/// `Expr::MethodCall` found in argument positions.
///
/// Returns `(callees_map, callers_map)`:
/// - `callees_map[caller]` is the set of functions/events that `caller` calls.
/// - `callers_map[callee]` is the set of functions/events that call `callee`.
pub fn build_call_graph(asset: &DecodedAsset) -> (CalleesMap, CallersMap) {
    let mut callees_map: CalleesMap = BTreeMap::new();
    let mut callers_map: CallersMap = BTreeMap::new();

    let bodies = asset
        .functions
        .iter()
        .map(|func| (func.name.as_str(), func.body.as_slice()))
        .chain(
            asset
                .events
                .iter()
                .map(|event| (event.name.as_str(), event.body.as_slice())),
        );
    for (caller, body) in bodies {
        let mut callees: BTreeSet<String> = BTreeSet::new();
        let mut visited_resumes: BTreeSet<usize> = BTreeSet::new();
        for stmt in body {
            collect_stmt_calls(
                stmt,
                &asset.resume_bodies,
                &mut visited_resumes,
                &mut callees,
            );
        }
        for callee in &callees {
            callers_map
                .entry(callee.clone())
                .or_default()
                .insert(caller.to_string());
        }
        if !callees.is_empty() {
            callees_map.insert(caller.to_string(), callees);
        }
    }

    (callees_map, callers_map)
}

/// Collect all callee names reachable from a single statement, appending
/// them into `out`. Handles all structured `Stmt` variants recursively.
///
/// A latent `Stmt::Call` (`Delay`, `MoveComponentTo`, etc.) with a resume
/// continuation at its disk offset descends into that continuation, so the
/// calls in a latent action's resume body are attributed to the function
/// that issued the call. This mirrors the summary emitter, which interleaves
/// the resume body inline at the call site. `visited` guards against
/// re-walking a resume body if the same offset is reached twice.
fn collect_stmt_calls(
    stmt: &Stmt,
    resume_bodies: &ResumeBodies,
    visited: &mut BTreeSet<usize>,
    out: &mut BTreeSet<String>,
) {
    match stmt {
        Stmt::Call { func, args, offset } => {
            if let Some(name) = callee_name_from_expr(func) {
                if is_latent_function(&name) && visited.insert(*offset) {
                    if let Some(resume_body) = resume_bodies.get(offset) {
                        for stmt in resume_body {
                            collect_stmt_calls(stmt, resume_bodies, visited, out);
                        }
                    }
                }
                out.insert(name);
            }
            for arg in args {
                collect_expr_calls(arg, out);
            }
        }

        Stmt::EventCall { event_name, .. } => {
            out.insert(event_name.clone());
        }

        Stmt::Assignment { rhs, .. } => {
            collect_expr_calls(rhs, out);
        }

        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_expr_calls(cond, out);
            for stmt in then_body {
                collect_stmt_calls(stmt, resume_bodies, visited, out);
            }
            for stmt in else_body {
                collect_stmt_calls(stmt, resume_bodies, visited, out);
            }
        }

        Stmt::Sequence { pins, .. } => {
            for pin_body in pins {
                for stmt in pin_body {
                    collect_stmt_calls(stmt, resume_bodies, visited, out);
                }
            }
        }

        Stmt::Loop {
            cond,
            body,
            completion,
            ..
        } => {
            if let Some(cond_expr) = cond {
                collect_expr_calls(cond_expr, out);
            }
            for stmt in body {
                collect_stmt_calls(stmt, resume_bodies, visited, out);
            }
            if let Some(completion_body) = completion {
                for stmt in completion_body {
                    collect_stmt_calls(stmt, resume_bodies, visited, out);
                }
            }
        }

        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            collect_expr_calls(expr, out);
            for case in cases {
                for value in &case.values {
                    collect_expr_calls(value, out);
                }
                for stmt in &case.body {
                    collect_stmt_calls(stmt, resume_bodies, visited, out);
                }
            }
            if let Some(default_body) = default {
                for stmt in default_body {
                    collect_stmt_calls(stmt, resume_bodies, visited, out);
                }
            }
        }

        Stmt::Latch { init, body, .. } => {
            for stmt in init {
                collect_stmt_calls(stmt, resume_bodies, visited, out);
            }
            for stmt in body {
                collect_stmt_calls(stmt, resume_bodies, visited, out);
            }
        }

        Stmt::Return { value, .. } => {
            if let Some(val_expr) = value {
                collect_expr_calls(val_expr, out);
            }
        }

        Stmt::Break { .. } | Stmt::Unknown { .. } => {}
    }
}

/// Collect callee names from call-bearing expression positions.
///
/// Handles `Expr::Call` and `Expr::MethodCall` directly, and descends
/// into sub-expressions inside compound forms (Binary, Unary, Cast, etc.)
/// so that calls nested in argument chains are not missed.
fn collect_expr_calls(expr: &Expr, out: &mut BTreeSet<String>) {
    match expr {
        Expr::Call { name, args } => {
            out.insert(name.clone());
            for arg in args {
                collect_expr_calls(arg, out);
            }
        }

        Expr::MethodCall { recv, name, args } => {
            out.insert(name.clone());
            collect_expr_calls(recv, out);
            for arg in args {
                collect_expr_calls(arg, out);
            }
        }

        Expr::Binary { lhs, rhs, .. } => {
            collect_expr_calls(lhs, out);
            collect_expr_calls(rhs, out);
        }

        Expr::Unary { operand, .. } => {
            collect_expr_calls(operand, out);
        }

        Expr::Cast { inner, .. } => {
            collect_expr_calls(inner, out);
        }

        Expr::Index { recv, idx } => {
            collect_expr_calls(recv, out);
            collect_expr_calls(idx, out);
        }

        Expr::FieldAccess { recv, .. } => {
            collect_expr_calls(recv, out);
        }

        Expr::ArrayLit(items) => {
            for item in items {
                collect_expr_calls(item, out);
            }
        }

        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_calls(cond, out);
            collect_expr_calls(then_expr, out);
            collect_expr_calls(else_expr, out);
        }

        Expr::Switch {
            index,
            cases,
            default,
        } => {
            collect_expr_calls(index, out);
            for case in cases {
                collect_expr_calls(&case.value, out);
                collect_expr_calls(&case.body, out);
            }
            collect_expr_calls(default, out);
        }

        Expr::Out(inner) | Expr::Interface(inner) | Expr::Persistent(inner) => {
            collect_expr_calls(inner, out);
        }

        Expr::Resume { inner, .. } => {
            collect_expr_calls(inner, out);
        }

        Expr::StructConstruct { fields, .. } => {
            for (_field_name, field_expr) in fields {
                collect_expr_calls(field_expr, out);
            }
        }

        Expr::Literal(_) | Expr::Var(_) | Expr::Unknown { .. } => {}
    }
}

/// Extract a callee name string from the function-position expression of a
/// `Stmt::Call`. The decoder places the call target here as one of:
/// - `Expr::Var(name)` for a plain local or global function reference.
/// - `Expr::Call { name, .. }` for a free-function call in func position
///   (unusual but possible in nested patterns).
/// - `Expr::MethodCall { name, .. }` for a method call.
/// - `Expr::FieldAccess { field, .. }` for a field-resolved call target.
///
/// Anything else (Literal, Index, Unknown, etc.) cannot be named and returns
/// `None`.
fn callee_name_from_expr(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Var(name) => Some(name.clone()),
        Expr::Call { name, .. } => Some(name.clone()),
        Expr::MethodCall { name, .. } => Some(name.clone()),
        Expr::FieldAccess { field, .. } => Some(field.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::asset::{DecodedAsset, Event, Function};
    use crate::bytecode::expr::Expr;
    use crate::bytecode::stmt::Stmt;

    fn make_asset(functions: Vec<Function>, events: Vec<Event>) -> DecodedAsset {
        DecodedAsset {
            functions,
            events,
            resume_bodies: std::collections::BTreeMap::new(),
            ubergraph_byte_map: None,
        }
    }

    fn make_function(name: &str, body: Vec<Stmt>) -> Function {
        Function {
            name: name.to_string(),
            body,
            export_index: None,
        }
    }

    fn make_event(name: &str, body: Vec<Stmt>) -> Event {
        Event {
            name: name.to_string(),
            body,
            export_index: None,
        }
    }

    fn call_stmt(func_expr: Expr) -> Stmt {
        Stmt::Call {
            func: func_expr,
            args: vec![],
            offset: 0,
        }
    }

    #[test]
    fn empty_asset_yields_empty_maps() {
        let asset = make_asset(vec![], vec![]);
        let (callees, callers) = build_call_graph(&asset);
        assert!(callees.is_empty());
        assert!(callers.is_empty());
    }

    #[test]
    fn simple_function_call() {
        let body = vec![call_stmt(Expr::Var("Bar".into()))];
        let asset = make_asset(vec![make_function("Foo", body)], vec![]);
        let (callees, callers) = build_call_graph(&asset);

        assert_eq!(
            callees.get("Foo").unwrap(),
            &BTreeSet::from(["Bar".to_string()])
        );
        assert_eq!(
            callers.get("Bar").unwrap(),
            &BTreeSet::from(["Foo".to_string()])
        );
    }

    #[test]
    fn nested_call_in_branch_arm() {
        let inner_call = call_stmt(Expr::Var("DeepFn".into()));
        let branch = Stmt::Branch {
            cond: Expr::Literal("true".into()),
            then_body: vec![inner_call],
            else_body: vec![],
            offset: 0,
        };
        let asset = make_asset(vec![make_function("Outer", vec![branch])], vec![]);
        let (callees, callers) = build_call_graph(&asset);

        assert!(callees["Outer"].contains("DeepFn"));
        assert!(callers["DeepFn"].contains("Outer"));
    }

    #[test]
    fn method_call_resolves_to_method_name() {
        let method_call_expr = Expr::MethodCall {
            recv: Box::new(Expr::Var("self".into())),
            name: "GetHealth".into(),
            args: vec![],
        };
        let stmt = Stmt::Call {
            func: Expr::Var("Wrapper".into()),
            args: vec![method_call_expr],
            offset: 0,
        };
        let asset = make_asset(vec![make_function("Actor", vec![stmt])], vec![]);
        let (callees, _callers) = build_call_graph(&asset);

        let actor_callees = callees.get("Actor").unwrap();
        assert!(actor_callees.contains("Wrapper"));
        assert!(actor_callees.contains("GetHealth"));
    }

    #[test]
    fn multiple_callers_to_same_callee() {
        let foo_body = vec![call_stmt(Expr::Var("Bar".into()))];
        let baz_body = vec![call_stmt(Expr::Var("Bar".into()))];
        let asset = make_asset(
            vec![
                make_function("Foo", foo_body),
                make_function("Baz", baz_body),
            ],
            vec![],
        );
        let (_callees, callers) = build_call_graph(&asset);

        let bar_callers = callers.get("Bar").unwrap();
        assert!(bar_callers.contains("Foo"));
        assert!(bar_callers.contains("Baz"));
    }

    #[test]
    fn eventcall_routes_through_callgraph() {
        // Event-host case: an event body issuing an EventCall.
        let event_body = vec![Stmt::EventCall {
            event_name: "Foo".into(),
            offset: 0,
        }];
        let asset = make_asset(vec![], vec![make_event("Trigger", event_body)]);
        let (callees, callers) = build_call_graph(&asset);

        assert!(callees["Trigger"].contains("Foo"));
        assert!(callers["Foo"].contains("Trigger"));

        // Function-host case: a function body issuing an EventCall.
        let function_body = vec![Stmt::EventCall {
            event_name: "OnOverlap".into(),
            offset: 0,
        }];
        let asset = make_asset(vec![make_function("Trigger", function_body)], vec![]);
        let (callees, callers) = build_call_graph(&asset);

        assert!(callees["Trigger"].contains("OnOverlap"));
        assert!(callers["OnOverlap"].contains("Trigger"));
    }
}
