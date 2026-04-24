//! Common-subexpression elimination for pure Blueprint node outputs.
//!
//! The decoder naturally emits each pure-node call at every consumer site, so
//! `GetInteractableActor(...)` or `BreakHitResult(...)` can appear multiple
//! times inside one function. The Blueprint editor treats these as a single
//! cached node whose output feeds all consumers.
//!
//! This pass runs on the pre-structure `Vec<BcStatement>`, detects pure-call
//! statements that appear at more than one site, and collapses later
//! occurrences so the downstream inline / discard passes produce a single
//! hoisted assignment followed by plain variable references.
//!
//! Two statement shapes carry a pure-node result:
//! - `$CallName_ReturnValue = CallName(args)` — a normal assignment whose
//!   lhs name is tied to the call (the decoder's `$<Call>_<Param>` /
//!   `$<Call>_ReturnValue` convention).
//! - `CallName(args, $CallName_OutParam, ...)` — a bare call whose output
//!   lives entirely in `$<Call>_*` out-param vars referenced at consumer
//!   sites.
//!
//! For the assignment shape, later occurrences rewrite their RHS to
//! `Expr::Var(keeper_lhs)`, the chain collapses through
//! `discard_unused_assignments` and the text-level inline passes. For the
//! bare-call shape, later occurrences become phantoms — the out-param vars
//! already reference the keeper's result.

use super::super::decode::{fmt_expr, BcStatement, Expr};
use crate::helpers::find_matching_paren;

/// Entry point. Walk the statement list, detect duplicate pure-call shapes,
/// and collapse later occurrences.
///
/// The identity key is the canonical rendering of the call expression
/// (`fmt_expr` of the RHS for assignments, `fmt_expr` of the whole call
/// for bare calls). This matches the task spec's "`fmt_expr`-based equality"
/// contract — two pure calls are considered equivalent iff their call trees
/// render identically.
///
/// Preserves `mem_offset` / `inlined_away` semantics so the structurer's
/// jump-target resolution still sees the original offsets.
pub fn cse_pure_calls(stmts: &mut [BcStatement]) {
    // First pass: classify every live statement, collect (idx, shape, key,
    // keeper_lhs_if_assignment).
    let mut entries: Vec<(usize, PureShape, String, Option<String>)> = Vec::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        if stmt.inlined_away {
            continue;
        }
        if let Some((shape, key, lhs)) = classify_pure(stmt) {
            entries.push((idx, shape, key, lhs));
        }
    }

    // Group by key; track the earliest index (with its lhs if any) as the
    // keeper.
    use std::collections::HashMap;
    struct Keeper {
        idx: usize,
        lhs: Option<String>,
    }
    let mut keepers: HashMap<String, Keeper> = HashMap::new();
    let mut duplicates: Vec<(usize, PureShape, String)> = Vec::new();
    for (idx, shape, key, lhs) in entries {
        use std::collections::hash_map::Entry;
        match keepers.entry(key.clone()) {
            Entry::Occupied(_) => duplicates.push((idx, shape, key)),
            Entry::Vacant(slot) => {
                slot.insert(Keeper { idx, lhs });
            }
        }
    }

    // Rewrite duplicates in order. We only mutate in place or phantom-mark,
    // so index positions stay valid.
    for (dup_idx, shape, key) in duplicates {
        let keeper = match keepers.get(&key) {
            Some(k) => k,
            None => continue,
        };
        if keeper.idx == dup_idx {
            continue;
        }
        match shape {
            PureShape::Assignment => {
                let Some(keeper_lhs) = keeper.lhs.as_ref() else {
                    continue;
                };
                let Some(dup_lhs) = lhs_name(&stmts[dup_idx]) else {
                    continue;
                };
                // Rewrite the duplicate's RHS to the keeper's lhs. The
                // chained `$X_1 = $X` assignment collapses through
                // discard_unused_assignments / inline_single_use_temps
                // downstream.
                let new_text = format!("{} = {}", dup_lhs, keeper_lhs);
                stmts[dup_idx].set_text(new_text);
            }
            PureShape::BareCall => {
                // The keeper's call already populated the shared
                // `$Call_*` out-param vars consumers reference; the
                // duplicate call is redundant. Mark phantom so its
                // mem_offset still anchors jump resolution.
                stmts[dup_idx].text.clear();
                stmts[dup_idx].inlined_away = true;
                stmts[dup_idx].reclassify();
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum PureShape {
    /// `$Name_ReturnValue = CallName(args)` where `Name` is linked to
    /// `CallName` via the decoder's naming convention.
    Assignment,
    /// `CallName(args, $CallName_OutParam, ...)` — bare call whose outputs
    /// live in `$CallName_*` out-param vars.
    BareCall,
}

/// Classify a statement as a pure-call shape.
///
/// Returns `Some((shape, key, lhs_if_assignment))` for pure-node shapes, or
/// `None` for anything else. The `key` is the canonical rendering used to
/// group duplicates — the call's RHS for assignments (so two assignments
/// whose lhs differ but whose call tree is identical bucket together), the
/// whole call for bare calls.
///
/// Uses the typed IR for assignment detection (shapes the parser handles)
/// and a text-based check for bare calls (the decoder's out-param
/// label syntax `Label: $Value` and `out $Var` prefixes aren't modeled by
/// the 5d.2 parser yet, so bare-call dedup stays on the text surface).
fn classify_pure(stmt: &BcStatement) -> Option<(PureShape, String, Option<String>)> {
    // Typed path via cached assignment() accessor: covers shapes the 5d.2
    // parser models.
    if let Some((lhs, rhs)) = stmt.assignment() {
        if let (
            Expr::Var(lhs_name),
            Expr::Call {
                name: call_name, ..
            },
        ) = (lhs, rhs)
        {
            if lhs_is_pure_shape(lhs_name, call_name) {
                let key = fmt_expr(rhs);
                return Some((PureShape::Assignment, key, Some(lhs_name.clone())));
            }
        }
        return None;
    }

    // Fall through to text-based bare-call detection. Handles shapes the
    // typed parser doesn't model (`Label: $Value`, `out $Var`).
    classify_bare_call_text(&stmt.text)
}

/// Text-level bare-call classifier. Recognises `CallName(args...)` shapes
/// where at least one argument looks like a `$CallName_*` out-param.
/// Returns the whole statement text as the key.
fn classify_bare_call_text(text: &str) -> Option<(PureShape, String, Option<String>)> {
    let text = text.trim();
    if !text.ends_with(')') {
        return None;
    }
    let paren_open = text.find('(')?;
    // Reject shapes that aren't a bare call: anything with ` = `, control
    // keywords, or non-identifier characters before the paren.
    if text[..paren_open].contains(' ') || text[..paren_open].contains('.') {
        return None;
    }
    let close_rel = find_matching_paren(&text[paren_open..])?;
    if paren_open + close_rel + 1 != text.len() {
        // Matched paren isn't the final char — this isn't a bare call.
        return None;
    }
    let call_name = &text[..paren_open];
    if call_name.is_empty()
        || !call_name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return None;
    }
    let args_str = &text[paren_open + 1..paren_open + close_rel];
    let out_marker = format!("${}_", call_name);
    if !args_str.contains(&out_marker) {
        return None;
    }
    Some((PureShape::BareCall, text.to_owned(), None))
}

/// True if `lhs_name` matches the decoder's pure-output naming convention
/// for `call`, i.e. `$<call>_ReturnValue` or `$<call>_<Something>`.
fn lhs_is_pure_shape(lhs_name: &str, call: &str) -> bool {
    let prefix = format!("${}_", call);
    lhs_name.starts_with(&prefix)
}

/// Extract the lhs name from a pure assignment statement. Uses the cached
/// `assignment()` accessor on `BcStatement` to avoid re-parsing.
fn lhs_name(stmt: &BcStatement) -> Option<String> {
    match stmt.assignment()? {
        (Expr::Var(name), _) => Some(name.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(stmts: &[BcStatement]) -> Vec<String> {
        stmts.iter().map(|s| s.text.clone()).collect()
    }

    #[test]
    fn empty_stmts_is_noop() {
        let mut stmts: Vec<BcStatement> = Vec::new();
        cse_pure_calls(&mut stmts);
        assert!(stmts.is_empty());
    }

    #[test]
    fn single_pure_call_is_noop() {
        let mut stmts = vec![BcStatement::new(
            0,
            "$GetInteractableActor_InteractableActor = GetInteractableActor(Hand)",
        )];
        let before = texts(&stmts);
        cse_pure_calls(&mut stmts);
        assert_eq!(texts(&stmts), before);
    }

    #[test]
    fn two_identical_pure_assignments_chain_second() {
        let mut stmts = vec![
            BcStatement::new(
                0,
                "$GetInteractableActor_InteractableActor = GetInteractableActor(Hand)",
            ),
            BcStatement::new(
                4,
                "$GetInteractableActor_InteractableActor_1 = GetInteractableActor(Hand)",
            ),
        ];
        cse_pure_calls(&mut stmts);
        assert_eq!(
            stmts[0].text,
            "$GetInteractableActor_InteractableActor = GetInteractableActor(Hand)"
        );
        assert_eq!(
            stmts[1].text,
            "$GetInteractableActor_InteractableActor_1 = $GetInteractableActor_InteractableActor"
        );
    }

    #[test]
    fn different_args_is_noop() {
        let mut stmts = vec![
            BcStatement::new(
                0,
                "$GetInteractableActor_InteractableActor = GetInteractableActor(LeftHand)",
            ),
            BcStatement::new(
                4,
                "$GetInteractableActor_InteractableActor_1 = GetInteractableActor(RightHand)",
            ),
        ];
        let before = texts(&stmts);
        cse_pure_calls(&mut stmts);
        assert_eq!(texts(&stmts), before);
    }

    #[test]
    fn four_identical_pure_assignments_chain_three() {
        let call = "Foo(x)";
        let mut stmts = vec![
            BcStatement::new(0, format!("$Foo_ReturnValue = {}", call)),
            BcStatement::new(4, format!("$Foo_ReturnValue_1 = {}", call)),
            BcStatement::new(8, format!("$Foo_ReturnValue_2 = {}", call)),
            BcStatement::new(12, format!("$Foo_ReturnValue_3 = {}", call)),
        ];
        cse_pure_calls(&mut stmts);
        assert_eq!(stmts[0].text, format!("$Foo_ReturnValue = {}", call));
        assert_eq!(stmts[1].text, "$Foo_ReturnValue_1 = $Foo_ReturnValue");
        assert_eq!(stmts[2].text, "$Foo_ReturnValue_2 = $Foo_ReturnValue");
        assert_eq!(stmts[3].text, "$Foo_ReturnValue_3 = $Foo_ReturnValue");
    }

    #[test]
    fn non_pure_shaped_lhs_not_touched() {
        // Two calls whose lhs names don't match the decoder's $Call_*
        // convention. These aren't pure-node outputs per the heuristic.
        let mut stmts = vec![
            BcStatement::new(0, "self.X = Foo(1)"),
            BcStatement::new(4, "self.Y = Foo(1)"),
        ];
        let before = texts(&stmts);
        cse_pure_calls(&mut stmts);
        assert_eq!(texts(&stmts), before);
    }

    #[test]
    fn bare_call_duplicates_phantomed() {
        let call = "BreakHitResult($Hit, out $BreakHitResult_HitActor)";
        let mut stmts = vec![
            BcStatement::new(0, call),
            BcStatement::new(4, "other_stmt"),
            BcStatement::new(8, call),
            BcStatement::new(12, call),
        ];
        cse_pure_calls(&mut stmts);
        assert_eq!(stmts[0].text, call);
        assert_eq!(stmts[1].text, "other_stmt");
        assert!(
            stmts[2].inlined_away,
            "second BreakHitResult should be phantomed"
        );
        assert!(stmts[2].text.is_empty());
        assert!(
            stmts[3].inlined_away,
            "third BreakHitResult should be phantomed"
        );
    }

    #[test]
    fn bare_call_with_labeled_args_dedups() {
        // Real-world shape from AttemptGrip: labeled out-params the 5d.2
        // parser currently renders as `Stmt::Unknown`, so the pass falls
        // back to text-level classification.
        let call = "BreakHitResult($TraceForGrippableActors_HitResult, ImpactPoint: $BreakHitResult_ImpactPoint, HitActor: $BreakHitResult_HitActor)";
        let mut stmts = vec![
            BcStatement::new(0, call),
            BcStatement::new(4, "some_other_stmt"),
            BcStatement::new(8, call),
        ];
        cse_pure_calls(&mut stmts);
        assert_eq!(stmts[0].text, call);
        assert_eq!(stmts[1].text, "some_other_stmt");
        assert!(stmts[2].inlined_away);
        assert!(stmts[2].text.is_empty());
    }

    #[test]
    fn bare_call_without_out_param_not_touched() {
        // A call that doesn't populate any `$Foo_*` out-param is not a
        // pure-node output by the heuristic; leave it alone even if it
        // repeats.
        let call = "SetHealth(100)";
        let mut stmts = vec![BcStatement::new(0, call), BcStatement::new(4, call)];
        let before = texts(&stmts);
        cse_pure_calls(&mut stmts);
        assert_eq!(texts(&stmts), before);
    }
}
