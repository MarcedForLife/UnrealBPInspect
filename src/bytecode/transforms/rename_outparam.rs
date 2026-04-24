//! Contextual rename of out-param temps from `$<Call>_<Param>` to `$<Param>`.
//!
//! The decoder names out-param temps as `$<CallName>_<OutParam>` (e.g.
//! `$GetInteractableActor_InteractableActor`). That's unambiguous machine-
//! readable output, but noisy for pseudocode. When the short form
//! `$<OutParam>` is unambiguous within the function scope, we prefer it.
//!
//! This pass runs late in the per-function pipeline, after CSE, so the
//! surviving out-param temps are the ones consumers actually reference.
//!
//! ## Collection
//!
//! Per function:
//! - `call_names`: every identifier that appears as a callable name in
//!   `Expr::Call` or `Expr::MethodCall`.
//! - `var_names`: every `$<...>` identifier that appears in `Expr::Var`,
//!   both read and LHS.
//!
//! ## Rename rules
//!
//! For each `$<Call>_<Rest>` var whose `<Call>` matches a collected call
//! name (longest prefix wins, since some call names contain underscores),
//! the candidate short form is `$<Rest>`. A candidate is promoted to a
//! rename only when:
//! - `$<Rest>` is not already in `var_names` (no shadowing), AND
//! - No other `$<OtherCall>_<Rest>` produces the same `$<Rest>`.
//!
//! Collisions stay as their full form.
//!
//! ## Rewrite
//!
//! Rewrite happens on the text surface via whole-token replacement. The
//! typed-IR is used strictly for collection, the text rewrite guarantees
//! that pass output is byte-for-byte identical except for the renamed
//! tokens.

use super::super::decode::{parse_stmt, Expr, Stmt};
use super::is_var_boundary;
use super::temps::visit_exprs;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Operates on the post-structure line list. Parses each line through
/// `parse_stmt` to collect call names and `$`-temps, then rewrites
/// `$<Call>_<Rest>` -> `$<Rest>` wherever the short form is unambiguous.
/// Structured lines such as `if (COND) {` or `} else {` surface their
/// embedded expressions through `Stmt::IfOpen` / `Stmt::Else`. Shapes
/// `parse_stmt` can't model fall through to `Stmt::Unknown`, which a
/// text-level call/var extractor handles as a best-effort fallback.
pub fn rename_outparam_temps_text(lines: &mut [String]) {
    let mut call_names: BTreeSet<String> = BTreeSet::new();
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    for line in lines.iter() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let parsed = parse_stmt(trimmed);
        collect_from_stmt(&parsed, &mut call_names, &mut var_names);
    }

    let rename_map = build_rename_map(&call_names, &var_names);
    if rename_map.is_empty() {
        return;
    }

    for line in lines.iter_mut() {
        let new_line = apply_rename_map(line, &rename_map);
        if new_line != *line {
            *line = new_line;
        }
    }
}

/// Build the final `full -> short` rename map, applying the collision
/// rules described in the module header.
fn build_rename_map(
    call_names: &BTreeSet<String>,
    var_names: &BTreeSet<String>,
) -> HashMap<String, String> {
    // First pass: for every `$<Call>_<Rest>` var, compute its candidate
    // short form `$<Rest>`. Use the longest matching call-name prefix.
    // Group candidates by short form so we can detect collisions.
    let mut candidates: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for var in var_names {
        let Some(rest) = var.strip_prefix('$') else {
            continue;
        };
        let Some(short_rest) = longest_call_prefix_strip(rest, call_names) else {
            continue;
        };
        if short_rest.is_empty() {
            continue;
        }
        // Reject pure-digit remainders. `$Foo_1` is the CSE-chained
        // duplicate disambiguator, not an out-param; renaming to `$1`
        // would produce an invalid identifier.
        if short_rest.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        let short = format!("${}", short_rest);
        candidates.entry(short).or_default().push(var.clone());
    }

    // Promote unambiguous candidates to the rename map.
    let mut map: HashMap<String, String> = HashMap::new();
    for (short, sources) in candidates {
        if sources.len() != 1 {
            // Two full-form vars would collapse to the same short form.
            continue;
        }
        if var_names.contains(&short) {
            // Short form already exists as its own var, keep the full
            // form to avoid aliasing.
            continue;
        }
        map.insert(sources.into_iter().next().unwrap(), short);
    }
    map
}

/// Strip the longest call-name prefix of the form `Call_` from `rest`.
/// Returns the remainder (the candidate short name) or `None` if no
/// known call prefixes `rest`.
fn longest_call_prefix_strip(rest: &str, call_names: &BTreeSet<String>) -> Option<String> {
    let best_call = call_names
        .iter()
        .filter(|call| rest.starts_with(&format!("{}_", call)))
        .max_by_key(|call| call.len())?;
    rest.strip_prefix(&format!("{}_", best_call))
        .map(str::to_owned)
}

/// Apply every rename in `map` to `text` via whole-token substitution.
/// Iterates the map entries in a stable order (longest full-form first)
/// so a longer full-form var can't be partially matched by a shorter
/// entry's short form inside another token.
fn apply_rename_map(text: &str, map: &HashMap<String, String>) -> String {
    if map.is_empty() {
        return text.to_string();
    }
    let mut entries: Vec<(&String, &String)> = map.iter().collect();
    // Longest full-form first so `$Foo_ReturnValue_1` is rewritten
    // before `$Foo_ReturnValue` (if both were in the map, which is
    // rejected by the collision rule, but defensive ordering doesn't
    // hurt).
    entries.sort_by(|left, right| right.0.len().cmp(&left.0.len()));

    let mut current = text.to_string();
    for (full, short) in entries {
        current = replace_whole_token(&current, full, short);
    }
    current
}

/// Replace every whole-token occurrence of `needle` with `replacement`
/// in `text`. Uses `is_var_boundary` so `$Foo_X` does not match inside
/// `$Foo_X_Y`.
fn replace_whole_token(text: &str, needle: &str, replacement: &str) -> String {
    if !text.contains(needle) {
        return text.to_string();
    }
    let mut out = String::with_capacity(text.len());
    let mut start = 0;
    while let Some(rel) = text[start..].find(needle) {
        let pos = start + rel;
        if is_var_boundary(text, pos, needle) {
            out.push_str(&text[start..pos]);
            out.push_str(replacement);
            start = pos + needle.len();
        } else {
            // No boundary: copy through the char we found and advance
            // past it.
            out.push_str(&text[start..pos + needle.len()]);
            start = pos + needle.len();
        }
    }
    out.push_str(&text[start..]);
    out
}

/// Drive `collect_from_expr` over every `Expr` reachable from `stmt`, plus
/// fall back to a text-level extractor for `Stmt::Unknown` and
/// `Stmt::Comment` whose payloads `visit_exprs` skips.
fn collect_from_stmt(stmt: &Stmt, calls: &mut BTreeSet<String>, vars: &mut BTreeSet<String>) {
    match stmt {
        Stmt::Unknown(raw) | Stmt::Comment(raw) => collect_from_text(raw, calls, vars),
        _ => visit_exprs(stmt, &mut |expr| collect_from_expr(expr, calls, vars)),
    }
}

fn collect_from_expr(expr: &Expr, calls: &mut BTreeSet<String>, vars: &mut BTreeSet<String>) {
    expr.walk(&mut |node| match node {
        Expr::Var(name) if name.starts_with('$') => {
            vars.insert(name.clone());
        }
        Expr::Call { name, .. } | Expr::MethodCall { name, .. } => {
            calls.insert(name.clone());
        }
        Expr::Unknown(raw) => collect_from_text(raw, calls, vars),
        _ => {}
    });
}

/// Extract `$Name` tokens and likely call names from a raw text payload.
/// Used as a best-effort fallback for `Stmt::Unknown` / `Expr::Unknown`
/// shapes the typed parser doesn't model.
fn collect_from_text(text: &str, calls: &mut BTreeSet<String>, vars: &mut BTreeSet<String>) {
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let byte = bytes[i];
        if byte == b'$' {
            let start = i;
            i += 1;
            while i < bytes.len() && is_ident_byte(bytes[i]) {
                i += 1;
            }
            if i > start + 1 {
                vars.insert(text[start..i].to_string());
            }
            continue;
        }
        if is_ident_start(byte) {
            let start = i;
            while i < bytes.len() && is_ident_byte(bytes[i]) {
                i += 1;
            }
            // Treat as call name only if followed by `(`.
            if i < bytes.len() && bytes[i] == b'(' {
                calls.insert(text[start..i].to_string());
            }
            continue;
        }
        i += 1;
    }
}

#[inline]
fn is_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

#[inline]
fn is_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(texts: &[&str]) -> Vec<String> {
        texts.iter().map(|text| text.to_string()).collect()
    }

    #[test]
    fn empty_is_noop() {
        let mut list: Vec<String> = Vec::new();
        rename_outparam_temps_text(&mut list);
        assert!(list.is_empty());
    }

    #[test]
    fn single_occurrence_is_renamed() {
        let mut list = lines(&[
            "GetInteractableActor(Hand, $GetInteractableActor_InteractableActor)",
            "if (IsValid($GetInteractableActor_InteractableActor)) {",
            "    self.X = $GetInteractableActor_InteractableActor",
            "}",
        ]);
        rename_outparam_temps_text(&mut list);
        assert_eq!(
            list,
            lines(&[
                "GetInteractableActor(Hand, $InteractableActor)",
                "if (IsValid($InteractableActor)) {",
                "    self.X = $InteractableActor",
                "}",
            ])
        );
    }

    #[test]
    fn short_form_collision_keeps_full_form() {
        // `$InteractableActor` is already in use as a standalone var,
        // so the short form is unavailable.
        let mut list = lines(&[
            "self.Y = $InteractableActor",
            "GetInteractableActor(Hand, $GetInteractableActor_InteractableActor)",
            "self.X = $GetInteractableActor_InteractableActor",
        ]);
        let before = list.clone();
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, before);
    }

    #[test]
    fn two_call_prefix_collision_keeps_full_form() {
        // Both `FooA_Actor` and `FooB_Actor` would rename to `$Actor`,
        // so neither gets renamed.
        let mut list = lines(&[
            "FooA(out $FooA_Actor)",
            "FooB(out $FooB_Actor)",
            "self.X = $FooA_Actor",
            "self.Y = $FooB_Actor",
        ]);
        let before = list.clone();
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, before);
    }

    #[test]
    fn short_form_digit_only_rejected() {
        // `$Foo_1` shouldn't produce candidate `$1` — pure-digit
        // remainders are CSE dedup markers, not meaningful names.
        let mut list = lines(&["Foo(x)", "$Foo = Foo(a)", "$Foo_1 = Foo(b)"]);
        let before = list.clone();
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, before);
    }

    #[test]
    fn dollar_cast_class_not_renamed() {
        // `$Cast_ClassName` uses the dynamic-cast temp convention, not
        // the out-param convention. The rename pass ignores it because
        // `Cast` is not a collected call name (there is no `Cast(...)`
        // call in this input).
        let mut list = lines(&["$Cast_AsActor = icast<Actor>($Foo)"]);
        let before = list.clone();
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, before);
    }

    #[test]
    fn word_boundary_respected() {
        // Two different full forms produce two different short forms,
        // each unique; both rename without one partially matching inside
        // the other's token.
        let mut list = lines(&["Foo(out $Foo_Bar, out $Foo_Bar_Baz)"]);
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, lines(&["Foo(out $Bar, out $Bar_Baz)"]));
    }

    #[test]
    fn longest_call_prefix_wins() {
        // Both `Do` and `DoThing` are call names in scope. The var
        // `$DoThing_Result` should strip the longer prefix so the
        // short form is `$Result`, not `$Thing_Result`.
        let mut list = lines(&[
            "Do(x)",
            "DoThing(y, out $DoThing_Result)",
            "self.X = $DoThing_Result",
        ]);
        rename_outparam_temps_text(&mut list);
        assert_eq!(
            list,
            lines(&["Do(x)", "DoThing(y, out $Result)", "self.X = $Result",])
        );
    }

    #[test]
    fn call_name_not_in_scope_skipped() {
        let mut list = lines(&["self.X = $Foo_Bar"]);
        let before = list.clone();
        rename_outparam_temps_text(&mut list);
        assert_eq!(list, before);
    }
}
