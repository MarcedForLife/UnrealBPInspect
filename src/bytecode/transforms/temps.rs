//! Temp variable inlining and dead assignment removal.

use super::{
    count_var_refs, expr_has_call, is_trivial_expr, parse_temp_assignment, substitute_var,
};
use crate::bytecode::decode::{
    fmt_expr, fmt_stmt, parse_expr, parse_stmt, top_level_eq_split, BcStatement, Expr, Stmt,
    StmtKind,
};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Recursively substitute every `Expr::Var(var_name)` occurrence in `expr`
/// with `replacement`. Consumes `replacement` only when needed; callers
/// typically clone once up front and rely on `Expr::Clone` for each hit.
fn substitute_in_expr(expr: &mut Expr, var_name: &str, replacement: &Expr) {
    match expr {
        Expr::Var(name) => {
            if name == var_name {
                *expr = replacement.clone();
            }
        }
        Expr::Literal(_) | Expr::Unknown(_) => {}
        Expr::Call { args, .. } => {
            for arg in args {
                substitute_in_expr(arg, var_name, replacement);
            }
        }
        Expr::MethodCall { recv, args, .. } => {
            substitute_in_expr(recv, var_name, replacement);
            for arg in args {
                substitute_in_expr(arg, var_name, replacement);
            }
        }
        Expr::FieldAccess { recv, .. } => {
            substitute_in_expr(recv, var_name, replacement);
        }
        Expr::Index { recv, idx } => {
            substitute_in_expr(recv, var_name, replacement);
            substitute_in_expr(idx, var_name, replacement);
        }
        Expr::Binary { lhs, rhs, .. } => {
            substitute_in_expr(lhs, var_name, replacement);
            substitute_in_expr(rhs, var_name, replacement);
        }
        Expr::Unary { operand, .. } => {
            substitute_in_expr(operand, var_name, replacement);
        }
        Expr::Cast { inner, .. } => {
            substitute_in_expr(inner, var_name, replacement);
        }
        Expr::StructConstruct { fields, .. } => {
            for (_, value) in fields {
                substitute_in_expr(value, var_name, replacement);
            }
        }
        Expr::Select {
            cond,
            then_expr,
            else_expr,
        }
        | Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            substitute_in_expr(cond, var_name, replacement);
            substitute_in_expr(then_expr, var_name, replacement);
            substitute_in_expr(else_expr, var_name, replacement);
        }
        Expr::Switch {
            scrut,
            arms,
            default,
        } => {
            substitute_in_expr(scrut, var_name, replacement);
            for arm in arms {
                substitute_in_expr(&mut arm.pat, var_name, replacement);
                substitute_in_expr(&mut arm.body, var_name, replacement);
            }
            if let Some(default_expr) = default {
                substitute_in_expr(default_expr, var_name, replacement);
            }
        }
        Expr::Trailer { inner, .. } => {
            substitute_in_expr(inner, var_name, replacement);
        }
        Expr::Out(inner) => {
            substitute_in_expr(inner, var_name, replacement);
        }
        Expr::ArrayLit(items) => {
            for item in items {
                substitute_in_expr(item, var_name, replacement);
            }
        }
    }
}

/// True if any node in `expr` is `Expr::Unknown`. Used to fall back to text
/// substitution when the 5d.2 parser hasn't modelled a shape yet.
fn expr_contains_unknown(expr: &Expr) -> bool {
    let mut found = false;
    expr.walk(&mut |node| {
        if matches!(node, Expr::Unknown(_)) {
            found = true;
        }
    });
    found
}

/// Visit every `Expr` immediately embedded in `stmt` with `f`. `WithTrailer`
/// recurses into its inner `Stmt`; `Stmt::Unknown` and the expression-free
/// control-flow markers (PopFlow, BlockClose, Break, Else, ...) are
/// skipped. New `Stmt` variants that carry an `Expr` must be added here
/// — it's the single source of truth for "which statements carry
/// substitutable expressions."
pub(crate) fn visit_exprs_mut(stmt: &mut Stmt, f: &mut impl FnMut(&mut Expr)) {
    match stmt {
        Stmt::Assignment { lhs, rhs } | Stmt::CompoundAssign { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        Stmt::Call { expr }
        | Stmt::PopFlowIfNot { cond: expr }
        | Stmt::ContinueIfNot { cond: expr }
        | Stmt::IfJump { cond: expr, .. }
        | Stmt::JumpComputed { expr } => f(expr),
        Stmt::IfOpen { cond } => f(cond),
        Stmt::WithTrailer { inner, .. } => visit_exprs_mut(inner, f),
        Stmt::PopFlow
        | Stmt::PushFlow { .. }
        | Stmt::Jump { .. }
        | Stmt::ReturnNop
        | Stmt::BareReturn
        | Stmt::Comment(_)
        | Stmt::BlockClose
        | Stmt::Break
        | Stmt::Else
        | Stmt::Unknown(_) => {}
    }
}

/// Immutable version of [`visit_exprs_mut`] used by contains-predicate
/// walkers. Keeps the variant list in lockstep by dispatching through the
/// same match shape.
pub(crate) fn visit_exprs(stmt: &Stmt, f: &mut impl FnMut(&Expr)) {
    match stmt {
        Stmt::Assignment { lhs, rhs } | Stmt::CompoundAssign { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        Stmt::Call { expr }
        | Stmt::PopFlowIfNot { cond: expr }
        | Stmt::ContinueIfNot { cond: expr }
        | Stmt::IfJump { cond: expr, .. }
        | Stmt::JumpComputed { expr } => f(expr),
        Stmt::IfOpen { cond } => f(cond),
        Stmt::WithTrailer { inner, .. } => visit_exprs(inner, f),
        Stmt::PopFlow
        | Stmt::PushFlow { .. }
        | Stmt::Jump { .. }
        | Stmt::ReturnNop
        | Stmt::BareReturn
        | Stmt::Comment(_)
        | Stmt::BlockClose
        | Stmt::Break
        | Stmt::Else
        | Stmt::Unknown(_) => {}
    }
}

/// Walk every `Expr` inside `stmt` and substitute `Expr::Var(var_name)`
/// nodes with `replacement`. No-op for `Stmt::Unknown` (the raw text has
/// no typed tree to rewrite).
fn substitute_in_stmt(stmt: &mut Stmt, var_name: &str, replacement: &Expr) {
    visit_exprs_mut(stmt, &mut |expr| {
        substitute_in_expr(expr, var_name, replacement)
    });
}

/// True if any `Expr` inside `stmt` contains an `Unknown` node, or the
/// whole statement is `Stmt::Unknown`. Used to gate tree rewrite on
/// parser coverage before attempting a substitution.
///
/// `Stmt::IfOpen` reports `true` even when its cond is clean. This is an
/// architectural limit: `inline_single_use_temps_text` uses this
/// predicate as an "is this line safe to inline a temp into?" gate, and
/// flipping it inlines a temp's RHS into the guard cond while the
/// original assignment stays downstream (ordering inversion that breaks
/// `ApplyClimbingMovement` across all three VRPlayer UE versions). See
/// `docs/remaining-work.md`, "Architectural limits" section.
fn stmt_contains_unknown(stmt: &Stmt) -> bool {
    if matches!(stmt, Stmt::Unknown(_) | Stmt::IfOpen { .. }) {
        return true;
    }
    let mut found = false;
    visit_exprs(stmt, &mut |expr| {
        if expr_contains_unknown(expr) {
            found = true;
        }
    });
    found
}

/// Collect all bytecode offsets that are jump targets (conditional and unconditional).
/// Used to protect these offsets from being lost when inline passes remove statements.
pub fn collect_jump_targets(stmts: &[BcStatement]) -> HashSet<usize> {
    let mut targets = HashSet::new();
    for stmt in stmts {
        if let Some((_, target)) = stmt.if_jump() {
            targets.insert(target);
        }
        if let Some(target) = stmt.jump_target() {
            targets.insert(target);
        }
    }
    targets
}

/// Rename every `Expr::Var(old_name)` reference inside `stmt` to `new_name`.
/// Pure identifier rewrite, does NOT move expressions around. Safe to run on
/// `Stmt::IfOpen` conds despite the `stmt_contains_unknown` gate because a
/// rename can't trigger the assignment-reordering class of regressions that
/// gate exists for.
pub(super) fn rename_var_in_stmt(stmt: &mut Stmt, old_name: &str, new_name: &str) {
    let replacement = Expr::Var(new_name.to_owned());
    substitute_in_stmt(stmt, old_name, &replacement);
}

/// Substitute ALL occurrences of `var` in `text`, repeating until stable.
fn substitute_var_all(text: &str, var: &str, expr: &str) -> String {
    // Bail immediately if expr contains var (would loop forever).
    if count_var_refs(expr, var) > 0 {
        return text.to_string();
    }
    let mut result = text.to_string();
    // Limit iterations to the number of references (each call replaces one).
    let limit = count_var_refs(text, var) + 1;
    for _ in 0..limit {
        let next = substitute_var(&result, var, expr);
        if next == result {
            return result;
        }
        result = next;
    }
    result
}

/// Inline `Temp_*` / `$temp` variables that are always assigned the same value.
/// UE Select nodes re-assign the index input before every use; this pass
/// collapses `Temp_bool_Variable = LeftHand` + `switch(Temp_bool_Variable)`
/// into `switch(LeftHand)`.
pub fn inline_constant_temps(stmts: &mut Vec<BcStatement>, jump_targets: &HashSet<usize>) {
    let texts: Vec<&str> = stmts.iter().map(|s| s.text.as_str()).collect();
    let Some((constant_vars, remove_indices)) = resolve_constant_vars(&texts) else {
        return;
    };

    // Preparse RHS expressions once per var so the inner loop stays cheap.
    // `None` means the RHS didn't model cleanly through the 5d.2 parser and
    // the site must fall back to text substitution for that var.
    let rhs_exprs: BTreeMap<String, Option<Expr>> = constant_vars
        .iter()
        .map(|(var, expr)| {
            let parsed = parse_expr(expr);
            let usable = (!expr_contains_unknown(&parsed)).then_some(parsed);
            (var.clone(), usable)
        })
        .collect();

    for s in stmts.iter_mut() {
        let mut rewrote = false;
        let original_text = s.text.clone();
        let mut parsed_stmt = parse_stmt(&original_text);
        let stmt_parse_ok = !stmt_contains_unknown(&parsed_stmt);

        for (var, expr) in &constant_vars {
            if count_var_refs(&s.text, var) == 0 {
                continue;
            }
            match (stmt_parse_ok, rhs_exprs.get(var).and_then(|e| e.as_ref())) {
                (true, Some(rhs_expr)) => {
                    substitute_in_stmt(&mut parsed_stmt, var, rhs_expr);
                    s.text = fmt_stmt(&parsed_stmt);
                    rewrote = true;
                }
                _ => {
                    // Fall back to text substitution for shapes the 5d.2
                    // parser doesn't yet model.
                    s.text = substitute_var_all(&s.text, var, expr);
                    // Rehydrate the typed form so a later var in the same
                    // loop iteration still sees the mutated state.
                    parsed_stmt = parse_stmt(&s.text);
                    rewrote = true;
                }
            }
        }
        if rewrote {
            s.reclassify();
        }
    }

    let sorted_targets = sorted_jump_targets(jump_targets);
    let removed: Vec<usize> = remove_indices.iter().copied().collect();
    transfer_offsets_on_removal(stmts, &removed, &sorted_targets);

    let mut idx = 0;
    stmts.retain(|_| {
        let keep = !remove_indices.contains(&idx);
        idx += 1;
        keep
    });
}

/// Inline single-use `$temp` variables to reduce noise.
///
/// Only inlines vars that:
/// - Start with `$` (compiler temporaries)
/// - Are assigned exactly once (`$X = expr`)
/// - Are referenced exactly once in a later statement
/// - Would not produce a line longer than MAX_LINE_WIDTH chars
///
/// Tree rewrite: the RHS and the consumer are parsed into `Expr` trees,
/// the consumer tree has matching `Var` nodes replaced with the RHS tree,
/// and the result is reprinted via `fmt_expr`. The text `substitute_var`
/// path is kept as a fallback for shapes the 5d.2 parser doesn't model.
pub fn inline_single_use_temps(stmts: &mut Vec<BcStatement>, jump_targets: &HashSet<usize>) {
    const MAX_PASSES: usize = 6;
    // A temp whose offset is the explicit target of a jump must survive as a
    // phantom so the structurer can still resolve the jump. Non-anchor temps
    // are simply removed (baseline behavior). Using exact-match here, not
    // fuzzy, so we only anchor offsets that are actually jumped to.
    let is_jump_anchor = |off: usize| off > 0 && jump_targets.contains(&off);

    for _ in 0..MAX_PASSES {
        let assignments: Vec<(usize, String, String)> = stmts
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                let (var, expr) = parse_temp_assignment(&s.text)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var, _) in &assignments {
            *assign_counts.entry(var.as_str()).or_default() += 1;
        }

        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var, expr) in &assignments {
            if assign_counts.get(var.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, stmt) in stmts.iter().enumerate() {
                if i == *assign_idx {
                    continue;
                }
                ref_count += count_var_refs(&stmt.text, var);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var.clone(), expr.clone()));
            }
        }

        let mut removed: HashSet<usize> = HashSet::new();
        let mut removed_consumers: HashMap<usize, usize> = HashMap::new();
        let mut inlined_any = false;
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }
            let current_expr = match parse_temp_assignment(&stmts[*assign_idx].text) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };
            let mut refs = 0usize;
            let mut target_idx = None;
            for (i, stmt) in stmts.iter().enumerate() {
                if i == *assign_idx || removed.contains(&i) {
                    continue;
                }
                let count = count_var_refs(&stmt.text, var_name);
                refs += count;
                if count == 1 && target_idx.is_none() {
                    target_idx = Some(i);
                }
            }
            if refs != 1 {
                continue;
            }
            let Some(target_idx) = target_idx else {
                continue;
            };

            let Some(new_text) = rewrite_consumer_tree(&stmts[target_idx], var_name, &current_expr)
            else {
                // Fall back to text substitution for shapes the 5d.2 parser
                // doesn't yet model.
                let replacement = substitute_var(&stmts[target_idx].text, var_name, &current_expr);
                let shortens = current_expr.len() + 2 <= var_name.len();
                let trivial = is_trivial_expr(&current_expr);
                if !shortens && !trivial && replacement.len() > crate::bytecode::MAX_LINE_WIDTH {
                    continue;
                }
                stmts[target_idx].set_text(replacement);
                removed.insert(*assign_idx);
                removed_consumers.insert(*assign_idx, target_idx);
                inlined_any = true;
                continue;
            };

            let shortens = current_expr.len() + 2 <= var_name.len();
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && new_text.len() > crate::bytecode::MAX_LINE_WIDTH {
                continue;
            }
            stmts[target_idx].set_text(new_text);
            removed.insert(*assign_idx);
            removed_consumers.insert(*assign_idx, target_idx);
            inlined_any = true;
        }

        // Phantom-mark offsets that are explicit jump targets so the
        // structurer can still resolve those jumps. Skip phantoms whose
        // consumer is a flow opcode: those temps are condition variables
        // and keeping them as anchor entries perturbs region/CFG slicing
        // in ways the structurer wasn't designed to tolerate (the walking
        // block in VRPlayer Evaluate Movement Sounds is the canary). The
        // 5d.6 hypothesis that tree rewrite would eliminate this need was
        // disproven empirically, the exclusion is structural, not a
        // tooling artefact. Non-anchor temps remove outright.
        for &assign_idx in &removed {
            if !is_jump_anchor(stmts[assign_idx].mem_offset) {
                continue;
            }
            let consumer_is_flow = removed_consumers
                .get(&assign_idx)
                .is_some_and(|&c_idx| stmts[c_idx].kind.is_flow_opcode_consumer());
            if consumer_is_flow {
                continue;
            }
            stmts[assign_idx].text.clear();
            stmts[assign_idx].inlined_away = true;
            stmts[assign_idx].reclassify();
        }
        let mut idx = 0;
        stmts.retain(|s| {
            let keep = !removed.contains(&idx) || s.inlined_away;
            idx += 1;
            keep
        });
        if !inlined_any {
            break;
        }
    }
}

/// Rewrite the consumer statement's parsed tree by substituting `var_name`
/// with `rhs_text` (itself parsed). Returns `None` when either side hits
/// `Expr::Unknown` at a load-bearing position, or when the consumer shape
/// isn't one the tree rewrite supports. The outer caller is expected to
/// fall back to text substitution in that case.
fn rewrite_consumer_tree(consumer: &BcStatement, var_name: &str, rhs_text: &str) -> Option<String> {
    let rhs_expr = parse_expr(rhs_text);
    if expr_contains_unknown(&rhs_expr) {
        // TODO(5d.2): parser gap hit by inliner RHS, falling back to text
        return None;
    }

    match consumer.kind {
        StmtKind::IfJump { cond, target } => {
            let (cond_start, cond_end) = cond;
            let cond_expr = consumer.cond_expr()?;
            if expr_contains_unknown(cond_expr) {
                return None;
            }
            let mut rewritten = cond_expr.clone();
            substitute_in_expr(&mut rewritten, var_name, &rhs_expr);
            let prefix = &consumer.text[..cond_start];
            let suffix = &consumer.text[cond_end..];
            // Sanity check: suffix should look like `) jump 0x...`.
            let _ = target;
            Some(format!("{}{}{}", prefix, fmt_expr(&rewritten), suffix))
        }
        StmtKind::PopFlowIfNot { cond } | StmtKind::ContinueIfNot { cond } => {
            let (cond_start, cond_end) = cond;
            let cond_expr = consumer.cond_expr()?;
            if expr_contains_unknown(cond_expr) {
                return None;
            }
            let mut rewritten = cond_expr.clone();
            substitute_in_expr(&mut rewritten, var_name, &rhs_expr);
            let prefix = &consumer.text[..cond_start];
            let suffix = &consumer.text[cond_end..];
            Some(format!("{}{}{}", prefix, fmt_expr(&rewritten), suffix))
        }
        StmtKind::Other => {
            // Try assignment shape first, then bare-expression.
            if let Some((lhs, rhs)) = consumer.assignment() {
                if expr_contains_unknown(lhs) || expr_contains_unknown(rhs) {
                    return None;
                }
                let mut new_lhs = lhs.clone();
                let mut new_rhs = rhs.clone();
                substitute_in_expr(&mut new_lhs, var_name, &rhs_expr);
                substitute_in_expr(&mut new_rhs, var_name, &rhs_expr);
                return Some(format!("{} = {}", fmt_expr(&new_lhs), fmt_expr(&new_rhs)));
            }
            // Bare-expression (call-as-statement). Parse directly.
            if top_level_eq_split(&consumer.text).is_some() {
                // Assignment shape the accessor refused — don't invent a tree.
                return None;
            }
            let parsed = parse_expr(&consumer.text);
            if expr_contains_unknown(&parsed) {
                return None;
            }
            let mut rewritten = parsed;
            substitute_in_expr(&mut rewritten, var_name, &rhs_expr);
            Some(fmt_expr(&rewritten))
        }
        // Flow opcodes without a cond slice shouldn't be consumers of named
        // temps, fall back defensively rather than speculate on the shape.
        _ => None,
    }
}

/// Rewrite a post-structure text line by parsing it into a `Stmt`,
/// substituting `var_name` with `rhs_text` (itself parsed into an `Expr`),
/// and printing the result. Returns `None` when either side's parse hits
/// `Expr::Unknown` or when the line itself parses as `Stmt::Unknown` (a
/// block delimiter, comment, label, or other non-statement shape). The
/// outer caller is expected to fall back to text substitution in that case.
fn rewrite_consumer_text_tree(
    consumer_trimmed: &str,
    var_name: &str,
    rhs_text: &str,
) -> Option<String> {
    let rhs_expr = parse_expr(rhs_text);
    if expr_contains_unknown(&rhs_expr) {
        return None;
    }
    let mut parsed = parse_stmt(consumer_trimmed);
    if stmt_contains_unknown(&parsed) {
        return None;
    }
    substitute_in_stmt(&mut parsed, var_name, &rhs_expr);
    Some(fmt_stmt(&parsed))
}

/// Transfer mem_offsets from removed statements to the next surviving statement
/// when the removed offset is near a known jump target.
fn transfer_offsets_on_removal(
    stmts: &mut [BcStatement],
    removed: &[usize],
    sorted_targets: &[usize],
) {
    let tolerance = crate::bytecode::JUMP_OFFSET_TOLERANCE;
    let is_near_target = |off: usize| -> bool {
        let pos = sorted_targets.partition_point(|&t| t < off.saturating_sub(tolerance));
        pos < sorted_targets.len() && sorted_targets[pos].abs_diff(off) <= tolerance
    };
    let removed_set: HashSet<usize> = removed.iter().copied().collect();
    let mut pending: Vec<usize> = Vec::new();
    for (i, stmt) in stmts.iter_mut().enumerate() {
        if removed_set.contains(&i) {
            let off = stmt.mem_offset;
            if off > 0 && is_near_target(off) {
                pending.push(off);
            }
        } else if !pending.is_empty() {
            stmt.offset_aliases.append(&mut pending);
        }
    }
}

/// Build sorted jump target array for binary search.
fn sorted_jump_targets(jump_targets: &HashSet<usize>) -> Vec<usize> {
    let mut sorted: Vec<usize> = jump_targets.iter().copied().collect();
    sorted.sort_unstable();
    sorted
}

/// Discard assignments to `$temp` variables that are never referenced.
/// Keeps the RHS expression only if it has side effects (contains a function call).
/// Pure expressions (no function call) are removed entirely.
pub fn discard_unused_assignments(stmts: &mut Vec<BcStatement>) {
    let texts: Vec<&str> = stmts.iter().map(|s| s.text.as_str()).collect();
    let ref_counts = count_unused_assignments(&texts);

    for s in stmts.iter_mut() {
        if s.inlined_away {
            continue;
        }
        if let Some((var, expr)) = parse_temp_assignment(&s.text) {
            if ref_counts.get(var).copied() == Some(0) {
                if expr_has_call(expr) {
                    s.set_text(expr.to_string());
                } else {
                    s.text.clear();
                    s.kind = StmtKind::Other;
                }
            }
        }
    }

    // Preserve phantom (inlined-away) statements so their mem_offset still
    // anchors jump resolution. Only drop truly empty non-phantom lines.
    stmts.retain(|s| !s.text.is_empty() || s.inlined_away);
}

/// Text-based constant temp inlining for post-structure pipelines.
///
/// Operates on structured text lines (`Vec<String>`) after `structure_bytecode`.
/// Uses the shared `resolve_constant_vars` core for the algorithm.
pub fn inline_constant_temps_text(lines: &mut Vec<String>) {
    let texts: Vec<&str> = lines.iter().map(|l| l.trim()).collect();
    let Some((constant_vars, remove_indices)) = resolve_constant_vars(&texts) else {
        return;
    };

    // Preparse each RHS once. `None` marks vars whose RHS doesn't round-trip
    // through the 5d.2 parser, those force a text-substitution fallback.
    let rhs_exprs: BTreeMap<String, Option<Expr>> = constant_vars
        .iter()
        .map(|(var, expr)| {
            let parsed = parse_expr(expr);
            let usable = (!expr_contains_unknown(&parsed)).then_some(parsed);
            (var.clone(), usable)
        })
        .collect();

    for line in lines.iter_mut() {
        let trimmed = line.trim();
        let indent_len = line.len() - trimmed.len();
        let indent = line[..indent_len].to_owned();
        let mut current = trimmed.to_owned();
        let mut parsed_stmt = parse_stmt(&current);
        let mut stmt_parse_ok = !stmt_contains_unknown(&parsed_stmt);
        let mut rewrote = false;

        for (var, expr) in &constant_vars {
            if count_var_refs(&current, var) == 0 {
                continue;
            }
            match (stmt_parse_ok, rhs_exprs.get(var).and_then(|e| e.as_ref())) {
                (true, Some(rhs_expr)) => {
                    substitute_in_stmt(&mut parsed_stmt, var, rhs_expr);
                    current = fmt_stmt(&parsed_stmt);
                    rewrote = true;
                }
                _ => {
                    // Fall back to text substitution for shapes the 5d.2
                    // parser doesn't yet model.
                    current = substitute_var_all(&current, var, expr);
                    parsed_stmt = parse_stmt(&current);
                    stmt_parse_ok = !stmt_contains_unknown(&parsed_stmt);
                    rewrote = true;
                }
            }
        }
        if rewrote {
            *line = format!("{indent}{current}");
        }
    }

    let mut idx = 0;
    lines.retain(|_| {
        let keep = !remove_indices.contains(&idx);
        idx += 1;
        keep
    });
}

/// Text-based single-use temp inlining for post-structure pipelines.
///
/// Operates on structured text lines (`Vec<String>`) after `structure_bytecode`.
/// Mirrors `inline_single_use_temps` but respects brace scoping: an assignment
/// only inlines into a consumer that sits in the same logical block or a
/// nested child block, never across an `if` / `else` boundary that would
/// change semantics.
pub fn inline_single_use_temps_text(lines: &mut Vec<String>) {
    use crate::bytecode::MAX_LINE_WIDTH;
    const MAX_PASSES: usize = 6;

    for _ in 0..MAX_PASSES {
        let assignments: Vec<(usize, String, String)> = lines
            .iter()
            .enumerate()
            .filter_map(|(i, line)| {
                let trimmed = line.trim();
                let (var, expr) = parse_temp_assignment(trimmed)?;
                Some((i, var.to_string(), expr.to_string()))
            })
            .collect();

        let mut assign_counts: HashMap<&str, usize> = HashMap::new();
        for (_, var, _) in &assignments {
            *assign_counts.entry(var.as_str()).or_default() += 1;
        }

        let mut to_inline: Vec<(usize, String, String)> = Vec::new();
        for (assign_idx, var, expr) in &assignments {
            if assign_counts.get(var.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            let mut ref_count = 0usize;
            for (i, line) in lines.iter().enumerate() {
                if i == *assign_idx {
                    continue;
                }
                ref_count += count_var_refs(line.trim(), var);
            }
            if ref_count == 1 {
                to_inline.push((*assign_idx, var.clone(), expr.clone()));
            }
        }

        let mut removed: HashSet<usize> = HashSet::new();
        let mut inlined_any = false;
        for (assign_idx, var_name, _) in &to_inline {
            if removed.contains(assign_idx) {
                continue;
            }
            let current_expr = match parse_temp_assignment(lines[*assign_idx].trim()) {
                Some((v, e)) if v == var_name => e.to_string(),
                _ => continue,
            };

            let Some(target_idx) =
                find_single_use_target_in_scope(lines, *assign_idx, var_name, &removed)
            else {
                continue;
            };

            let consumer_trimmed = lines[target_idx].trim();
            let replacement =
                match rewrite_consumer_text_tree(consumer_trimmed, var_name, &current_expr) {
                    Some(text) => text,
                    None => {
                        // Fall back to text substitution for shapes the 5d.2
                        // parser doesn't yet model.
                        substitute_var(consumer_trimmed, var_name, &current_expr)
                    }
                };
            let shortens = current_expr.len() + 2 <= var_name.len();
            let trivial = is_trivial_expr(&current_expr);
            if !shortens && !trivial && replacement.len() > MAX_LINE_WIDTH {
                continue;
            }

            // Preserve the consumer's indentation.
            let consumer_indent = super::indent_prefix(&lines[target_idx]);
            lines[target_idx] = format!("{}{}", consumer_indent, replacement);
            removed.insert(*assign_idx);
            inlined_any = true;
        }

        let mut idx = 0;
        lines.retain(|_| {
            let keep = !removed.contains(&idx);
            idx += 1;
            keep
        });
        if !inlined_any {
            break;
        }
    }
}

/// Find the consumer line for `var_name` in the same block or a nested child
/// block as the assignment. Returns `None` when the var is referenced more
/// than once in scope, zero times, or only in a sibling block.
fn find_single_use_target_in_scope(
    lines: &[String],
    assign_idx: usize,
    var_name: &str,
    removed: &HashSet<usize>,
) -> Option<usize> {
    let assign_depth = indent_depth(&lines[assign_idx]);

    let mut depth = assign_depth;
    let mut target = None;
    let mut refs = 0usize;

    for (i, line) in lines.iter().enumerate().skip(assign_idx + 1) {
        if removed.contains(&i) {
            continue;
        }
        let trimmed = line.trim();

        // A closing brace that returns us below the assignment's depth
        // means we've left the scope the assignment lives in.
        if trimmed.starts_with('}') && indent_depth(line) < assign_depth {
            break;
        }

        let count = count_var_refs(trimmed, var_name);
        if count > 0 {
            refs += count;
            if refs > 1 {
                return None;
            }
            if target.is_none() {
                target = Some(i);
            }
        }

        // Track depth transitions so a `} else {` on one line still counts as
        // leaving the original branch.
        if trimmed.starts_with('}') {
            depth = depth.saturating_sub(1);
            if depth < assign_depth {
                break;
            }
        }
        if trimmed.ends_with('{') {
            depth += 1;
        }
    }

    if refs == 1 {
        target
    } else {
        None
    }
}

fn indent_depth(line: &str) -> usize {
    // Treat each 4-space stride as one depth level; tabs count as one each.
    let mut spaces = 0usize;
    for b in line.as_bytes() {
        match b {
            b' ' => spaces += 1,
            b'\t' => spaces += 4,
            _ => break,
        }
    }
    spaces / 4
}

/// Text-based dead-assignment removal for post-structure pipelines.
///
/// Removes `$temp = expr` lines with zero external references.
/// Keeps the RHS expression when it has side effects (function calls).
pub fn discard_unused_assignments_text(lines: &mut Vec<String>) {
    let texts: Vec<&str> = lines.iter().map(|l| l.trim()).collect();
    let ref_counts = count_unused_assignments(&texts);

    for line in lines.iter_mut() {
        if let Some((var, expr)) = parse_temp_assignment(line.trim()) {
            if ref_counts.get(var).copied() == Some(0) {
                if expr_has_call(expr) {
                    *line = expr.to_string();
                } else {
                    line.clear();
                }
            }
        }
    }

    lines.retain(|line| !line.trim().is_empty());
}

/// Resolve constant temp variables from a slice of text lines.
///
/// Shared core for both `inline_constant_temps` (BcStatement) and
/// `inline_constant_temps_text` (Vec<String>). Returns the resolved
/// variable map and the set of assignment indices to remove.
fn resolve_constant_vars(texts: &[&str]) -> Option<(BTreeMap<String, String>, HashSet<usize>)> {
    let mut assignments: HashMap<String, Vec<(usize, String)>> = HashMap::new();
    for (i, text) in texts.iter().enumerate() {
        if let Some((var, expr)) = parse_temp_assignment(text) {
            assignments
                .entry(var.to_string())
                .or_default()
                .push((i, expr.to_string()));
        }
    }

    // Multi-assignment same-value (Select pattern) or single Temp_* assignment
    let mut constant_vars: BTreeMap<String, String> = assignments
        .into_iter()
        .filter(|(var, entries)| {
            let all_same = entries.iter().all(|(_, expr)| *expr == entries[0].1);
            let multi = entries.len() > 1;
            all_same && (multi || var.starts_with("Temp_"))
        })
        .map(|(var, entries)| (var, entries[0].1.clone()))
        .collect();

    if constant_vars.is_empty() {
        return None;
    }

    // Resolve transitively: a constant var's expression may reference another
    let keys: Vec<String> = constant_vars.keys().cloned().collect();
    for _ in 0..6 {
        let mut changed = false;
        for key in &keys {
            let expr = constant_vars[key].clone();
            let mut resolved = expr.clone();
            for (other_var, other_expr) in constant_vars.iter() {
                if other_var == key {
                    continue;
                }
                if count_var_refs(&resolved, other_var) > 0 {
                    resolved = substitute_var_all(&resolved, other_var, other_expr);
                }
            }
            if resolved != expr {
                constant_vars.insert(key.clone(), resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Drop circular dependencies (FlipFlop: A = !B, B = A)
    constant_vars.retain(|var, expr| count_var_refs(expr, var) == 0);

    if constant_vars.is_empty() {
        return None;
    }

    let remove_indices: HashSet<usize> = texts
        .iter()
        .enumerate()
        .filter_map(|(i, text)| {
            let (var, _) = parse_temp_assignment(text)?;
            constant_vars.contains_key(var).then_some(i)
        })
        .collect();

    Some((constant_vars, remove_indices))
}

/// Count unreferenced single-assignment temp variables.
///
/// Shared core for both `discard_unused_assignments` variants.
/// Returns a map of variable names to their external reference count (0 = unused).
fn count_unused_assignments(texts: &[&str]) -> HashMap<String, usize> {
    let mut assign_counts: HashMap<String, usize> = HashMap::new();
    for text in texts {
        if let Some((var, _)) = parse_temp_assignment(text) {
            *assign_counts.entry(var.to_string()).or_default() += 1;
        }
    }

    let mut ref_counts: HashMap<String, usize> = HashMap::new();
    for (var, ac) in &assign_counts {
        if *ac != 1 {
            continue;
        }
        let mut total = 0usize;
        for text in texts {
            total += count_var_refs(text, var);
        }
        // total includes the assignment LHS (1 occurrence)
        ref_counts.insert(var.clone(), total.saturating_sub(1));
    }
    ref_counts
}
