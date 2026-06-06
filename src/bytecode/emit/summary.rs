//! Summary pseudocode emitter for the decoded statement tree.
//!
//! Walks the decoded statement tree and renders human-readable pseudocode.
//! Indentation is tracked by recursion depth. Renders the summary mode
//! (params, return types, nested control flow bodies) consistently
//! across asset versions so cross-version diffs stay clean.

use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::bytecode::asset::DecodedAsset;
use crate::bytecode::emit::sections::{emit_prefix_sections, filter_flags_for_summary, EmitCtx};
use crate::bytecode::expr::{
    binary_op_symbol, unary_op_symbol, BinaryOp, CastKind, Expr, SwitchExprCase,
};
use crate::bytecode::stmt::{LatchKind, LoopKind, Stmt, SwitchCase};
use crate::bytecode::transforms::fold_long_lines;
use crate::enums::{resolve_enum_args, resolve_enum_comparison};
use crate::output_summary::ubergraph::clean_event_header;
use crate::types::ParsedAsset;

thread_local! {
    /// Editor then-pin connected-mask for the block currently being
    /// emitted, or `None` for blocks that aren't gate-eligible (zero or
    /// multiple `K2Node_ExecutionSequence` nodes). Set by
    /// [`emit_function_block`] / [`emit_event_block`] around each block's
    /// body so the `Stmt::Sequence` arm can render disconnected then-pins
    /// as `// sequence [N] (empty):` headers with faithful editor-index
    /// numbering, without threading the mask through every Stmt variant.
    static ACTIVE_SEQUENCE_MASK: RefCell<Option<*const Vec<bool>>> =
        const { RefCell::new(None) };
}

/// RAII guard over a thread-local raw-pointer cell. On construction it
/// installs `value` and saves the previous binding; on `Drop` it restores
/// the saved binding. The `Drop`-based restore closes the latent hole the
/// hand-rolled set/restore pairs left open: a panic or early return inside
/// the wrapped body would otherwise skip the restore and leave a stale
/// pointer installed for re-entrant emits.
struct ScopedPtr<T: 'static> {
    key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>,
    previous: Option<*const T>,
}

impl<T: 'static> ScopedPtr<T> {
    /// Install `value` in `key`, returning a guard that restores the
    /// previous binding when dropped.
    fn set(
        key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>,
        value: Option<*const T>,
    ) -> Self {
        let previous = key.with(|cell| cell.replace(value));
        ScopedPtr { key, previous }
    }

    /// The pointer currently installed in `key`, or `None`.
    fn get(key: &'static std::thread::LocalKey<RefCell<Option<*const T>>>) -> Option<*const T> {
        key.with(|cell| *cell.borrow())
    }
}

impl<T: 'static> Drop for ScopedPtr<T> {
    fn drop(&mut self) {
        self.key.with(|cell| *cell.borrow_mut() = self.previous);
    }
}

/// Look up a latent call's resume body by the call's disk offset.
/// Returns `None` when the call carries no harvested continuation.
fn lookup_resume_body(
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
    offset: usize,
) -> Option<&[Stmt]> {
    resume_bodies.get(&offset).map(|body| body.as_slice())
}

/// True if `name` is a recognised latent UFUNCTION whose Call statement
/// carries an interleaved resume continuation.
pub(crate) fn is_latent_function(name: &str) -> bool {
    crate::bytecode::names::LATENT_FUNCTIONS.contains(&name)
}

/// Set the active block's editor then-pin mask for the duration of `body`,
/// restoring the previous binding on the way out. `mask` is `None` for
/// blocks that aren't gate-eligible.
fn with_sequence_mask<R>(mask: Option<&Vec<bool>>, body: impl FnOnce() -> R) -> R {
    let next = mask.map(|inner| inner as *const _);
    let _guard = ScopedPtr::set(&ACTIVE_SEQUENCE_MASK, next);
    body()
}

/// Faithful editor pin numbering for a `Stmt::Sequence`, when the active
/// block's then-pin mask makes it unambiguous.
///
/// Returns `Some(mask)` only when all three gate conditions hold:
/// - a mask is installed (the block has exactly one ExecutionSequence node),
/// - its connected-pin count equals `decoded_pin_count` (the decoded
///   `Stmt::Sequence` covers exactly the wired pins), and
/// - it has more total then-pins than decoded pins (a real gap to recover).
///
/// Otherwise `None`, and the caller renders the compact decoded numbering.
fn faithful_sequence_mask(decoded_pin_count: usize) -> Option<Vec<bool>> {
    let mask_ptr = ScopedPtr::get(&ACTIVE_SEQUENCE_MASK)?;
    // Safety: the pointer is installed by `with_sequence_mask` for the
    // duration of one block's emit and cleared before the guard drops;
    // the mask outlives the block body it wraps.
    let mask: &Vec<bool> = unsafe { &*mask_ptr };
    let connected = mask.iter().filter(|wired| **wired).count();
    if connected == decoded_pin_count && mask.len() > decoded_pin_count {
        Some(mask.clone())
    } else {
        None
    }
}

/// Emit summary pseudocode for a decoded Blueprint (Unreal Blueprint) asset.
///
/// This renders only the function and event bodies in the decoder's
/// native pseudocode shape. The full summary (Blueprint header,
/// Components, Variables, Call graph, Functions header) is produced by
/// [`emit_summary_with_asset`] which threads the original `ParsedAsset`
/// through to the section formatters.
pub fn emit_summary(asset: &DecodedAsset) -> String {
    let resume_bodies = &asset.resume_bodies;
    let mut output = String::new();
    for function in &asset.functions {
        emit_block_header(&mut output, "function", &function.name);
        emit_body(&mut output, &function.body, 1, resume_bodies);
        output.push_str("}\n\n");
    }
    for event in &asset.events {
        emit_block_header(&mut output, "event", &event.name);
        emit_body(&mut output, &event.body, 1, resume_bodies);
        output.push_str("}\n\n");
    }
    // Trim the trailing newline added after the last block.
    if output.ends_with("\n\n") {
        output.truncate(output.len() - 1);
    }
    output
}

/// Emit the full summary for a decoded Blueprint asset.
///
/// Renders the Blueprint header, Components, Variables, Call graph, and
/// `Functions:` header from `parsed` (delegating to the section
/// formatters), then the function and event bodies from `decoded` in
/// pseudocode shape. Used by the baseline regression harness to compare
/// against the committed snapshots.
pub fn emit_summary_with_asset(decoded: &DecodedAsset, parsed: &ParsedAsset) -> String {
    let resume_bodies = &decoded.resume_bodies;
    let mut output = String::new();
    let ctx = emit_prefix_sections(&mut output, decoded, parsed);
    let mut emitted = 0usize;
    for function in &decoded.functions {
        section_separator(&mut output, &mut emitted);
        emit_function_block(
            &mut output,
            &function.name,
            &function.body,
            &ctx,
            resume_bodies,
        );
    }
    for event in &decoded.events {
        section_separator(&mut output, &mut emitted);
        emit_event_block(&mut output, &event.name, &event.body, &ctx, resume_bodies);
    }
    // Trailing blank line after the last function block.
    output.push('\n');
    // Fold prefix-section lines to keep them under 120 chars.
    let mut lines: Vec<String> = output.split('\n').map(|line| line.to_string()).collect();
    fold_long_lines(&mut lines);
    lines.join("\n")
}

/// Render one decoded function/event body to its summary-mode lines.
///
/// Produces exactly the lines the summary emitter writes for that body
/// (the same `emit_body` walk at indent level 1, with latent-call resume
/// continuations interleaved from `resume_bodies`), one `String` per line
/// with the trailing newline stripped. Used by the `--dump`/`--json`
/// override bridge so the `BytecodeSummary` property they render stays
/// byte-identical to the summary mode's function-body output.
pub fn render_body_lines(body: &[Stmt], resume_bodies: &BTreeMap<usize, Vec<Stmt>>) -> Vec<String> {
    let mut output = String::new();
    emit_body(&mut output, body, 1, resume_bodies);
    output
        .strip_suffix('\n')
        .unwrap_or(&output)
        .split('\n')
        .map(|line| line.to_string())
        .collect()
}

/// Emit a blank-line separator between consecutive function/event blocks.
/// The first block emits no leading blank line.
fn section_separator(output: &mut String, emitted: &mut usize) {
    if *emitted > 0 {
        output.push('\n');
    }
    *emitted += 1;
}

/// Emit one regular function block: optional `// called by:` line,
/// signature header (`  Name(args) [flags]`), then the body indented by
/// one extra level. Falls back to `<name>()` when the export's
/// `Signature` property is missing.
fn emit_function_block(
    output: &mut String,
    name: &str,
    body: &[Stmt],
    ctx: &EmitCtx,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    if let Some(callers) = ctx.callers_map.get(name) {
        output.push_str("  // called by: ");
        output.push_str(&callers.join(", "));
        output.push('\n');
    }
    let signature = ctx
        .signatures
        .get(name)
        .cloned()
        .unwrap_or_else(|| format!("{}()", name));
    let flags = ctx
        .flags
        .get(name)
        .map(|raw| filter_flags_for_summary(raw))
        .filter(|filtered| !filtered.is_empty())
        .map(|filtered| format!(" [{}]", filtered))
        .unwrap_or_default();
    output.push_str("  ");
    output.push_str(&signature);
    output.push_str(&flags);
    output.push('\n');
    with_sequence_mask(ctx.sequence_masks.get(name), || {
        emit_body(output, body, 1, resume_bodies);
    });
}

/// Emit one ubergraph event block: optional `// called by:` line,
/// header (`  EventName():` or `  InputAxis_X(AxisValue: float):`), then
/// the body indented by one extra level. Event names are normalised
/// through `clean_event_header` so `InpActEvt_*` sections render as
/// `InputAction_*_Pressed/Released`.
fn emit_event_block(
    output: &mut String,
    raw_name: &str,
    body: &[Stmt],
    ctx: &EmitCtx,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let display_name = clean_event_header(raw_name, &ctx.action_key_events);
    if let Some(callers) = ctx.callers_map.get(raw_name) {
        output.push_str("  // called by: ");
        output.push_str(&callers.join(", "));
        output.push('\n');
    }
    output.push_str("  ");
    output.push_str(&display_name);
    if display_name.contains('(') {
        output.push_str(":\n");
    } else {
        output.push_str("():\n");
    }
    with_sequence_mask(ctx.sequence_masks.get(raw_name), || {
        emit_body(output, body, 1, resume_bodies);
    });
}

fn emit_block_header(output: &mut String, kind: &str, name: &str) {
    output.push_str(kind);
    output.push(' ');
    output.push_str(name);
    output.push_str(" {\n");
}

fn emit_body(
    output: &mut String,
    stmts: &[Stmt],
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    for stmt in stmts {
        emit_stmt(output, stmt, indent_level, resume_bodies);
    }
}

fn indent_str(level: usize) -> String {
    "    ".repeat(level)
}

fn emit_stmt(
    output: &mut String,
    stmt: &Stmt,
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let indent = indent_str(indent_level);
    match stmt {
        Stmt::Assignment { lhs, rhs, .. } => {
            output.push_str(&indent);
            output.push_str(&expr_to_string(lhs));
            output.push_str(" = ");
            output.push_str(&expr_to_string(rhs));
            output.push('\n');
        }
        Stmt::Call { func, args, offset } => {
            output.push_str(&indent);
            output.push_str(&func_head_to_string(func));
            output.push('(');
            output.push_str(&args_to_string(args, func_name_for_resolve(func)));
            output.push_str(")\n");
            // Interleave a latent call's resume continuation at the
            // same indent level as the call itself: the body the latent
            // action eventually resumes onto is an orphan continuation,
            // the post-resume statements run in the same scope as the call
            // site, not nested inside it. Only look up when the callee is
            // in the recognised latent set so the cost stays bounded.
            let callee = func_name_for_resolve(func);
            if is_latent_function(callee) {
                if let Some(resume_body) = lookup_resume_body(resume_bodies, *offset) {
                    emit_body(output, resume_body, indent_level, resume_bodies);
                }
            }
        }
        Stmt::Return { value: None, .. } => {
            output.push_str(&indent);
            output.push_str("return\n");
        }
        Stmt::Return {
            value: Some(expr), ..
        } => {
            output.push_str(&indent);
            output.push_str("return ");
            output.push_str(&expr_to_string(expr));
            output.push('\n');
        }
        Stmt::Unknown {
            reason,
            offset,
            length,
            ..
        } => {
            output.push_str(&indent);
            output.push_str(&format!(
                "// UNKNOWN at 0x{:x}: {} [{} bytes]\n",
                offset, reason, length
            ));
        }
        Stmt::Branch {
            cond,
            then_body,
            else_body,
            ..
        } => {
            output.push_str(&indent);
            output.push_str("if (");
            let cond_str = expr_to_string(cond);
            output.push_str(strip_outer_parens(&cond_str));
            output.push_str(") {\n");
            emit_body(output, then_body, indent_level + 1, resume_bodies);
            if else_body.is_empty() {
                output.push_str(&indent);
                output.push_str("}\n");
            } else {
                output.push_str(&indent);
                output.push_str("} else {\n");
                emit_body(output, else_body, indent_level + 1, resume_bodies);
                output.push_str(&indent);
                output.push_str("}\n");
            }
        }
        Stmt::Sequence { pins, .. } => {
            emit_sequence(output, pins, indent_level, resume_bodies);
        }
        Stmt::Loop {
            kind,
            cond,
            body,
            completion,
            ..
        } => {
            emit_loop(
                output,
                kind,
                cond,
                body,
                completion,
                indent_level,
                resume_bodies,
            );
        }
        Stmt::Switch {
            expr,
            cases,
            default,
            ..
        } => {
            emit_switch(
                output,
                expr,
                cases,
                default.as_deref(),
                indent_level,
                resume_bodies,
            );
        }
        Stmt::Latch {
            kind, init, body, ..
        } => {
            emit_latch(output, kind, init, body, indent_level, resume_bodies);
        }
        Stmt::EventCall { event_name, .. } => {
            output.push_str(&indent);
            output.push_str(event_name);
            output.push_str("()\n");
        }
        Stmt::Break { .. } => {
            output.push_str(&indent);
            output.push_str("break\n");
        }
    }
}

/// Render a `Stmt::Sequence`'s pin bodies inline at the parent indent.
///
/// The `// sequence [N]:` comment is a legibility aid for the human reader,
/// no consumer parses it. Two numbering modes:
///
/// - Faithful editor numbering (when [`faithful_sequence_mask`] resolves
///   for this block): walk the editor then-pins in order. A disconnected
///   pin emits an explicit `// sequence [N] (empty):` header with no body;
///   a connected pin consumes the next decoded body and keeps the existing
///   suppression (labelled only when there is more than one decoded pin and
///   the body is non-empty). This recovers the editor pin index across gaps
///   so a disconnected slot keeps its number and later pins stay faithful.
/// - Compact numbering (fallback): index the decoded pins directly. A pin
///   whose body decoded to nothing emits no label, preserving the original
///   index so a gap signals the empty pin rather than misleading the reader
///   with a labelled-but-bodyless entry.
fn emit_sequence(
    output: &mut String,
    pins: &[Vec<Stmt>],
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let indent = "    ".repeat(indent_level);
    let multi_pin = pins.len() > 1;
    let faithful = faithful_sequence_mask(pins.len());

    // A block's single ExecutionSequence maps to a single Sequence; clear the
    // mask while recursing into pin bodies so a nested Sequence (e.g. one
    // synthesised inside a loop or latch) falls back to compact numbering
    // instead of inheriting this block's editor mask.
    with_sequence_mask(None, || {
        if let Some(mask) = &faithful {
            let mut cursor = 0usize;
            for (editor_index, wired) in mask.iter().enumerate() {
                if *wired {
                    let pin = &pins[cursor];
                    cursor += 1;
                    if multi_pin && !pin.is_empty() {
                        output.push_str(&indent);
                        output.push_str(&format!("// sequence [{editor_index}]:\n"));
                    }
                    emit_body(output, pin, indent_level, resume_bodies);
                } else {
                    output.push_str(&indent);
                    output.push_str(&format!("// sequence [{editor_index}] (empty):\n"));
                }
            }
            return;
        }

        for (pin_index, pin) in pins.iter().enumerate() {
            if multi_pin && !pin.is_empty() {
                output.push_str(&indent);
                output.push_str(&format!("// sequence [{pin_index}]:\n"));
            }
            emit_body(output, pin, indent_level, resume_bodies);
        }
    });
}

/// Render a `Stmt::Loop` body. The header form depends on the
/// `LoopKind`:
///
/// - `While`   -> `while (cond) { ... }`
/// - `ForC`    -> `for (counter = init to bound) { ... }` when the loop
///   matches the canonical Pascal-style shape (single counter init, an
///   `<=` or `<` comparison against the same counter, an increment that
///   bumps that counter). Otherwise falls back to the C-style
///   `for (init; cond; increment) { ... }` form.
/// - `ForEach` -> `for (item in array) { ... }`
///
/// `completion` (currently only populated by ForEach) renders as a
/// trailing `// completed:` block beneath the loop body.
fn emit_loop(
    output: &mut String,
    kind: &LoopKind,
    cond: &Option<Expr>,
    body: &[Stmt],
    completion: &Option<Vec<Stmt>>,
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let indent = indent_str(indent_level);
    match kind {
        LoopKind::While => {
            output.push_str(&indent);
            output.push_str("while (");
            let cond_str = loop_cond_string(cond);
            output.push_str(strip_outer_parens(&cond_str));
            output.push_str(") {\n");
            emit_body(output, body, indent_level + 1, resume_bodies);
            output.push_str(&indent);
            output.push_str("}\n");
        }
        LoopKind::ForC { init, increment } => {
            if let Some(header) = pascal_forc_header(init, cond, increment) {
                output.push_str(&indent);
                output.push_str(&header);
                output.push_str(" {\n");
            } else {
                output.push_str(&indent);
                output.push_str("for (");
                output.push_str(&increment_inline_string(init));
                output.push_str("; ");
                output.push_str(&loop_cond_string(cond));
                output.push_str("; ");
                output.push_str(&increment_inline_string(increment));
                output.push_str(") {\n");
            }
            emit_body(output, body, indent_level + 1, resume_bodies);
            output.push_str(&indent);
            output.push_str("}\n");
        }
        LoopKind::ForEach { item, array } => {
            // Render as `for (item in array)`.
            output.push_str(&indent);
            output.push_str("for (");
            output.push_str(item);
            output.push_str(" in ");
            output.push_str(&expr_to_string(array));
            output.push_str(") {\n");
            emit_body(output, body, indent_level + 1, resume_bodies);
            output.push_str(&indent);
            output.push_str("}\n");
        }
    }
    if let Some(stmts) = completion {
        if !stmts.is_empty() {
            output.push_str(&indent);
            output.push_str("// completed:\n");
            emit_body(output, stmts, indent_level, resume_bodies);
        }
    }
}

/// Render a `Stmt::Switch` body as
/// `switch (expr) { case <c>: <body> ... default: <body> }`. Each case
/// body and the default block render at one extra indent level.
fn emit_switch(
    output: &mut String,
    expr: &Expr,
    cases: &[SwitchCase],
    default: Option<&[Stmt]>,
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let indent = indent_str(indent_level);
    output.push_str(&indent);
    output.push_str("switch (");
    output.push_str(&expr_to_string(expr));
    output.push_str(") {\n");
    let case_indent = indent_str(indent_level + 1);
    for case in cases {
        output.push_str(&case_indent);
        output.push_str("case ");
        let rendered_values: Vec<String> = case.values.iter().map(expr_to_string).collect();
        output.push_str(&rendered_values.join(", "));
        output.push_str(":\n");
        emit_body(output, &case.body, indent_level + 2, resume_bodies);
    }
    if let Some(stmts) = default {
        output.push_str(&case_indent);
        output.push_str("default:\n");
        emit_body(output, stmts, indent_level + 2, resume_bodies);
    }
    output.push_str(&indent);
    output.push_str("}\n");
}

/// Render a `Stmt::Latch` body. The header form depends on the
/// `LatchKind`:
///
/// - `DoOnce { name }` -> `DoOnce(name) { ... }` when name is a bare
///   identifier, else `DoOnce("name") { ... }`.
/// - `FlipFlop { gate_var, names: Some((a, b)) }` ->
///   `FlipFlop(<a>) { A|B: { ... } }` when `a == b` (the common case
///   after `derive_flipflop_names` populates a single display name);
///   `FlipFlop(<a>|<b>) { ... }` when the labels differ.
/// - `FlipFlop { gate_var, names: None }` -> `FlipFlop("<gate_var>") { ... }`
///   as a legacy fallback when no display name was derived.
///
/// When the FlipFlop body holds a single `Branch { cond, then, else: [] }`
/// (the recognizer's canonical wrapper), the inner branch renders as
/// `A|B: { <then-body> }` directly, suppressing the `if (...)` wrapper
/// that would otherwise show the gate-var read. Bodies with any other
/// shape fall through to the regular branch emission so unexpected
/// patterns stay legible rather than crashing.
///
/// `init` (preceding assignments) is currently always empty; a
/// future pass may detect compiler-emitted init blocks and place them here.
fn emit_latch(
    output: &mut String,
    kind: &LatchKind,
    init: &[Stmt],
    body: &[Stmt],
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    let indent = indent_str(indent_level);
    if !init.is_empty() {
        output.push_str(&indent);
        output.push_str("// init:\n");
        emit_body(output, init, indent_level, resume_bodies);
    }
    match kind {
        LatchKind::DoOnce { name, .. } => {
            output.push_str(&indent);
            if is_bare_identifier(name) {
                output.push_str("DoOnce(");
                output.push_str(name);
                output.push_str(") {\n");
            } else {
                output.push_str("DoOnce(\"");
                output.push_str(name);
                output.push_str("\") {\n");
            }
            emit_body(output, body, indent_level + 1, resume_bodies);
            output.push_str(&indent);
            output.push_str("}\n");
        }
        LatchKind::FlipFlop { gate_var, names } => {
            output.push_str(&indent);
            output.push_str(&flipflop_header(gate_var, names.as_ref()));
            output.push_str(" {\n");
            emit_flipflop_body(output, body, indent_level, resume_bodies);
            output.push_str(&indent);
            output.push_str("}\n");
        }
    }
}

/// Render the `FlipFlop(...)` header text (no trailing brace). When
/// `names` carries a single derived label (the common case post
/// `derive_flipflop_names`), the unquoted label appears bare. When the
/// labels differ, both are joined with `|`. Falling back to `None` keeps
/// the legacy quoted-gate-var form for shapes the naming pass couldn't
/// resolve.
fn flipflop_header(gate_var: &str, names: Option<&(String, String)>) -> String {
    match names {
        Some((a, b)) if a == b => format!("FlipFlop({})", a),
        Some((a, b)) => format!("FlipFlop({}|{})", a, b),
        None => format!("FlipFlop(\"{}\")", gate_var),
    }
}

/// Render the FlipFlop body. The recognizer wraps consumer statements in
/// a `Branch { cond: Var(gate), then: <consumers>, else: [] }`; that
/// shape collapses to `A|B: { <consumers> }` here. Bodies with any other
/// shape fall through to the standard `emit_body` path.
fn emit_flipflop_body(
    output: &mut String,
    body: &[Stmt],
    indent_level: usize,
    resume_bodies: &BTreeMap<usize, Vec<Stmt>>,
) {
    if let [Stmt::Branch {
        then_body,
        else_body,
        ..
    }] = body
    {
        if else_body.is_empty() {
            let label_indent = indent_str(indent_level + 1);
            output.push_str(&label_indent);
            output.push_str("A|B: {\n");
            emit_body(output, then_body, indent_level + 2, resume_bodies);
            output.push_str(&label_indent);
            output.push_str("}\n");
            return;
        }
    }
    emit_body(output, body, indent_level + 1, resume_bodies);
}

/// Strip a single matched outer pair of parens from `s`. Returns
/// `&s[1..s.len()-1]` only when the leading `(` and trailing `)` are
/// the same syntactic pair, not separate parens around different
/// sub-expressions. `(a) + (b)` is left alone; `((a + b))` strips to
/// `(a + b)`. Used by `if`/`while` emit so we don't double-wrap an
/// already-parenthesized condition expression.
fn strip_outer_parens(s: &str) -> &str {
    if !s.starts_with('(') || !s.ends_with(')') {
        return s;
    }
    let inner = &s[1..s.len() - 1];
    let mut depth: i32 = 0;
    for ch in inner.chars() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return s;
                }
            }
            _ => {}
        }
    }
    if depth == 0 {
        inner
    } else {
        s
    }
}

/// True when `name` is a Rust-style bare identifier (alphanumeric +
/// underscore, not starting with a digit). Used to skip quotes around
/// DoOnce names that don't need them.
fn is_bare_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) if first.is_alphabetic() || first == '_' => {
            chars.all(|c| c.is_alphanumeric() || c == '_')
        }
        _ => false,
    }
}

/// Render the loop condition. `None` (infinite loop) becomes `true`.
fn loop_cond_string(cond: &Option<Expr>) -> String {
    match cond {
        Some(expr) => expr_to_string(expr),
        None => "true".to_string(),
    }
}

/// Try to render a `LoopKind::ForC` header in the Pascal-style
/// `for (counter = init to bound)` shape. Returns `Some(header_text)`
/// (with no trailing `{`) when the loop matches the canonical pattern,
/// otherwise `None` so the caller falls back to the C-style header.
///
/// The pattern recognised:
///
/// - `init` is exactly one `Stmt::Assignment` whose lhs is a `Var`.
/// - `cond` is a `Binary` with op `Le` or `Lt` whose lhs is the same
///   `Var` as the init's lhs.
/// - `increment` is one statement whose lhs is the same `Var`. The rhs
///   shape is unconstrained, the inliner may not have folded
///   `counter = counter + 1` into its final form yet.
///
/// For `Le`, the bound expression is rendered verbatim. For `Lt`, the
/// rendered bound is `<rhs> - 1` so the half-open `<` range matches the
/// inclusive `to` semantics.
fn pascal_forc_header(init: &[Stmt], cond: &Option<Expr>, increment: &[Stmt]) -> Option<String> {
    let (counter, init_rhs) = match init {
        [Stmt::Assignment {
            lhs: Expr::Var(name),
            rhs,
            ..
        }] => (name.as_str(), rhs),
        _ => return None,
    };

    let cond_expr = cond.as_ref()?;
    let (op, cond_lhs, cond_rhs) = match cond_expr {
        Expr::Binary { op, lhs, rhs } => (op, lhs.as_ref(), rhs.as_ref()),
        _ => return None,
    };
    match cond_lhs {
        Expr::Var(name) if name == counter => {}
        _ => return None,
    }

    let increment_targets_counter = increment.iter().any(|stmt| match stmt {
        Stmt::Assignment {
            lhs: Expr::Var(name),
            ..
        } => name == counter,
        _ => false,
    });
    if !increment_targets_counter {
        return None;
    }

    let bound_text = match op {
        BinaryOp::Le => expr_unwrapped_string(cond_rhs),
        BinaryOp::Lt => format!("{} - 1", expr_unwrapped_string(cond_rhs)),
        _ => return None,
    };

    Some(format!(
        "for ({} = {} to {})",
        counter,
        expr_unwrapped_string(init_rhs),
        bound_text
    ))
}

/// Render an expression but strip a single layer of outer parentheses
/// added by `expr_to_string` for `Binary` operators. Used by the Pascal
/// `for` header so the bound expression reads `Count - 1` rather
/// than `(Count - 1)`.
fn expr_unwrapped_string(expr: &Expr) -> String {
    let rendered = expr_to_string(expr);
    if matches!(expr, Expr::Binary { .. }) && rendered.starts_with('(') && rendered.ends_with(')') {
        rendered[1..rendered.len() - 1].to_string()
    } else {
        rendered
    }
}

/// Render a small list of increment statements as a single inline
/// expression-style string. Each statement contributes `lhs = rhs`
/// without the trailing semicolon. Multiple statements are joined with
/// `, ` so a `for (; cond; a = a + 1, b = b + 1)` form is possible.
fn increment_inline_string(stmts: &[Stmt]) -> String {
    stmts
        .iter()
        .filter_map(|stmt| match stmt {
            Stmt::Assignment { lhs, rhs, .. } => {
                Some(format!("{} = {}", expr_to_string(lhs), expr_to_string(rhs)))
            }
            Stmt::Call { func, args, .. } => Some(format!(
                "{}({})",
                func_head_to_string(func),
                args_to_string(args, func_name_for_resolve(func))
            )),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Render an expression as a compact string.
pub(super) fn expr_to_string(expr: &Expr) -> String {
    match expr {
        Expr::Literal(text) => text.clone(),
        Expr::Var(name) => name.clone(),
        Expr::Call { name, args } => {
            format!(
                "{}({})",
                strip_func_prefix(name),
                args_to_string(args, name)
            )
        }
        Expr::MethodCall { recv, name, args } => {
            format!(
                "{}.{}({})",
                expr_to_string_recv(recv),
                strip_k2_prefix(name),
                args_to_string(args, name)
            )
        }
        Expr::FieldAccess { recv, field } => {
            format!("{}.{}", expr_to_string_recv(recv), field)
        }
        Expr::Index { recv, idx } => {
            format!("{}[{}]", expr_to_string_recv(recv), expr_to_string(idx))
        }
        Expr::Binary { op, lhs, rhs } => {
            let mut lhs_str = expr_to_string_operand(lhs);
            let mut rhs_str = expr_to_string_operand(rhs);
            if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                resolve_enum_comparison(&mut lhs_str, &mut rhs_str);
            }
            format!("({} {} {})", lhs_str, binary_op_symbol(*op), rhs_str)
        }
        Expr::Unary { op, operand } => {
            format!("{}{}", unary_op_symbol(*op), expr_to_string(operand))
        }
        Expr::Cast { kind, inner } => render_cast(kind, inner),
        Expr::ArrayLit(items) => {
            let rendered: Vec<String> = items.iter().map(expr_to_string).collect();
            format!("[{}]", rendered.join(", "))
        }
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            format!(
                "{} ? {} : {}",
                expr_to_string(cond),
                expr_to_string(then_expr),
                expr_to_string(else_expr)
            )
        }
        Expr::StructConstruct { type_name, fields } => {
            let rendered: Vec<String> = fields
                .iter()
                .map(|(name, value)| format!("{}={}", name, expr_to_string(value)))
                .collect();
            format!("Make{}({})", type_name, rendered.join(", "))
        }
        Expr::Switch {
            index,
            cases,
            default,
        } => render_switch_expr(index, cases, default),
        Expr::Out(inner) => format!("out {}", expr_to_string(inner)),
        Expr::Interface(inner) => format!("({} as Interface)", expr_to_string(inner)),
        Expr::Persistent(inner) => format!("[persistent] {}", expr_to_string(inner)),
        Expr::Resume { inner, target } => {
            format!("{} /*resume:0x{:x}*/", expr_to_string(inner), target)
        }
        Expr::Unknown { reason, offset, .. } => {
            format!("/*?{}@0x{:x}?*/", reason, offset)
        }
    }
}

fn args_to_string(args: &[Expr], func_name: &str) -> String {
    let mut rendered: Vec<String> = args.iter().map(expr_to_string).collect();
    resolve_enum_args(func_name, &mut rendered);
    rendered.join(", ")
}

/// Render an expression that sits at the receiver position of a
/// `FieldAccess`, `MethodCall`, or `Index`. Wraps the result in parens
/// when the inner expression is one whose textual form binds looser
/// than the trailing `.field` / `.method()` / `[idx]`. Without this,
/// `(cond ? L : R).Field` would render as `cond ? L : R.Field` and parse
/// as `cond ? L : (R.Field)`, breaking the editor-truth meaning.
fn expr_to_string_recv(expr: &Expr) -> String {
    let needs_parens = matches!(expr, Expr::Ternary { .. });
    let rendered = expr_to_string(expr);
    if needs_parens {
        format!("({})", rendered)
    } else {
        rendered
    }
}

/// Render an expression at a binary operand position. Wraps a `Ternary`
/// in parens: `? :` binds looser than any binary operator, so without
/// this `$Roll - cond ? a : b` parses as `($Roll - cond) ? a : b`,
/// changing the arithmetic (a MakeRotator argument that subtracts a
/// ternary).
fn expr_to_string_operand(expr: &Expr) -> String {
    let rendered = expr_to_string(expr);
    if matches!(expr, Expr::Ternary { .. }) {
        format!("({})", rendered)
    } else {
        rendered
    }
}

/// Trailing name segment of a `Stmt::Call`'s `func` expression, used as
/// the lookup key for enum-name argument resolution. Matches the shape
/// `canonical_name` in `enums.rs` expects, an unqualified identifier
/// (the `Class.` prefix it would strip is already absent here).
fn func_name_for_resolve(func: &Expr) -> &str {
    match func {
        Expr::Var(name) => name,
        Expr::FieldAccess { field, .. } => field,
        _ => "",
    }
}

/// Render an expression that appears in function-name position (the
/// `func` of `Stmt::Call`). The decoder lowers calls so `func` is a
/// `Var(name)` for free / static-library calls and a `FieldAccess`
/// for instance method calls. Strip cosmetic prefixes from the
/// trailing name segment in both shapes; fall back to plain
/// `expr_to_string` for anything else.
fn func_head_to_string(func: &Expr) -> String {
    match func {
        Expr::Var(name) => strip_func_prefix(name),
        Expr::FieldAccess { recv, field } => {
            format!("{}.{}", expr_to_string_recv(recv), strip_k2_prefix(field))
        }
        other => expr_to_string(other),
    }
}

/// Strip the leading `K2_` or `Conv_` Blueprint-editor cosmetic
/// prefix from a function name. Returns the original name if neither
/// prefix is present.
fn strip_k2_prefix(name: &str) -> &str {
    name.strip_prefix("K2_")
        .or_else(|| name.strip_prefix("Conv_"))
        .unwrap_or(name)
}

/// Strip both the cosmetic prefix and, when the qualifier is a known
/// UE4 library class (KismetMathLibrary, GameplayStatics, etc.), the
/// `Class.` qualifier. Free-function call names from the decoder
/// arrive as `Class.Method` for member functions; library-class
/// qualifiers are noise in summary output.
fn strip_func_prefix(name: &str) -> String {
    if let Some(dot_pos) = name.rfind('.') {
        let class_part = &name[..dot_pos];
        let func = strip_k2_prefix(&name[dot_pos + 1..]);
        if is_ue4_library_class(class_part) {
            func.to_string()
        } else {
            format!("{}.{}", class_part, func)
        }
    } else {
        strip_k2_prefix(name).to_string()
    }
}

/// Library classes whose qualifier is stripped in summary output.
/// Lookup is on the short class name (after the last `.`) so deeply
/// qualified references resolve correctly.
fn is_ue4_library_class(name: &str) -> bool {
    let short = name.rsplit('.').next().unwrap_or(name);
    matches!(
        short,
        "KismetArrayLibrary"
            | "KismetMathLibrary"
            | "KismetSystemLibrary"
            | "KismetStringLibrary"
            | "KismetTextLibrary"
            | "KismetInputLibrary"
            | "KismetMaterialLibrary"
            | "KismetNodeHelperLibrary"
            | "KismetRenderingLibrary"
            | "KismetGuidLibrary"
            | "GameplayStatics"
            | "HeadMountedDisplayFunctionLibrary"
            | "BlueprintMapLibrary"
            | "BlueprintSetLibrary"
    )
}

/// Render a typed cast. Dynamic class casts use `Cast<T>(x)` to match
/// Blueprint editor terminology; everything else uses `(x as Type)`.
/// `Other(byte)` falls back to `cast_0xNN` so unrecognised opcodes are
/// still readable rather than `Debug`-formatted.
fn render_cast(kind: &CastKind, inner: &Expr) -> String {
    let inner_str = expr_to_string(inner);
    match kind {
        CastKind::Class { target } => format!("Cast<{}>({})", target, inner_str),
        CastKind::ToInterface { target } => format!("({} as {})", inner_str, target),
        CastKind::ToObject => format!("({} as Object)", inner_str),
        CastKind::ToBool => format!("({} as bool)", inner_str),
        CastKind::Other(byte) => format!("({} as cast_{:#04x})", inner_str, byte),
    }
}

/// Render an inline `Expr::Switch`: when the default expression is the
/// compiler's `$Select_Default*` sentinel (an empty default arm), omit
/// the `default:` clause; otherwise emit it after the cases.
fn render_switch_expr(index: &Expr, cases: &[SwitchExprCase], default: &Expr) -> String {
    let case_strs: Vec<String> = cases
        .iter()
        .map(|case| {
            format!(
                "{}: {}",
                expr_to_string(&case.value),
                expr_to_string(&case.body)
            )
        })
        .collect();
    if is_select_default_sentinel(default) {
        format!(
            "switch({}) {{ {} }}",
            expr_to_string(index),
            case_strs.join(", ")
        )
    } else {
        format!(
            "switch({}) {{ {}, default: {} }}",
            expr_to_string(index),
            case_strs.join(", "),
            expr_to_string(default)
        )
    }
}

/// Detect the compiler-emitted `$Select_Default*` placeholder that
/// stands in for an absent default arm. The decoder surfaces it as a
/// `Var` whose name carries the `$Select_Default` prefix.
fn is_select_default_sentinel(expr: &Expr) -> bool {
    matches!(expr, Expr::Var(name) if name.starts_with("$Select_Default"))
}
