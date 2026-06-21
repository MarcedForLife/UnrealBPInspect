# Bytecode decompiler maintainability notes

A set of behavior-preserving refactors to `src/bytecode/` that pull accidental
duplication behind explicit, principled helpers. Every change keeps
`--dump`/`--json`/summary output byte-identical (gated by `tests/v2_baseline.rs`
over the summary baseline and `tests/snapshots/` over dump/json), stays
deterministic, and adds no dependency.

## What changed

- **CFG graph-walk helpers** (`cfg/`). A single `DomChain` ancestor iterator
  behind the dominator/post-dominator chain walks, `reachable_bounded` as the
  one reachability primitive, and the execution-flow-stack walk delegated to
  `partition::step_successors` instead of a second inline copy.

- **Rewrite drivers** (`transforms/visit.rs`). Named `rewrite_stmts_preorder`
  and `rewrite_stmts_postorder` put the act-vs-recurse order in the function
  name, replacing four hand-rolled per-pass recursion shells.

- **Slot-addressed traversal** (`transforms/visit.rs`). The slot-tagged walker
  lives beside the plain `walk_stmt_children` with a parity test, so the next
  variant-adder updates both in one place; the CSE projection pass reads it
  through an untagged view instead of its own copy.

- **Region-emit extractions** (`decode/region_decode/`). The shared emitter
  prologue (`region_entry_terminator`), the own-exit drop predicate
  (`tail_is_droppable`), and the per-block decode core (`decode_opcode_at`) are
  one helper each instead of six near-identical copies; the read-once
  `MatchedEmitter` enum becomes a bool.

- **Field-path and sub-context plumbing** (`decode/`). One FFieldPath reader
  (`walker::read_field_path`) with a `FieldPath::leaf_member` accessor, plus a
  `DecodeCtx::child` that copies the shared references and resets the per-scope
  cells in one place, and an `arm_last_end` extractor for the region arm
  extents.

- **Variable-reference primitives** (`transforms/var_refs.rs`). One home for
  variable use-counting (`count_var` over explicit `VarScope` and `Defs`
  policies), renaming (`rename_var_in_stmt`, including the `ForEach` item slot),
  and common-subexpression keying (`expr_key`), replacing per-pass copies whose
  scope rules were subtly different and unstated.

- **DoOnce scaffold classification** (`transforms/latch_recognition/`). A
  `PinClass` classifier plus `DoOnceRole` query methods (`is_scaffold`,
  `suffix`) the pin-purity predicates share, while each predicate still spells
  its own accept-set so the deliberate divergences (roles-only vs
  roles+noop+reset) stay visible at the call site.

## Left alone on purpose

The irreducible case analysis stays as-is: the if/else arm cascade in
`ifthenelse.rs`, the latch shape-matchers, `decide_branch_layout`, the
dominator-tree core, and `is_tail_role_acceptable` (whose raw prefix handling
must not be folded into the trimmed `DoOnceRole::suffix`).
