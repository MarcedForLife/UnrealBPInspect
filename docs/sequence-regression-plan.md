# Sequence-detection regression on VRPlayer_BP EventTick

## Status (2026-04-25)

- Branch: `bugfix/sequence-nested-displaced-else`. Tag `archive/pre-sequence-fix`
  marks the pre-touch state on `main`.
- Phase 1 (relax interleaved-sequence reject + permanent diagnostic trace) is
  ready to commit. It is **not** a fix for the user-visible bug. The trace
  helped pinpoint the actual bug site, which is described below.
- Phase 2 (extend `inline_end` in detect_*_sequences) is deferred. It would
  also be inert for the EventTick output because the per-event ubergraph
  rendering path bypasses `reorder_flow_patterns` entirely.
- Helm snapshot tests (22) and unit tests (467) remain green.

## What the user reported

Adding a `PrintString` to the `else` pin of the `if (FlyEnabled)` node in
`VRPlayer_BP::EventTick` produces wildly inaccurate `bp-inspect` output and a
chaotic `--diff`. The user notes similar fallout on edits to other graphs, so
the underlying issue is generic.

## What investigation showed

### Fact A — sequence detection is fine

`reorder_flow_patterns` correctly detects the 7-pair parent
(`ExecutionSequence_2`) and emits 8 sequence markers + 2 nested sub-sequence
markers (for `ExecutionSequence_3` inside step_3). The trace
(`BP_INSPECT_TRACE_SEQUENCES=1`) confirms after Phase 1's relaxation:

```
[seq:accept] chain=222..236 pairs=7 inline_end=238
  pins=[249..254,246..248,239..245,77..80,255..271,272..273,274..275]
```

`structure_function` preserves all 18 markers through every pass (inline,
cse, discard, split_by_sequence_markers, structure each segment). The trace
(`BP_INSPECT_TRACE_PIPELINE=1`) confirms 18 markers at every stage.

### Fact B — the rendered ReceiveTick body has only 7 markers

The user-visible output for ReceiveTick (which calls `ExecuteUbergraph_*`)
shows two separate Sequences (`// sequence [0..2]` then `// sequence [0..3]`
with numbering restart, ProcessDesiredGrip dropped, CameraVelocity orphaned
after the if/else). That's not what `structure_function` produced, so
something between `structure_function` and the final text has stripped or
re-partitioned the markers.

### Fact C — the per-event ubergraph path bypasses sequence detection

Event functions (ReceiveTick, ReceiveBeginPlay, etc.) that consist of
`ExecuteUbergraph_*(N)` get their body rendered by
`output_summary/ubergraph/emit.rs::emit_ubergraph_events`, which calls
`output_summary/ubergraph/linearize.rs::split_ubergraph_sections`. That
function:

1. Builds a stmt-level CFG on the **raw** ubergraph statements
   (`build_stmt_cfg`, `cfg/stmt.rs:17`).
2. Partitions stmts by reachability from each event entry offset
   (`partition_by_reachability`, `cfg/stmt.rs:109`).
3. Extracts each partition's stmts (`extract_partition_stmts`,
   `cfg/stmt.rs:182`).
4. For each partition, runs `transform_latch_patterns`,
   `linearize_from_entry`, then `structure_segment`
   (`pipeline.rs::structure_segment`).

`structure_segment` does NOT call `reorder_flow_patterns`. It therefore
**never emits sequence markers** for the per-event content. The markers
that DO appear in the rendered ReceiveTick come from a separate
`structure_function` invocation on the whole ubergraph that feeds a
different code path (likely `format.rs::emit_ubergraph_section` reading
`ctx.structured`).

Net result: the per-event partition gets its event's stmts via reachability
BFS over raw bytecode, with all the latch/sub-sequence layout that
`reorder_flow_patterns` would have flattened still in place. Index shifts
from a small content edit (like adding a PrintString to one pin) cascade
through the partition's reachability set, the linearization order, and the
downstream structurer.

### Fact D — Phase 1 is sound but inert for this case

Phase 1 (relax `detect_interleaved_sequences` to accept pins lying entirely
before the chain) is correct in isolation: a parent Sequence whose pin
bodies the compiler emitted earlier in bytecode is a real and legal pattern.
With Phase 1 the 7-pair parent at chain=222..236 is accepted (per the
trace). But because the per-event path bypasses
`reorder_flow_patterns`, the acceptance has no effect on the ReceiveTick
output. Phase 1 still lands as a stability improvement: detection no longer
flips on/off based on small index shifts upstream of the chain.

## Architectural limits found

- The per-event partition's reachability BFS treats `pop_flow` as a
  terminator. That's intentional — events shouldn't share state across
  pop_flow boundaries. Nothing in this BFS uses Sequence-detection results,
  so adding markers to the input wouldn't help.
- `structure_segment` cannot cheaply call `reorder_flow_patterns` on a
  per-event partition because the partition's stmts are a SUBSET of the
  function's bytecode — sequence chains may span partitions, jump targets
  may be missing.

## Worth trying next (ranked by leverage)

1. **Move sequence detection earlier than per-event partitioning.** Run
   `reorder_flow_patterns` on the FULL ubergraph stmts before
   `partition_by_reachability`. Then partition the post-reorder stmts (which
   already have markers and inlined pin bodies) so each event's partition
   inherits its share of markers. Risk: the post-reorder stmts have
   different offsets than the raw bytecode, which `partition_by_reachability`
   uses to find event entries. Need a stable offset → reordered-index map.

2. **Treat sequence markers as partition boundaries.** Have
   `partition_by_reachability` follow sequence/sub-sequence marker
   boundaries when a partition reaches a marker — pull the whole marker's
   body into the partition atomically. Less invasive than (1) but requires
   the markers to be present in the input, which means running
   `reorder_flow_patterns` first anyway.

3. **Have `structure_segment` invoke flow detection on the per-event
   partition.** Each event is small and self-contained, so running flow
   detection per-event MIGHT work if cross-partition jumps are first
   resolved. The existing `resolve_cross_segment_jumps` already does some of
   this. Risk: a partition's local indices won't match the function-level
   indices, breaking offset-based heuristics in `detect_*_sequences`.

(1) feels like the right fix but is the largest. (2) is the smallest but
might leave correctness gaps for nested patterns. (3) is the
local/incremental approach.

## Branch and tag map

- `archive/pre-sequence-fix` — the pre-touch state on `main`.
- `bugfix/sequence-nested-displaced-else` — Phase 1 commit lives here.
- Read first in a fresh session: this doc, then
  - `src/output_summary/ubergraph/linearize.rs::split_ubergraph_sections`
    around line 433 (`let cleaned = stmts;`).
  - `src/bytecode/cfg/stmt.rs::partition_by_reachability` (line 109).
  - `src/bytecode/pipeline.rs::structure_function` (full function) and
    `structure_segment` (line 98).
  - `src/output_summary/ubergraph/emit.rs::emit_ubergraph_events` (line 104).

## Diagnostics retained

Two env-var-gated traces are now permanent in the codebase. They print to
stderr and produce no overhead when off.

- `BP_INSPECT_TRACE_SEQUENCES=1` — `src/bytecode/flow/loops.rs`. Logs
  per-candidate accept/reject decisions in `detect_grouped_sequences` and
  `detect_interleaved_sequences`. Useful when a parser change drops a
  Sequence and the structurer's downstream output looks scrambled.

- `BP_INSPECT_TRACE_PIPELINE=1` — `src/bytecode/pipeline.rs`. Logs marker
  positions at every stage of `structure_function` (post-emit_reordered,
  post-inline, post-cse, post-discard, post-split_by_sequence_markers,
  pre-cleanup, post-cleanup). Confirms marker preservation through the
  function-level pipeline. Does NOT cover the per-event ubergraph path.

## Phase 1 changeset

`src/bytecode/flow/loops.rs`:
- `SEQ_TRACE_ENV` const, `seq_trace_enabled()` helper, `format_pin_ranges`
  helper.
- `detect_grouped_sequences` emits `[seq:grouped]` accept lines.
- `detect_interleaved_sequences`:
  - Replaced the rejecting `body_start_idx <= inline_end` with the
    overlap-correct `!(body_end_idx < chain_start || body_start_idx >
    inline_end)`. Pins lying entirely before `chain_start` are now legal.
  - Emits `[seq:reject]` and `[seq:accept]` lines under the env var.

`src/bytecode/pipeline.rs`:
- `trace_enabled()`, `trace_markers()`, `trace_segments()`, `trace_lines()`
  helpers gated by `BP_INSPECT_TRACE_PIPELINE`.
- `structure_function` calls them at every pipeline stage.

No behavioral changes in `emit.rs`, `cfg/`, `structure/`, or
`output_summary/`. The relaxation in `loops.rs` is the only logic change and
is sound — Helm snapshots and 489 tests pass.
