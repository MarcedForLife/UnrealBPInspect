//! Decode context threaded through all bytecode decoder functions.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::cfg::region::{RegionId, RegionTree};
use crate::bytecode::cfg::{BlockId, ControlFlowGraph};
use crate::bytecode::partition::OpcodeGraph;
use crate::bytecode::structure::StructureSkeleton;
use crate::types::{FunctionSignature, ImportEntry};

use super::cross_event_inline::CrossEventInlineCtx;

/// Identifies a construct that owns a claimed byte range.
///
/// A claim is owner-tagged so that a construct decoding its own
/// previously-claimed bytes (e.g. an IsValid Branch decoding its
/// `then_body`) can bypass the claim, while sibling decode contexts
/// (the outer Sequence pin's linear sweep) still skip past it. Multiple
/// owners are allowed for the convergence case where two absorbing
/// constructs both claim the same nested range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum OwnerId {
    /// IsValid macro Branch keyed by its `EX_JUMP_IF_NOT` disk offset.
    IsValid { jin_disk: usize },
    /// Trampoline-shared cascade keyed by its convergence body disk
    /// offset.
    TrampolineCascade { merge_disk: usize },
    /// Sequence push-chain keyed by chain head disk offset.
    SequenceChain { head_disk: usize },
    /// Tail-JIN displaced-arm Branch keyed by its `EX_JUMP_IF_NOT` disk
    /// offset. Used for the tail-JIN displaced-arm shape: a backward-target JIN
    /// whose THEN and ELSE bodies live at lower disk offsets as
    /// push-chain heads (tracepoint + push_flow + jump). The arms are
    /// claimed by `prescan_tail_jin_claims` so the outer linear sweep
    /// skips them; `decide_branch_layout` decodes them into the
    /// Branch's then/else bodies.
    TailJinArm { jin_disk: usize },
    /// Cross-event shared body inlined at a source pin. Used for the
    /// trampoline shape where a single K2Node (e.g. a DoOnce macro) is
    /// reachable from two event entries via a fan-in knot, and the
    /// compiler emits a jump from one event into another event's body
    /// region. The variant carries the target K2Node export index
    /// (`target_node_id`) and the disk offset of the inlined region's
    /// anchor (`anchor_disk`) so a co-owner claim on the shared range
    /// can be distinguished per call site. Consumed by
    /// `decode/branch.rs::decode_inlined_shared_body`.
    SharedBody {
        target_node_id: usize,
        anchor_disk: usize,
    },
    /// Disjoint-range jump target inlined at the JUMP source. Used when
    /// an `EX_JUMP` (or an `EX_JUMP_IF_NOT`'s else target) inside one
    /// owned range targets a body sitting in a DIFFERENT owned range of
    /// the same event. The target body is claimed under this owner so
    /// the linear sweep skips it; the JUMP source's decoder then
    /// inlines the body region as the jump's syntactic continuation.
    /// Keyed on the disk offset of the JUMP source so per-call-site
    /// decode contexts can bypass independently.
    DisjointJumpTarget { jump_disk: usize },
    /// CFG region currently being decoded as an arm body. The recogniser
    /// (Branch arm, Sequence pin, cascade convergence, disjoint jump
    /// target) installs this owner before recursing into the arm's
    /// bytes. The claim lookup then bypasses any prescan claim whose
    /// extent sits inside the region's transitive block byte ranges,
    /// regardless of which prescan registered it. Resolves the geometry
    /// mismatch between disk-byte prescan claims (Sequence pin
    /// partitions, IsValid arm segments, DoOnce scaffolds, tail-JIN
    /// arms, trampoline cascades, disjoint-jump targets) and the
    /// CFG-region coordinates the recogniser operates in.
    CfgRegion { region_id: RegionId },
}

/// One claimed byte range with the set of constructs that own it.
#[derive(Debug, Clone)]
pub(crate) struct Claim {
    pub end: usize,
    pub owners: Vec<OwnerId>,
}

/// Shared immutable context for the bytecode decoder.
///
/// Carries the per-asset state every decoder function reads (name table,
/// claim map, skeleton, pin data) and is constructed once per decode.
pub(crate) struct DecodeCtx<'a> {
    /// Raw bytecode bytes for the export being decoded.
    pub bytecode: &'a [u8],
    /// Asset name table, needed to read FName operands during length scanning.
    pub name_table: &'a NameTable,
    /// Import table, needed for object-reference resolution in later phases.
    pub _imports: &'a [ImportEntry],
    /// Export object names (one per export, by index). Used for reference
    /// resolution in later phases.
    pub _export_names: &'a [String],
    /// UE5 file version (`file_ver_ue5`). 0 for UE4 assets, 1000+ for UE5.
    /// Controls Large World Coordinates (LWC) opcode branching and operand
    /// sizes.
    pub ue5: i32,
    /// Memory-to-disk offset map for the entire ubergraph stream. Jump
    /// operands in EX_JUMP / EX_JUMP_IF_NOT are written in memory
    /// coordinates (as the runtime sees them), but the byte slice we
    /// decode is the on-disk representation. The decoder consults this
    /// map to translate jump targets to slice indices. None for standalone
    /// function exports where the bytecode mem and disk coordinates
    /// coincide because no FName-bearing literals shift them apart.
    pub mem_to_disk: Option<&'a BTreeMap<usize, usize>>,
    /// Reverse map from event-entry mem_offset to event name. Populated
    /// for ubergraph decoding only. When a jump target lands on one of
    /// these offsets, the decoder emits Stmt::EventCall instead of
    /// recursing into a Stmt::Branch body.
    pub event_entries: Option<&'a BTreeMap<usize, String>>,
    /// Function name to parameter signature, populated from the parsed
    /// asset. Used at call sites to wrap arguments at OUT-parameter
    /// positions in `Expr::Out`. None for synthetic decode contexts in
    /// unit tests, in which case the wrap step is a no-op.
    pub function_signatures: Option<&'a BTreeMap<String, FunctionSignature>>,
    /// All disk-coordinate byte ranges owned by the event currently being
    /// decoded. Populated for ubergraph events only; the partition splits
    /// each event's bytes into multiple disjoint ranges when sibling
    /// events sit between them. `classify_target` treats any target that
    /// lands in any of these ranges as `InRange`, and `decode_subrange`
    /// uses them to skip bytes that don't belong to the current event
    /// when a body crosses range boundaries. None for standalone function
    /// bodies (single full range) and synthetic test contexts.
    pub owned_ranges: Option<&'a [Range<usize>]>,
    /// Pre-computed structural skeleton for the current event or
    /// function, keyed by Sequence push-chain head disk offset.
    /// `try_decode_sequence` looks up pin partitions here. None for
    /// synthetic test contexts that don't exercise Sequence decoding.
    pub skeleton: Option<&'a StructureSkeleton>,
    /// Owner-tagged claim map: disk-coordinate byte ranges already
    /// recognised by an absorbing construct (IsValid macro, trampoline
    /// cascade, Sequence chain) and therefore off-limits to any decode
    /// context that isn't one of the recorded owners. Each claim records
    /// the set of constructs that may decode its bytes; everyone else
    /// skips past the claim's `end`. Stored behind `RefCell` so nested
    /// decode calls can register and extend claims while the outer walk
    /// is still in progress. None for synthetic test contexts that don't
    /// need claim tracking.
    pub claimed: Option<&'a RefCell<BTreeMap<usize, Claim>>>,
    /// Identity of the construct currently driving body decode. Set by
    /// an absorbing construct (the IsValid Branch's then-body decode)
    /// before recursing into a sub-range, restored after. The claim
    /// lookup compares this against each claim's owners and bypasses
    /// when the current owner is listed. None at top level and within
    /// non-absorbing recursive contexts. Use `with_decoding_owner` to
    /// swap and auto-restore via RAII.
    pub decoding_owner: Cell<Option<OwnerId>>,
    /// Opcode boundary table and successor edges for the bytecode being
    /// decoded. The region walk uses this graph in execution order to
    /// emit statements, so every production caller threads it through.
    /// `None` only for synthetic unit-test contexts that exercise
    /// individual recognisers without running the BFS. The graph is
    /// keyed in disk coordinates, matching everything else in the
    /// decoder.
    pub graph: Option<&'a OpcodeGraph>,
    /// Basic-block CFG + SESE region tree for the current event.
    /// Recognisers in `branch.rs` use these to compute region-aware
    /// arm extents (the immediate post-dominator bounds arm bodies
    /// without disk-byte pattern walks). None for synthetic unit-test
    /// contexts and standalone function decode (no partition).
    pub cfg: Option<&'a ControlFlowGraph>,
    pub region_tree: Option<&'a RegionTree>,
    /// Per-region transitive disk-byte coverage: each `RegionId` maps to
    /// the merged byte ranges of the region's own blocks plus every
    /// descendant region's blocks. Populated alongside `region_tree`
    /// for ubergraph event decode. Consulted by `claimed_end_inner`
    /// when `decoding_owner` is `OwnerId::CfgRegion { region_id }`: a
    /// claim sitting fully inside the region's transitive coverage is
    /// treated as bypassable so the recogniser can decode arm bytes
    /// under a single uniform owner regardless of which prescan
    /// originally claimed them. `None` for standalone function decode
    /// and synthetic test contexts.
    pub region_byte_ranges: Option<&'a BTreeMap<RegionId, Vec<Range<usize>>>>,
    /// State the cross-event inline classifier needs at decode time:
    /// the current event's name, every event's owned ranges, the
    /// event-entry K2Node export id per event, and class/macro name
    /// lookup tables. Bundled into one optional reference so existing
    /// `DecodeCtx` construction sites only grow by one field. Populated
    /// for ubergraph decoding only; standalone function decode and
    /// synthetic test contexts pass `None` and the classifier short-
    /// circuits to the existing drop behaviour.
    pub cross_event_inline: Option<&'a CrossEventInlineCtx<'a>>,
    /// K2Node-to-bytes attribution map. Populated for ubergraph
    /// decoding when the build site in `decode/mod.rs` constructs one;
    /// standalone function decode and synthetic test contexts pass
    /// `None`. Consumed by cross-event inline, claim tracking, and the
    /// recogniser classifiers.
    pub k2node_byte_map: Option<&'a crate::bytecode::k2node_byte_map::K2NodeByteMap>,
    /// Scoped boundary stop-set for the boundary-aware region-walk descent.
    /// When a SequenceChain pin walk
    /// dispatches a descendant IfThenElse/Loop/Switch via
    /// `dispatch_child_region_at`, it installs the parent walk's
    /// sibling-pin entry blocks here so the dispatched region's arm slicer
    /// (`arm_byte_slice`, `reachable_blocks_in_arm`) treats those blocks as
    /// additional walk boundaries and cannot over-walk into a sibling pin
    /// (which would then re-emit the same content). Empty at top level and
    /// in every context where the descent flag is off, so reading it is a
    /// no-op for the current production path. Set via
    /// `with_arm_descent_stops` so a temporary scope can't leak into
    /// sibling decode paths.
    pub arm_descent_stops: RefCell<BTreeSet<BlockId>>,
    /// When set, the loop emitter is decoding a `RegionKind::Loop`'s
    /// body/completion byte range and `decode_segment_into` should route
    /// any nested `RegionKind::IfThenElse` region whose entry it reaches
    /// to the structured emitter (`try_emit_ifthenelse_region`) rather
    /// than the legacy byte-slice `decode_branch`. Holds the loop's own
    /// `RegionId` so the dispatch only fires for IfThenElse regions that
    /// are descendants of this loop (the loop-shadowed-IfThenElse case).
    /// `None` everywhere else, so the byte-slice path is unchanged outside
    /// the loop emitter. Set via `with_loop_completion_region` (RAII).
    pub loop_completion_region: Cell<Option<RegionId>>,
    /// Active loop-break-guard context. Set by `try_decode_loop` around
    /// the decode of an absorbed ForEach loop's displaced body so the
    /// naked-if recognizer can recover a loop-internal `if` break-guard
    /// whose `EX_POP_FLOW_IF_NOT` has no balancing `EX_POP_EXECUTION_FLOW`
    /// (the false path pops the trampoline frame and resumes the loop
    /// increment instead of closing an inner frame). `None` outside the
    /// loop body decode, so the recognizer's loop-aware fallback never
    /// fires in non-loop contexts. Set via `with_loop_break_guard` (RAII).
    pub loop_break_guard: Cell<Option<LoopBreakGuard>>,
    /// Set true ONLY for the lifetime of the
    /// `try_dispatch_loop_body_loop_region_at` helper's `try_emit_loop_region`
    /// call. When set, `try_decode_loop`'s skip-target gate
    /// (`post_loop_disk != resume_disk`) is bypassed IFF the skip target is a
    /// flow-pop block that converges to the loop's post-loop landing (the
    /// narrow displaced-trampoline shape). The flag is reached ONLY via the
    /// dispatch helper, so the linear-sweep caller (`block.rs`) and the
    /// sibling-walk caller keep the strict gate. Set via
    /// `with_loop_dispatch_relaxed` (RAII). Always `false` outside the
    /// dispatch, so the gate is unchanged on every other path.
    pub loop_dispatch_relaxed: Cell<bool>,
    /// RegionIds whose `Stmt::Loop` was already emitted by the
    /// `try_dispatch_loop_body_loop_region_at` helper. `walk_region` checks
    /// this at its TOP (before any `try_emit_*`) and skips the region when
    /// present, suppressing the sibling re-emit that a `CfgRegion` claim
    /// cannot stop (the region self-bypasses its own claim under
    /// `decoding_owner = CfgRegion{region}`). Lives on `ctx` because the
    /// dispatch fires inside a `decode_subrange` recursion that does NOT share
    /// the top-level walk's `consumed`/`visited_blocks`. Per-function-scoped:
    /// `ctx` (and therefore this set) is rebuilt per function/event decode, so
    /// a RegionId can never leak across functions. `BTreeSet` for determinism.
    pub dispatched_loop_regions: RefCell<BTreeSet<RegionId>>,
    /// Disk byte segments of the recogniser arm currently being decoded
    /// by `decode_arm_segments`, accumulated as each segment is processed.
    /// The disjoint-range inline path (`disjoint_jump_target_extent`)
    /// consults this so it does not re-decode a JUMP target body whose
    /// bytes an EARLIER segment of the same arm already covered directly
    /// (suppressing a spurious leading `ResetDoOnce` on the arm). A body
    /// that lies in its own owned range, NOT covered by any earlier arm
    /// segment (a genuine cross-range reset), is genuinely disjoint
    /// and still pulls. Empty outside an arm-segment decode, so every
    /// other disjoint pull is unchanged. Set via
    /// `with_arm_covered_segments` (RAII).
    pub arm_covered_segments: RefCell<Vec<Range<usize>>>,
}

impl<'a> DecodeCtx<'a> {
    /// Construct a decode context with the always-present inputs, every optional
    /// reference defaulted to `None`, and all transient state initialised empty.
    /// Construction sites override only the fields they actually populate via
    /// struct-update syntax: `DecodeCtx { skeleton: Some(&s), ..DecodeCtx::new(..) }`.
    pub(crate) fn new(
        bytecode: &'a [u8],
        name_table: &'a NameTable,
        imports: &'a [ImportEntry],
        export_names: &'a [String],
        ue5: i32,
    ) -> Self {
        DecodeCtx {
            bytecode,
            name_table,
            _imports: imports,
            _export_names: export_names,
            ue5,
            mem_to_disk: None,
            event_entries: None,
            function_signatures: None,
            owned_ranges: None,
            skeleton: None,
            claimed: None,
            decoding_owner: Cell::new(None),
            graph: None,
            cfg: None,
            region_tree: None,
            region_byte_ranges: None,
            cross_event_inline: None,
            k2node_byte_map: None,
            arm_descent_stops: RefCell::new(BTreeSet::new()),
            loop_completion_region: Cell::new(None),
            loop_break_guard: Cell::new(None),
            loop_dispatch_relaxed: Cell::new(false),
            dispatched_loop_regions: RefCell::new(BTreeSet::new()),
            arm_covered_segments: RefCell::new(Vec::new()),
        }
    }
}

/// Context the naked-if recognizer needs to recover a loop-internal
/// break-guard from a `EX_POP_FLOW_IF_NOT` that has no balancing
/// `EX_POP_EXECUTION_FLOW`.
///
/// All offsets are disk coordinates. The guard's true-body is bounded by
/// `tail` (the loop's displaced-body terminator). The discriminator fires
/// only when the guard's false-path continuation (the trampoline frame's
/// pushed target, i.e. the loop increment) lands inside
/// `[scope_start, scope_end)`. The recovered body range is claimed under
/// `owner` so the region walker's disk-order re-walk skips it instead of
/// re-emitting the body as a dead tail after the loop.
#[derive(Clone, Copy, Debug)]
pub(crate) struct LoopBreakGuard {
    /// Loop tail: the displaced-body terminator disk offset. Bounds the
    /// guard true-body so it stops at the loop continue point rather than
    /// running to `range_end`.
    pub tail: usize,
    /// Innermost active loop scope start (the loop head disk offset).
    pub scope_start: usize,
    /// Innermost active loop scope end (the loop's post-back-edge resume
    /// disk offset).
    pub scope_end: usize,
    /// The guard's false-path continuation: the trampoline frame's pushed
    /// target, i.e. the loop increment the matching pop resumes. The
    /// discriminator fires only when this lands inside
    /// `[scope_start, scope_end)`.
    pub continuation: usize,
    /// Disk offset where the loop's displaced body begins. Bounds the
    /// backward-break discriminator: an `EX_JUMP` inside the displaced
    /// body whose target lands within `[displaced_start, tail]` is a
    /// loop break-jump back to a sibling break-guard, not a normal
    /// continuation. Used by the multi-break fix.
    pub displaced_start: usize,
    /// Owner under which the recovered guard body is claimed for the
    /// region-walker dedup.
    pub owner: OwnerId,
}

/// RAII guard that restores a `Cell`'s previous value on drop. Returned by
/// the `DecodeCtx::with_*` accessors backed by a `Cell` so a temporary
/// field swap can't leak into sibling decode paths.
pub(crate) struct ScopedCell<'a, T: Copy> {
    cell: &'a Cell<T>,
    previous: T,
}

impl<'a, T: Copy> ScopedCell<'a, T> {
    /// Set `cell` to `value`, capturing the prior value for restoration on drop.
    fn set(cell: &'a Cell<T>, value: T) -> Self {
        let previous = cell.get();
        cell.set(value);
        ScopedCell { cell, previous }
    }
}

impl<T: Copy> Drop for ScopedCell<'_, T> {
    fn drop(&mut self) {
        self.cell.set(self.previous);
    }
}

/// RAII guard that restores a `RefCell`'s previous contents on drop.
/// Returned by the `DecodeCtx::with_*` accessors backed by a `RefCell` so a
/// temporary set/segment swap can't leak into sibling decode paths.
pub(crate) struct ScopedRefCell<'a, T: Default> {
    cell: &'a RefCell<T>,
    previous: T,
}

impl<'a, T: Default> ScopedRefCell<'a, T> {
    /// Replace `cell`'s contents with `value`, capturing the prior contents
    /// for restoration on drop.
    fn replace(cell: &'a RefCell<T>, value: T) -> Self {
        let previous = std::mem::replace(&mut *cell.borrow_mut(), value);
        ScopedRefCell { cell, previous }
    }
}

impl<T: Default> Drop for ScopedRefCell<'_, T> {
    fn drop(&mut self) {
        *self.cell.borrow_mut() = std::mem::take(&mut self.previous);
    }
}

impl<'a> DecodeCtx<'a> {
    /// Compute disk-byte arm extents for a recogniser at `entry_disk`
    /// reaching `arm_targets`. Returns one `Vec<Range>` per arm, each
    /// being the union of disk segments reachable from the arm entry
    /// without crossing the SESE region exit. Returns `None` when this
    /// context has no CFG / region tree or `entry_disk` doesn't fall
    /// in any CFG block; callers fall back to their disk-byte paths.
    pub(crate) fn region_arm_extents_for(
        &self,
        entry_disk: usize,
        arm_targets: &[usize],
    ) -> Option<Vec<Vec<Range<usize>>>> {
        let cfg = self.cfg?;
        let region_tree = self.region_tree?;
        let region_id = self.region_id_for(entry_disk)?;
        let region_exit = region_tree.regions[region_id].exit;
        let arm_entries: Vec<Option<BlockId>> = arm_targets
            .iter()
            .map(|&target| {
                cfg.block_at_start(target)
                    .or_else(|| block_containing_opcode(cfg, target))
            })
            .collect();
        Some(crate::bytecode::decode::branch::region_arm_extents(
            &arm_entries,
            region_exit,
            cfg,
        ))
    }

    /// Map a disk address to the innermost CFG region containing it.
    /// Returns `None` when this context has no CFG / region tree or the
    /// address doesn't fall inside any basic block. Used by recognisers
    /// to install `OwnerId::CfgRegion { region_id }` before recursing
    /// into arm bytes, and shared with `region_arm_extents_for` so the
    /// lookup logic lives in one place.
    pub(crate) fn region_id_for(&self, disk_offset: usize) -> Option<RegionId> {
        let cfg = self.cfg?;
        let region_tree = self.region_tree?;
        let block = block_containing_opcode(cfg, disk_offset)?;
        region_tree.block_to_region.get(&block).copied()
    }

    /// Set `decoding_owner` to `owner` for the lifetime of the returned
    /// guard, restoring the previous value on drop.
    pub(crate) fn with_decoding_owner(&self, owner: OwnerId) -> ScopedCell<'_, Option<OwnerId>> {
        ScopedCell::set(&self.decoding_owner, Some(owner))
    }

    /// Replace `arm_descent_stops` with `stops` for the lifetime of the
    /// returned guard, restoring the previous contents on drop. The
    /// boundary-aware region-walk descent installs the parent pin walk's
    /// sibling-pin entry blocks before dispatching a descendant region so
    /// the dispatched region's arm slicer treats them as walk boundaries.
    pub(crate) fn with_arm_descent_stops(
        &self,
        stops: BTreeSet<BlockId>,
    ) -> ScopedRefCell<'_, BTreeSet<BlockId>> {
        ScopedRefCell::replace(&self.arm_descent_stops, stops)
    }

    /// Replace `arm_covered_segments` with `segments` for the lifetime of
    /// the returned guard, restoring the previous contents on drop. The
    /// arm-segment decode installs the segments it has decoded so far so
    /// the disjoint-range inline path can skip re-decoding a JUMP target
    /// body those segments already covered.
    pub(crate) fn with_arm_covered_segments(
        &self,
        segments: Vec<Range<usize>>,
    ) -> ScopedRefCell<'_, Vec<Range<usize>>> {
        ScopedRefCell::replace(&self.arm_covered_segments, segments)
    }

    /// True when `[body_start, body_end)` lies fully inside one of the
    /// arm segments currently registered in `arm_covered_segments` (the
    /// earlier-decoded segments of the arm being processed). The disjoint
    /// inline path uses this to drop a re-pull of a body an earlier arm
    /// segment already decoded directly. Returns `false` when
    /// no arm segment is registered, so disjoint pulls outside an
    /// arm-segment decode are unaffected.
    pub(crate) fn arm_segment_covers(&self, body_start: usize, body_end: usize) -> bool {
        self.arm_covered_segments
            .borrow()
            .iter()
            .any(|segment| segment.start <= body_start && body_end <= segment.end)
    }

    /// Set `loop_completion_region` to `region_id` for the lifetime of the
    /// returned guard so `decode_segment_into` can route nested IfThenElse
    /// regions of this loop to the structured emitter. Restores the
    /// previous value on drop.
    pub(crate) fn with_loop_completion_region(
        &self,
        region_id: RegionId,
    ) -> ScopedCell<'_, Option<RegionId>> {
        ScopedCell::set(&self.loop_completion_region, Some(region_id))
    }

    /// Set `loop_break_guard` to `guard` for the lifetime of the returned
    /// guard so the naked-if recognizer can recover a loop-internal break
    /// guard while decoding the loop's displaced body. Restores the
    /// previous value on drop.
    pub(crate) fn with_loop_break_guard(
        &self,
        guard: LoopBreakGuard,
    ) -> ScopedCell<'_, Option<LoopBreakGuard>> {
        ScopedCell::set(&self.loop_break_guard, Some(guard))
    }

    /// Set `loop_dispatch_relaxed` to true for the lifetime of the returned
    /// guard. Restores the previous value on drop. Only the
    /// loop-body dispatch helper sets this, so the relaxed skip-target gate
    /// branch in `try_decode_loop` is reachable from no other path.
    pub(crate) fn with_loop_dispatch_relaxed(&self) -> ScopedCell<'_, bool> {
        ScopedCell::set(&self.loop_dispatch_relaxed, true)
    }
}

/// Find the basic block whose opcode list contains `addr`. Used by the
/// region-aware accessor to map a JIN / Switch / IsValid disk offset
/// (always the terminator of its enclosing block, not the block start)
/// to the BlockId that owns it.
fn block_containing_opcode(cfg: &ControlFlowGraph, addr: usize) -> Option<BlockId> {
    cfg.blocks
        .iter()
        .find(|block| !block.opcodes.is_empty() && addr >= block.start && addr < block.end)
        .map(|block| block.id)
}

/// Environment variable that gates verbose decode debug logging.
pub(crate) const DEBUG_ENV_VAR: &str = "BP_INSPECT_DEBUG";

/// True when verbose decode debug logging is enabled via `DEBUG_ENV_VAR`.
pub(crate) fn debug_enabled() -> bool {
    std::env::var_os(DEBUG_ENV_VAR).is_some()
}

/// Insert `[start, end)` into the claimed-range map with the given owner.
/// No-op when `claimed` is `None` (synthetic contexts) or when
/// `start >= end`.
///
/// When a claim with the exact same `start` already exists with the
/// same `end`, the new owner is appended to its owner set (deduplicated).
/// Partial overlaps (same start, different end, or interleaved ranges)
/// aren't expected with the current call sites; mismatched-end inserts
/// log under `BP_INSPECT_DEBUG` and overwrite, preserving previous
/// behaviour for accidental conflicts.
pub(crate) fn mark_claimed(ctx: &DecodeCtx, start: usize, end: usize, owner: OwnerId) {
    if start >= end {
        return;
    }
    let Some(claimed) = ctx.claimed else {
        return;
    };
    let mut map = claimed.borrow_mut();
    match map.get_mut(&start) {
        Some(existing) if existing.end == end => {
            if !existing.owners.contains(&owner) {
                existing.owners.push(owner);
            }
        }
        Some(existing) => {
            if debug_enabled() {
                eprintln!(
                    "mark_claimed: end mismatch at start=0x{:x}: existing end=0x{:x} new end=0x{:x}",
                    start, existing.end, end
                );
            }
            existing.end = end;
            if !existing.owners.contains(&owner) {
                existing.owners.push(owner);
            }
        }
        None => {
            map.insert(
                start,
                Claim {
                    end,
                    owners: vec![owner],
                },
            );
        }
    }
}

/// When an absorbing construct (IsValid macro, trampoline cascade)
/// claims `[claim_start, claim_end)`, walk the existing claim map and
/// add `absorber` as an owner of every SequenceChain claim whose extent
/// sits inside the absorbed range. The absorbing construct's body
/// decode (which sets `decoding_owner` to `absorber`) then bypasses
/// those inner claims and emits the chain nested inside its body.
///
/// When a claim's `[start, end)` range matches the absorbed range
/// exactly, additionally REMOVE every SequenceChain owner from that
/// claim. This handles the case where an outer Sequence pin partition
/// coincides with an absorbed range: the outer chain's pin body decode
/// (running with `decoding_owner = SequenceChain{outer}`) must skip the
/// absorbed bytes wholesale rather than walk into them and emit the
/// inner chain a second time. The absorber's own body decode still
/// bypasses the claim because it's now the sole owner. Inner chain
/// claims that sit STRICTLY inside the absorbed range keep their
/// SequenceChain owner so the inner chain's own pin body decode
/// (running with `decoding_owner = SequenceChain{inner}`) bypasses.
pub(crate) fn absorb_overlapping_chains(
    ctx: &DecodeCtx,
    claim_start: usize,
    claim_end: usize,
    absorber: OwnerId,
) {
    let Some(claimed) = ctx.claimed else { return };
    let mut map = claimed.borrow_mut();
    for (&start, claim) in map.range_mut(claim_start..claim_end) {
        if claim.end > claim_end {
            continue;
        }
        let already_owns = claim.owners.contains(&absorber);
        let is_chain = claim
            .owners
            .iter()
            .any(|owner| matches!(owner, OwnerId::SequenceChain { .. }));
        if !is_chain {
            continue;
        }
        // Exact-match: absorbed range coincides with a SequenceChain pin
        // partition. Transfer ownership to the absorber so the chain's
        // own pin body decode (which sets `decoding_owner` to the chain
        // SequenceChain owner) skips this pin wholesale rather than
        // walking into it and re-emitting the absorbed inner content.
        let exact_match = start == claim_start && claim.end == claim_end;
        if exact_match {
            claim
                .owners
                .retain(|owner| !matches!(owner, OwnerId::SequenceChain { .. }));
            if !claim.owners.contains(&absorber) {
                claim.owners.push(absorber);
            }
        } else if !already_owns {
            claim.owners.push(absorber);
        }
    }
}

/// True when `owner` represents an absorbing construct, i.e. a
/// recogniser that decodes bytes belonging to another construct's
/// region into its own body. SequenceChain claims, by themselves, only
/// exist to make the outer linear sweep skip pin partition bytes; they
/// don't absorb. `TailJinArm` is likewise a non-absorbing co-owner tag.
/// `SharedBody` is the cross-event inline co-owner tag: the inline
/// recursion bypasses the standalone event's existing claim by setting
/// `decoding_owner` to the SharedBody owner before recursing, so the
/// claim must be treated as bypassable rather than absorbed.
fn is_absorbing(owner: &OwnerId) -> bool {
    matches!(
        owner,
        OwnerId::IsValid { .. } | OwnerId::TrampolineCascade { .. }
    )
}

/// If `pos` falls inside a claimed range AND the current
/// `ctx.decoding_owner` isn't listed among that claim's owners, return
/// the claim's end so the caller can skip past it.
///
/// `disk_sweep` controls how SequenceChain-only claims (claims with
/// no absorbing owner) are treated:
/// - `true` (the region walk's outer disk-order sweep): skip them so pin
///   partitions sitting at lower disk offsets than their chain head
///   don't decode at top level before the chain head's
///   `try_decode_sequence` dispatch.
/// - `false` (recursive body decode): ignore them. Pin partition
///   bypass for legitimate chain decoders happens because
///   `try_decode_sequence` sets the chain owner before recursing into
///   pin bodies; a body decode that didn't set an owner wouldn't get a
///   bypass match either. Skipping non-absorbed chain claims here
///   would suppress the inner chain's nested emission inside other
///   constructs (e.g. a ForLoop body that contains a Sequence chain
///   start) when the parent decoder is operating without an owner.
///
/// Returns `None` when:
/// - the context has no claim map,
/// - `pos` lies outside every claim,
/// - the current `decoding_owner` matches a claim owner (bypass), or
/// - `disk_sweep` is `false` and the claim has no absorbing owner.
pub(crate) fn claimed_end_for(ctx: &DecodeCtx, pos: usize) -> Option<usize> {
    claimed_end_inner(ctx, pos, false)
}

/// Variant for the region walk's outer disk-order sweep. See
/// [`claimed_end_for`] for the `disk_sweep` semantics.
pub(crate) fn claimed_end_for_disk_sweep(ctx: &DecodeCtx, pos: usize) -> Option<usize> {
    claimed_end_inner(ctx, pos, true)
}

fn claimed_end_inner(ctx: &DecodeCtx, pos: usize, disk_sweep: bool) -> Option<usize> {
    let claimed = ctx.claimed?;
    let map = claimed.borrow();
    let (&start, claim) = map.range(..=pos).next_back()?;
    if pos < start || pos >= claim.end {
        return None;
    }
    if let Some(owner) = ctx.decoding_owner.get() {
        if claim.owners.contains(&owner) {
            return None;
        }
        if let OwnerId::CfgRegion { region_id } = owner {
            if claim_contained_in_region(ctx, region_id, start, claim.end) {
                return None;
            }
        }
    }
    if !disk_sweep && !claim.owners.iter().any(is_absorbing) {
        return None;
    }
    Some(claim.end)
}

/// True when `[claim_start, claim_end)` lies fully inside the transitive
/// disk-byte coverage of `region_id`. Strict containment: the entire
/// claim must be covered by the merged region ranges (the claim cannot
/// straddle a coverage gap). Returns `false` when `region_byte_ranges`
/// is `None` (synthetic contexts or standalone function decode where
/// CfgRegion ownership shouldn't be installed in the first place).
fn claim_contained_in_region(
    ctx: &DecodeCtx,
    region_id: RegionId,
    claim_start: usize,
    claim_end: usize,
) -> bool {
    let Some(map) = ctx.region_byte_ranges else {
        return false;
    };
    let Some(ranges) = map.get(&region_id) else {
        return false;
    };
    let mut cursor = claim_start;
    while cursor < claim_end {
        let covering = ranges
            .iter()
            .find(|range| range.start <= cursor && cursor < range.end);
        match covering {
            Some(range) => {
                if range.end >= claim_end {
                    return true;
                }
                cursor = range.end;
            }
            None => return false,
        }
    }
    cursor >= claim_end
}

/// Build the per-region transitive byte-range cache. For each region in
/// the tree, collect every block id reachable through descendant
/// regions (including the region itself), map to `[block.start,
/// block.end)`, sort, and merge adjacent ranges. The resulting map is
/// stored on `DecodeCtx::region_byte_ranges` and consulted by the
/// CfgRegion bypass in `claimed_end_inner`.
pub(crate) fn build_region_byte_ranges(
    cfg: &ControlFlowGraph,
    region_tree: &RegionTree,
) -> BTreeMap<RegionId, Vec<Range<usize>>> {
    let block_range = |block_id: BlockId| -> Option<Range<usize>> {
        let block = cfg.blocks.get(block_id)?;
        if block.opcodes.is_empty() || block.end <= block.start {
            return None;
        }
        Some(block.start..block.end)
    };
    fn collect_subtree(
        tree: &RegionTree,
        region_id: RegionId,
        blocks_per_region: &BTreeMap<RegionId, Vec<BlockId>>,
        out: &mut Vec<BlockId>,
    ) {
        if let Some(own) = blocks_per_region.get(&region_id) {
            out.extend(own.iter().copied());
        }
        for &child in &tree.regions[region_id].children {
            collect_subtree(tree, child, blocks_per_region, out);
        }
    }
    // Group blocks by their innermost enclosing region first.
    let mut blocks_per_region: BTreeMap<RegionId, Vec<BlockId>> = BTreeMap::new();
    for (&block_id, &region_id) in &region_tree.block_to_region {
        blocks_per_region
            .entry(region_id)
            .or_default()
            .push(block_id);
    }
    let mut result: BTreeMap<RegionId, Vec<Range<usize>>> = BTreeMap::new();
    for region_id in 0..region_tree.regions.len() {
        let mut blocks: Vec<BlockId> = Vec::new();
        collect_subtree(region_tree, region_id, &blocks_per_region, &mut blocks);
        let mut ranges: Vec<Range<usize>> = blocks.into_iter().filter_map(block_range).collect();
        ranges.sort_by_key(|range| range.start);
        let merged = merge_adjacent_ranges(ranges);
        result.insert(region_id, merged);
    }
    result
}

fn merge_adjacent_ranges(ranges: Vec<Range<usize>>) -> Vec<Range<usize>> {
    let mut merged: Vec<Range<usize>> = Vec::with_capacity(ranges.len());
    for range in ranges {
        match merged.last_mut() {
            Some(prev) if range.start <= prev.end => {
                if range.end > prev.end {
                    prev.end = range.end;
                }
            }
            _ => merged.push(range),
        }
    }
    merged
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::NameTable;

    fn ctx_with_claims<'a>(
        bytecode: &'a [u8],
        name_table: &'a NameTable,
        claims: &'a RefCell<BTreeMap<usize, Claim>>,
    ) -> DecodeCtx<'a> {
        DecodeCtx {
            claimed: Some(claims),
            ..DecodeCtx::new(bytecode, name_table, &[], &[], 0)
        }
    }

    #[test]
    fn claim_with_owner_a_skips_for_none() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn claim_with_owner_a_bypasses_for_a() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        let _g = ctx.with_decoding_owner(owner_a);
        assert_eq!(claimed_end_for(&ctx, 0x15), None);
    }

    #[test]
    fn claim_with_owner_a_skips_for_b() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        let owner_b = OwnerId::IsValid { jin_disk: 0x200 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        let _g = ctx.with_decoding_owner(owner_b);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn multi_owner_bypasses_for_each_owner() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        let owner_b = OwnerId::SequenceChain { head_disk: 0x300 };
        let owner_c = OwnerId::TrampolineCascade { merge_disk: 0x500 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        mark_claimed(&ctx, 0x10, 0x20, owner_b);
        {
            let _g = ctx.with_decoding_owner(owner_a);
            assert_eq!(claimed_end_for(&ctx, 0x15), None);
        }
        {
            let _g = ctx.with_decoding_owner(owner_b);
            assert_eq!(claimed_end_for(&ctx, 0x15), None);
        }
        {
            let _g = ctx.with_decoding_owner(owner_c);
            assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
        }
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn disk_sweep_claim_bypasses_only_for_matching_owner() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        // `IsValid` is a non-absorbing prescan-style owner, so the relevant
        // query is the outer disk-order sweep (`claimed_end_for_disk_sweep`),
        // which the region walker uses to skip prescan-claimed bytes. The
        // recursive-body query (`claimed_end_for`) ignores non-absorbing
        // claims by design and returns None regardless of owner.
        let owner = OwnerId::IsValid { jin_disk: 0x10 };
        mark_claimed(&ctx, 0x10, 0x20, owner);
        // No decoding owner: the disk-order sweep skips the claimed bytes.
        assert_eq!(claimed_end_for_disk_sweep(&ctx, 0x15), Some(0x20));
        // Same owner key: bypass under both query variants.
        {
            let _g = ctx.with_decoding_owner(owner);
            assert_eq!(claimed_end_for_disk_sweep(&ctx, 0x15), None);
            assert_eq!(claimed_end_for(&ctx, 0x15), None);
        }
        // Different owner key (same kind): no bypass.
        {
            let _g = ctx.with_decoding_owner(OwnerId::IsValid { jin_disk: 0x11 });
            assert_eq!(claimed_end_for_disk_sweep(&ctx, 0x15), Some(0x20));
        }
        // Unrelated owner kind: no bypass.
        {
            let _g = ctx.with_decoding_owner(OwnerId::DisjointJumpTarget { jump_disk: 0x100 });
            assert_eq!(claimed_end_for_disk_sweep(&ctx, 0x15), Some(0x20));
        }
    }

    #[test]
    fn owner_guard_restores_previous_owner_on_drop() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        let owner_b = OwnerId::SequenceChain { head_disk: 0x300 };
        let _outer = ctx.with_decoding_owner(owner_a);
        {
            let _inner = ctx.with_decoding_owner(owner_b);
            assert_eq!(ctx.decoding_owner.get(), Some(owner_b));
        }
        assert_eq!(ctx.decoding_owner.get(), Some(owner_a));
    }

    #[test]
    fn duplicate_owner_insert_is_noop() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        let map = claims.borrow();
        let claim = map.get(&0x10).expect("claim present");
        assert_eq!(claim.owners.len(), 1);
        assert_eq!(claim.end, 0x20);
    }

    #[test]
    fn pos_outside_claim_returns_none() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let owner_a = OwnerId::IsValid { jin_disk: 0x100 };
        mark_claimed(&ctx, 0x10, 0x20, owner_a);
        assert_eq!(claimed_end_for(&ctx, 0x05), None);
        assert_eq!(claimed_end_for(&ctx, 0x20), None);
        assert_eq!(claimed_end_for(&ctx, 0x25), None);
    }

    fn ctx_with_region_ranges<'a>(
        bytecode: &'a [u8],
        name_table: &'a NameTable,
        claims: &'a RefCell<BTreeMap<usize, Claim>>,
        region_ranges: &'a BTreeMap<RegionId, Vec<Range<usize>>>,
    ) -> DecodeCtx<'a> {
        let mut ctx = ctx_with_claims(bytecode, name_table, claims);
        ctx.region_byte_ranges = Some(region_ranges);
        ctx
    }

    fn region_ranges_with(
        region_id: RegionId,
        ranges: &[(usize, usize)],
    ) -> BTreeMap<RegionId, Vec<Range<usize>>> {
        let mut map: BTreeMap<RegionId, Vec<Range<usize>>> = BTreeMap::new();
        let owned: Vec<Range<usize>> = ranges.iter().map(|(start, end)| *start..*end).collect();
        map.insert(region_id, owned);
        map
    }

    #[test]
    fn cfg_region_owner_bypasses_contained_claim() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let region_ranges = region_ranges_with(7, &[(0x00, 0x100)]);
        let ctx = ctx_with_region_ranges(&[], &names, &claims, &region_ranges);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        mark_claimed(&ctx, 0x10, 0x20, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x15), None);
    }

    #[test]
    fn cfg_region_owner_does_not_bypass_uncovered_claim() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let region_ranges = region_ranges_with(7, &[(0x00, 0x10)]);
        let ctx = ctx_with_region_ranges(&[], &names, &claims, &region_ranges);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        // Claim [0x10, 0x20): starts AT region's end boundary, fully
        // outside the coverage.
        mark_claimed(&ctx, 0x10, 0x20, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn cfg_region_owner_does_not_bypass_partially_covered_claim() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        // Coverage stops at 0x18, claim extends to 0x20.
        let region_ranges = region_ranges_with(7, &[(0x00, 0x18)]);
        let ctx = ctx_with_region_ranges(&[], &names, &claims, &region_ranges);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        mark_claimed(&ctx, 0x10, 0x20, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn cfg_region_owner_bypasses_claim_spanning_adjacent_ranges() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        // Two non-adjacent ranges; the claim must NOT straddle the gap.
        let region_ranges = region_ranges_with(7, &[(0x00, 0x10), (0x18, 0x30)]);
        let ctx = ctx_with_region_ranges(&[], &names, &claims, &region_ranges);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        mark_claimed(&ctx, 0x20, 0x28, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x22), None);
    }

    #[test]
    fn cfg_region_owner_skips_claim_in_gap() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let region_ranges = region_ranges_with(7, &[(0x00, 0x10), (0x20, 0x30)]);
        let ctx = ctx_with_region_ranges(&[], &names, &claims, &region_ranges);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        // Claim straddles the gap [0x10, 0x20).
        mark_claimed(&ctx, 0x14, 0x22, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x22));
    }

    #[test]
    fn cfg_region_owner_without_byte_ranges_does_not_bypass() {
        let claims = RefCell::new(BTreeMap::new());
        let names = NameTable::from_names(vec![]);
        let ctx = ctx_with_claims(&[], &names, &claims);
        let prescan_owner = OwnerId::IsValid { jin_disk: 0x50 };
        mark_claimed(&ctx, 0x10, 0x20, prescan_owner);
        let region_owner = OwnerId::CfgRegion { region_id: 7 };
        let _guard = ctx.with_decoding_owner(region_owner);
        assert_eq!(claimed_end_for(&ctx, 0x15), Some(0x20));
    }

    #[test]
    fn merge_adjacent_ranges_coalesces_touching_and_overlapping() {
        let merged = merge_adjacent_ranges(vec![0..10, 10..20, 25..30, 28..35]);
        assert_eq!(merged, vec![0..20, 25..35]);
    }
}
