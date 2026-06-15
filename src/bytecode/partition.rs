//! Per-event bytecode partitioning for the bytecode decoder.
//!
//! Walks opcode-level reachability (breadth-first search) from each event
//! entry point and assigns bytecode byte ranges to events, working directly
//! on opcode reachability rather than splitting a flat statement stream
//! after the fact (which needed Sequence super-block collapse, augment
//! passes, and fuzzy offset resolution).
//!
//! The public entry point is [`partition_ubergraph`].
//!
//! Opcode length scanning is self-contained (see [`advance_expr`]) rather than
//! delegating to the expression decoder in `src/bytecode/decode/`, because
//! `DecodeCtx` fields are `pub(super)` and cannot be constructed from outside
//! that module. The scanner mirrors its dispatch table closely enough to stay
//! correct while remaining independent of its internals.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Range;

use crate::binary::NameTable;
use crate::bytecode::decode::walker::{walk_opcode, OpcodeVisitor, SwitchValueCase, WalkCtx};
use crate::bytecode::opcodes::*;
use crate::bytecode::readers::BytecodeView;

/// An event entry point into the ubergraph bytecode.
///
/// `mem_offset` is the memory-address offset (as stored in the
/// `ExecuteUbergraph_Name(N)` call sites), which maps directly onto a byte
/// position in the raw bytecode slice. For UE4 uncooked assets the
/// on-disk/in-memory adjustment is zero, so `mem_offset` equals the byte index.
///
/// `export_index` is the 1-based package export index of the export whose
/// bytecode holds the `ExecuteUbergraph_Name(N)` dispatch call (the event's
/// stub function export, named after the event). It uses the same convention
/// as `ParsedAsset::bytecode_by_export` keys (`export_idx + 1`). The decoder
/// carries it through partition so the resulting event body can be keyed back
/// to its originating export rather than re-joined by name downstream.
pub struct EventEntry {
    pub name: String,
    pub mem_offset: usize,
    pub export_index: usize,
}

/// Shared context threaded through the stack-aware partition pipeline.
///
/// Bundles the opcode graph and tail-JIN displaced-arm boundary list so
/// that callers don't need to forward both individually through every
/// layer of the partitioner. `arm_boundaries` is empty for the common
/// case (events with no tail-JIN arms).
pub(crate) struct PartitionCtx<'a> {
    pub graph: &'a OpcodeGraph,
    pub arm_boundaries: &'a [Range<usize>],
}

/// Errors from [`partition_ubergraph`].
#[derive(Debug)]
pub enum PartitionError {
    /// `event_entries` was empty; nothing to partition.
    NoEventEntries,
    /// An event entry's `mem_offset` does not land on an opcode boundary.
    EntryNotOpcodeBoundary { name: String, mem_offset: usize },
    /// A jump instruction targets a byte that is not an opcode boundary,
    /// indicating corrupt or unrecognised bytecode.
    JumpToMidInstruction {
        from_offset: usize,
        to_offset: usize,
    },
}

impl std::fmt::Display for PartitionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PartitionError::NoEventEntries => {
                write!(formatter, "partition: no event entries")
            }
            PartitionError::EntryNotOpcodeBoundary { name, mem_offset } => write!(
                formatter,
                "partition: event '{}' entry offset 0x{:x} is not an opcode boundary",
                name, mem_offset
            ),
            PartitionError::JumpToMidInstruction {
                from_offset,
                to_offset,
            } => write!(
                formatter,
                "partition: jump at 0x{:x} targets 0x{:x} which is not an opcode boundary",
                from_offset, to_offset
            ),
        }
    }
}

/// A resolved `EX_PUSH_EXECUTION_FLOW` -> `EX_POP_EXECUTION_FLOW` pairing.
///
/// Records the static correspondence the VM's execution flow stack
/// realises at runtime: the PUSH defers `fallthrough` (its continuation)
/// while running the gated body at `pushed_target`; the matching POP
/// (`pop_addr`) resumes that deferred continuation. All four fields are
/// disk offsets, homogeneous with `OpcodeGraph::successors`.
///
/// Frames are computed by `wire_pop_resume_edges` as a by-product of the
/// depth-tracked abstract interpretation that installs the
/// `pop -> fallthrough` resume edge, and are persisted here for the
/// flow-stack region-formation probe. They are NOT consumed by region
/// building or decode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FlowFrame {
    /// Disk offset of the `EX_PUSH_EXECUTION_FLOW` opcode.
    pub push_addr: usize,
    /// Disk offset of the matching depth-1 `EX_POP_EXECUTION_FLOW`.
    pub pop_addr: usize,
    /// The deferred continuation target the PUSH operand encodes (disk
    /// coords). This is the macro body's entry that runs before the POP.
    pub pushed_target: usize,
    /// The PUSH's fallthrough address, the continuation the matching POP
    /// resumes.
    pub fallthrough: usize,
}

/// Opcode boundary table and successor edges for the whole bytecode stream.
pub struct OpcodeGraph {
    /// Byte offsets of valid opcode starts.
    pub boundaries: BTreeSet<usize>,
    /// Control-flow edges: `successors[addr]` lists every address that may
    /// execute immediately after the opcode at `addr`.
    pub successors: BTreeMap<usize, Vec<usize>>,
    /// Opcode byte at each boundary, keyed by instruction start address
    /// (disk coords). Used by control-flow analyses that need to
    /// discriminate jumps from other terminators (e.g. back-edge
    /// detection) without re-reading the bytecode buffer.
    pub opcodes: BTreeMap<usize, u8>,
    /// Resolved PUSH->POP pairings, one per `EX_PUSH_EXECUTION_FLOW` whose
    /// matching depth-1 POP was found. Persisted from
    /// `wire_pop_resume_edges` for the flow-stack region probe; no
    /// production decode path reads it.
    pub flow_frames: Vec<FlowFrame>,
}

/// A loop scope, mapping a loop head address (the back-edge target) to
/// the highest exit address (`max(back_edge_pos + jump_size)` over all
/// back-edges into this head). The scope spans `[loop_head, loop_exit)`.
pub(crate) type LoopScopes = BTreeMap<usize, usize>;

/// Visitor that records control-flow successors for one opcode while the
/// generic walker advances `pos` past every operand.
///
/// Successors are populated only for opcodes the partitioner cares about:
/// `EX_Jump`, `EX_JumpIfNot`, `EX_PushExecutionFlow`, `EX_SwitchValue`,
/// `EX_Return`, `EX_EndOfScript`, `EX_PopExecutionFlow`. Any other
/// top-level opcode fills in a single linear fallthrough computed by the
/// `scan_one_opcode` wrapper.
///
/// `depth` distinguishes the outermost opcode from nested sub-expressions.
/// Only the outermost visit records successors; sub-expressions are walked
/// for their byte length only.
///
/// Operand-derived targets (the integer addresses encoded directly into
/// `EX_Jump`, `EX_JumpIfNot`, `EX_PushExecutionFlow`, and the `end_offset`
/// / `next_offset` fields of `EX_SwitchValue`) live in **memory** coordinates
/// at rest. The visitor translates them into **disk** coordinates immediately
/// using `mem_to_disk` so the recorded successor list is homogeneous with the
/// fallthrough address `scan_one_opcode` appends, which is already a disk
/// offset. Translating after the walk would corrupt fallthrough addresses
/// that happen to coincide with another opcode's memory address.
struct LengthVisitor<'a> {
    top_level_successors: Vec<usize>,
    /// Latent-call continuation targets harvested from `EX_SKIP_OFFSET_CONST`
    /// operands inside a `LatentActionInfo` struct argument. These are
    /// the bytecode addresses at which the VM resumes after a latent
    /// UFUNCTION call (Delay, MoveComponentTo, etc.) completes.
    ///
    /// Unlike regular control-flow successors, latent resume targets are
    /// NOT merged into the opcode graph's successor edges. The resume body
    /// is treated as an orphaned chunk (unreachable from the event
    /// entry), split into a separate `ResumeBlock`, and interleaved
    /// AFTER the latent call in display order: the targets are harvested
    /// here and exposed via
    /// [`build_opcode_graph_with_resume`] for downstream decode + emit,
    /// rather than corrupting BFS reachability with edges the runtime
    /// doesn't traverse synchronously.
    latent_resume_targets: Vec<usize>,
    depth: u32,
    mem_to_disk: &'a BTreeMap<usize, usize>,
}

impl<'a> LengthVisitor<'a> {
    fn new(mem_to_disk: &'a BTreeMap<usize, usize>) -> Self {
        Self {
            top_level_successors: Vec::new(),
            latent_resume_targets: Vec::new(),
            depth: 0,
            mem_to_disk,
        }
    }

    /// True when the visitor is currently inside the outermost opcode.
    /// `enter_opcode` increments depth before reaching the visit method,
    /// so depth == 1 at the top level.
    fn at_top_level(&self) -> bool {
        self.depth == 1
    }

    /// Translate a memory-coordinate operand target to a disk-coordinate
    /// successor address. Targets absent from the map pass through
    /// unchanged, which matches the synthetic-stream and UE4-uncooked
    /// case where mem and disk coincide.
    fn translate(&self, mem_target: usize) -> usize {
        self.mem_to_disk
            .get(&mem_target)
            .copied()
            .unwrap_or(mem_target)
    }
}

impl<'a> OpcodeVisitor for LengthVisitor<'a> {
    type Result = ();

    fn enter_opcode(&mut self, _opcode: u8, _start_offset: usize) {
        self.depth += 1;
    }

    fn exit_opcode(&mut self, _opcode: u8, _start_offset: usize) {
        self.depth = self.depth.saturating_sub(1);
    }

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) {}

    fn on_jump(&mut self, _opcode: u8, target: u32, _start_offset: usize) {
        if self.at_top_level() {
            self.top_level_successors = vec![self.translate(target as usize)];
        }
    }

    fn on_jump_if_not(&mut self, target: u32, _condition: (), _start_offset: usize) {
        if self.at_top_level() {
            // The fallthrough position is unknown until the walker returns;
            // record only the explicit target here. `scan_one_opcode`
            // appends the fallthrough after the walk completes.
            self.top_level_successors = vec![self.translate(target as usize)];
        }
    }

    fn on_push_execution_flow(&mut self, target: u32, _start_offset: usize) {
        if self.at_top_level() {
            self.top_level_successors = vec![self.translate(target as usize)];
        }
    }

    fn on_return(&mut self, _value: (), _start_offset: usize) {
        if self.at_top_level() {
            // Returns terminate linear flow; leave successors empty.
            self.top_level_successors.clear();
        }
    }

    fn on_switch_value(
        &mut self,
        end_offset: u32,
        _index: (),
        cases: Vec<SwitchValueCase<()>>,
        _default: (),
        _start_offset: usize,
    ) {
        if !self.at_top_level() {
            return;
        }
        // Targets list is `end_offset + per-case next_offset + fallthrough`.
        // `scan_one_opcode` appends the fallthrough after the walk completes.
        let mut targets: Vec<usize> = Vec::with_capacity(cases.len() + 1);
        targets.push(self.translate(end_offset as usize));
        for case in &cases {
            targets.push(self.translate(case.next_offset as usize));
        }
        self.top_level_successors = targets;
    }

    /// `EX_SKIP_OFFSET_CONST` carries the `Linkage` field of a
    /// `LatentActionInfo` struct passed to a latent UFUNCTION call (Delay,
    /// SetTimerByEvent, etc.). When valid, the operand is the bytecode
    /// memory address at which the VM resumes after the latent action
    /// completes, i.e. a real successor edge from the enclosing call.
    ///
    /// Recording the edge here lets plain BFS in
    /// `partition_ubergraph_with_translation` claim the latent
    /// continuation chain for the same event seed that owns the call site.
    /// Without it the chain ends at the `EX_POP_EXECUTION_FLOW` after the
    /// call and the resume bytes get tie-broken to a sibling event.
    ///
    /// Filters:
    /// - `Linkage == -1` (encoded as `0xFFFFFFFF` by the compiler when no
    ///   continuation is wired) is skipped.
    /// - A target of zero is skipped; the ubergraph never resumes at byte 0.
    /// - The translated address is recorded; out-of-bounds or
    ///   non-boundary targets are caught by the jump validator in
    ///   `partition_ubergraph_with_translation`.
    fn on_skip_offset_const(&mut self, target: u32, _start_offset: usize) {
        if target == u32::MAX || target == 0 {
            return;
        }
        self.latent_resume_targets
            .push(self.translate(target as usize));
    }
}

/// True for control-flow opcodes that already supply their full successor
/// list and do not need a linear fallthrough appended.
///
/// `EX_Jump` and `EX_Return` / `EX_EndOfScript` / `EX_PopExecutionFlow`
/// terminate linear flow; `EX_JumpIfNot`, `EX_PushExecutionFlow`, and
/// `EX_SwitchValue` do need a fallthrough appended after the walker
/// finishes consuming their operands.
fn opcode_skips_fallthrough(opcode: u8) -> bool {
    matches!(
        opcode,
        EX_JUMP | EX_RETURN | EX_END_OF_SCRIPT | EX_POP_EXECUTION_FLOW
    )
}

/// True for control-flow opcodes that have an explicit target plus a
/// linear fallthrough to append.
fn opcode_appends_fallthrough(opcode: u8) -> bool {
    matches!(
        opcode,
        EX_JUMP_IF_NOT | EX_PUSH_EXECUTION_FLOW | EX_SWITCH_VALUE
    )
}

/// Result of scanning one opcode: its successor addresses and any
/// latent-call resume targets harvested from the operand stream.
///
/// `successors` are real control-flow edges the runtime traverses
/// synchronously: jump targets, conditional fallthroughs, switch case
/// offsets, the linear fallthrough of a non-branching opcode. The
/// opcode graph wires these directly into `successors[addr]`.
///
/// `latent_resume_targets` are async-resume targets harvested from
/// `EX_SKIP_OFFSET_CONST` operands inside `LatentActionInfo` struct
/// arguments. The runtime does NOT traverse these synchronously, the
/// latent action returns to the caller via the flow-execution stack and
/// the VM resumes the body separately when the action signals
/// completion. Modelling them as graph edges (the original design)
/// caused per-event BFS to claim resume bytes for the calling event,
/// rendering post-resume code inline before the actual then-arm. The
/// decoder now treats resume targets as orphans, downstream decode + emit
/// interleaves the resume body AFTER the latent call.
pub(crate) struct OpcodeScan {
    pub successors: Vec<usize>,
    pub latent_resume_targets: Vec<usize>,
}

/// Scan one opcode at `pos`, advance `pos` past it, and return its
/// real successor addresses plus any harvested latent-resume targets.
///
/// The walker drives a [`LengthVisitor`] that captures successors for
/// the branching opcodes (`EX_Jump`, `EX_JumpIfNot`,
/// `EX_PushExecutionFlow`, `EX_SwitchValue`) plus the terminators
/// (`EX_Return`, `EX_EndOfScript`, `EX_PopExecutionFlow`). Every other
/// opcode produces a single linear fallthrough computed from `pos`
/// after the walk completes.
///
/// `mem_to_disk` translates operand-derived targets (jump destinations,
/// switch case offsets) from memory to disk coordinates as the visitor
/// reads them. The fallthrough address appended below is always a disk
/// offset and is left untranslated. Pass an empty map for synthetic
/// streams or UE4-uncooked assets where the two coordinate spaces coincide.
pub(crate) fn scan_one_opcode_full(view: &BytecodeView, pos: &mut usize) -> OpcodeScan {
    let bytecode = view.bytecode;
    let start = *pos;
    if start >= bytecode.len() {
        return OpcodeScan {
            successors: vec![],
            latent_resume_targets: vec![],
        };
    }

    let opcode_byte = bytecode[start];
    let ctx = WalkCtx::new(bytecode, view.name_table, view.ue5);
    let mut visitor = LengthVisitor::new(view.mem_to_disk);
    walk_opcode(&ctx, pos, &mut visitor);

    if *pos == start {
        // Walker stalled on an unrecognised opcode; advance one byte to
        // prevent infinite loops at the caller.
        *pos = start + 1;
    }

    let latent_resume_targets = visitor.latent_resume_targets;

    let successors = if opcode_skips_fallthrough(opcode_byte) {
        visitor.top_level_successors
    } else if opcode_appends_fallthrough(opcode_byte) {
        let fallthrough = *pos;
        let mut successors = visitor.top_level_successors;
        successors.push(fallthrough);
        successors
    } else {
        // All other opcodes: linear fallthrough only.
        let fallthrough = *pos;
        let mut successors: Vec<usize> = Vec::new();
        if fallthrough < bytecode.len() {
            successors.push(fallthrough);
        }
        successors
    };

    OpcodeScan {
        successors,
        latent_resume_targets,
    }
}

/// Thin wrapper around [`scan_one_opcode_full`] that returns only the
/// real control-flow successors. Latent-resume targets are dropped at
/// the boundary, callers that need them use
/// [`scan_one_opcode_full`] directly.
pub(crate) fn scan_one_opcode(
    bytecode: &[u8],
    pos: &mut usize,
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> Vec<usize> {
    let view = BytecodeView {
        bytecode,
        name_table,
        ue5,
        mem_to_disk,
    };
    scan_one_opcode_full(&view, pos).successors
}

/// Byte length of the opcode at `offset`, measured by [`scan_one_opcode`].
///
/// Length scanning is independent of jump-target translation, so an empty
/// `mem_to_disk` map is supplied to [`scan_one_opcode`].
pub(crate) fn opcode_length_at(
    offset: usize,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> usize {
    let mut pos = offset;
    let empty_translation: BTreeMap<usize, usize> = BTreeMap::new();
    scan_one_opcode(bytecode, &mut pos, ue5, name_table, &empty_translation);
    pos.saturating_sub(offset).max(1)
}

/// Advance `pos` past one complete expression without recording successors.
///
/// Thin wrapper around [`walk_opcode`] used by callers that only need the
/// length-scanning behaviour without the control-flow target extraction
/// `scan_one_opcode` provides. Returns `true` when at least one byte was
/// consumed; returns `false` on EOF.
pub(crate) fn advance_expr(
    bytecode: &[u8],
    pos: &mut usize,
    ue5: i32,
    name_table: &NameTable,
) -> bool {
    if *pos >= bytecode.len() {
        return false;
    }
    let start = *pos;
    let ctx = WalkCtx::new(bytecode, name_table, ue5);
    let empty_translation: BTreeMap<usize, usize> = BTreeMap::new();
    let mut visitor = LengthVisitor::new(&empty_translation);
    walk_opcode(&ctx, pos, &mut visitor);
    if *pos == start {
        *pos = start + 1;
    }
    true
}

/// Walk the whole bytecode once and build the opcode boundary table plus
/// successor edge map. Successor edges are emitted in **disk** coordinates,
/// so `mem_to_disk` is plumbed into the per-opcode scan rather than applied
/// as a post-pass.
pub(crate) fn build_opcode_graph(
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> OpcodeGraph {
    build_opcode_graph_with_resume(bytecode, ue5, name_table, mem_to_disk).0
}

/// Like [`build_opcode_graph`] but also returns the latent-call resume
/// targets harvested from `EX_SKIP_OFFSET_CONST` operands.
///
/// The returned map is keyed by the call opcode's disk offset (the
/// `Stmt::Call.offset` the decoder will later carry) and maps to the
/// resume target's disk offset. Multiple latent calls in the same event
/// each get their own entry, the inline-emit pass uses the call offset
/// as the lookup key when interleaving the resume body.
pub(crate) fn build_opcode_graph_with_resume(
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
    mem_to_disk: &BTreeMap<usize, usize>,
) -> (OpcodeGraph, BTreeMap<usize, usize>) {
    let mut boundaries: BTreeSet<usize> = BTreeSet::new();
    let mut successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut opcodes: BTreeMap<usize, u8> = BTreeMap::new();
    let mut latent_resumes: BTreeMap<usize, usize> = BTreeMap::new();
    let mut pos = 0;
    let view = BytecodeView {
        bytecode,
        name_table,
        ue5,
        mem_to_disk,
    };

    while pos < bytecode.len() {
        let opcode_start = pos;
        boundaries.insert(opcode_start);
        opcodes.insert(opcode_start, bytecode[opcode_start]);
        let scan = scan_one_opcode_full(&view, &mut pos);
        successors.insert(opcode_start, scan.successors);
        // A latent call carries at most one resume target, but
        // defensively record the first non-conflicting one. Conflicting
        // entries (same call offset, different resume target) would
        // indicate a malformed `LatentActionInfo` and are skipped.
        if let Some(&first) = scan.latent_resume_targets.first() {
            latent_resumes.entry(opcode_start).or_insert(first);
        }
        if pos == opcode_start {
            // Failsafe: scan_one_opcode_full must always advance.
            break;
        }
    }

    let mut graph = OpcodeGraph {
        boundaries,
        successors,
        opcodes,
        flow_frames: Vec::new(),
    };
    let flow_frames = wire_pop_resume_edges(&mut graph);
    graph.flow_frames = flow_frames;
    (graph, latent_resumes)
}

/// Walk every `EX_PUSH_EXECUTION_FLOW` site and add a successor edge
/// from each paired `EX_POP_EXECUTION_FLOW` to the push's fallthrough.
///
/// Without this pass, POP-terminated blocks have empty successor lists
/// in the opcode graph (POP is in `opcode_skips_fallthrough`), so the
/// CFG construction sees them as leaves connected only to the synthetic
/// sink. That makes every SESE region whose body terminates with a POP
/// post-dominated by the sink, collapsing all arm-extent semantics.
///
/// Pairing uses a stack-aware DFS from each PUSH's pushed_target with
/// depth=1; each PUSH encountered increments depth; POP at depth=1 is
/// paired with the originating PUSH (add edge POP -> push.fallthrough);
/// POP at depth>1 belongs to a nested PUSH and is handled by that
/// PUSH's own iteration.
///
/// Counterpart to the latent-call resume edges installed by
/// `scan_one_opcode` for `LatentActionInfo` arguments.
///
/// Returns the resolved [`FlowFrame`] pairings (one per push/matching-pop
/// pair) as a by-product. The installed edges are unchanged by this; the
/// frames are purely additional output the caller persists on the graph
/// for the flow-stack region probe.
fn wire_pop_resume_edges(graph: &mut OpcodeGraph) -> Vec<FlowFrame> {
    let push_addrs: Vec<usize> = graph
        .opcodes
        .iter()
        .filter(|(_, &opcode)| opcode == EX_PUSH_EXECUTION_FLOW)
        .map(|(&addr, _)| addr)
        .collect();

    let mut new_edges: BTreeSet<(usize, usize)> = BTreeSet::new();
    let mut frames: Vec<FlowFrame> = Vec::new();

    for push_addr in push_addrs {
        let push_succs = graph
            .successors
            .get(&push_addr)
            .cloned()
            .unwrap_or_default();
        // PUSH successors are [pushed_target, fallthrough].
        let pushed_target = match push_succs.first() {
            Some(&addr) => addr,
            None => continue,
        };
        let fallthrough = match push_succs.get(1) {
            Some(&addr) => addr,
            None => continue,
        };

        // DFS from pushed_target, tracking simulated stack depth. The
        // (addr, depth) visited set keeps the walk finite when a body
        // loops without crossing a PUSH; the depth distinguishes a POP
        // that pairs with THIS push (depth=1) from POPs that pair with
        // nested pushes. A depth cap prevents unbounded growth when a
        // cycle passes through a PUSH (each lap would otherwise generate
        // a fresh (addr, depth) pair forever).
        const MAX_DEPTH: usize = 64;
        let mut visited: BTreeSet<(usize, usize)> = BTreeSet::new();
        // Depth-1 POPs paired with this push, deduped so a body that
        // reaches the same POP via two paths records one frame.
        let mut matched_pops: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<(usize, usize)> = vec![(pushed_target, 1)];
        while let Some((addr, depth)) = stack.pop() {
            if depth > MAX_DEPTH {
                continue;
            }
            if !visited.insert((addr, depth)) {
                continue;
            }
            let opcode = graph.opcodes.get(&addr).copied();

            if opcode == Some(EX_POP_EXECUTION_FLOW) {
                if depth == 1 {
                    new_edges.insert((addr, fallthrough));
                    matched_pops.insert(addr);
                }
                continue;
            }

            let next_depth = if opcode == Some(EX_PUSH_EXECUTION_FLOW) {
                depth + 1
            } else {
                depth
            };

            if let Some(succs) = graph.successors.get(&addr) {
                for &next in succs {
                    stack.push((next, next_depth));
                }
            }
        }

        for pop_addr in matched_pops {
            frames.push(FlowFrame {
                push_addr,
                pop_addr,
                pushed_target,
                fallthrough,
            });
        }
    }

    for (pop_addr, target) in new_edges {
        let entry = graph.successors.entry(pop_addr).or_default();
        if !entry.contains(&target) {
            entry.push(target);
        }
    }

    frames
}

/// BFS from `start` through the successor graph; returns all reachable addresses.
pub(crate) fn bfs_reachable(start: usize, graph: &OpcodeGraph) -> BTreeSet<usize> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(start);
    while let Some(addr) = queue.pop_front() {
        if !visited.insert(addr) {
            continue;
        }
        if let Some(targets) = graph.successors.get(&addr) {
            for &target in targets {
                if !visited.contains(&target) {
                    queue.push_back(target);
                }
            }
        }
    }
    visited
}

/// Detect all back-edges in `owner_range` and collapse them into a
/// LoopScopes map keyed by loop head.
///
/// A back-edge is an `EX_JUMP target` or `EX_JUMP_IF_NOT target` opcode
/// in `owner_range` where `target < instr_pos`. The target is the loop
/// head (the smallest address that's a back-edge target is the canonical
/// loop entry). Multiple back-edges to the same head collapse into one
/// scope whose exit is the max of `(back_edge_pos + jump_instr_size)`,
/// modelling tail-merged loops or `continue` paths uniformly.
///
/// Operates on disk addresses (the same coordinate space `OpcodeGraph`
/// uses). Forward jumps and break-out jumps (`EX_JUMP` with target past
/// the loop's exit) are NOT recorded; only true back-edges.
///
/// Range filter: a back-edge whose `instr_pos` is outside `owner_range`
/// is skipped, and a back-edge whose target lands outside `owner_range`
/// is also skipped (the loop head is outside the range we're partitioning).
///
/// Used by [`bfs_reachable_with_scope`] to bound propagation: a sibling
/// partition's BFS that arrives at a back-edge target via a forward
/// edge is fine; one that arrives at the same target via the back-edge
/// itself (i.e. by following the JUMP that constitutes the back-edge)
/// is walking out of the loop scope and should be rejected.
pub(crate) fn back_edges_in_range(graph: &OpcodeGraph, owner_range: Range<usize>) -> LoopScopes {
    let mut scopes: LoopScopes = BTreeMap::new();
    for (&instr_pos, &opcode) in &graph.opcodes {
        if !owner_range.contains(&instr_pos) {
            continue;
        }
        if opcode != EX_JUMP && opcode != EX_JUMP_IF_NOT {
            continue;
        }
        let Some(targets) = graph.successors.get(&instr_pos) else {
            continue;
        };
        // EX_JUMP has one successor (target). EX_JUMP_IF_NOT has two
        // (target, fallthrough); the explicit target is appended first
        // by the visitor, so `successors[0]` is the operand-derived
        // target in both cases.
        let Some(&target) = targets.first() else {
            continue;
        };
        if target >= instr_pos {
            continue;
        }
        if !owner_range.contains(&target) {
            continue;
        }
        // Instruction size: distance to the next boundary in the graph.
        // For a non-terminal jump this equals (instr_pos + jump_size).
        // For a terminator at the very end of the buffer, no next
        // boundary exists; that case can't form a back-edge that matters
        // for partitioning, so skip it.
        let Some(&next_boundary) = graph.boundaries.range((instr_pos + 1)..).next() else {
            continue;
        };
        let exit = next_boundary;
        scopes
            .entry(target)
            .and_modify(|existing| {
                if exit > *existing {
                    *existing = exit;
                }
            })
            .or_insert(exit);
    }
    scopes
}

/// Stack-tracking, scope-aware BFS. Models the VM's flow-execution stack
/// so a pin body BFS terminates when its continuation pops, instead of
/// leaking into the chain's sibling pin territory, and additionally
/// bounds propagation by loop scopes so a sibling partition's BFS that
/// would otherwise walk into a loop via its back-edge is rejected.
///
/// State per queue entry is `(addr, stack)` where `stack` lists pending
/// flow-execution-stack continuations (top of stack = `stack.last()`).
/// `EX_PUSH_EXECUTION_FLOW` pushes its operand and follows fallthrough;
/// `EX_POP_EXECUTION_FLOW` pops the top continuation and resumes there;
/// `EX_POP_FLOW_IF_NOT` branches both fallthrough (stack unchanged) and
/// pop. When `stack.len()` would drop below `baseline_depth`, the pop is
/// skipped and that branch terminates, which is how the BFS bounds a pin
/// body at its own continuation.
///
/// Visited keying is `(addr, stack_depth, stack_top)` so paths with the
/// same caller frame collapse. Exact stack tracking would be unbounded
/// across PUSH/POP cycles; the coarser key is sufficient because it
/// still distinguishes "pin body before its own pop" from "post-pop
/// chain territory" (different `stack_top`s).
///
/// When BFS encounters a successor edge `(addr, succ)` where
/// `(addr, succ)` is the back-edge of a loop scope `[head, exit)`:
///   - if `seed` is inside `[head, exit)`: admit `succ` (BFS legitimately
///     traverses the back-edge to reach the loop head from inside the
///     loop body, same as today's BFS).
///   - if `seed` is outside `[head, exit)`: reject `succ`. A sibling
///     partition's BFS that would walk into the loop scope via the
///     back-edge is a category error; the loop's bytes belong to the
///     partition that legitimately enters the loop via the forward
///     entry edge, not via the back-edge.
///
/// Forward edges and break-out edges (a forward `EX_JUMP` from inside
/// the loop to past `loop_exit`) propagate normally regardless of seed
/// position.
///
/// Back-edge detection at runtime: for an edge `(addr, succ)`, treat it
/// as a back-edge iff `succ < addr` AND `succ` is a registered loop head
/// in `scopes`. The opcode at `addr` does not need re-checking because
/// `back_edges_in_range` already filtered for `EX_JUMP` / `EX_JUMP_IF_NOT`
/// when populating the scopes map; if `succ` is a scope key, the edge
/// that produced it must have been a back-edge.
///
/// Seed-on-head edge case: a seed at `head` is treated as inside
/// `[head, exit)` (standard half-open interval).
///
/// `boundary` clips reachable addresses: addresses outside `boundary`
/// are not enqueued and not added to the result. The boundary filter
/// is folded directly into the BFS rather than applied post-hoc.
///
/// Opcode dispatch reads `graph.opcodes` rather than the raw bytecode
/// buffer (the caller passes only `graph` and `boundary`).
///
/// `scopes` is computed once per owner range via [`back_edges_in_range`]
/// and shared across multiple BFS invocations.
///
/// `chain_head_floor` is the optional hard FLOOR a Sequence-chain inline
/// pin uses to bound its own BFS. When `Some(floor)`, any successor edge
/// `(addr, succ)` with `succ < floor` is rejected at admission, BEFORE the
/// back-edge gate, regardless of edge mechanism (back-edge, forward jump,
/// `EX_POP_EXECUTION_FLOW` resume, switch case offset). This subsumes the
/// scope-aware back-edge gate for the inline-pin use case: the inline pin
/// of an interleaved Sequence chain seeded at `T_{N-1}` can otherwise
/// escape below `chain_head` via several mechanisms; the floor closes
/// every path uniformly. Pass `None` for any seed that legitimately may
/// reach pre-chain bytes (event entries, non-inline pins).
///
/// `arm_boundaries` lists tail-JIN displaced-arm ranges within the
/// owning event. When non-empty, every successor admission must
/// preserve the seed's arm membership: an edge from inside arm A to
/// outside A (or vice-versa) is rejected. A seed that sits inside arm
/// A may only reach addresses within A; a seed outside every arm may
/// only reach addresses outside every arm. Without this, a chain whose
/// head sits outside an arm could partition into the arm via reverse
/// edges (arm-internal POP resumes pointing at the chain's pin
/// continuation), and a chain inside an arm could partition outward
/// across the arm-head's tracepoint padding into sibling event
/// territory. Pass `&[]` to disable.
pub(crate) fn bfs_reachable_with_scope(
    seed: usize,
    initial_stack: Vec<usize>,
    baseline_depth: usize,
    ctx: &PartitionCtx<'_>,
    boundary: Range<usize>,
    scopes: &LoopScopes,
    chain_head_floor: Option<usize>,
) -> BTreeSet<usize> {
    let graph = ctx.graph;
    let arm_boundaries = ctx.arm_boundaries;
    // Decide once: is the seed inside any loop scope's `[head, exit)`?
    // Used at every successor admission to gate back-edge propagation.
    let seed_inside_scope = |head: usize, exit: usize| seed >= head && seed < exit;

    // Returns true if edge (addr -> succ) is a back-edge that should be
    // rejected for this seed. A back-edge is one where `succ < addr` and
    // `succ` is a registered loop head; the scope is `[succ, scopes[succ])`.
    let reject_back_edge = |addr: usize, succ: usize| -> bool {
        if succ >= addr {
            return false;
        }
        let Some(&exit) = scopes.get(&succ) else {
            return false;
        };
        // Sanity: only treat as a back-edge if the originating addr is
        // inside the scope. (back_edges_in_range guarantees this when
        // building scopes from a range, but checking here keeps the
        // gate self-consistent if a caller passes a scopes map built
        // from a wider range.)
        if addr < succ || addr >= exit {
            return false;
        }
        !seed_inside_scope(succ, exit)
    };

    // Decide once: which arm (if any) does `seed` belong to? `None` here
    // means the seed sits outside every arm; `Some(idx)` indexes into
    // `arm_boundaries`. The admit check below uses this to enforce arm
    // membership: the seed can only reach addresses in the same arm
    // bucket as itself.
    let containing_arm_index = |addr: usize| -> Option<usize> {
        arm_boundaries
            .iter()
            .position(|range| range.contains(&addr))
    };
    let seed_arm = containing_arm_index(seed);

    // Push a successor onto the queue if it's within `boundary`, above the
    // optional `chain_head_floor`, on the seed's arm side of every arm
    // boundary, and not a rejected back-edge from `addr`. The floor check
    // runs FIRST: any successor below the chain head is rejected
    // regardless of the edge mechanism that produced it.
    let admit =
        |addr: usize, succ: usize, stack: &[usize], queue: &mut VecDeque<(usize, Vec<usize>)>| {
            if !boundary.contains(&succ) {
                return;
            }
            if let Some(floor) = chain_head_floor {
                if succ < floor {
                    return;
                }
            }
            if !arm_boundaries.is_empty() && containing_arm_index(succ) != seed_arm {
                return;
            }
            if reject_back_edge(addr, succ) {
                return;
            }
            queue.push_back((succ, stack.to_vec()));
        };

    let mut reached: BTreeSet<usize> = BTreeSet::new();
    let mut visited: BTreeSet<(usize, usize, Option<usize>)> = BTreeSet::new();
    let mut queue: VecDeque<(usize, Vec<usize>)> = VecDeque::new();
    if boundary.contains(&seed) {
        queue.push_back((seed, initial_stack));
    }

    while let Some((addr, stack)) = queue.pop_front() {
        let key = (addr, stack.len(), stack.last().copied());
        if !visited.insert(key) {
            continue;
        }
        reached.insert(addr);
        let Some(&opcode) = graph.opcodes.get(&addr) else {
            continue;
        };

        step_successors(
            addr,
            opcode,
            &stack,
            graph,
            baseline_depth,
            &admit,
            &mut queue,
        );
    }

    reached
}

/// Simulate the flow-stack effect of one opcode and admit its successors,
/// dispatching across PUSH/POP/POP_IF_NOT and a graph-successor default.
///
/// `admit` carries the boundary, floor, arm, and back-edge gates; this
/// helper only models the stack: PUSH records the pushed target and follows
/// the fallthrough, POP returns to the stack top (unless that drops below
/// `baseline_depth`, which lands in sibling territory), POP_IF_NOT follows
/// the fallthrough and additionally the conditional pop, and every other
/// opcode follows graph successors with the stack unchanged.
#[allow(clippy::too_many_arguments)]
fn step_successors(
    addr: usize,
    opcode: u8,
    stack: &[usize],
    graph: &OpcodeGraph,
    baseline_depth: usize,
    admit: &impl Fn(usize, usize, &[usize], &mut VecDeque<(usize, Vec<usize>)>),
    queue: &mut VecDeque<(usize, Vec<usize>)>,
) {
    if opcode == EX_PUSH_EXECUTION_FLOW {
        if let Some(succs) = graph.successors.get(&addr) {
            // Successors of PUSH are [pushed_target, fallthrough].
            // Track the pushed target on the simulated stack and
            // follow only the fallthrough through the graph.
            if let Some(&pushed_target) = succs.first() {
                let mut new_stack = stack.to_vec();
                new_stack.push(pushed_target);
                for &succ in succs {
                    if succ == pushed_target {
                        continue;
                    }
                    admit(addr, succ, &new_stack, queue);
                }
            }
        }
        return;
    }

    if opcode == EX_POP_EXECUTION_FLOW {
        if stack.is_empty() {
            return;
        }
        let new_depth = stack.len() - 1;
        if new_depth < baseline_depth {
            // Popping below baseline lands in sibling territory.
            return;
        }
        let mut new_stack = stack.to_vec();
        let popped = new_stack.pop().expect("non-empty by check above");
        admit(addr, popped, &new_stack, queue);
        return;
    }

    if opcode == EX_POP_FLOW_IF_NOT {
        // Fallthrough always permitted (stack unchanged). The
        // graph's successor list for this opcode is just the
        // fallthrough; the conditional pop is added below.
        if let Some(succs) = graph.successors.get(&addr) {
            for &succ in succs {
                admit(addr, succ, stack, queue);
            }
        }
        if stack.len() > baseline_depth {
            let mut new_stack = stack.to_vec();
            let popped = new_stack.pop().expect("non-empty");
            admit(addr, popped, &new_stack, queue);
        }
        return;
    }

    // Default: follow graph successors with stack unchanged.
    if let Some(succs) = graph.successors.get(&addr) {
        for &succ in succs {
            admit(addr, succ, stack, queue);
        }
    }
}

/// One pin's BFS seed for [`partition_seeds_with_stack`].
///
/// `seed` is the body head address (disk coords). `initial_stack` is the
/// flow-execution stack the pin starts with, modelling the chain's
/// pending continuations: a pin reached via PUSH(cont)+JUMP(body) starts
/// with `[cont]`. The inline body that runs after every other pin pops
/// starts with an empty stack.
///
/// `is_inline_pin` flags a Sequence chain's inline-pin seed (the last
/// pin to execute, after every pushed continuation has popped). When
/// true, [`partition_seeds_with_stack`] passes the chain's `head` as a
/// hard floor to scope-aware BFS, rejecting any successor below `head`
/// regardless of edge mechanism. Non-inline seeds (event entries, pushed
/// pin bodies) leave this `false`.
pub(crate) struct StackSeed {
    pub seed: usize,
    pub initial_stack: Vec<usize>,
    pub is_inline_pin: bool,
}

/// Stack-aware partition. Each pin's BFS uses the supplied initial
/// stack so popping its own continuation terminates the pin's reach
/// instead of bleeding into the chain's sibling pins.
///
/// Addresses outside `boundary` are dropped from each seed's reachable
/// set, so a pin body can't bleed into bytes belonging to another event
/// or past the enclosing construct's `range_end`. The seed at the
/// lowest index wins shared addresses, mirroring the lowest-offset
/// tie-break the top-level partition uses, but indexed by seed position
/// rather than offset value so callers (Sequence pin recognition) keep
/// their pin order intact.
///
/// `chain_head` is the disk offset of the owning Sequence chain's PUSH
/// head. Threaded into scope-aware BFS as the chain-head FLOOR for
/// inline-pin seeds (`StackSeed::is_inline_pin == true`): every successor
/// below `chain_head` is rejected regardless of edge mechanism, which
/// uniformly closes the back-edge / forward-jump / POP / switch-case
/// escape paths an inline-pin BFS could otherwise take below the chain.
/// Non-inline seeds receive `None` as the floor.
///
/// Loop scopes are computed once via [`back_edges_in_range`] over the
/// partition boundary and shared across seeds.
///
/// Returns one `Vec<Range<usize>>` per seed, in the order seeds were
/// supplied. Empty Vecs are returned for seeds whose owned set ends up
/// empty after the tie-break.
pub(crate) fn partition_seeds_with_stack(
    bytecode: &[u8],
    seeds: &[StackSeed],
    ctx: &PartitionCtx<'_>,
    boundary: Range<usize>,
    ue5: i32,
    name_table: &NameTable,
    chain_head: usize,
) -> Vec<Vec<Range<usize>>> {
    let baseline_depth = 0usize;
    let scopes = back_edges_in_range(ctx.graph, boundary.clone());

    let seed_reachable: Vec<BTreeSet<usize>> = seeds
        .iter()
        .map(|stack_seed| {
            let floor = if stack_seed.is_inline_pin {
                Some(chain_head)
            } else {
                None
            };
            bfs_reachable_with_scope(
                stack_seed.seed,
                stack_seed.initial_stack.clone(),
                stack_seed.initial_stack.len().max(baseline_depth),
                ctx,
                boundary.clone(),
                &scopes,
                floor,
            )
        })
        .collect();

    let mut owner: BTreeMap<usize, usize> = BTreeMap::new();
    for (seed_idx, reachable) in seed_reachable.iter().enumerate() {
        for &addr in reachable {
            owner.entry(addr).or_insert(seed_idx);
        }
    }

    collect_owned_ranges(seeds.len(), &owner, bytecode, ue5, name_table)
}

/// Convert the address-to-owner map into one `Vec<Range<usize>>` per
/// seed, parallel to seed order. Empty seeds get an empty Vec.
fn collect_owned_ranges(
    seed_count: usize,
    owner: &BTreeMap<usize, usize>,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> Vec<Vec<Range<usize>>> {
    (0..seed_count)
        .map(|seed_idx| {
            let mut owned: Vec<usize> = owner
                .iter()
                .filter_map(|(&addr, &owner_idx)| {
                    if owner_idx == seed_idx {
                        Some(addr)
                    } else {
                        None
                    }
                })
                .collect();
            owned.sort_unstable();
            if owned.is_empty() {
                Vec::new()
            } else {
                addresses_to_ranges(&owned, bytecode, ue5, name_table)
            }
        })
        .collect()
}

/// Convert a sorted list of owned byte addresses into contiguous `Range<usize>`
/// spans. Addresses that are exactly one opcode apart merge into one span;
/// gaps (where an opcode belongs to a different event) produce separate ranges.
pub(crate) fn addresses_to_ranges(
    owned: &[usize],
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> Vec<Range<usize>> {
    debug_assert!(!owned.is_empty());
    let mut ranges: Vec<Range<usize>> = Vec::new();
    let mut span_start = owned[0];
    let mut prev = owned[0];

    for &addr in &owned[1..] {
        let prev_len = opcode_length_at(prev, bytecode, ue5, name_table);
        if addr == prev + prev_len {
            prev = addr;
        } else {
            ranges.push(span_start..prev + prev_len);
            span_start = addr;
            prev = addr;
        }
    }
    let last_len = opcode_length_at(prev, bytecode, ue5, name_table);
    ranges.push(span_start..prev + last_len);
    ranges
}

/// Output of [`partition_ubergraph_with_translation`].
///
/// `event_ranges` is the per-event byte-range partition the decoder
/// consumes for normal control-flow recovery.
///
/// `resume_blocks` maps each latent call's disk offset (the
/// `Stmt::Call.offset` the decoder later carries) to the byte range
/// covering the resume continuation. These ranges are NOT included in
/// `event_ranges`, the resume body is decoded separately and the
/// emitter interleaves it after the matching latent call.
pub struct PartitionOutput {
    pub event_ranges: BTreeMap<String, Vec<Range<usize>>>,
    pub resume_blocks: BTreeMap<usize, Range<usize>>,
}

/// Partition ubergraph bytecode into per-event byte ranges.
///
/// Performs five steps:
/// 1. Validate that every jump target is an opcode boundary.
/// 2. Validate that every event entry offset is an opcode boundary.
/// 3. BFS from each event entry to collect its reachable address set.
/// 4. Assign each address to exactly one event (lowest `mem_offset` wins).
/// 5. Convert per-event owned addresses to contiguous `Range<usize>` spans.
///
/// `name_table` is consulted by the length scanner for FName reads.
///
/// `graph` and `latent_resumes` are built once by the caller via
/// [`build_opcode_graph_with_resume`] and shared across the whole ubergraph
/// decode. The graph's successor edges (jump/conditional/push targets,
/// switch case offsets) are already in disk coordinates: the memory-to-disk
/// translation happened inside the per-opcode scan when the graph was built,
/// so they align with the disk-coordinate boundary set the partitioner
/// reads. `latent_resumes` maps each latent call's disk offset to its
/// resume target, harvested by the same build.
///
/// Returns a [`PartitionOutput`] carrying both the per-event byte
/// ranges and the latent-call resume chunks (orphan continuations of
/// `Delay` / `MoveComponentTo` / similar UFUNCTIONs). Callers that only
/// need the events use [`PartitionOutput::event_ranges`].
pub fn partition_ubergraph_with_translation(
    bytecode: &[u8],
    event_entries: &[EventEntry],
    name_table: &NameTable,
    ue5: i32,
    graph: &OpcodeGraph,
    latent_resumes: &BTreeMap<usize, usize>,
    pin_attribution: Option<&crate::bytecode::pin_attribution::PinEventAttribution>,
) -> Result<PartitionOutput, PartitionError> {
    // The opcode graph and latent-call resume targets are built once by
    // the caller (`build_opcode_graph_with_resume`) and shared across the
    // whole ubergraph decode. Operand-derived successor targets were
    // translated to disk coordinates inside the per-opcode scan; the
    // fallthrough address appended is already a disk offset. Latent resume
    // targets are NOT wired as graph edges, so BFS leaves the resume bytes
    // unowned, the decoder picks them up via `resume_blocks` and
    // interleaves them at emit time.

    // Validate that every jump target is an opcode boundary. This also
    // catches the regression class fixed by translating at scan time:
    // any successor address that slipped through unmapped would land
    // mid-instruction here.
    for (&from_offset, targets) in &graph.successors {
        for &to_offset in targets {
            if !graph.boundaries.contains(&to_offset) {
                return Err(PartitionError::JumpToMidInstruction {
                    from_offset,
                    to_offset,
                });
            }
        }
    }

    // Validate event entries.
    if event_entries.is_empty() {
        return Err(PartitionError::NoEventEntries);
    }
    for entry in event_entries {
        if !graph.boundaries.contains(&entry.mem_offset) {
            return Err(PartitionError::EntryNotOpcodeBoundary {
                name: entry.name.clone(),
                mem_offset: entry.mem_offset,
            });
        }
    }

    // Sort entries ascending by mem_offset, then BFS each entry. The
    // ascending order pins the tie-break below: shared opcodes go to the
    // lowest-offset event.
    let mut sorted_entries: Vec<&EventEntry> = event_entries.iter().collect();
    sorted_entries.sort_by_key(|entry| entry.mem_offset);

    let event_reachable: Vec<BTreeSet<usize>> = sorted_entries
        .iter()
        .map(|entry| bfs_reachable(entry.mem_offset, graph))
        .collect();

    // Pin-attribution probe. For every address reachable from
    // more than one event seed, log when the lowest-offset opcode-BFS
    // tie-break disagrees with the pin-BFS event set. Probe only, no
    // override applied.
    if let Some(attribution) = pin_attribution {
        log_pin_attribution_divergences(&sorted_entries, &event_reachable, attribution);
    }

    // Assign each address to exactly one event. `or_insert` means
    // the first (lowest-offset) claimant wins.
    let mut owner: BTreeMap<usize, usize> = BTreeMap::new();
    for (event_idx, reachable) in event_reachable.iter().enumerate() {
        for &addr in reachable {
            owner.entry(addr).or_insert(event_idx);
        }
    }

    // Build per-event range spans.
    let mut event_ranges: BTreeMap<String, Vec<Range<usize>>> = BTreeMap::new();
    for (event_idx, entry) in sorted_entries.iter().enumerate() {
        let mut owned: Vec<usize> = owner
            .iter()
            .filter_map(|(&addr, &ev)| if ev == event_idx { Some(addr) } else { None })
            .collect();
        owned.sort_unstable();

        if owned.is_empty() {
            eprintln!(
                "partition: skipping empty event '{}' (no owned opcodes)",
                entry.name
            );
            continue;
        }

        let ranges = addresses_to_ranges(&owned, bytecode, ue5, name_table);
        event_ranges.insert(entry.name.clone(), ranges);
    }

    // Compute per-latent-call resume chunks. Each chunk is the byte
    // range covering the resume continuation, BFS'd from the target
    // through the same opcode graph and bounded by addresses already
    // claimed by an event partition. Because we no longer wire latent
    // edges into the graph, the resume target is naturally orphaned
    // and BFS terminates cleanly at the next event-owned address or at
    // a flow terminator (POP/RET/EOS).
    let resume_blocks =
        compute_resume_blocks(latent_resumes, graph, &owner, bytecode, ue5, name_table);

    Ok(PartitionOutput {
        event_ranges,
        resume_blocks,
    })
}

/// Compute the byte range covering each latent-call resume continuation.
///
/// `latent_resumes` maps each latent call's disk offset to its resume
/// target address. For each call/target pair, BFS through the opcode
/// graph from the target, stopping at addresses already owned by an
/// event partition (the orphan continuation lives in the gap between
/// the latent call and the next event-owned region). The reachable set
/// is converted into a single span covering the contiguous region; if
/// the reach is non-contiguous (one resume body links forward into
/// another), the span clips to the LOWEST contiguous block so two
/// adjacent resume chunks don't bleed into each other.
fn compute_resume_blocks(
    latent_resumes: &BTreeMap<usize, usize>,
    graph: &OpcodeGraph,
    event_owner: &BTreeMap<usize, usize>,
    bytecode: &[u8],
    ue5: i32,
    name_table: &NameTable,
) -> BTreeMap<usize, Range<usize>> {
    // Set of every address that's also a resume target. A resume
    // body's BFS should NOT cross into a sibling resume chunk, so we
    // treat the union of (event-owned U other-resume-targets) as the
    // hard stop set.
    let other_resume_targets: BTreeSet<usize> = latent_resumes.values().copied().collect();

    let mut output: BTreeMap<usize, Range<usize>> = BTreeMap::new();
    for (&call_offset, &resume_target) in latent_resumes {
        if !graph.boundaries.contains(&resume_target) {
            continue;
        }
        // Defensive: if the resume target somehow lands inside an
        // event partition (extremely unlikely now that latent edges
        // aren't wired), drop the entry rather than claim event
        // statements as the resume body.
        if event_owner.contains_key(&resume_target) {
            continue;
        }
        let mut reached: BTreeSet<usize> = BTreeSet::new();
        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(resume_target);
        while let Some(addr) = queue.pop_front() {
            if !reached.insert(addr) {
                continue;
            }
            if let Some(successors) = graph.successors.get(&addr) {
                for &succ in successors {
                    // Stop at addresses claimed by an event partition;
                    // those belong to the synchronous control flow and
                    // are already in the event's `body`.
                    if event_owner.contains_key(&succ) {
                        continue;
                    }
                    // Stop at OTHER resume targets so adjacent latent
                    // resumes don't merge into a single block.
                    if succ != resume_target && other_resume_targets.contains(&succ) {
                        continue;
                    }
                    if !reached.contains(&succ) {
                        queue.push_back(succ);
                    }
                }
            }
        }
        if reached.is_empty() {
            continue;
        }
        let mut owned: Vec<usize> = reached.into_iter().collect();
        owned.sort_unstable();
        let ranges = addresses_to_ranges(&owned, bytecode, ue5, name_table);
        // Use the first contiguous span starting at the resume target
        // so non-contiguous reach (rare; would imply the resume body
        // forward-jumps over an event-owned region) clips cleanly.
        let chunk = ranges
            .into_iter()
            .find(|range| range.start == resume_target)
            .unwrap_or_else(|| resume_target..resume_target + 1);
        output.insert(call_offset, chunk);
    }
    output
}

/// Pin-attribution divergence diagnostic. For every address claimed by two or more event
/// seeds, emit `PIN_ATTR_DIVERGE` to stderr when the pin-attribution map
/// has an entry for that address and that entry disagrees with the
/// opcode-BFS lowest-offset tie-break.
///
/// "Disagrees" means: the lowest-offset event (the one `or_insert` would
/// pick) is not in the pin-attribution set for that address. Pin-only
/// addresses (no opcode-BFS contention) and addresses with no
/// pin-attribution entry are silently skipped, the divergence channel is
/// intentionally narrow so the log only surfaces genuine tie-break
/// disagreements.
fn log_pin_attribution_divergences(
    sorted_entries: &[&EventEntry],
    event_reachable: &[BTreeSet<usize>],
    pin_attribution: &crate::bytecode::pin_attribution::PinEventAttribution,
) {
    // Build a per-address list of claiming event indices, in
    // ascending-offset order. The first entry is the opcode-BFS winner.
    let mut claimants: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (event_idx, reachable) in event_reachable.iter().enumerate() {
        for &addr in reachable {
            claimants.entry(addr).or_default().push(event_idx);
        }
    }

    let debug_all = std::env::var_os("BP_INSPECT_PIN_ATTR_DEBUG").is_some();
    for (addr, event_indices) in claimants {
        if event_indices.len() < 2 {
            continue;
        }
        // `event_indices` is non-empty here and its values index
        // `sorted_entries`; skip the address rather than panic if either
        // invariant breaks on a malformed asset.
        let Some(opcode_bfs_winner) = event_indices
            .first()
            .and_then(|&idx| sorted_entries.get(idx))
            .map(|entry| &entry.name)
        else {
            continue;
        };
        let pin_events = pin_attribution.attribution.get(&addr);
        if debug_all {
            let opcode_set: Vec<&str> = event_indices
                .iter()
                .map(|&idx| sorted_entries[idx].name.as_str())
                .collect();
            eprintln!(
                "PIN_ATTR_DEBUG addr=0x{:x} opcode_bfs_set={:?} pin_attr={:?}",
                addr, opcode_set, pin_events
            );
        }
        let Some(pin_events) = pin_events else {
            continue;
        };
        if pin_events.contains(opcode_bfs_winner) {
            continue;
        }
        eprintln!(
            "PIN_ATTR_DIVERGE addr=0x{:x} opcode_bfs_picks={} pin_attr_picks={:?}",
            addr, opcode_bfs_winner, pin_events
        );
    }
}
