//! Reaching-condition analysis over a basic-block CFG.
//!
//! For each block, the *reaching condition* is the boolean formula over
//! branch predicates under which control can reach that block. This is the
//! core primitive of condition-based control-flow structuring (DREAM /
//! Phoenix): instead of pattern-matching CFG shapes, you classify each
//! block by the predicate combination that guards it, then emit the
//! then/else/tail structure that the formula implies.
//!
//! This module is a READ-ONLY diagnostic. Nothing here is wired into the
//! decode / emit pipeline; the production structurer still drives output.
//! The fixture probe in `probe_tests` uses this to ask, per gnarly event,
//! whether reaching-condition bucketing agrees with what the current
//! special-case emitters do.
//!
//! Scope: the forward (loop-free) DAG. Back edges (a `u -> v` edge where
//! `v` dominates `u`) are excluded before the pass, matching DREAM's
//! treatment of loops as out of scope for reaching-condition derivation.
//! Loop *bodies* still receive a reaching condition via their forward
//! predecessors; only the back edge itself is dropped.

use std::collections::{BTreeMap, BTreeSet};

use super::dom::DomChain;
use super::region::{RegionKind, RegionTree};
use super::{BlockId, ControlFlowGraph};

/// The genuine predicate-atom set for `cfg`, with the macro gates suppressed
/// to reach it.
///
/// Returns `(conditionals, suppressed_gates)`. `conditionals` is every block
/// whose terminator opcode is a genuine boolean conditional
/// (`EX_JUMP_IF_NOT` 0x07 or `EX_POP_FLOW_IF_NOT` 0x4F), MINUS the blocks the
/// region tree classified as `RegionKind::DoOnceGate` entries. DoOnce gates
/// are compiler-generated run-once latches, not user branches; their
/// predicate would pollute every downstream reaching condition, so
/// suppressing them keeps the atom set to real user conditions.
/// `suppressed_gates` lists the conditional blocks removed, so the collapse
/// stays auditable.
///
/// `opcode_at` resolves a disk offset to its opcode byte. Production reads
/// `ctx.bytecode.get(addr).copied()`; the probe harness reads its
/// `OpcodeGraph`. When `region_tree` is `None` (synthetic/standalone
/// contexts with no SESE decomposition) no gate is suppressed.
pub fn collect_genuine_conditionals(
    cfg: &ControlFlowGraph,
    region_tree: Option<&RegionTree>,
    opcode_at: impl Fn(usize) -> Option<u8>,
) -> (BTreeSet<BlockId>, Vec<BlockId>) {
    const EX_JUMP_IF_NOT: u8 = 0x07;
    const EX_POP_FLOW_IF_NOT: u8 = 0x4F;

    let gate_blocks: BTreeSet<BlockId> = region_tree
        .map(|tree| {
            tree.regions
                .iter()
                .filter(|region| region.kind == RegionKind::DoOnceGate)
                .map(|region| region.entry)
                .collect()
        })
        .unwrap_or_default();

    let mut conditionals: BTreeSet<BlockId> = BTreeSet::new();
    let mut suppressed: Vec<BlockId> = Vec::new();
    for block in &cfg.blocks {
        if block.id == cfg.sink {
            continue;
        }
        let Some(&terminator) = block.opcodes.last() else {
            continue;
        };
        // Genuine boolean conditionals: a forward `EX_JUMP_IF_NOT`, or an
        // `EX_POP_FLOW_IF_NOT` (the if-without-else-inside-a-Sequence-pin
        // shape, where the false arm pops to the next pin). Both branch on a
        // real condition; flow-stack forks (`EX_PushExecutionFlow`) do not.
        let terminator_op = opcode_at(terminator);
        if terminator_op != Some(EX_JUMP_IF_NOT) && terminator_op != Some(EX_POP_FLOW_IF_NOT) {
            continue;
        }
        if gate_blocks.contains(&block.id) {
            suppressed.push(block.id);
        } else {
            conditionals.insert(block.id);
        }
    }
    (conditionals, suppressed)
}

/// Boolean formula over branch predicates.
///
/// `Atom(b)` means "the condition at conditional block `b` evaluated TRUE"
/// (the fallthrough edge of its `EX_JUMP_IF_NOT`). `Not(Atom(b))` is the
/// jump-target edge. Formulas are kept in a normalised shape by
/// [`simplify`]; see that function for the rewrite rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    True,
    False,
    Atom(BlockId),
    Not(Box<Cond>),
    And(Vec<Cond>),
    Or(Vec<Cond>),
}

impl Cond {
    fn not(inner: Cond) -> Cond {
        Cond::Not(Box::new(inner))
    }

    /// The atom this formula is, if it is a bare `Atom(b)`.
    fn as_atom(&self) -> Option<BlockId> {
        match self {
            Cond::Atom(block) => Some(*block),
            _ => None,
        }
    }

    /// The atom this formula negates, if it is a bare `Not(Atom(b))`.
    fn as_negated_atom(&self) -> Option<BlockId> {
        match self {
            Cond::Not(inner) => inner.as_atom(),
            _ => None,
        }
    }
}

/// Normalise a formula to a compact canonical-ish shape.
///
/// Rewrites applied (recursively, bottom-up):
/// - flatten nested `And` into `And`, nested `Or` into `Or`;
/// - drop `True` from `And` and `False` from `Or` (identity elements);
/// - short-circuit: `And` containing `False` -> `False`; `Or` containing
///   `True` -> `True`;
/// - dedup structurally equal terms;
/// - complementation: an `And` holding both `x` and `Not(x)` -> `False`;
///   an `Or` holding both -> `True`;
/// - absorption: `x Or (x And y)` -> `x`, and dually
///   `x And (x Or y)` -> `x`;
/// - collapse singletons (`And([t])` -> `t`) and empties (`And([])` ->
///   `True`, `Or([])` -> `False`).
///
/// This is deliberately modest: enough to collapse the diamond / nested-if
/// cases that arise in Blueprint bytecode down to `Atom(b)`,
/// `Not(Atom(b))`, or `True`. It is not a full SAT simplifier and will not
/// canonicalise arbitrary formulas.
pub fn simplify(cond: Cond) -> Cond {
    match cond {
        Cond::True | Cond::False | Cond::Atom(_) => cond,
        Cond::Not(inner) => simplify_not(simplify(*inner)),
        Cond::And(terms) => simplify_junction(terms, Junction::And),
        Cond::Or(terms) => simplify_junction(terms, Junction::Or),
    }
}

fn simplify_not(inner: Cond) -> Cond {
    match inner {
        Cond::True => Cond::False,
        Cond::False => Cond::True,
        Cond::Not(double) => *double,
        other => Cond::not(other),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Junction {
    And,
    Or,
}

impl Junction {
    /// The identity element dropped from this junction (`True` for `And`,
    /// `False` for `Or`).
    fn identity(self) -> Cond {
        match self {
            Junction::And => Cond::True,
            Junction::Or => Cond::False,
        }
    }

    /// The absorbing element that short-circuits this junction (`False`
    /// for `And`, `True` for `Or`).
    fn absorbing(self) -> Cond {
        match self {
            Junction::And => Cond::False,
            Junction::Or => Cond::True,
        }
    }
}

fn simplify_junction(terms: Vec<Cond>, kind: Junction) -> Cond {
    let identity = kind.identity();
    let absorbing = kind.absorbing();

    // Simplify children, flatten same-kind nesting, drop identity elements.
    let mut flat: Vec<Cond> = Vec::new();
    for term in terms {
        let simplified = simplify(term);
        if simplified == absorbing {
            return absorbing;
        }
        if simplified == identity {
            continue;
        }
        match (&simplified, kind) {
            (Cond::And(children), Junction::And) | (Cond::Or(children), Junction::Or) => {
                flat.extend(children.iter().cloned());
            }
            _ => flat.push(simplified),
        }
    }

    dedup_terms(&mut flat);

    if has_complementary_pair(&flat) {
        return absorbing;
    }

    absorb_terms(&mut flat, kind);

    if kind == Junction::Or {
        if let Some(factored) = factor_common_conjunct(&flat) {
            return factored;
        }
    }

    match flat.len() {
        0 => identity,
        1 => flat.pop().expect("len checked"),
        _ => match kind {
            Junction::And => Cond::And(flat),
            Junction::Or => Cond::Or(flat),
        },
    }
}

/// Factor a conjunct shared by every disjunct out of an `Or` of `And`s.
///
/// `(A & x1) | (A & x2) | ...` -> `A & ((x1) | (x2) | ...)`, then
/// re-simplified. This is the rewrite that collapses a merge block's
/// reaching condition: a join reached down both arms of an inner branch
/// carries `(outer & inner) | (outer & !inner)`, which factors to
/// `outer & (inner | !inner)` -> `outer`. Returns `None` if the terms
/// share no common conjunct, or the list is not all `And`s of length >= 2.
fn factor_common_conjunct(terms: &[Cond]) -> Option<Cond> {
    if terms.len() < 2 {
        return None;
    }
    let conjuncts: Vec<Vec<Cond>> = terms
        .iter()
        .map(|term| match term {
            Cond::And(children) => Some(children.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;

    let common: Vec<Cond> = conjuncts
        .first()?
        .iter()
        .filter(|candidate| {
            conjuncts
                .iter()
                .all(|group| group.iter().any(|item| item == *candidate))
        })
        .cloned()
        .collect();
    if common.is_empty() {
        return None;
    }

    let remainders: Vec<Cond> = conjuncts
        .iter()
        .map(|group| {
            let rest: Vec<Cond> = group
                .iter()
                .filter(|item| !common.contains(item))
                .cloned()
                .collect();
            simplify(Cond::And(rest))
        })
        .collect();

    let mut factored = common;
    factored.push(simplify(Cond::Or(remainders)));
    Some(simplify(Cond::And(factored)))
}

/// Remove structurally-duplicate terms, preserving first-seen order.
fn dedup_terms(terms: &mut Vec<Cond>) {
    let mut seen: Vec<Cond> = Vec::new();
    terms.retain(|term| {
        if seen.contains(term) {
            false
        } else {
            seen.push(term.clone());
            true
        }
    });
}

/// True if the term list contains some `x` alongside its negation `Not(x)`.
fn has_complementary_pair(terms: &[Cond]) -> bool {
    terms.iter().any(|term| {
        let negation = simplify_not(term.clone());
        terms.contains(&negation)
    })
}

/// Apply absorption within one junction: in an `Or`, drop any term that is
/// an `And` containing another (simpler) term of the list; dually in an
/// `And`, drop any `Or` term containing another list term. Implements
/// `x Or (x And y)` -> `x` and `x And (x Or y)` -> `x`.
fn absorb_terms(terms: &mut Vec<Cond>, kind: Junction) {
    let snapshot = terms.clone();
    terms.retain(|term| {
        let absorbed_children = match (term, kind) {
            (Cond::And(children), Junction::Or) | (Cond::Or(children), Junction::And) => children,
            _ => return true,
        };
        // Drop `term` if any sibling appears among its children.
        let absorbed = snapshot.iter().any(|sibling| {
            sibling != term && absorbed_children.iter().any(|child| child == sibling)
        });
        !absorbed
    });
}

/// The two outgoing edge conditions of a conditional block.
///
/// `fallthrough` is the successor whose `start == cond_block.end` (the
/// instruction right after the `EX_JUMP_IF_NOT`); it carries `Atom(b)`.
/// `jump_target` is the other successor; it carries `Not(Atom(b))`.
struct BranchEdges {
    fallthrough: BlockId,
    jump_target: BlockId,
}

/// Resolve which successor of a 2-way block is the fallthrough (cond TRUE)
/// vs the jump target (cond FALSE).
///
/// Version-independent rule: the fallthrough successor's `start` equals the
/// conditional block's `end` (the next sequential opcode). The other
/// successor is the jump target. Returns `None` if the block does not have
/// exactly two successors among the given edges, or neither successor sits
/// immediately after the block.
fn branch_edges(
    cfg: &ControlFlowGraph,
    block: BlockId,
    successors: &[BlockId],
) -> Option<BranchEdges> {
    if successors.len() != 2 {
        return None;
    }
    let block_end = cfg.blocks.get(block)?.end;
    let first = successors[0];
    let second = successors[1];
    let first_start = cfg.blocks.get(first)?.start;
    let second_start = cfg.blocks.get(second)?.start;

    if first_start == block_end {
        Some(BranchEdges {
            fallthrough: first,
            jump_target: second,
        })
    } else if second_start == block_end {
        Some(BranchEdges {
            fallthrough: second,
            jump_target: first,
        })
    } else {
        None
    }
}

/// Forward-DAG edge set: every CFG edge except back edges and edges into
/// the synthetic sink. A `u -> v` edge is a back edge iff `v` dominates
/// `u`. Self-loops (`u -> u`) are back edges too.
fn forward_edges(
    cfg: &ControlFlowGraph,
    idom: &BTreeMap<BlockId, BlockId>,
) -> BTreeSet<(BlockId, BlockId)> {
    let mut edges: BTreeSet<(BlockId, BlockId)> = BTreeSet::new();
    for (&source, targets) in &cfg.successors {
        for &target in targets {
            if target == cfg.sink {
                continue;
            }
            if is_back_edge(source, target, idom) {
                continue;
            }
            edges.insert((source, target));
        }
    }
    edges
}

/// True if `target` dominates `source` (so `source -> target` closes a
/// natural loop). Walks the immediate-dominator chain up from `source`.
fn is_back_edge(source: BlockId, target: BlockId, idom: &BTreeMap<BlockId, BlockId>) -> bool {
    source == target
        || DomChain(idom)
            .ancestors(source)
            .any(|parent| parent == target)
}

/// Kahn topological order over the forward DAG. Returns `None` if a cycle
/// remains (irreducible / unresolved back edge), which the caller surfaces
/// rather than papering over.
fn topo_order(
    cfg: &ControlFlowGraph,
    forward: &BTreeSet<(BlockId, BlockId)>,
) -> Option<Vec<BlockId>> {
    let real_blocks: Vec<BlockId> = cfg
        .blocks
        .iter()
        .map(|block| block.id)
        .filter(|&id| id != cfg.sink)
        .collect();

    let mut indegree: BTreeMap<BlockId, usize> =
        real_blocks.iter().map(|&id| (id, 0usize)).collect();
    let mut out: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &(source, target) in forward {
        out.entry(source).or_default().push(target);
        *indegree.entry(target).or_insert(0) += 1;
    }

    // BTreeSet keeps the ready set ordered for deterministic output.
    let mut ready: BTreeSet<BlockId> = indegree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(&id, _)| id)
        .collect();

    let mut order: Vec<BlockId> = Vec::with_capacity(real_blocks.len());
    while let Some(&next) = ready.iter().next() {
        ready.remove(&next);
        order.push(next);
        if let Some(targets) = out.get(&next) {
            for &target in targets {
                let deg = indegree.entry(target).or_insert(0);
                *deg = deg.saturating_sub(1);
                if *deg == 0 {
                    ready.insert(target);
                }
            }
        }
    }

    if order.len() == real_blocks.len() {
        Some(order)
    } else {
        None
    }
}

/// Outcome of [`compute_reaching_conditions`].
pub struct ReachingConditions {
    /// Reaching condition per reachable forward-DAG block.
    pub conditions: BTreeMap<BlockId, Cond>,
    /// Reachable blocks (forward DAG, excluding sink) that the pass left
    /// without a reaching condition. Non-empty signals a bug (or an
    /// irreducible shape the DAG construction did not fully untangle).
    pub missing: Vec<BlockId>,
    /// True if the forward DAG still had a cycle after back-edge removal
    /// (irreducible loop). When set, `conditions` is empty.
    pub irreducible: bool,
}

/// Compute the reaching condition for every block of `cfg`'s forward DAG.
///
/// `conditional_blocks` is the AUTHORITATIVE set of blocks that act as
/// genuine predicate atoms. Only an edge out of a block in this set carries
/// `Atom`/`Not(Atom)`; every other edge carries `True`. The caller derives
/// this set from real branch terminators (`EX_JUMP_IF_NOT`), so flow-stack
/// forks (`EX_PushExecutionFlow`, which sequence rather than branch) and
/// suppressed macro gates never become phantom predicates.
///
/// `RC(entry) = True`. For each block `n` in topological order,
/// `RC(n) = simplify(Or over forward preds p of (RC(p) And edge_cond(p, n)))`,
/// where `edge_cond` is `True` unless `p` is a conditional atom, in which
/// case it is `Atom(p)` / `Not(Atom(p))` for the fallthrough / jump-target
/// edges of the 2-way branch.
pub fn compute_reaching_conditions(
    cfg: &ControlFlowGraph,
    conditional_blocks: &BTreeSet<BlockId>,
) -> ReachingConditions {
    let idom = super::dom::compute_dominators(cfg);
    let forward = forward_edges(cfg, &idom);

    let Some(order) = topo_order(cfg, &forward) else {
        return ReachingConditions {
            conditions: BTreeMap::new(),
            missing: Vec::new(),
            irreducible: true,
        };
    };

    // Forward predecessors per block, and forward successor lists per block
    // (used to resolve fallthrough vs jump-target edges).
    let mut forward_preds: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut forward_succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &(source, target) in &forward {
        forward_preds.entry(target).or_default().push(source);
        forward_succs.entry(source).or_default().push(target);
    }

    let mut conditions: BTreeMap<BlockId, Cond> = BTreeMap::new();
    conditions.insert(cfg.entry, Cond::True);

    for &block in &order {
        if block == cfg.entry {
            continue;
        }
        let Some(preds) = forward_preds.get(&block) else {
            // Unreachable in the forward DAG (e.g. a loop head reachable
            // only via its back edge). Leave it for the `missing` report.
            continue;
        };

        let mut disjuncts: Vec<Cond> = Vec::new();
        for &pred in preds {
            let pred_rc = conditions.get(&pred).cloned().unwrap_or(Cond::True);
            let edge = edge_condition(cfg, pred, block, &forward_succs, conditional_blocks);
            disjuncts.push(simplify(Cond::And(vec![pred_rc, edge])));
        }
        conditions.insert(block, simplify(Cond::Or(disjuncts)));
    }

    let missing: Vec<BlockId> = order
        .iter()
        .copied()
        .filter(|block| !conditions.contains_key(block))
        .collect();

    ReachingConditions {
        conditions,
        missing,
        irreducible: false,
    }
}

/// Condition carried by the forward edge `pred -> block`.
///
/// `True` unless `pred` is a genuine predicate atom (in `conditional_blocks`)
/// with two resolvable forward successors. For such a branch the fallthrough
/// edge carries `Atom(pred)` and the jump-target edge `Not(Atom(pred))`.
/// A 2-way `pred` that is NOT in the conditional set (a flow-stack fork, a
/// suppressed macro gate) carries `True`, so it never becomes a predicate.
/// Falls back to `True` if the branch's edges cannot be resolved (keeps the
/// formula sound, just less precise).
fn edge_condition(
    cfg: &ControlFlowGraph,
    pred: BlockId,
    block: BlockId,
    forward_succs: &BTreeMap<BlockId, Vec<BlockId>>,
    conditional_blocks: &BTreeSet<BlockId>,
) -> Cond {
    if !conditional_blocks.contains(&pred) {
        return Cond::True;
    }
    let succs = match forward_succs.get(&pred) {
        Some(succs) => succs.as_slice(),
        None => return Cond::True,
    };
    if succs.len() < 2 {
        return Cond::True;
    }
    match branch_edges(cfg, pred, succs) {
        Some(edges) if edges.fallthrough == block => Cond::Atom(pred),
        Some(edges) if edges.jump_target == block => Cond::not(Cond::Atom(pred)),
        _ => Cond::True,
    }
}

/// Bucket of a descendant block relative to one conditional block `b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bucket {
    /// `RC` simplifies to `Atom(b)`: reached only when `b`'s cond is TRUE.
    Then,
    /// `RC` simplifies to `Not(Atom(b))`: reached only when FALSE.
    Else,
    /// `RC` simplifies to `True`: reached regardless of `b` (the merge /
    /// continuation after the branch).
    Tail,
    /// Anything else: the formula references other predicates, or a mix
    /// `b` does not cleanly determine.
    Other,
}

/// Maximum number of distinct atoms a formula may reference before
/// [`classify_bucket`] abandons exact truth-table evaluation (2^n grows
/// past a few thousand assignments) and falls back to the structural
/// `simplify`-based check. Real Blueprint reaching conditions reference a
/// handful of predicates, so the cap is never hit in practice.
const MAX_TRUTH_TABLE_VARS: usize = 24;

/// Collect every atom (`Atom(b)`) appearing anywhere in `cond`.
fn collect_atoms(cond: &Cond, atoms: &mut BTreeSet<BlockId>) {
    match cond {
        Cond::True | Cond::False => {}
        Cond::Atom(block) => {
            atoms.insert(*block);
        }
        Cond::Not(inner) => collect_atoms(inner, atoms),
        Cond::And(terms) | Cond::Or(terms) => {
            for term in terms {
                collect_atoms(term, atoms);
            }
        }
    }
}

/// Evaluate `cond` under a complete truth assignment of its atoms. Atoms
/// absent from `assignment` default to `false`; callers always pass a
/// complete assignment so the default is never relied on.
fn eval(cond: &Cond, assignment: &BTreeMap<BlockId, bool>) -> bool {
    match cond {
        Cond::True => true,
        Cond::False => false,
        Cond::Atom(block) => *assignment.get(block).unwrap_or(&false),
        Cond::Not(inner) => !eval(inner, assignment),
        Cond::And(terms) => terms.iter().all(|term| eval(term, assignment)),
        Cond::Or(terms) => terms.iter().any(|term| eval(term, assignment)),
    }
}

/// Classify `descendant_rc` against the conditional block `b` by exact
/// truth-table evaluation over the atoms the formula references (union
/// `{b}`). This does not depend on [`simplify`] being complete: a tautology
/// that `simplify` leaves un-collapsed (e.g. `(!a & !b) | a | (!a & b)`)
/// still classifies as `Tail` because every assignment satisfies it.
///
/// - `Tail` if `eval(rc)` is true under every assignment.
/// - `Then` if `eval(rc) == assignment[b]` under every assignment.
/// - `Else` if `eval(rc) == !assignment[b]` under every assignment.
/// - `Other` otherwise (the formula references predicates `b` alone does
///   not determine).
///
/// If the formula references more than [`MAX_TRUTH_TABLE_VARS`] atoms the
/// enumeration would blow up, so it falls back to the structural
/// `simplify`-based check.
///
/// This is the whole-function classifier; [`classify_bucket_in_context`]
/// restricts the same enumeration to assignments consistent with being inside
/// a region.
pub fn classify_bucket(conditional: BlockId, descendant_rc: &Cond) -> Bucket {
    classify_bucket_in_context(conditional, descendant_rc, &Cond::True)
}

/// Like [`classify_bucket`], but only assignments satisfying `context`
/// participate in the truth-table. The reaching condition of a descendant is
/// computed over the whole function, so an ancestor predicate can appear in a
/// nested branch's merge RC even though it is fixed within the region. Passing
/// `RC(region.entry)` as `context` pins those ancestor predicates to the values
/// they hold inside the region, collapsing their contribution and recovering
/// the local THEN/ELSE/TAIL classification.
///
/// With `context = Cond::True` no assignment is filtered, so this reduces to
/// the whole-function classifier exactly.
///
/// If `context` is unsatisfiable (no enumerated assignment satisfies it) the
/// region is unreachable, so the result is `Other` rather than a vacuous
/// `Tail`.
pub fn classify_bucket_in_context(
    conditional: BlockId,
    descendant_rc: &Cond,
    context: &Cond,
) -> Bucket {
    let mut vars_set: BTreeSet<BlockId> = BTreeSet::new();
    collect_atoms(descendant_rc, &mut vars_set);
    collect_atoms(context, &mut vars_set);
    vars_set.insert(conditional);
    let vars: Vec<BlockId> = vars_set.into_iter().collect();

    if vars.len() > MAX_TRUTH_TABLE_VARS {
        // Rare large-formula path: the structural fallback does not apply the
        // context (it classifies the whole-function RC structurally).
        return classify_bucket_structural(conditional, descendant_rc);
    }

    let mut any_in_context = false;
    let mut all_true = true;
    let mut matches_cond = true;
    let mut matches_not_cond = true;
    for bits in 0u32..(1u32 << vars.len()) {
        let assignment: BTreeMap<BlockId, bool> = vars
            .iter()
            .enumerate()
            .map(|(index, &block)| (block, bits & (1 << index) != 0))
            .collect();
        if !eval(context, &assignment) {
            continue;
        }
        any_in_context = true;
        let value = eval(descendant_rc, &assignment);
        let cond_value = *assignment.get(&conditional).unwrap_or(&false);
        all_true &= value;
        matches_cond &= value == cond_value;
        matches_not_cond &= value != cond_value;
    }

    if !any_in_context {
        Bucket::Other
    } else if all_true {
        Bucket::Tail
    } else if matches_cond {
        Bucket::Then
    } else if matches_not_cond {
        Bucket::Else
    } else {
        Bucket::Other
    }
}

/// Structural fallback for [`classify_bucket`] when the atom count exceeds
/// the truth-table cap. Relies on `simplify` collapsing the formula to a
/// bare atom / negated atom / `True`.
fn classify_bucket_structural(conditional: BlockId, descendant_rc: &Cond) -> Bucket {
    let simplified = simplify(descendant_rc.clone());
    if simplified == Cond::True {
        return Bucket::Tail;
    }
    if simplified.as_atom() == Some(conditional) {
        return Bucket::Then;
    }
    if simplified.as_negated_atom() == Some(conditional) {
        return Bucket::Else;
    }
    Bucket::Other
}

/// Render a formula with predicate atoms labelled `P@b<id>`. Probe-side
/// pretty-printer; production output has its own condition rendering.
pub fn format_cond(cond: &Cond) -> String {
    match cond {
        Cond::True => "true".to_string(),
        Cond::False => "false".to_string(),
        Cond::Atom(block) => format!("P@b{}", block),
        Cond::Not(inner) => format!("!{}", format_cond(inner)),
        Cond::And(terms) => {
            let parts: Vec<String> = terms.iter().map(format_cond).collect();
            format!("({})", parts.join(" & "))
        }
        Cond::Or(terms) => {
            let parts: Vec<String> = terms.iter().map(format_cond).collect();
            format!("({})", parts.join(" | "))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::bytecode::cfg::{BasicBlock, ControlFlowGraph};

    /// Build a synthetic CFG from `(source, target)` edges, mirroring the
    /// helper in `cfg::tests`. Block ids are `0..node_count`; a synthetic
    /// sink at id `node_count` collects every block with no outgoing edge.
    ///
    /// `start`/`end` are derived so that the *first* successor listed for a
    /// 2-way block is its fallthrough: block `id` occupies `[id*10,
    /// id*10+1)`, and `branch_edges` keys fallthrough off `start ==
    /// cond.end`. Tests that need a specific fallthrough wire that
    /// successor's start to the branch block's end explicitly via
    /// `fallthrough_of`.
    fn make_cfg(node_count: usize, edges: &[(BlockId, BlockId)]) -> ControlFlowGraph {
        let sink_id = node_count;
        let blocks: Vec<BasicBlock> = (0..=node_count)
            .map(|id| BasicBlock {
                id,
                start: id * 10,
                end: id * 10 + 1,
                opcodes: if id == sink_id { Vec::new() } else { vec![id] },
            })
            .collect();

        let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for block in &blocks {
            successors.insert(block.id, Vec::new());
            predecessors.insert(block.id, Vec::new());
        }
        let mut has_outgoing: BTreeSet<BlockId> = BTreeSet::new();
        for &(source, target) in edges {
            successors.entry(source).or_default().push(target);
            predecessors.entry(target).or_default().push(source);
            has_outgoing.insert(source);
        }
        for block_id in 0..node_count {
            if !has_outgoing.contains(&block_id) {
                successors.entry(block_id).or_default().push(sink_id);
                predecessors.entry(sink_id).or_default().push(block_id);
            }
        }

        ControlFlowGraph {
            blocks,
            successors,
            predecessors,
            entry: 0,
            sink: sink_id,
        }
    }

    /// Force `fallthrough`'s `start` to equal `cond_block`'s `end` so that
    /// `branch_edges` resolves the THEN/ELSE arms deterministically.
    fn set_fallthrough(cfg: &mut ControlFlowGraph, cond_block: BlockId, fallthrough: BlockId) {
        let cond_end = cfg.blocks[cond_block].end;
        cfg.blocks[fallthrough].start = cond_end;
    }

    /// Build the authoritative conditional-atom set from the listed block
    /// ids. The synthetic CFGs encode their branches positionally (via
    /// `set_fallthrough`); these helpers name which of those branch blocks
    /// the test wants treated as genuine predicate atoms.
    fn conds(blocks: &[BlockId]) -> BTreeSet<BlockId> {
        blocks.iter().copied().collect()
    }

    #[test]
    fn simplify_collapses_identity_and_absorbing() {
        // And([True, Atom]) -> Atom
        assert_eq!(
            simplify(Cond::And(vec![Cond::True, Cond::Atom(1)])),
            Cond::Atom(1)
        );
        // Or([False, Atom]) -> Atom
        assert_eq!(
            simplify(Cond::Or(vec![Cond::False, Cond::Atom(2)])),
            Cond::Atom(2)
        );
        // And([False, anything]) -> False
        assert_eq!(
            simplify(Cond::And(vec![Cond::False, Cond::Atom(3)])),
            Cond::False
        );
        // Or([True, anything]) -> True
        assert_eq!(
            simplify(Cond::Or(vec![Cond::True, Cond::Atom(3)])),
            Cond::True
        );
    }

    #[test]
    fn simplify_complementation_and_absorption() {
        // x And Not(x) -> False
        assert_eq!(
            simplify(Cond::And(vec![Cond::Atom(1), Cond::not(Cond::Atom(1))])),
            Cond::False
        );
        // x Or Not(x) -> True
        assert_eq!(
            simplify(Cond::Or(vec![Cond::Atom(1), Cond::not(Cond::Atom(1))])),
            Cond::True
        );
        // x Or (x And y) -> x
        assert_eq!(
            simplify(Cond::Or(vec![
                Cond::Atom(1),
                Cond::And(vec![Cond::Atom(1), Cond::Atom(2)]),
            ])),
            Cond::Atom(1)
        );
        // x And (x Or y) -> x
        assert_eq!(
            simplify(Cond::And(vec![
                Cond::Atom(1),
                Cond::Or(vec![Cond::Atom(1), Cond::Atom(2)]),
            ])),
            Cond::Atom(1)
        );
        // Double negation cancels.
        assert_eq!(simplify(Cond::not(Cond::not(Cond::Atom(5)))), Cond::Atom(5));
    }

    #[test]
    fn if_then_one_arm_bypasses() {
        // 0 branches to 1 (then-body) and 2 (merge); 1 -> 2; 2 exits.
        let mut cfg = make_cfg(3, &[(0, 1), (0, 2), (1, 2)]);
        set_fallthrough(&mut cfg, 0, 1); // arm 1 is THEN (cond TRUE)
        let rc = compute_reaching_conditions(&cfg, &conds(&[0]));
        assert!(rc.missing.is_empty());
        assert!(!rc.irreducible);

        assert_eq!(rc.conditions.get(&0), Some(&Cond::True));
        assert_eq!(rc.conditions.get(&1), Some(&Cond::Atom(0)));
        // Merge: Atom(0) Or Not(Atom(0)) -> True.
        assert_eq!(rc.conditions.get(&2), Some(&Cond::True));

        assert_eq!(
            classify_bucket(0, rc.conditions.get(&1).unwrap()),
            Bucket::Then
        );
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&2).unwrap()),
            Bucket::Tail
        );
    }

    #[test]
    fn if_then_else_diamond() {
        // 0 -> 1 (then), 0 -> 2 (else); both -> 3 (merge).
        let mut cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        set_fallthrough(&mut cfg, 0, 1); // arm 1 THEN, arm 2 ELSE
        let rc = compute_reaching_conditions(&cfg, &conds(&[0]));
        assert!(rc.missing.is_empty());

        assert_eq!(rc.conditions.get(&1), Some(&Cond::Atom(0)));
        assert_eq!(rc.conditions.get(&2), Some(&Cond::not(Cond::Atom(0))));
        assert_eq!(rc.conditions.get(&3), Some(&Cond::True));

        assert_eq!(
            classify_bucket(0, rc.conditions.get(&1).unwrap()),
            Bucket::Then
        );
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&2).unwrap()),
            Bucket::Else
        );
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&3).unwrap()),
            Bucket::Tail
        );
    }

    #[test]
    fn nested_if_inside_then_arm() {
        // 0 -> 1 (outer then) / 4 (outer merge).
        // 1 -> 2 (inner then) / 3 (inner merge); 2 -> 3; 3 -> 4.
        let mut cfg = make_cfg(5, &[(0, 1), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]);
        set_fallthrough(&mut cfg, 0, 1); // 1 is outer THEN
        set_fallthrough(&mut cfg, 1, 2); // 2 is inner THEN
        let rc = compute_reaching_conditions(&cfg, &conds(&[0, 1]));
        assert!(rc.missing.is_empty());

        // Inner then reached when outer cond AND inner cond.
        assert_eq!(
            simplify(rc.conditions.get(&2).cloned().unwrap()),
            Cond::And(vec![Cond::Atom(0), Cond::Atom(1)])
        );
        // Inner merge (3) reached whenever outer cond holds: Atom(0).
        assert_eq!(rc.conditions.get(&3), Some(&Cond::Atom(0)));
        // Block 3 is THEN of the OUTER branch and TAIL of the INNER branch.
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&3).unwrap()),
            Bucket::Then
        );
        assert_eq!(
            classify_bucket(1, rc.conditions.get(&3).unwrap()),
            Bucket::Other
        );
        // Outer merge (4) reached unconditionally.
        assert_eq!(rc.conditions.get(&4), Some(&Cond::True));
    }

    #[test]
    fn loop_back_edge_excluded_body_gets_rc() {
        // 0 -> 1 (loop head); 1 -> 2 (body) / 3 (exit); 2 -> 1 (back edge).
        let mut cfg = make_cfg(4, &[(0, 1), (1, 2), (1, 3), (2, 1)]);
        set_fallthrough(&mut cfg, 1, 2); // body is the fallthrough arm
        let rc = compute_reaching_conditions(&cfg, &conds(&[1]));
        assert!(!rc.irreducible, "back edge must be excluded, not loop-fail");
        assert!(rc.missing.is_empty());

        assert_eq!(rc.conditions.get(&0), Some(&Cond::True));
        // Loop head reached unconditionally on the forward DAG (back edge
        // dropped).
        assert_eq!(rc.conditions.get(&1), Some(&Cond::True));
        // Body reached when the loop cond is TRUE.
        assert_eq!(rc.conditions.get(&2), Some(&Cond::Atom(1)));
        // Exit reached when FALSE.
        assert_eq!(rc.conditions.get(&3), Some(&Cond::not(Cond::Atom(1))));
    }

    #[test]
    fn irreducible_shape_is_reported() {
        // Two entries into a cycle with no single header -> the forward DAG
        // construction cannot break it via dominator back edges alone, so a
        // cycle survives and topo order fails. We assert the pass reports
        // irreducibility instead of looping or papering over it.
        // 0 -> 1, 0 -> 2, 1 -> 2, 2 -> 1 (mutual edges between 1 and 2).
        let cfg = make_cfg(3, &[(0, 1), (0, 2), (1, 2), (2, 1)]);
        let rc = compute_reaching_conditions(&cfg, &conds(&[0]));
        assert!(rc.irreducible);
        assert!(rc.conditions.is_empty());
    }

    #[test]
    fn fork_not_in_conditional_set_carries_true_edges() {
        // Same diamond as `if_then_else_diamond` but block 0 is NOT in the
        // conditional set. It is a flow-stack fork (both arms run / sequence),
        // not a branch. Its edges must carry `True`, so no `P@b0` atom appears
        // and every reachable block buckets as TAIL.
        let mut cfg = make_cfg(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        set_fallthrough(&mut cfg, 0, 1);
        let rc = compute_reaching_conditions(&cfg, &conds(&[]));
        assert!(rc.missing.is_empty());

        // No phantom atom: every RC is `True`.
        assert_eq!(rc.conditions.get(&1), Some(&Cond::True));
        assert_eq!(rc.conditions.get(&2), Some(&Cond::True));
        assert_eq!(rc.conditions.get(&3), Some(&Cond::True));
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&1).unwrap()),
            Bucket::Tail
        );
        assert_eq!(
            classify_bucket(0, rc.conditions.get(&3).unwrap()),
            Bucket::Tail
        );
    }

    #[test]
    fn exact_classification_collapses_tautology() {
        // `(!a & !b) | a | (!a & b)` is a tautology over {a, b}. `simplify`
        // does not fully collapse it, but exact truth-table evaluation must
        // classify it TAIL regardless of which atom we ask about.
        let tautology = Cond::Or(vec![
            Cond::And(vec![Cond::not(Cond::Atom(0)), Cond::not(Cond::Atom(1))]),
            Cond::Atom(0),
            Cond::And(vec![Cond::not(Cond::Atom(0)), Cond::Atom(1)]),
        ]);
        assert_eq!(classify_bucket(0, &tautology), Bucket::Tail);
        assert_eq!(classify_bucket(1, &tautology), Bucket::Tail);
    }

    #[test]
    fn suppressed_gate_does_not_pollute_user_branch() {
        // Block 0 is a suppressed macro gate (2-way, excluded from the set);
        // block 1 is a genuine user branch (included). Layout:
        //   0 -> 1 (gate fallthrough) / 4 (gate bypass)
        //   1 -> 2 (user then) / 3 (user else); both -> 4 (merge)
        // With the gate suppressed, the user arms must bucket cleanly off
        // block 1: THEN=2, ELSE=3, and the merge is TAIL of block 1, with no
        // `P@b0` term leaking into any RC.
        let mut cfg = make_cfg(5, &[(0, 1), (0, 4), (1, 2), (1, 3), (2, 4), (3, 4)]);
        set_fallthrough(&mut cfg, 0, 1); // gate fallthrough is the body arm
        set_fallthrough(&mut cfg, 1, 2); // user THEN arm
        let rc = compute_reaching_conditions(&cfg, &conds(&[1]));
        assert!(rc.missing.is_empty());

        // Gate edges carry True, so block 1 is reached unconditionally.
        assert_eq!(rc.conditions.get(&1), Some(&Cond::True));
        // User arms reference only the user branch atom, never the gate.
        assert_eq!(rc.conditions.get(&2), Some(&Cond::Atom(1)));
        assert_eq!(rc.conditions.get(&3), Some(&Cond::not(Cond::Atom(1))));
        assert_eq!(rc.conditions.get(&4), Some(&Cond::True));
        assert_eq!(
            classify_bucket(1, rc.conditions.get(&2).unwrap()),
            Bucket::Then
        );
        assert_eq!(
            classify_bucket(1, rc.conditions.get(&3).unwrap()),
            Bucket::Else
        );
        assert_eq!(
            classify_bucket(1, rc.conditions.get(&4).unwrap()),
            Bucket::Tail
        );
        // No atom anywhere references the suppressed gate block 0.
        for cond in rc.conditions.values() {
            let mut atoms: BTreeSet<BlockId> = BTreeSet::new();
            collect_atoms(cond, &mut atoms);
            assert!(!atoms.contains(&0), "gate atom leaked into {:?}", cond);
        }
    }

    #[test]
    fn context_true_matches_whole_function_classifier() {
        // With `context = True` no assignment is filtered, so the in-context
        // classifier must agree with the whole-function classifier on every
        // shape: THEN, ELSE, TAIL, and OTHER.
        let then_rc = Cond::Atom(0);
        let else_rc = Cond::not(Cond::Atom(0));
        let tail_rc = Cond::True;
        let other_rc = Cond::Atom(7); // unrelated predicate

        for (conditional, rc) in [(0, &then_rc), (0, &else_rc), (0, &tail_rc), (0, &other_rc)] {
            assert_eq!(
                classify_bucket_in_context(conditional, rc, &Cond::True),
                classify_bucket(conditional, rc),
                "context=True disagreed with classify_bucket on {:?}",
                rc
            );
        }
    }

    #[test]
    fn ancestor_predicate_collapses_under_region_context() {
        // MouseY-shaped nested if: outer conditional b0 wraps inner conditional
        // b1. The merge RC of the inner branch is computed over the whole
        // function, so it carries the ancestor predicate `P@b0`. Asking about
        // the inner conditional b1 over the whole function gives OTHER (b0 is a
        // predicate b1 alone does not determine). Restricting to assignments
        // where the region entry RC (`Atom(b0)`) holds pins b0=true, under which
        // the merge RC collapses to true => TAIL, matching the local heuristic.
        let descendant_rc = Cond::Atom(0);
        let context = Cond::Atom(0);
        assert_eq!(
            classify_bucket(1, &descendant_rc),
            Bucket::Other,
            "whole-function classification should leak the ancestor predicate"
        );
        assert_eq!(
            classify_bucket_in_context(1, &descendant_rc, &context),
            Bucket::Tail,
            "region context should collapse the ancestor predicate to TAIL"
        );
    }

    #[test]
    fn genuine_then_else_preserved_under_nontrivial_context() {
        // A real inner branch on b1, nested inside an outer conditional b0.
        // Under the region context `Atom(b0)` (we are on b0's true side), the
        // inner THEN reaches when b1 is true and the inner ELSE when b1 is
        // false. The non-trivial context must not erase that distinction.
        let then_rc = Cond::And(vec![Cond::Atom(0), Cond::Atom(1)]);
        let else_rc = Cond::And(vec![Cond::Atom(0), Cond::not(Cond::Atom(1))]);
        let context = Cond::Atom(0);
        assert_eq!(
            classify_bucket_in_context(1, &then_rc, &context),
            Bucket::Then
        );
        assert_eq!(
            classify_bucket_in_context(1, &else_rc, &context),
            Bucket::Else
        );
        // An unsatisfiable context yields OTHER, never a vacuous TAIL.
        let unsat = Cond::And(vec![Cond::Atom(0), Cond::not(Cond::Atom(0))]);
        assert_eq!(
            classify_bucket_in_context(1, &Cond::True, &unsat),
            Bucket::Other
        );
    }
}
