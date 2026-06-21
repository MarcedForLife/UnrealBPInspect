//! Statement tree types for the decoder.
//!
//! Every reachable opcode produces a typed `Stmt`. Constructs recognised
//! during decode (Branch, Sequence, Loop, Switch, Latch, EventCall) appear
//! as dedicated variants. Unrecognised patterns become `Stmt::Unknown` with
//! structured diagnostics rather than a raw passthrough.
//!
//! The `offset` field on every variant is the bytecode mem_offset where
//! the construct begins. Synthetic statements produced by later transforms
//! reuse the originating statement's offset.

use crate::bytecode::expr::Expr;

/// A single statement in the decoded statement tree.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub enum Stmt {
    /// A value assignment (`lhs = rhs`).
    Assignment { lhs: Expr, rhs: Expr, offset: usize },

    /// A function or method call.
    Call {
        func: Expr,
        args: Vec<Expr>,
        offset: usize,
    },

    /// An if/else branch. Either branch may be empty.
    Branch {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
        offset: usize,
    },

    /// A Sequence node with one body per execution pin.
    Sequence { pins: Vec<Vec<Stmt>>, offset: usize },

    /// A loop construct (while, for-counter, or for-each).
    Loop {
        kind: LoopKind,
        /// Loop condition, absent for infinite loops.
        cond: Option<Expr>,
        body: Vec<Stmt>,
        /// Post-loop completion block (e.g. ForEach's "completed" pin body).
        completion: Option<Vec<Stmt>>,
        offset: usize,
    },

    /// A switch dispatch over a single expression.
    Switch {
        expr: Expr,
        cases: Vec<SwitchCase>,
        default: Option<Vec<Stmt>>,
        offset: usize,
    },

    /// A latch construct (DoOnce or FlipFlop). `init` holds the variable
    /// assignments that precede the gate; `body` is the gated block.
    Latch {
        kind: LatchKind,
        init: Vec<Stmt>,
        body: Vec<Stmt>,
        offset: usize,
    },

    /// A return statement, with an optional return value expression.
    Return { value: Option<Expr>, offset: usize },

    /// A loop break. Emitted for a jump that exits the enclosing loop
    /// (a forward jump to the loop epilogue, or a backward jump to an
    /// active loop-break guard). Renders as `break`.
    Break { offset: usize },

    /// A cross-event call. In Blueprint, one event scheduling another is
    /// a typed call, not a goto. The decoder models it explicitly so the
    /// renderer can link to the target event's section.
    EventCall { event_name: String, offset: usize },

    /// An opcode pattern the decoder could not classify. Contains the
    /// reason, raw bytes, offset, and byte length for diagnostics. Emit
    /// renders this as a clearly-marked block so unrecognised patterns
    /// are visible without crashing the surrounding output.
    Unknown {
        reason: String,
        raw_bytes: Vec<u8>,
        offset: usize,
        length: usize,
    },
}

impl Stmt {
    /// The bytecode mem_offset where this statement begins. Every variant
    /// carries an `offset` field; synthetic statements reuse the offset of
    /// the statement they originated from.
    pub fn offset(&self) -> usize {
        match self {
            Stmt::Assignment { offset, .. }
            | Stmt::Call { offset, .. }
            | Stmt::Branch { offset, .. }
            | Stmt::Sequence { offset, .. }
            | Stmt::Loop { offset, .. }
            | Stmt::Switch { offset, .. }
            | Stmt::Latch { offset, .. }
            | Stmt::Return { offset, .. }
            | Stmt::Break { offset, .. }
            | Stmt::EventCall { offset, .. }
            | Stmt::Unknown { offset, .. } => *offset,
        }
    }

    /// The nested statement bodies this statement owns, as immutable
    /// slices: branch then/else, sequence pins, loop body/completion,
    /// switch case bodies/default, latch init/body. Leaf variants
    /// (Assignment, Call, Return, Break, EventCall, Unknown) own none.
    ///
    /// ForC init/increment sub-bodies are intentionally NOT included.
    /// Callers that walk the construct's region structure (offset
    /// collection, DoOnce scans, K2Node carry) want them excluded; the
    /// expression/rewrite walkers that must reach the loop counter's init
    /// and increment use [`child_bodies_all`](Self::child_bodies_all).
    pub fn child_bodies_structural(&self) -> Vec<&[Stmt]> {
        self.child_bodies_impl(false)
    }

    /// [`child_bodies_structural`](Self::child_bodies_structural) plus a
    /// ForC loop's `init` and `increment` sub-bodies, appended after
    /// `body`/`completion`. This is the coverage the rewrite walkers
    /// ([`walk_stmt_children`](crate::bytecode::transforms::visit::walk_stmt_children))
    /// need so the loop counter's init and increment are visited once
    /// `refine_loops` has populated them.
    pub(crate) fn child_bodies_all(&self) -> Vec<&[Stmt]> {
        self.child_bodies_impl(true)
    }

    /// Single immutable child-body skeleton behind
    /// [`child_bodies_structural`] and [`child_bodies_all`]. `include_forc`
    /// toggles only the ForC loop's init/increment slots; every other
    /// variant is independent of it. Slot order per variant is fixed and
    /// asserted by the `child_bodies_*` unit tests.
    fn child_bodies_impl(&self, include_forc: bool) -> Vec<&[Stmt]> {
        match self {
            Stmt::Branch {
                then_body,
                else_body,
                ..
            } => vec![then_body.as_slice(), else_body.as_slice()],
            Stmt::Sequence { pins, .. } => pins.iter().map(Vec::as_slice).collect(),
            Stmt::Loop {
                body,
                completion,
                kind,
                ..
            } => {
                let mut bodies = vec![body.as_slice()];
                if let Some(comp) = completion {
                    bodies.push(comp.as_slice());
                }
                if include_forc {
                    if let LoopKind::ForC { init, increment } = kind {
                        bodies.push(init.as_slice());
                        bodies.push(increment.as_slice());
                    }
                }
                bodies
            }
            Stmt::Switch { cases, default, .. } => {
                let mut bodies: Vec<&[Stmt]> =
                    cases.iter().map(|case| case.body.as_slice()).collect();
                if let Some(def) = default {
                    bodies.push(def.as_slice());
                }
                bodies
            }
            Stmt::Latch { init, body, .. } => vec![init.as_slice(), body.as_slice()],
            _ => Vec::new(),
        }
    }

    /// Mutable counterpart of [`child_bodies_structural`], for in-place
    /// rewrite recursion. Same variant coverage and the same ForC exclusion.
    pub(crate) fn child_bodies_structural_mut(&mut self) -> Vec<&mut Vec<Stmt>> {
        self.child_bodies_impl_mut(false)
    }

    /// Mutable counterpart of [`child_bodies_all`]: structural slots plus a
    /// ForC loop's init/increment.
    pub(crate) fn child_bodies_all_mut(&mut self) -> Vec<&mut Vec<Stmt>> {
        self.child_bodies_impl_mut(true)
    }

    /// Single mutable child-body skeleton behind
    /// [`child_bodies_structural_mut`] and [`child_bodies_all_mut`]. Mirrors
    /// [`child_bodies_impl`](Self::child_bodies_impl) slot-for-slot.
    fn child_bodies_impl_mut(&mut self, include_forc: bool) -> Vec<&mut Vec<Stmt>> {
        match self {
            Stmt::Branch {
                then_body,
                else_body,
                ..
            } => vec![then_body, else_body],
            Stmt::Sequence { pins, .. } => pins.iter_mut().collect(),
            Stmt::Loop {
                body,
                completion,
                kind,
                ..
            } => {
                let mut bodies = vec![body];
                if let Some(comp) = completion {
                    bodies.push(comp);
                }
                if include_forc {
                    if let LoopKind::ForC { init, increment } = kind {
                        bodies.push(init);
                        bodies.push(increment);
                    }
                }
                bodies
            }
            Stmt::Switch { cases, default, .. } => {
                let mut bodies: Vec<&mut Vec<Stmt>> =
                    cases.iter_mut().map(|case| &mut case.body).collect();
                if let Some(def) = default {
                    bodies.push(def);
                }
                bodies
            }
            Stmt::Latch { init, body, .. } => vec![init, body],
            _ => Vec::new(),
        }
    }
}

/// Discriminates the three loop shapes the decoder recognises.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub enum LoopKind {
    /// A condition-checked loop with no implicit counter or collection.
    While,

    /// A counted loop with an explicit init and increment body.
    ///
    /// `init` holds the counter-variable assignment absorbed from the
    /// statement immediately preceding the loop. It is empty (`vec![]`)
    /// when no matching predecessor was found, which produces the bare
    /// `for (;` form.
    ForC {
        init: Vec<Stmt>,
        increment: Vec<Stmt>,
    },

    /// A collection iterator. `item` is the loop variable name;
    /// `array` is the collection expression.
    ForEach { item: String, array: Expr },
}

/// Discriminates the two latch constructs Blueprint exposes.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub enum LatchKind {
    /// A DoOnce gate. `name` is the derived display name (first user
    /// call inside the body, falling back to `DoOnce_<suffix>`).
    /// `gate_var` is the underlying compiler-emitted boolean
    /// (`Temp_bool_IsClosed_Variable[_N]`); kept on the IR so a
    /// post-pass can resolve sibling `ResetDoOnce(DoOnce_N)` calls
    /// back to the matching Latch's display name.
    DoOnce { name: String, gate_var: String },

    /// A FlipFlop toggle. `gate_var` is the internal boolean variable;
    /// `names` holds the (A-side label, B-side label) pair when resolved.
    FlipFlop {
        gate_var: String,
        names: Option<(String, String)>,
    },
}

/// One arm of a `Stmt::Switch`. Multiple case values map to a single
/// shared body, mirroring the editor graph shape where pin values like
/// Walking/Running/Swimming all wire to one downstream branch.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct SwitchCase {
    pub values: Vec<Expr>,
    pub body: Vec<Stmt>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A one-statement sub-body tagged by its `Break` offset, so a test can
    /// identify which slot a `child_bodies_*` entry came from by its offset.
    fn marker(offset: usize) -> Vec<Stmt> {
        vec![Stmt::Break { offset }]
    }

    fn first_offsets(bodies: &[&[Stmt]]) -> Vec<usize> {
        bodies.iter().map(|body| body[0].offset()).collect()
    }

    fn forc_loop() -> Stmt {
        Stmt::Loop {
            kind: LoopKind::ForC {
                init: marker(3),
                increment: marker(4),
            },
            cond: None,
            body: marker(1),
            completion: Some(marker(2)),
            offset: 0,
        }
    }

    #[test]
    fn structural_excludes_forc_init_increment() {
        assert_eq!(
            first_offsets(&forc_loop().child_bodies_structural()),
            vec![1, 2]
        );
    }

    #[test]
    fn all_appends_forc_init_then_increment_after_body_and_completion() {
        assert_eq!(
            first_offsets(&forc_loop().child_bodies_all()),
            vec![1, 2, 3, 4]
        );
    }

    #[test]
    fn branch_yields_then_then_else_with_no_forc_difference() {
        let branch = Stmt::Branch {
            cond: Expr::Literal("true".to_string()),
            then_body: marker(1),
            else_body: marker(2),
            offset: 0,
        };
        assert_eq!(first_offsets(&branch.child_bodies_structural()), vec![1, 2]);
        assert_eq!(first_offsets(&branch.child_bodies_all()), vec![1, 2]);
    }

    #[test]
    fn latch_yields_init_then_body() {
        let latch = Stmt::Latch {
            kind: LatchKind::DoOnce {
                name: "DoOnce_0".to_string(),
                gate_var: "g".to_string(),
            },
            init: marker(1),
            body: marker(2),
            offset: 0,
        };
        assert_eq!(first_offsets(&latch.child_bodies_structural()), vec![1, 2]);
    }

    #[test]
    fn switch_yields_cases_in_order_then_default() {
        let switch = Stmt::Switch {
            expr: Expr::Var("x".to_string()),
            cases: vec![
                SwitchCase {
                    values: vec![Expr::Literal("0".to_string())],
                    body: marker(1),
                },
                SwitchCase {
                    values: vec![Expr::Literal("1".to_string())],
                    body: marker(2),
                },
            ],
            default: Some(marker(3)),
            offset: 0,
        };
        assert_eq!(
            first_offsets(&switch.child_bodies_structural()),
            vec![1, 2, 3]
        );
    }

    #[test]
    fn sequence_yields_pins_in_order() {
        let sequence = Stmt::Sequence {
            pins: vec![marker(1), marker(2), marker(3)],
            offset: 0,
        };
        assert_eq!(
            first_offsets(&sequence.child_bodies_structural()),
            vec![1, 2, 3]
        );
    }

    #[test]
    fn leaf_variants_own_no_child_bodies() {
        let leaf = Stmt::Return {
            value: None,
            offset: 0,
        };
        assert!(leaf.child_bodies_structural().is_empty());
        assert!(leaf.child_bodies_all().is_empty());
    }

    #[test]
    fn mutable_skeletons_match_immutable_slot_order() {
        let all: Vec<usize> = forc_loop()
            .child_bodies_all_mut()
            .iter()
            .map(|body| body[0].offset())
            .collect();
        assert_eq!(all, vec![1, 2, 3, 4]);

        let structural: Vec<usize> = forc_loop()
            .child_bodies_structural_mut()
            .iter()
            .map(|body| body[0].offset())
            .collect();
        assert_eq!(structural, vec![1, 2]);
    }
}
