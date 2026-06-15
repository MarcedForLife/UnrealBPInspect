//! Control-flow recognition for the bytecode decoder.
//!
//! Recognises four shapes that all reduce to a recursive
//! subrange-decode helper plus a target-classifier:
//!
//! 1. **Classic if/else** — `EX_JUMP_IF_NOT cond target=A`
//!    followed by an inline then-body that ends in `EX_JUMP target=B`.
//!    Else-body lives at A, post-construct resumes at B.
//!
//! 2. **IsValid macro** — `EX_JUMP_IF_NOT cond target=A`
//!    immediately followed by `EX_JUMP target=B` so both branches are
//!    displaced. Then-body decodes from B, else-body from A.
//!
//! 3. **Displaced-else** — Variant of the classic if/else where the inline
//!    then-body's terminating `EX_JUMP` points past the else target.
//!    The classic if/else handler's recursive shape covers this without a
//!    separate handler.
//!
//! 4. **Cross-event jumps** — `EX_JUMP target=X` where X is
//!    another event's entry mem_offset. Emits `Stmt::EventCall` instead
//!    of treating the jump as intra-event control flow.
//!
//! The decoder receives the partition's range bounds and never decodes
//! past `range.end`. Jump targets are written in memory coordinates;
//! `DecodeCtx::mem_to_disk` translates them to slice indices before
//! recursion.

mod disjoint;
mod inline_shared;
mod layout;
mod subrange;
mod tail_jin;
mod target;

pub(crate) use disjoint::decode_jump;
pub(crate) use layout::decode_branch;
pub(crate) use subrange::{decode_subrange, decode_subrange_excluding};
pub(crate) use tail_jin::{region_arm_extents, tail_jin_arm_ranges};

// Branch-decoder surface kept reachable as `branch::X` for consumers and the
// `branch_tests` glob. These re-exports are not all named outside this module
// today; the allow preserves the facade without a dead-import warning.
#[allow(unused_imports)]
pub(crate) use disjoint::{disjoint_else_arm_for_jin, disjoint_jump_target_extent};
#[allow(unused_imports)]
pub(crate) use layout::{isvalid_else_body_end, BranchDecode};
#[allow(unused_imports)]
pub(crate) use tail_jin::TailJinArms;
#[allow(unused_imports)]
pub(crate) use target::{
    classify_target, event_scan_end, peek_jump_after_instrumentation, peek_jump_at,
    read_jump_target, JumpTarget,
};
