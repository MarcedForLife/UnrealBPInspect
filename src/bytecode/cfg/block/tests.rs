use std::collections::HashSet;

use crate::bytecode::decode::BcStatement;
use crate::bytecode::OffsetMap;

use super::analysis::{blocks_reachable_avoiding, find_convergence_target};
use super::types::{Block, BlockCfg, BlockExit, BlockId, BlockMetadata};

fn cfg_from(items: &[(usize, &str)]) -> (Vec<BcStatement>, BlockCfg) {
    let stmts: Vec<BcStatement> = items
        .iter()
        .map(|(off, t)| BcStatement::new(*off, t.to_string()))
        .collect();
    let offset_map = OffsetMap::build(&stmts);
    let cfg = BlockCfg::build(&stmts, &offset_map);
    (stmts, cfg)
}

#[test]
fn build_splits_at_jump_and_target() {
    // Three blocks: [before if-jump], [fall-through body], [jump target]
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "a = 1"),
        (0x14, "if !(cond) jump 0x20"),
        (0x18, "b = 2"),
        (0x20, "c = 3"),
    ]);
    assert_eq!(cfg.blocks.len(), 3);
    assert_eq!(cfg.blocks[0].stmt_range, 0..2);
    assert_eq!(cfg.blocks[1].stmt_range, 2..3);
    assert_eq!(cfg.blocks[2].stmt_range, 3..4);
    assert!(matches!(
        cfg.blocks[0].exit,
        BlockExit::CondJump {
            fall_through: 1,
            target: 2
        }
    ));
    assert!(matches!(cfg.blocks[1].exit, BlockExit::FallThrough));
    assert!(matches!(cfg.blocks[2].exit, BlockExit::FallThrough));
}

#[test]
fn build_marks_return_as_terminal() {
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "a = 1"),
        (0x14, "return nop"),
        (0x18, "b = 2"), // unreachable but still a block
    ]);
    assert_eq!(cfg.blocks.len(), 2);
    assert!(matches!(cfg.blocks[0].exit, BlockExit::ReturnTerminal));
}

#[test]
fn compute_in_degree_counts_all_edges() {
    // if !(cond) jump 0x20    -> ft=block1, target=block2
    //   block1: fall through  -> block2
    //   block2: convergence target (in_degree 2)
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(cond) jump 0x18"),
        (0x14, "a = 1"),
        (0x18, "b = 2"),
    ]);
    let deg = cfg.compute_in_degree();
    assert_eq!(deg.len(), 3);
    assert_eq!(deg[0], 0);
    assert_eq!(deg[1], 1); // fall-through from block 0
    assert_eq!(deg[2], 2); // both ft from block 1 and jump target from block 0
}

#[test]
fn compute_predecessors_lists_all_sources() {
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(cond) jump 0x18"),
        (0x14, "a = 1"),
        (0x18, "b = 2"),
    ]);
    let preds = cfg.compute_predecessors();
    assert_eq!(preds[0], Vec::<BlockId>::new());
    assert_eq!(preds[1], vec![0]);
    // block 2 has two predecessors: block 0 (via CondJump target) and block 1 (fall-through)
    let mut p2 = preds[2].clone();
    p2.sort();
    assert_eq!(p2, vec![0, 1]);
}

#[test]
fn find_convergence_target_returns_shared_exit() {
    // Both branches jump to a shared convergence block:
    //   block0: if !(cond) jump 0x18  (CondJump ft=1, target=2)
    //   block1: a = 1; jump 0x20
    //   block2: b = 2; jump 0x20
    //   block3: c = 3                 (convergence, in-degree 2)
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(cond) jump 0x18"),
        (0x14, "a = 1"),
        (0x15, "jump 0x20"),
        (0x18, "b = 2"),
        (0x19, "jump 0x20"),
        (0x20, "c = 3"),
    ]);
    assert!(matches!(
        cfg.blocks[0].exit,
        BlockExit::CondJump {
            fall_through: 1,
            target: 2
        }
    ));
    let conv = find_convergence_target(&cfg.blocks, 1, 2);
    assert_eq!(conv, Some(3));
}

#[test]
fn find_convergence_target_none_when_branch_returns() {
    // One branch ends in `return nop` -- there is no local convergence
    // because that side of the if exits the function entirely. The
    // defensive filter must reject the trailing block even though it
    // appears reachable from the other branch.
    //   block0: if !(cond) jump 0x18  (CondJump ft=1, target=2)
    //   block1: a = 1; return nop    (Terminal)
    //   block2: b = 2; jump 0x20
    //   block3: c = 3
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(cond) jump 0x18"),
        (0x14, "a = 1"),
        (0x15, "return nop"),
        (0x18, "b = 2"),
        (0x19, "jump 0x20"),
        (0x20, "c = 3"),
    ]);
    let conv = find_convergence_target(&cfg.blocks, 1, 2);
    assert_eq!(
        conv, None,
        "branch that returns has no convergence with the other branch"
    );
}

#[test]
fn find_convergence_target_none_when_both_branches_terminate() {
    // Both branches end in `return nop`. No convergence is possible
    // because execution exits the function from either side.
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(cond) jump 0x18"),
        (0x14, "a = 1"),
        (0x15, "return nop"),
        (0x18, "b = 2"),
        (0x19, "return nop"),
    ]);
    let conv = find_convergence_target(&cfg.blocks, 1, 2);
    assert_eq!(
        conv, None,
        "two terminal branches have no shared convergence"
    );
}

#[test]
fn block_exit_helpers_distinguish_return_from_latch() {
    // The helpers underpin the terminal-branch guard split: both variants
    // contribute no outgoing edges, but only ReturnTerminal blocks the
    // find_convergence_target early-return.
    assert!(BlockExit::ReturnTerminal.is_terminal());
    assert!(BlockExit::LatchTerminal.is_terminal());
    assert!(!BlockExit::FallThrough.is_terminal());

    assert!(BlockExit::ReturnTerminal.is_return());
    assert!(!BlockExit::LatchTerminal.is_return());
    assert!(!BlockExit::FallThrough.is_return());
}

/// Build a minimal [`Block`] with explicit `exit`, stmt_range 0..0
/// (unused by edge-only analyses), and default metadata.
fn synthetic_block(exit: BlockExit) -> Block {
    Block {
        stmt_range: 0..0,
        exit,
        metadata: BlockMetadata::Normal,
        emitted: false,
        push_flow_count: 0,
        return_kind: None,
    }
}

#[test]
fn find_convergence_target_allows_latch_terminal_branches() {
    // Construct a CFG manually so one branch's entry block exits via
    // LatchTerminal while a sibling pathway still Jumps into a shared
    // block. Old code guarded both Terminal variants together and
    // returned `None` here; the split lets the convergence through.
    //
    //   block0: CondJump ft=1, target=2
    //   block1: Jump(3)              (non-terminal branch entry)
    //   block2: Jump(3)              (also reaches block3)
    //   block3: LatchTerminal        (shared convergence candidate)
    //
    // Both branches contribute block3 to their Jump-target sets, so
    // the intersection picks block3. A latch-body `}` ending the
    // convergence block itself is fine: downstream passes still emit
    // the body correctly.
    let blocks = vec![
        synthetic_block(BlockExit::CondJump {
            fall_through: 1,
            target: 2,
        }),
        synthetic_block(BlockExit::Jump(3)),
        synthetic_block(BlockExit::Jump(3)),
        synthetic_block(BlockExit::LatchTerminal),
    ];

    let conv = find_convergence_target(&blocks, 1, 2);
    assert_eq!(
        conv,
        Some(3),
        "LatchTerminal convergence target must be detected"
    );

    // Sanity check: if block3 were ReturnTerminal, that wouldn't change
    // the convergence outcome on its own (the guard checks the branch
    // entries, not the convergence block itself).
    let mut with_return_conv = blocks.clone();
    with_return_conv[3].exit = BlockExit::ReturnTerminal;
    let conv = find_convergence_target(&with_return_conv, 1, 2);
    assert_eq!(
        conv,
        Some(3),
        "convergence block's own exit variant doesn't affect the guard"
    );

    // But if one BRANCH ENTRY is ReturnTerminal, the guard fires and
    // returns None. The old code would also fire for LatchTerminal here.
    let mut with_return_branch = blocks.clone();
    with_return_branch[1].exit = BlockExit::ReturnTerminal;
    let conv = find_convergence_target(&with_return_branch, 1, 2);
    assert_eq!(
        conv, None,
        "ReturnTerminal branch entry blocks convergence detection"
    );

    // Swap in LatchTerminal on the branch entry and the guard no longer
    // fires. The entry has no outgoing edges so the intersection is
    // empty and we still get None, but for the different structural
    // reason (no reachable convergence, not a hard-coded guard).
    let mut with_latch_branch = blocks;
    with_latch_branch[1].exit = BlockExit::LatchTerminal;
    let conv = find_convergence_target(&with_latch_branch, 1, 2);
    assert_eq!(
        conv, None,
        "LatchTerminal branch contributes no successors so intersection is empty"
    );
}

#[test]
fn find_convergence_target_handles_nested_convergence() {
    // Nested if/else whose branches both jump to a shared exit. The
    // non-terminal guard should NOT reject this case -- both branches
    // have non-terminal exits (Jump / CondJump) and the intersection
    // is well defined.
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "if !(x) jump 0x18"),
        (0x14, "a = 1"),
        (0x15, "jump 0x20"),
        (0x18, "if !(y) jump 0x1e"),
        (0x1a, "b = 2"),
        (0x1b, "jump 0x20"),
        (0x1e, "c = 3"),
        (0x1f, "jump 0x20"),
        (0x20, "conv()"),
    ]);
    let conv = find_convergence_target(&cfg.blocks, 1, 2);
    assert!(conv.is_some(), "should detect nested convergence");
}

#[test]
fn doonce_body_is_terminal_and_tagged() {
    // DoOnce body produced by transform_latch_patterns:
    //   DoOnce(Foo) {
    //     MyCall()
    //   }
    // The trailing `}` is a Terminal (no fall-through to the next stmt).
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "DoOnce(Foo) {"),
        (0x14, "MyCall()"),
        (0x18, "}"),
        (0x1c, "after = 1"),
    ]);
    // Two blocks: the DoOnce body (0..3) and the trailing statement (3..4).
    assert_eq!(cfg.blocks.len(), 2);
    assert_eq!(cfg.blocks[0].stmt_range, 0..3);
    assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
    assert_eq!(
        cfg.blocks[0].metadata,
        BlockMetadata::LatchBody {
            latch_name: "Foo".to_string(),
        }
    );
}

#[test]
fn flipflop_body_is_terminal_and_tagged() {
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "FlipFlop(Toggle) {"),
        (0x14, "HandleA()"),
        (0x18, "}"),
    ]);
    assert_eq!(cfg.blocks.len(), 1);
    assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
    assert_eq!(
        cfg.blocks[0].metadata,
        BlockMetadata::LatchBody {
            latch_name: "Toggle".to_string(),
        }
    );
}

#[test]
fn bare_brace_close_is_terminal_but_not_latch_body() {
    // Defensive: treat any `}` as LatchTerminal, even when not preceded by
    // a recognized DoOnce/FlipFlop header. Metadata stays Normal.
    let (_stmts, cfg) = cfg_from(&[(0x10, "do_something()"), (0x14, "}"), (0x18, "unrelated()")]);
    assert_eq!(cfg.blocks.len(), 2);
    assert_eq!(cfg.blocks[0].stmt_range, 0..2);
    assert!(matches!(cfg.blocks[0].exit, BlockExit::LatchTerminal));
    assert_eq!(cfg.blocks[0].metadata, BlockMetadata::Normal);
}

#[test]
fn grouped_sequence_collapses_into_super_block() {
    // Grouped (regular-function) Sequence pattern:
    //   push_flow pin0_end; push_flow pin1_end; jump pin0_body;
    //   push_flow pin2_end; jump pin1_body;
    //   inline_body_stmt; pop_flow;
    //   pin2_body_stmt; pop_flow;
    //   pin1_body_stmt; pop_flow;
    //   pin0_body_stmt; pop_flow;
    //
    // `detect_grouped_sequences` needs at least 2 push_flow/jump pairs and
    // a pop_flow terminator for the inline body. Build a minimal example
    // with two pins and verify the CFG collapses into a single super-block.
    let (_stmts, cfg) = cfg_from(&[
        (0x10, "push_flow 0x40"), // end-marker for the pair chain
        (0x14, "push_flow 0x20"), // pin0 continuation
        (0x18, "jump 0x34"),      // jump to pin0 body
        (0x1c, "push_flow 0x28"), // pin1 continuation
        (0x20, "jump 0x38"),      // jump to pin1 body
        (0x24, "inline_stmt()"),  // inline body
        (0x28, "pop_flow"),       // inline body terminator
        (0x34, "pin0_stmt()"),    // pin0 body
        (0x36, "pop_flow"),       // pin0 terminator
        (0x38, "pin1_stmt()"),    // pin1 body
        (0x3c, "pop_flow"),       // pin1 terminator
    ]);

    let super_block = cfg
        .blocks
        .iter()
        .find(|b| matches!(b.metadata, BlockMetadata::SequenceSuperBlock { .. }));
    assert!(
        super_block.is_some(),
        "expected a SequenceSuperBlock in the collapsed CFG"
    );
    let super_block = super_block.unwrap();
    // The super-block should cover the entire Sequence: from the first
    // push_flow through the last pin's terminator.
    assert_eq!(super_block.stmt_range.start, 0);
    assert_eq!(super_block.stmt_range.end, 11);
    // Super-block ends with a pin terminator (pop_flow) so its exit is ReturnTerminal.
    assert!(matches!(super_block.exit, BlockExit::ReturnTerminal));
}

#[test]
fn block_after_doonce_starts_after_close_brace() {
    // The block following a latch body must start AT the next statement,
    // not somewhere inside the DoOnce body.
    let (stmts, cfg) = cfg_from(&[
        (0x10, "DoOnce(Bar) {"),
        (0x14, "Inside()"),
        (0x18, "}"),
        (0x1c, "AfterCall()"),
        (0x20, "return nop"),
    ]);
    assert_eq!(cfg.blocks.len(), 2);
    assert_eq!(cfg.blocks[0].stmt_range, 0..3);
    assert_eq!(cfg.blocks[1].stmt_range, 3..5);
    // The next block starts on `AfterCall()`, confirming the `}` ended
    // its predecessor cleanly.
    assert_eq!(stmts[cfg.blocks[1].stmt_range.start].text, "AfterCall()");
    assert!(matches!(cfg.blocks[1].exit, BlockExit::ReturnTerminal));
    assert_eq!(
        cfg.blocks[0].metadata,
        BlockMetadata::LatchBody {
            latch_name: "Bar".to_string(),
        }
    );
}

#[test]
fn reachable_avoiding_excludes_sibling_branch() {
    // Classic if/else with shared convergence:
    //   b0: CondJump ft=b1, target=b2
    //   b1: Jump(b3)
    //   b2: Jump(b3)
    //   b3: shared convergence (ReturnTerminal to terminate)
    // From b1, avoiding b2: should reach {b1, b3}.
    // From b2, avoiding b1: should reach {b2, b3}.
    // Intersection gives b3 as the convergence, symmetric-difference is
    // empty here (nothing branch-exclusive beyond the entries).
    let blocks = vec![
        synthetic_block(BlockExit::CondJump {
            fall_through: 1,
            target: 2,
        }),
        synthetic_block(BlockExit::Jump(3)),
        synthetic_block(BlockExit::Jump(3)),
        synthetic_block(BlockExit::ReturnTerminal),
    ];
    let from_ft = blocks_reachable_avoiding(&blocks, 1, 2);
    let from_tgt = blocks_reachable_avoiding(&blocks, 2, 1);
    assert_eq!(from_ft, [1, 3].into_iter().collect::<HashSet<_>>());
    assert_eq!(from_tgt, [2, 3].into_iter().collect::<HashSet<_>>());
    let convergent: HashSet<_> = from_ft.intersection(&from_tgt).copied().collect();
    assert_eq!(convergent, [3].into_iter().collect::<HashSet<_>>());
}

#[test]
fn reachable_avoiding_identifies_branch_exclusive_blocks() {
    // Asymmetric shape: the target branch passes through an extra block
    // before converging.
    //   b0: CondJump ft=b1, target=b2
    //   b1: Jump(b4)                    <- fall-through goes straight to b4
    //   b2: FallThrough                 <- target passes through b3
    //   b3: Jump(b4)
    //   b4: ReturnTerminal
    // From b1 avoiding b2: {b1, b4}
    // From b2 avoiding b1: {b2, b3, b4}
    // b3 is target-exclusive (reachable only via the target branch).
    let blocks = vec![
        synthetic_block(BlockExit::CondJump {
            fall_through: 1,
            target: 2,
        }),
        synthetic_block(BlockExit::Jump(4)),
        synthetic_block(BlockExit::FallThrough),
        synthetic_block(BlockExit::Jump(4)),
        synthetic_block(BlockExit::ReturnTerminal),
    ];
    let from_ft = blocks_reachable_avoiding(&blocks, 1, 2);
    let from_tgt = blocks_reachable_avoiding(&blocks, 2, 1);
    let ft_only: HashSet<_> = from_ft.difference(&from_tgt).copied().collect();
    let tgt_only: HashSet<_> = from_tgt.difference(&from_ft).copied().collect();
    assert_eq!(ft_only, [1].into_iter().collect::<HashSet<_>>());
    assert_eq!(
        tgt_only,
        [2, 3].into_iter().collect::<HashSet<_>>(),
        "b3 is reachable only via the target branch"
    );
}

#[test]
fn reachable_avoiding_stops_at_avoid_and_terminals() {
    // Ensures the walk does not enter `avoid` and does not propagate
    // through terminal exits.
    //   b0: Jump(b1)
    //   b1: CondJump ft=b2, target=b3
    //   b2: ReturnTerminal
    //   b3: LatchTerminal
    let blocks = vec![
        synthetic_block(BlockExit::Jump(1)),
        synthetic_block(BlockExit::CondJump {
            fall_through: 2,
            target: 3,
        }),
        synthetic_block(BlockExit::ReturnTerminal),
        synthetic_block(BlockExit::LatchTerminal),
    ];
    // Avoid b1 entirely: we only see b0.
    let reached = blocks_reachable_avoiding(&blocks, 0, 1);
    assert_eq!(reached, [0].into_iter().collect::<HashSet<_>>());
    // No avoid (use an out-of-range id): terminals stop the walk but we
    // still see b0..b3.
    let all = blocks_reachable_avoiding(&blocks, 0, usize::MAX);
    assert_eq!(all, [0, 1, 2, 3].into_iter().collect::<HashSet<_>>());
}

#[test]
fn reachable_avoiding_handles_cycles() {
    // A backward edge in the CFG must not cause infinite recursion.
    //   b0: Jump(b1)
    //   b1: CondJump ft=b2, target=b0  (loop back)
    //   b2: ReturnTerminal
    let blocks = vec![
        synthetic_block(BlockExit::Jump(1)),
        synthetic_block(BlockExit::CondJump {
            fall_through: 2,
            target: 0,
        }),
        synthetic_block(BlockExit::ReturnTerminal),
    ];
    let reached = blocks_reachable_avoiding(&blocks, 0, usize::MAX);
    assert_eq!(reached, [0, 1, 2].into_iter().collect::<HashSet<_>>());
}

#[test]
fn reachable_avoiding_returns_empty_when_entry_is_avoid() {
    let blocks = vec![synthetic_block(BlockExit::ReturnTerminal)];
    let reached = blocks_reachable_avoiding(&blocks, 0, 0);
    assert!(reached.is_empty());
}
