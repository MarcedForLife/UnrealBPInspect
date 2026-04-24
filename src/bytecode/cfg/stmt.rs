//! Statement-level CFG for ubergraph event splitting: reachability from each
//! entry point, replacing older fuzzy-offset-based splitting.

use std::collections::{HashSet, VecDeque};

use crate::bytecode::decode::{BcStatement, StmtKind};
use crate::bytecode::{OffsetMap, STRUCTURE_OFFSET_TOLERANCE};

/// Control flow graph mapping each statement index to its successor indices.
pub struct StmtCfg {
    pub successors: Vec<Vec<usize>>,
}

/// Build a statement-level CFG. Terminal statements (pop_flow, return,
/// computed jumps) have no successors, which stops reachability walks at
/// event boundaries.
pub fn build_stmt_cfg(stmts: &[BcStatement], offset_map: &OffsetMap) -> StmtCfg {
    let stmt_count = stmts.len();
    let successors: Vec<Vec<usize>> = stmts
        .iter()
        .enumerate()
        .map(|(idx, stmt)| {
            match stmt.kind {
                StmtKind::PopFlow
                | StmtKind::ReturnNop
                | StmtKind::BareReturn
                | StmtKind::JumpComputed => return Vec::new(),
                _ => {}
            }
            if stmt.text.starts_with("return ") {
                return Vec::new();
            }

            if let Some(target_offset) = stmt.jump_target() {
                if let Some(target_idx) =
                    offset_map.find_fuzzy_forward(target_offset, STRUCTURE_OFFSET_TOLERANCE)
                {
                    return vec![target_idx];
                }
                return Vec::new();
            }

            if let Some((_cond, target_offset)) = stmt.if_jump() {
                let mut succs = Vec::with_capacity(2);
                let fallthrough = idx + 1;
                if fallthrough < stmt_count {
                    succs.push(fallthrough);
                }
                if let Some(target_idx) =
                    offset_map.find_fuzzy_forward(target_offset, STRUCTURE_OFFSET_TOLERANCE)
                {
                    if !succs.contains(&target_idx) {
                        succs.push(target_idx);
                    }
                }
                return succs;
            }

            // push_flow: fallthrough + pushed resume address (reached later via pop_flow).
            if let Some(resume_offset) = stmt.push_flow_target() {
                let mut succs = Vec::with_capacity(2);
                let fallthrough = idx + 1;
                if fallthrough < stmt_count {
                    succs.push(fallthrough);
                }
                if let Some(resume_idx) =
                    offset_map.find_fuzzy_forward(resume_offset, STRUCTURE_OFFSET_TOLERANCE)
                {
                    if !succs.contains(&resume_idx) {
                        succs.push(resume_idx);
                    }
                }
                return succs;
            }

            // pop_flow_if_not: fallthrough only (pop side isn't statically resolvable).
            if stmt.pop_flow_if_not_cond().is_some() {
                let fallthrough = idx + 1;
                if fallthrough < stmt_count {
                    return vec![fallthrough];
                }
                return Vec::new();
            }

            let fallthrough = idx + 1;
            if fallthrough < stmt_count {
                vec![fallthrough]
            } else {
                Vec::new()
            }
        })
        .collect();

    StmtCfg { successors }
}

/// One event's statements: name, entry index, and owned indices.
///
/// Unreachable statements (latent resume code that only runs via pop_flow
/// from a pushed address) are collected into an unnamed partition returned
/// first.
pub struct EventPartition {
    pub name: String,
    /// Global entry-statement index. `None` for latent-resume groups.
    pub entry_idx: Option<usize>,
    pub indices: Vec<usize>,
}

pub fn partition_by_reachability(
    cfg: &StmtCfg,
    stmts: &[BcStatement],
    labels: &[(usize, &String)],
    offset_map: &OffsetMap,
) -> Vec<EventPartition> {
    let mut sorted_labels: Vec<(usize, &String)> = labels.to_vec();
    sorted_labels.sort_by_key(|(offset, _)| *offset);

    let entry_points: Vec<(usize, &str)> = sorted_labels
        .iter()
        .filter_map(|&(offset, name)| {
            offset_map
                .find_fuzzy_forward(offset, STRUCTURE_OFFSET_TOLERANCE)
                .map(|idx| (idx, name.as_str()))
        })
        .collect();

    // Independent BFS per event: shared code (DoOnce bodies, trampolines)
    // appears in every partition that reaches it so each event is self-contained.
    let mut event_reachable: Vec<HashSet<usize>> = Vec::with_capacity(entry_points.len());

    for &(entry_idx, _name) in &entry_points {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(entry_idx);

        while let Some(stmt_idx) = queue.pop_front() {
            if stmt_idx >= stmts.len() || !visited.insert(stmt_idx) {
                continue;
            }
            for &succ in &cfg.successors[stmt_idx] {
                if succ < stmts.len() && !visited.contains(&succ) {
                    queue.push_back(succ);
                }
            }
        }
        event_reachable.push(visited);
    }

    let any_reached: HashSet<usize> = event_reachable
        .iter()
        .flat_map(|s| s.iter().copied())
        .collect();
    let unreachable_indices: Vec<usize> = (0..stmts.len())
        .filter(|idx| !any_reached.contains(idx))
        .collect();

    let mut result: Vec<EventPartition> = Vec::new();

    // Latent-resume (unreachable) statements come first.
    if !unreachable_indices.is_empty() {
        result.push(EventPartition {
            name: String::new(),
            entry_idx: None,
            indices: unreachable_indices,
        });
    }

    for (event_idx, &(entry_idx, name)) in entry_points.iter().enumerate() {
        let mut indices: Vec<usize> = event_reachable[event_idx].iter().copied().collect();
        indices.sort();
        result.push(EventPartition {
            name: name.to_string(),
            entry_idx: Some(entry_idx),
            indices,
        });
    }

    result
}

/// Extract statements for one event partition, preserving original order.
pub fn extract_partition_stmts(stmts: &[BcStatement], indices: &[usize]) -> Vec<BcStatement> {
    indices
        .iter()
        .filter_map(|&idx| stmts.get(idx).cloned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stmt(offset: usize, text: &str) -> BcStatement {
        BcStatement::new(offset, text.to_string())
    }

    #[test]
    fn pop_flow_is_terminal() {
        let stmts = vec![
            stmt(100, "DoThing()"),
            stmt(110, "pop_flow"),
            stmt(120, "OtherEvent()"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        assert_eq!(cfg.successors[0], vec![1]);
        assert!(cfg.successors[1].is_empty());
        assert!(cfg.successors[2].is_empty());
    }

    #[test]
    fn unconditional_jump_single_successor() {
        let stmts = vec![
            stmt(100, "jump 0x78"),
            stmt(110, "unreachable"),
            stmt(120, "target"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        assert_eq!(cfg.successors[0], vec![2]); // jumps to offset 0x78 = 120
    }

    #[test]
    fn conditional_jump_two_successors() {
        let stmts = vec![
            stmt(100, "if !(cond) jump 0x78"),
            stmt(110, "true_branch"),
            stmt(120, "target"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        assert_eq!(cfg.successors[0].len(), 2);
        assert!(cfg.successors[0].contains(&1)); // fallthrough
        assert!(cfg.successors[0].contains(&2)); // jump target
    }

    #[test]
    fn push_flow_includes_resume_address() {
        let stmts = vec![
            stmt(100, "push_flow 0x78"),
            stmt(110, "body"),
            stmt(120, "resume_target"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        assert_eq!(cfg.successors[0].len(), 2);
        assert!(cfg.successors[0].contains(&1)); // fallthrough
        assert!(cfg.successors[0].contains(&2)); // resume at 0x78 = 120
    }

    #[test]
    fn partition_separates_events() {
        let stmts = vec![
            stmt(100, "EventA_body"),
            stmt(110, "pop_flow"),
            stmt(120, "EventB_body"),
            stmt(130, "pop_flow"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event_a = "EventA".to_string();
        let event_b = "EventB".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event_a), (120, &event_b)];

        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        assert_eq!(partitions.len(), 2);
        assert_eq!(partitions[0].name, "EventA");
        assert_eq!(partitions[0].indices, vec![0, 1]);
        assert_eq!(partitions[1].name, "EventB");
        assert_eq!(partitions[1].indices, vec![2, 3]);
    }

    #[test]
    fn unreachable_stmts_collected_separately() {
        // Latent resume code before first event entry
        let stmts = vec![
            stmt(50, "latent_code"),
            stmt(60, "return nop"),
            stmt(100, "EventA_body"),
            stmt(110, "pop_flow"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event_a = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event_a)];

        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        assert_eq!(partitions.len(), 2);
        assert_eq!(partitions[0].name, ""); // unnamed latent resume
        assert_eq!(partitions[0].indices, vec![0, 1]);
        assert_eq!(partitions[1].name, "EventA");
        assert_eq!(partitions[1].indices, vec![2, 3]);
    }

    #[test]
    fn shared_code_duplicated_across_events() {
        // Both events reach the same shared code, both get it in their partition
        let stmts = vec![
            stmt(100, "jump 0x96"), // EventA jumps to shared
            stmt(110, "jump 0x96"), // EventB jumps to shared
            stmt(150, "shared_code"),
            stmt(160, "pop_flow"),
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event_a = "EventA".to_string();
        let event_b = "EventB".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event_a), (110, &event_b)];

        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        let event_a_part = partitions.iter().find(|p| p.name == "EventA").unwrap();
        assert!(event_a_part.indices.contains(&2)); // shared_code in EventA
        assert!(event_a_part.indices.contains(&3)); // pop_flow in EventA

        let event_b_part = partitions.iter().find(|p| p.name == "EventB").unwrap();
        assert!(event_b_part.indices.contains(&2)); // shared_code ALSO in EventB
        assert!(event_b_part.indices.contains(&3)); // pop_flow ALSO in EventB
    }

    #[test]
    fn push_flow_bridges_past_latch_pop_flow() {
        // Simulates a Sequence pin wrapping a latch block. push_flow creates
        // an edge to RESUME, so BFS reaches post-latch code even though the
        // latch body ends with a terminal pop_flow.
        let stmts = vec![
            stmt(100, "push_flow 0xb4"), // Sequence pin: resume at 180
            stmt(110, "jump 0x78"),      // jump to latch body
            stmt(120, "LatchBody()"),    // latch body code
            stmt(130, "pop_flow"),       // latch body end (terminal)
            stmt(180, "AfterLatch()"),   // RESUME from push_flow
            stmt(190, "pop_flow"),       // event boundary
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event)];
        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        let part = partitions.iter().find(|p| p.name == "EventA").unwrap();
        assert!(
            part.indices.contains(&4),
            "BFS should reach AfterLatch via push_flow resume edge"
        );
        assert!(
            part.indices.contains(&2),
            "BFS should reach LatchBody via jump"
        );
    }

    #[test]
    fn gate_check_reaches_past_body() {
        // DoOnce gate check without push_flow wrapper. The if-jump creates
        // a CFG edge to PAST_BODY, bypassing the body-end pop_flow.
        let stmts = vec![
            stmt(100, "if !(gate) jump 0x96"), // gate check -> past body
            stmt(110, "pop_flow"),             // closed-gate exit
            stmt(120, "gate = true"),          // close gate
            stmt(130, "DoOnceBody()"),         // body
            stmt(140, "pop_flow"),             // body end
            stmt(150, "AfterDoOnce()"),        // past body
            stmt(160, "pop_flow"),             // event boundary
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(100, &event)];
        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        let part = partitions.iter().find(|p| p.name == "EventA").unwrap();
        assert!(
            part.indices.contains(&5),
            "BFS should reach AfterDoOnce via gate check jump edge"
        );
    }

    #[test]
    fn backward_init_body_reachable() {
        // Layout A: init body at lower offset, reached via backward jump
        // from the init check. BFS should include it in the event partition.
        let stmts = vec![
            stmt(80, "InitVar = true"), // init body
            stmt(90, "pop_flow_if_not(false)"),
            stmt(100, "GateVar = true"),
            stmt(110, "pop_flow"),                // init body end
            stmt(120, "if !(InitVar) jump 0x50"), // init check -> backward
            stmt(130, "pop_flow"),                // already initialized
            stmt(140, "if !(GateVar) jump 0xa0"), // gate check
            stmt(150, "pop_flow"),                // closed gate
            stmt(160, "pop_flow"),                // event boundary
        ];
        let offset_map = OffsetMap::build(&stmts);
        let cfg = build_stmt_cfg(&stmts, &offset_map);

        let event = "EventA".to_string();
        let labels: Vec<(usize, &String)> = vec![(120, &event)];
        let partitions = partition_by_reachability(&cfg, &stmts, &labels, &offset_map);

        let part = partitions.iter().find(|p| p.name == "EventA").unwrap();
        assert!(
            part.indices.contains(&0),
            "BFS should reach init body via backward jump from init check"
        );
    }
}
