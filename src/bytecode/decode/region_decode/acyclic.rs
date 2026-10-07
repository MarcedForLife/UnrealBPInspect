//! Structured decoding of acyclic paths and bounded flow-stack states.

use super::*;
use crate::bytecode::cfg::dom::DomChain;

/// Acyclic function bodies need no byte-range ownership heuristics. A join
/// belongs after a branch only when every path reaches it. Shared blocks
/// reached by selected subpaths remain inside those paths, even if that
/// requires representing the same block in more than one branch arm.
pub(super) fn decode_acyclic_body(
    cfg: &ControlFlowGraph,
    context: &DecodeCtx,
) -> Option<Vec<Stmt>> {
    if context.event_entries.is_some()
        || context.cross_event_inline.is_some()
        || context.owned_ranges.is_some()
    {
        return None;
    }
    let expanded = if cfg
        .blocks
        .iter()
        .flat_map(|block| &block.opcodes)
        .any(|offset| {
            matches!(
                context.bytecode.get(*offset),
                Some(&EX_PUSH_EXECUTION_FLOW) | Some(&EX_POP_FLOW_IF_NOT)
            )
        }) {
        Some(expand_flow_stack(cfg, context)?)
    } else {
        None
    };
    let empty_continuations = BTreeMap::new();
    let (cfg, continuations) = expanded
        .as_ref()
        .map(|(graph, continuations)| (graph, continuations))
        .unwrap_or((cfg, &empty_continuations));
    if !acyclic_blocks(cfg, context) {
        return None;
    }
    let postdominators = crate::bytecode::cfg::dom::compute_postdominators(cfg);
    let mut budget = cfg.blocks.len().saturating_mul(32);
    decode_acyclic_path(
        (cfg.entry, cfg.sink, 0),
        cfg,
        context,
        &postdominators,
        continuations,
        &mut budget,
    )
}

fn acyclic_blocks(cfg: &ControlFlowGraph, context: &DecodeCtx) -> bool {
    let mut incoming = BTreeMap::new();
    for block in &cfg.blocks {
        let Some(successors) = cfg.successors.get(&block.id) else {
            return false;
        };
        if successors.len() > 2 {
            return false;
        }
        for (index, offset) in block.opcodes.iter().enumerate() {
            let Some(opcode) = context.bytecode.get(*offset) else {
                return false;
            };
            if matches!(
                *opcode,
                EX_PUSH_EXECUTION_FLOW | crate::bytecode::opcodes::EX_POP_EXECUTION_FLOW
            ) {
                return false;
            }
            if matches!(
                *opcode,
                EX_JUMP | EX_JUMP_IF_NOT | EX_POP_FLOW_IF_NOT | EX_RETURN | EX_END_OF_SCRIPT
            ) && index + 1 != block.opcodes.len()
            {
                return false;
            }
        }
        let conditional = matches!(
            block
                .opcodes
                .last()
                .and_then(|offset| context.bytecode.get(*offset)),
            Some(&EX_JUMP_IF_NOT) | Some(&EX_POP_FLOW_IF_NOT)
        );
        if conditional != (successors.len() == 2) {
            return false;
        }
        incoming.insert(
            block.id,
            cfg.predecessors.get(&block.id).map_or(0, Vec::len),
        );
    }
    let mut ready: VecDeque<_> = incoming
        .iter()
        .filter_map(|(block, count)| (*count == 0).then_some(*block))
        .collect();
    let mut visited = 0;
    while let Some(block) = ready.pop_front() {
        visited += 1;
        for next in &cfg.successors[&block] {
            let Some(count) = incoming.get_mut(next) else {
                return false;
            };
            let Some(remaining) = count.checked_sub(1) else {
                return false;
            };
            *count = remaining;
            if remaining == 0 {
                ready.push_back(*next);
            }
        }
    }
    visited == cfg.blocks.len()
}

fn decode_acyclic_path(
    (start, stop, depth): (BlockId, BlockId, usize),
    cfg: &ControlFlowGraph,
    context: &DecodeCtx,
    postdominators: &BTreeMap<BlockId, BlockId>,
    continuations: &BTreeMap<BlockId, BlockId>,
    budget: &mut usize,
) -> Option<Vec<Stmt>> {
    if depth >= 128 {
        return None;
    }
    let mut output = Vec::new();
    let mut current = start;
    while current != stop && current != cfg.sink {
        *budget = budget.checked_sub(1)?;
        let block = cfg.blocks.get(current)?;
        let successors = cfg.successors.get(&current)?;
        if let Some(resume) = continuations.get(&current) {
            let first = decode_acyclic_path(
                (successors[0], *resume, depth + 1),
                cfg,
                context,
                postdominators,
                continuations,
                budget,
            )?;
            let remainder = decode_acyclic_path(
                (*resume, stop, depth + 1),
                cfg,
                context,
                postdominators,
                continuations,
                budget,
            )?;
            let chain = context.skeleton.and_then(|skeleton| {
                skeleton
                    .push_chains
                    .values()
                    .filter(|chain| chain.head <= block.start && block.start < chain.after_chain)
                    .max_by_key(|chain| chain.head)
            });
            if let Some(chain) = chain {
                let mut pins = Vec::new();
                for pin in [first, remainder] {
                    match pin.as_slice() {
                        [Stmt::Sequence {
                            pins: nested,
                            offset,
                        }] if chain.head <= *offset && *offset < chain.after_chain => {
                            pins.extend(nested.clone())
                        }
                        _ => pins.push(pin),
                    }
                }
                output.push(Stmt::Sequence {
                    pins,
                    offset: block.start,
                });
            } else {
                // A function's return continuation also uses PUSH, but is not
                // an editor Sequence. Keep its statements in execution order.
                output.extend(first);
                output.extend(remainder);
            }
            return Some(output);
        }
        let mut branch = None;
        for offset in &block.opcodes {
            match context.bytecode.get(*offset)? {
                &EX_JUMP => {}
                &EX_JUMP_IF_NOT | &EX_POP_FLOW_IF_NOT => {
                    let cond = if context.bytecode[*offset] == EX_JUMP_IF_NOT {
                        decode_jin_cond(*offset, context)?
                    } else {
                        let mut cursor = offset + 1;
                        decode_expr(&mut cursor, context)
                    };
                    let mut join = *postdominators.get(&current)?;
                    if DomChain(postdominators)
                        .ancestors(stop)
                        .any(|ancestor| ancestor == join)
                    {
                        join = stop;
                    }
                    let then_body = decode_acyclic_path(
                        (successors[1], join, depth + 1),
                        cfg,
                        context,
                        postdominators,
                        continuations,
                        budget,
                    )?;
                    let else_body = decode_acyclic_path(
                        (successors[0], join, depth + 1),
                        cfg,
                        context,
                        postdominators,
                        continuations,
                        budget,
                    )?;
                    output.push(Stmt::Branch {
                        cond,
                        then_body,
                        else_body,
                        offset: *offset,
                    });
                    branch = Some(join);
                }
                _ => {
                    let mut cursor = *offset;
                    match super::super::block::decode_one(&mut cursor, context) {
                        Ok(Some(stmt)) => output.push(stmt),
                        Ok(None) => {}
                        Err(unknown) => output.push(*unknown),
                    }
                    if cursor > block.end {
                        return None;
                    }
                }
            }
        }
        current = branch
            .or_else(|| successors.first().copied())
            .unwrap_or(cfg.sink);
    }
    Some(output)
}

/// Split flow-stack control at opcode boundaries before finding joins.
/// Ordinary CFG resume edges conflate callers and can give a sequence pin
/// another pin's continuation. The existing VM transition helper keeps the
/// complete pending stack in each state instead.
fn expand_flow_stack(
    cfg: &ControlFlowGraph,
    context: &DecodeCtx,
) -> Option<(ControlFlowGraph, BTreeMap<BlockId, BlockId>)> {
    use crate::bytecode::opcodes::EX_POP_EXECUTION_FLOW;
    let graph = context.graph?;
    // Preserve the dedicated Sequence presentation when there is no branch.
    if !graph
        .opcodes
        .values()
        .any(|opcode| matches!(*opcode, EX_JUMP_IF_NOT | EX_POP_FLOW_IF_NOT))
    {
        return None;
    }
    let start = cfg.blocks.get(cfg.entry)?.start;
    let mut states = vec![(start, Vec::<usize>::new())];
    let mut identifiers = BTreeMap::from([((start, Vec::<usize>::new()), 0)]);
    let mut blocks = Vec::new();
    let mut successors = BTreeMap::new();
    let mut pending_continuations = BTreeMap::new();
    let max_states = graph.boundaries.len().saturating_mul(16).min(4096);
    let mut index = 0;
    while index < states.len() {
        if states.len() > max_states {
            return None;
        }
        let (offset, stack) = states[index].clone();
        if stack.len() > 64 {
            return None;
        }
        let opcode = *graph.opcodes.get(&offset)?;
        let length = crate::bytecode::partition::opcode_length_at(
            offset,
            context.bytecode,
            context.ue5,
            context.name_table,
        );
        if length == 0 || offset.checked_add(length)? > context.bytecode.len() {
            return None;
        }
        if opcode == EX_PUSH_EXECUTION_FLOW {
            let target = *graph.successors.get(&offset)?.first()?;
            pending_continuations.insert(index, (target, stack.clone()));
        }
        let mut next = VecDeque::new();
        if !matches!(opcode, EX_RETURN | EX_END_OF_SCRIPT) {
            crate::bytecode::partition::step_successors(
                offset,
                opcode,
                &stack,
                graph,
                0,
                &|_, target, pending, queue| queue.push_back((target, pending.to_vec())),
                &mut next,
            );
        }
        let mut edges = Vec::new();
        for state in next {
            if !graph.boundaries.contains(&state.0) {
                return None;
            }
            let next_id = if let Some(identifier) = identifiers.get(&state) {
                *identifier
            } else {
                let identifier = states.len();
                identifiers.insert(state.clone(), identifier);
                states.push(state);
                identifier
            };
            edges.push(next_id);
        }
        if opcode == EX_POP_FLOW_IF_NOT {
            // step_successors yields fallthrough first, conditional pop last.
            // An empty stack exits the function on the false path.
            if stack.is_empty() {
                edges.push(usize::MAX);
            }
            if edges.len() != 2 {
                return None;
            }
            edges.reverse();
        }
        if edges.is_empty() {
            edges.push(usize::MAX);
        }
        successors.insert(index, edges);
        blocks.push(BasicBlock {
            id: index,
            start: offset,
            end: offset + length,
            opcodes: if matches!(opcode, EX_PUSH_EXECUTION_FLOW | EX_POP_EXECUTION_FLOW) {
                vec![]
            } else {
                vec![offset]
            },
        });
        index += 1;
    }
    let sink = blocks.len();
    blocks.push(BasicBlock {
        id: sink,
        start: context.bytecode.len(),
        end: context.bytecode.len(),
        opcodes: vec![],
    });
    successors.insert(sink, vec![]);
    let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> =
        (0..=sink).map(|index| (index, vec![])).collect();
    for (source, edges) in &mut successors {
        for target in edges {
            if *target == usize::MAX {
                *target = sink;
            }
            predecessors.get_mut(target)?.push(*source);
        }
    }
    let continuations = pending_continuations
        .into_iter()
        .map(|(block, state)| (block, identifiers.get(&state).copied().unwrap_or(sink)))
        .collect();
    Some((
        ControlFlowGraph {
            blocks,
            successors,
            predecessors,
            entry: 0,
            sink,
        },
        continuations,
    ))
}
