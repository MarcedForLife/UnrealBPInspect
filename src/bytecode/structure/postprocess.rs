use super::super::{BARE_RETURN, BLOCK_CLOSE};
use crate::helpers::{closes_block, is_loop_header, opens_block, SECTION_SEPARATOR};
use std::collections::{HashMap, HashSet};

/// Convert `goto LABEL` to `break` (in a loop) or remove (outside a loop)
/// when the label sits near a closing brace or end-of-output. Cleans up
/// orphaned labels afterward.
pub(super) fn convert_gotos_to_breaks(output: &mut Vec<String>) {
    let break_labels = find_break_labels(output);
    if break_labels.is_empty() {
        return;
    }
    rewrite_gotos(output, &break_labels);
    remove_orphaned_labels(output, &break_labels);
}

/// A label is "break-able" when it sits right after a `}` or near EOF
/// (only blanks, returns, or braces follow).
fn find_break_labels(output: &[String]) -> HashSet<String> {
    let mut labels = HashSet::new();
    for (i, line) in output.iter().enumerate() {
        let trimmed = line.trim();
        if !trimmed.ends_with(':')
            || trimmed.starts_with(SECTION_SEPARATOR)
            || trimmed.starts_with("//")
        {
            continue;
        }
        let label = &trimmed[..trimmed.len() - 1];
        let after_brace = output[..i]
            .iter()
            .rev()
            .find(|l| !l.trim().is_empty())
            .is_some_and(|l| l.trim() == BLOCK_CLOSE);
        let near_end = output[i + 1..].iter().all(|l| {
            let trimmed = l.trim();
            trimmed.is_empty() || trimmed == BARE_RETURN || trimmed == BLOCK_CLOSE
        });
        if after_brace || near_end {
            labels.insert(label.to_string());
        }
    }
    labels
}

/// Replace `goto LABEL` with `break` or remove, via backward brace scan to
/// detect the enclosing loop.
fn rewrite_gotos(output: &mut [String], break_labels: &HashSet<String>) {
    for i in 0..output.len() {
        let trimmed = output[i].trim().to_string();
        let Some(label) = trimmed.strip_prefix("goto ") else {
            continue;
        };
        if !break_labels.contains(label) {
            continue;
        }
        // Scan backward: closing brace increases depth (we're going up).
        let in_loop = {
            let mut depth = 0i32;
            output[..i].iter().rev().any(|line| {
                let ltrim = line.trim();
                if closes_block(ltrim) {
                    depth += 1;
                }
                if opens_block(ltrim) {
                    if depth == 0 {
                        return is_loop_header(ltrim);
                    }
                    depth -= 1;
                }
                false
            })
        };
        if in_loop {
            output[i] = "break".to_string();
        } else {
            output[i] = String::new();
        }
    }
}

/// Drop empty lines from goto removal, then drop labels without remaining gotos.
fn remove_orphaned_labels(output: &mut Vec<String>, break_labels: &HashSet<String>) {
    output.retain(|line| !line.is_empty());
    let remaining_gotos: HashSet<String> = output
        .iter()
        .filter_map(|l| l.trim().strip_prefix("goto ").map(|s| s.to_string()))
        .collect();
    output.retain(|line| {
        let trimmed = line.trim();
        if trimmed.ends_with(':')
            && !trimmed.starts_with(SECTION_SEPARATOR)
            && !trimmed.starts_with("//")
        {
            let label = &trimmed[..trimmed.len() - 1];
            if break_labels.contains(label) {
                return remaining_gotos.contains(label);
            }
        }
        true
    });
}

/// Extent of convergence code starting at `code_start`: stops when a closing
/// brace exits the current scope.
fn find_convergence_extent(output: &[String], code_start: usize) -> usize {
    let mut depth = 0i32;
    let mut code_end = code_start;
    for (j, line) in output[code_start..].iter().enumerate() {
        let j = j + code_start;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            code_end = j + 1;
            continue;
        }
        if trimmed.starts_with('}') {
            depth -= 1;
            if depth < 0 {
                break;
            }
        }
        if j > code_start
            && trimmed.ends_with(':')
            && !trimmed.starts_with("//")
            && !trimmed.starts_with(SECTION_SEPARATOR)
        {
            break;
        }
        if opens_block(trimmed) {
            depth += 1;
        }
        code_end = j + 1;
    }
    code_end
}

/// Closing `}` that exits the scope containing all gotos, scanning forward
/// from after the last goto.
fn find_insertion_point(output: &[String], max_goto: usize) -> usize {
    let mut depth = 0i32;
    for (j, line) in output[(max_goto + 1)..].iter().enumerate() {
        let j = j + max_goto + 1;
        let trimmed = line.trim();
        if opens_block(trimmed) {
            depth += 1;
        }
        if closes_block(trimmed) {
            if depth == 0 {
                return j;
            }
            depth -= 1;
        }
    }
    output.len()
}

/// Remove old convergence lines and insert at the new position. Text is flat.
fn splice_convergence(
    output: &mut Vec<String>,
    label_idx: usize,
    code_range: std::ops::Range<usize>,
    goto_indices: &[usize],
    insert_pos: usize,
    conv_content: Vec<String>,
) {
    let mut to_remove: Vec<usize> = Vec::new();
    to_remove.push(label_idx);
    to_remove.extend(code_range);
    to_remove.extend(goto_indices);
    to_remove.sort();
    to_remove.dedup();

    for &idx in to_remove.iter().rev() {
        if idx < output.len() {
            output.remove(idx);
        }
    }

    let removed_before = to_remove.iter().filter(|&&idx| idx < insert_pos).count();
    let adjusted_pos = insert_pos.saturating_sub(removed_before);

    for (i, content) in conv_content.iter().enumerate() {
        let pos = (adjusted_pos + 1 + i).min(output.len());
        output.insert(pos, content.clone());
    }
}

/// Strip backward gotos to a latch header whose body has just finished
/// emitting: re-entering is a no-op (latch self-gates), and the label has no
/// other referrers. Narrow check (latch opener + sole goto + goto right
/// after the body close + only dead tail after) covers UberGraph post-latch
/// trampolines without touching ordinary backward loops.
pub(super) fn strip_dead_backward_gotos(output: &mut Vec<String>) {
    loop {
        let goto_map = build_goto_map(output);
        let mut target: Option<(usize, usize)> = None;
        for (label_name, gotos) in &goto_map {
            if gotos.len() != 1 {
                continue;
            }
            let goto_idx = gotos[0];
            let label_text = format!("{}:", label_name);
            let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
                continue;
            };
            if label_idx >= goto_idx {
                continue; // only backward gotos
            }
            // Next non-empty line must be a latch opener (`DoOnce(`/`FlipFlop(`).
            let label_on_latch = output[label_idx + 1..].iter().find_map(|line| {
                let t = line.trim();
                if t.is_empty() {
                    None
                } else {
                    Some(t.starts_with("DoOnce(") || t.starts_with("FlipFlop("))
                }
            });
            if label_on_latch != Some(true) {
                continue;
            }
            // Goto must immediately follow the latch body's `}` (pins the
            // pattern to post-latch trampolines).
            let prev_is_close = output[..goto_idx].iter().rev().find_map(|line| {
                let t = line.trim();
                if t.is_empty() {
                    None
                } else {
                    Some(t == BLOCK_CLOSE)
                }
            });
            if prev_is_close != Some(true) {
                continue;
            }
            // Everything after the goto must be dead (blank/close/return).
            let tail_is_dead = output[goto_idx + 1..].iter().all(|line| {
                let t = line.trim();
                t.is_empty() || t == BLOCK_CLOSE || t == BARE_RETURN
            });
            if !tail_is_dead {
                continue;
            }
            target = Some((label_idx, goto_idx));
            break;
        }
        let Some((label_idx, goto_idx)) = target else {
            break;
        };
        // Strip goto first so removing label doesn't shift its index.
        output.remove(goto_idx);
        output.remove(label_idx);
    }
}

/// Extract convergence code (shared by multiple branches) and relocate after
/// the outermost closing brace. Repeats until stable since each splice
/// shifts indices.
pub(super) fn extract_convergence(output: &mut Vec<String>) {
    loop {
        let goto_map = build_goto_map(output);
        let Some((label_name, goto_indices)) = pick_convergence_candidate(&goto_map, output) else {
            break;
        };

        let label_text = format!("{}:", label_name);
        let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
            break;
        };
        let code_start = label_idx + 1;
        if code_start >= output.len() {
            break;
        }
        let code_end = find_convergence_extent(output, code_start);
        if code_end <= code_start {
            break;
        }

        let conv_content: Vec<String> = output[code_start..code_end].to_vec();

        let max_goto = goto_indices.iter().copied().max().unwrap_or(0);
        let insert_pos = find_insertion_point(output, max_goto);

        splice_convergence(
            output,
            label_idx,
            code_start..code_end,
            &goto_indices,
            insert_pos,
            conv_content,
        );
    }
}

/// Map each goto label to its line indices.
fn build_goto_map(output: &[String]) -> HashMap<String, Vec<usize>> {
    let mut map: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, line) in output.iter().enumerate() {
        if let Some(label) = line.trim().strip_prefix("goto ") {
            map.entry(label.to_string()).or_default().push(i);
        }
    }
    map
}

/// Best convergence candidate: label with 2+ gotos, or a single goto crossing
/// a structural boundary. Earliest by first goto position.
fn pick_convergence_candidate(
    goto_map: &HashMap<String, Vec<usize>>,
    output: &[String],
) -> Option<(String, Vec<usize>)> {
    let mut candidates: Vec<(String, Vec<usize>)> = goto_map
        .iter()
        .filter(|(label_name, gotos)| {
            if gotos.len() >= 2 {
                return true;
            }
            // Single goto: only a candidate if a structural boundary separates it from the label.
            gotos.len() == 1 && has_boundary_between(output, label_name, gotos[0])
        })
        .map(|(name, gotos)| (name.clone(), gotos.clone()))
        .collect();
    if candidates.is_empty() {
        return None;
    }
    candidates.sort_by_key(|(_, gotos)| gotos.iter().copied().min().unwrap_or(usize::MAX));
    Some(candidates.remove(0))
}

/// True when a `}` or `} else` appears between goto and label.
fn has_boundary_between(output: &[String], label_name: &str, goto_idx: usize) -> bool {
    let label_text = format!("{}:", label_name);
    let Some(label_idx) = output.iter().position(|l| l.trim() == label_text) else {
        return false;
    };
    // Label right after `} else` is the else-body entry, not a convergence
    // target; skip so extraction doesn't empty the else and destroy its braces.
    if label_idx > 0 && output[label_idx - 1].trim().starts_with("} else") {
        return false;
    }
    let (lo, hi) = if label_idx < goto_idx {
        (label_idx, goto_idx)
    } else {
        (goto_idx, label_idx)
    };
    output[lo + 1..hi].iter().any(|l| {
        let trimmed = l.trim();
        trimmed == BLOCK_CLOSE || trimmed.starts_with("} else")
    })
}

pub(super) fn collapse_double_else(output: &mut Vec<String>) {
    loop {
        let mut changed = false;
        let mut i = 0;
        while i + 1 < output.len() {
            let trimmed = output[i].trim();
            let next_trimmed = output[i + 1].trim();

            if trimmed == "} else {" && next_trimmed == "} else {" {
                output.remove(i);
                changed = true;
                continue;
            }

            if trimmed == "} else {" && next_trimmed == BLOCK_CLOSE {
                output.remove(i);
                output.remove(i);
                changed = true;
                continue;
            }

            i += 1;
        }
        if !changed {
            break;
        }
    }
}
