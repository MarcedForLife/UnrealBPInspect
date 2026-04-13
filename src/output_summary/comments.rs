//! EdGraph comment placement: pin-based structural analysis with spatial fallback.
//!
//! Primary path: use exec pin connections to find entry points into a comment box's
//! node group, then map entry points to bytecode lines.
//! Fallback: rank-based identifier matching and cluster heuristics for assets
//! without pin data.

use std::collections::{HashMap, HashSet, VecDeque};

use super::{CommentBox, NodeInfo, BRANCH_IDENTIFIER, MAX_BUBBLE_DISTANCE_SQ};
use crate::helpers::is_comment_or_empty;
use crate::helpers::{indent_of, is_ident_char};
use crate::types::{NodePinData, PIN_DIRECTION_INPUT, PIN_TYPE_EXEC};

/// Pin name substring identifying the true-branch exec output of a Branch node.
const THEN_PIN: &str = "then";

/// A box comment covering more than this percentage of a function's nodes is treated
/// as a top-level description rather than an inline annotation.
const COVERAGE_THRESHOLD_PERCENT: usize = 80;

/// How a comment should be placed in the output.
pub(super) enum CommentPlacement {
    /// Comment wraps an entire event (the event node is inside the box).
    EventWrapping { event_name: String },
    /// Comment is inline, placed above the exec entry point. The event is not
    /// pre-resolved: the caller tries each candidate event's bytecode to find
    /// where the entry point's identifier actually appears.
    InlineAtEntry { entry_export: usize },
    /// Bubble comment attached to a specific node.
    BubbleOwned { owner_export: usize },
    /// Pin data unavailable or classification failed. Use spatial fallback.
    Fallback,
}

/// Find all node exports spatially inside a comment box on the same graph page.
///
/// Uses per-page position data so cross-page nodes don't leak into containment.
/// Falls back to checking all pages when the comment's page has no node data
/// (can happen when a comment node is shared across many pages and the dedup
/// assigned it to a page without its own node entries).
fn find_contained_exports(
    comment: &CommentBox,
    all_positions: &HashMap<String, HashMap<usize, (i32, i32)>>,
) -> HashSet<usize> {
    if let Some(page_nodes) = all_positions.get(&comment.graph_page) {
        let result: HashSet<usize> = page_nodes
            .iter()
            .filter(|(_, (x, y))| comment.contains_point(*x, *y))
            .map(|(&idx, _)| idx)
            .collect();
        if !result.is_empty() {
            return result;
        }
    }
    // Fallback: search all pages for contained nodes
    all_positions
        .values()
        .flat_map(|page| page.iter())
        .filter(|(_, (x, y))| comment.contains_point(*x, *y))
        .map(|(&idx, _)| idx)
        .collect()
}

/// Find exec entry points: nodes inside the set that receive execution flow
/// from outside. These are nodes with an input exec pin linked to a node
/// not in the contained set.
fn find_exec_entry_points(
    contained: &HashSet<usize>,
    pin_data: &HashMap<usize, NodePinData>,
    all_positions: &HashMap<String, HashMap<usize, (i32, i32)>>,
) -> Vec<usize> {
    let mut entries: Vec<usize> = Vec::new();
    for &exp_idx in contained {
        let Some(pd) = pin_data.get(&exp_idx) else {
            continue;
        };
        let is_entry = pd.pins.iter().any(|pin| {
            pin.pin_type == PIN_TYPE_EXEC
                && pin.direction == PIN_DIRECTION_INPUT
                && pin.linked_to.iter().any(|src| !contained.contains(src))
        });
        if is_entry {
            entries.push(exp_idx);
        }
    }
    // Sort by (y, x) for deterministic top-to-bottom ordering
    let pos_lookup = |idx: &usize| -> (i32, i32) {
        all_positions
            .values()
            .find_map(|page| page.get(idx).copied())
            .unwrap_or((i32::MAX, i32::MAX))
    };
    entries.sort_by_key(|idx| {
        let (x, y) = pos_lookup(idx);
        (y, x)
    });
    entries
}

/// Classify a comment box using pin connection data.
///
/// Returns a `CommentPlacement` that determines where the comment appears
/// in the output. Falls back to `Fallback` when pin data is unavailable.
pub(super) fn classify_comment_by_pins(
    comment: &CommentBox,
    pin_data: &HashMap<usize, NodePinData>,
    all_positions: &HashMap<String, HashMap<usize, (i32, i32)>>,
    event_export_indices: &HashMap<String, usize>,
) -> CommentPlacement {
    if pin_data.is_empty() {
        return CommentPlacement::Fallback;
    }

    // Bubble comments: direct owner lookup
    if comment.is_bubble && comment.owner_export > 0 {
        return CommentPlacement::BubbleOwned {
            owner_export: comment.owner_export,
        };
    }

    let contained = find_contained_exports(comment, all_positions);
    if contained.is_empty() {
        return CommentPlacement::Fallback;
    }

    // Check if the box contains an event node
    for (event_name, &event_idx) in event_export_indices {
        if contained.contains(&event_idx) {
            return CommentPlacement::EventWrapping {
                event_name: event_name.clone(),
            };
        }
    }

    // Find exec entry points from outside the box
    let entries = find_exec_entry_points(&contained, pin_data, all_positions);
    if !entries.is_empty() {
        return CommentPlacement::InlineAtEntry {
            entry_export: entries[0],
        };
    }

    // No exec boundary crossings: self-contained block
    CommentPlacement::Fallback
}

/// Build a reverse index from export index to owning event name.
///
/// When a node is reachable from multiple events (shared execution sub-graphs),
/// the event appearing first in `section_order` wins. This makes the result
/// deterministic regardless of HashMap iteration order in `event_node_ownership`.
pub(super) fn build_ownership_index(
    event_node_ownership: &HashMap<String, HashSet<usize>>,
    section_order: &[&str],
) -> HashMap<usize, String> {
    let mut index: HashMap<usize, String> = HashMap::new();
    // Process events in section order so earlier events take precedence.
    // Events not in section_order are appended after in sorted order for determinism.
    let mut ordered_names: Vec<&str> = section_order
        .iter()
        .filter(|name| event_node_ownership.contains_key(**name))
        .copied()
        .collect();
    let mut remaining: Vec<&str> = event_node_ownership
        .keys()
        .map(|s| s.as_str())
        .filter(|name| !ordered_names.contains(name))
        .collect();
    remaining.sort();
    ordered_names.extend(remaining);

    for event_name in ordered_names {
        if let Some(owned_set) = event_node_ownership.get(event_name) {
            for &idx in owned_set {
                // First writer wins (earlier in section order).
                index.entry(idx).or_insert_with(|| event_name.to_string());
            }
        }
    }
    index
}

/// Build a lookup index from export index to NodeInfo for O(1) lookups.
pub(super) fn build_node_index(nodes: &[NodeInfo]) -> HashMap<usize, &NodeInfo> {
    nodes
        .iter()
        .filter(|n| n.export_index > 0)
        .map(|n| (n.export_index, n))
        .collect()
}

/// Strategy:
/// 1. Direct: if the export is an identifiable non-pure node, use its identifier
/// 2. Data consumer: for pure nodes, follow output data pins to find the consuming
///    execution node (the expression is inlined at that call site in bytecode)
/// 3. Exec successor: follow outgoing exec pins to the first identifiable node
pub(super) fn map_export_to_line(
    export_idx: usize,
    nodes: &[NodeInfo],
    node_index: &HashMap<usize, &NodeInfo>,
    pin_data: &HashMap<usize, NodePinData>,
    bytecode_lines: &[String],
) -> Option<usize> {
    if let Some(node) = node_index.get(&export_idx) {
        // Branch nodes: first try matching by condition pin identifiers.
        // Then try finding the first identifiable exec successor and walking
        // backward to the enclosing `if`. The exec path is more reliable than
        // rank-based matching because it follows the actual control flow.
        if node.identifier == BRANCH_IDENTIFIER {
            if let Some(line) =
                match_branch_by_condition(export_idx, pin_data, node_index, bytecode_lines)
            {
                return Some(line);
            }
            if let Some(line) =
                match_branch_by_true_body(export_idx, nodes, node_index, pin_data, bytecode_lines)
            {
                return Some(line);
            }
            return map_node_to_line(node, nodes, bytecode_lines);
        }
        if !node.is_pure {
            return map_node_to_line(node, nodes, bytecode_lines);
        }
        // Pure nodes: try operand fingerprinting (matches the specific bytecode line
        // whose operands correspond to this node's inputs), then direct rank match,
        // then data consumer following as last resort.
        if let Some(line) =
            match_by_input_operands(export_idx, node, node_index, pin_data, bytecode_lines)
        {
            return Some(line);
        }
        if let Some(line) = map_node_to_line(node, nodes, bytecode_lines) {
            return Some(line);
        }
        return find_data_consumer_line(export_idx, nodes, node_index, pin_data, bytecode_lines, 0);
    }

    // Exec successor: BFS through outgoing exec pins to find the nearest
    // identifiable node. Nodes like K2Node_DynamicCast or K2Node_SwitchEnum
    // don't have identifiers, so we may need to traverse several hops.
    let mut queue: VecDeque<usize> = VecDeque::new();
    let mut visited: HashSet<usize> = HashSet::new();
    visited.insert(export_idx);
    queue.push_back(export_idx);
    while let Some(current) = queue.pop_front() {
        let Some(pd) = pin_data.get(&current) else {
            continue;
        };
        for pin in &pd.pins {
            if !pin.is_exec_output() {
                continue;
            }
            for &target in &pin.linked_to {
                if !visited.insert(target) {
                    continue;
                }
                if let Some(node) = node_index.get(&target) {
                    if let Some(line_idx) = map_node_to_line(node, nodes, bytecode_lines) {
                        return Some(find_enclosing_structure(bytecode_lines, line_idx));
                    }
                }
                queue.push_back(target);
            }
        }
    }

    // Data consumer: for untracked pure nodes (K2Node_GetArrayItem, etc.) that
    // have no exec pins, follow data output pins to the consuming execution node.
    find_data_consumer_line(export_idx, nodes, node_index, pin_data, bytecode_lines, 0)
}

/// Match a Branch node by finding the first identifiable exec successor in its
/// true body, then walking backward to the enclosing `if (...)`.
///
/// More reliable than rank-based matching because it follows the actual control
/// flow: the Branch's "then" pin leads to the first statement of the true body,
/// which maps to a specific bytecode line. The `if` line is immediately above.
fn match_branch_by_true_body(
    branch_export: usize,
    nodes: &[NodeInfo],
    node_index: &HashMap<usize, &NodeInfo>,
    pin_data: &HashMap<usize, NodePinData>,
    bytecode_lines: &[String],
) -> Option<usize> {
    let pd = pin_data.get(&branch_export)?;

    // Find the "then" (true) exec output pin and its target
    let mut then_targets: Vec<usize> = Vec::new();
    for pin in &pd.pins {
        if pin.is_exec_output() && pin.name.contains(THEN_PIN) {
            then_targets.extend(&pin.linked_to);
        }
    }
    if then_targets.is_empty() {
        return None;
    }

    // BFS through exec successors to find the first identifiable node
    let mut queue: VecDeque<usize> = then_targets.into_iter().collect();
    let mut visited: HashSet<usize> = HashSet::new();
    visited.insert(branch_export);
    while let Some(current) = queue.pop_front() {
        if !visited.insert(current) {
            continue;
        }
        if let Some(node) = node_index.get(&current) {
            if node.identifier != BRANCH_IDENTIFIER && !node.identifier.is_empty() {
                // Found an identifiable node in the true body.
                // Map it to a bytecode line, then find the enclosing `if`.
                if let Some(line_idx) = map_node_to_line(node, nodes, bytecode_lines) {
                    return Some(find_enclosing_if(bytecode_lines, line_idx).unwrap_or(line_idx));
                }
            }
        }
        // Follow exec output pins to continue the search
        if let Some(next_pd) = pin_data.get(&current) {
            for pin in &next_pd.pins {
                if pin.is_exec_output() {
                    for &target in &pin.linked_to {
                        queue.push_back(target);
                    }
                }
            }
        }
    }
    None
}

/// Match a Branch node to a specific `if (...)` line by collecting identifiers
/// from its condition pin's expression chain. Each Branch's condition connects to
/// a unique expression tree, so the identifiers disambiguate multiple if-lines.
fn match_branch_by_condition(
    branch_export: usize,
    pin_data: &HashMap<usize, NodePinData>,
    node_index: &HashMap<usize, &NodeInfo>,
    bytecode_lines: &[String],
) -> Option<usize> {
    let pd = pin_data.get(&branch_export)?;

    // Find the condition pin source (non-exec input pin, typically "Condition")
    let mut condition_sources: Vec<usize> = Vec::new();
    for pin in &pd.pins {
        if pin.is_data_input() {
            condition_sources.extend(&pin.linked_to);
        }
    }
    if condition_sources.is_empty() {
        return None;
    }

    // Recursively collect identifiers from the condition expression tree.
    // Also extract field names from split-struct sub-pin names (e.g.
    // "Output_Get_IsClimbable_8_..." yields "IsClimbable").
    let mut condition_ids: Vec<String> = Vec::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut queue: VecDeque<usize> = condition_sources.into_iter().collect();
    while let Some(idx) = queue.pop_front() {
        if !visited.insert(idx) {
            continue;
        }
        if let Some(node) = node_index.get(&idx) {
            if node.identifier != BRANCH_IDENTIFIER {
                condition_ids.push(node.identifier.clone());
            }
        }
        if let Some(source_pd) = pin_data.get(&idx) {
            // Extract struct field names from data output pins.
            for pin in &source_pd.pins {
                if pin.is_data_output() {
                    condition_ids.extend(extract_pin_field_names(&pin.name));
                }
            }
            for pin in &source_pd.pins {
                if pin.is_data_input() {
                    for &src in &pin.linked_to {
                        queue.push_back(src);
                    }
                }
            }
        }
    }
    if condition_ids.is_empty() {
        return None;
    }

    // Add operator text aliases so Kismet function names match bytecode operators.
    // BooleanAND compiles to `&&`, BooleanOR to `||`, Not_PreBool to `!`.
    let mut operator_aliases: Vec<&str> = Vec::new();
    for id in &condition_ids {
        match id.as_str() {
            "BooleanOR" => operator_aliases.push("||"),
            "BooleanAND" => operator_aliases.push("&&"),
            "Less_FloatFloat" | "LessEqual_FloatFloat" => operator_aliases.push("<="),
            "Greater_FloatFloat" | "GreaterEqual_FloatFloat" => operator_aliases.push(">="),
            _ if id.starts_with("Not_PreBool") => operator_aliases.push("!"),
            _ => {}
        }
    }
    condition_ids.extend(operator_aliases.iter().map(|s| s.to_string()));

    // Find the `if (...)` line with the most condition identifier matches.
    // Return None if tied (ambiguous), letting the true-body fallback handle it.
    let mut best_line: Option<usize> = None;
    let mut best_matches = 0usize;
    let mut is_unique = true;
    for (i, line) in bytecode_lines.iter().enumerate() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("if (") && !trimmed.starts_with("} else if (") {
            continue;
        }
        let matches = condition_ids
            .iter()
            .filter(|id| line_contains_identifier(line, id))
            .count();
        if matches > best_matches {
            best_matches = matches;
            best_line = Some(i);
            is_unique = true;
        } else if matches == best_matches && matches > 0 {
            is_unique = false;
        }
    }
    if best_matches > 0 && is_unique {
        best_line
    } else {
        None
    }
}

/// Extract field names from a split-struct pin name.
///
/// Struct field pins have names like `IsClimbable_8_45D4CE4F481CFD3ACEBEE887D596440C`
/// or `Output_Get_IsClimbable_8_GUID`. Extracts PascalCase identifiers that aren't
/// common prefixes, numeric indices, or hex GUIDs.
fn extract_pin_field_names(pin_name: &str) -> Vec<String> {
    let segments: Vec<&str> = pin_name.split('_').collect();
    let mut fields = Vec::new();
    for seg in &segments {
        // Skip short segments (single chars, "0", "8", etc.)
        if seg.len() < 3 {
            continue;
        }
        if seg.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        // UE4 GUIDs are 32 hex chars, split by underscores into 16-char halves
        if seg.len() >= 16 && seg.chars().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        if matches!(
            *seg,
            "Output" | "Get" | "Set" | "Pin" | "Return" | "ReturnValue"
        ) {
            continue;
        }
        if seg.starts_with(|c: char| c.is_ascii_uppercase())
            && seg.contains(|c: char| c.is_ascii_lowercase())
        {
            fields.push(seg.to_string());
        }
    }
    fields
}

/// Match a pure node to a bytecode line by checking input operands.
///
/// For each bytecode line containing the node's identifier, check whether the
/// line also contains identifiers from the node's input data pins. This
/// disambiguates multiple instances of the same function (e.g. two different
/// Multiply_FloatFloat calls) by their operand context.
fn match_by_input_operands(
    export_idx: usize,
    node: &NodeInfo,
    node_index: &HashMap<usize, &NodeInfo>,
    pin_data: &HashMap<usize, NodePinData>,
    bytecode_lines: &[String],
) -> Option<usize> {
    let pd = pin_data.get(&export_idx)?;

    // Collect identifiers of nodes connected to input data pins
    let mut input_ids: Vec<&str> = Vec::new();
    for pin in &pd.pins {
        if !pin.is_data_input() {
            continue;
        }
        for &source in &pin.linked_to {
            if let Some(source_node) = node_index.get(&source) {
                if source_node.identifier != BRANCH_IDENTIFIER {
                    input_ids.push(&source_node.identifier);
                }
            }
        }
    }
    if input_ids.is_empty() {
        return None;
    }

    // Find bytecode lines containing the node's identifier, then pick the one
    // that also contains the most input operand identifiers
    let mut best_line: Option<usize> = None;
    let mut best_matches = 0usize;
    for (i, line) in bytecode_lines.iter().enumerate() {
        if !line_contains_identifier(line, &node.identifier) {
            continue;
        }
        let matches = input_ids
            .iter()
            .filter(|id| line_contains_identifier(line, id))
            .count();
        if matches > best_matches {
            best_matches = matches;
            best_line = Some(i);
        }
    }

    // Require at least one input operand match to avoid false positives
    if best_matches > 0 {
        best_line
    } else {
        None
    }
}

/// Follow output data pins to find the first execution node that consumes the
/// result. Traverses through chains of pure/non-identifiable intermediate nodes.
fn find_data_consumer_line(
    source_export: usize,
    nodes: &[NodeInfo],
    node_index: &HashMap<usize, &NodeInfo>,
    pin_data: &HashMap<usize, NodePinData>,
    bytecode_lines: &[String],
    depth: usize,
) -> Option<usize> {
    if depth > 10 {
        return None;
    }
    let pd = pin_data.get(&source_export)?;
    for pin in &pd.pins {
        if pin.is_data_output() {
            for &target in &pin.linked_to {
                if let Some(node) = node_index.get(&target) {
                    if !node.is_pure {
                        return map_node_to_line(node, nodes, bytecode_lines);
                    }
                }
                if let Some(line) = find_data_consumer_line(
                    target,
                    nodes,
                    node_index,
                    pin_data,
                    bytecode_lines,
                    depth + 1,
                ) {
                    return Some(line);
                }
            }
        }
    }
    None
}

/// Map an identifiable node to a bytecode line using its identifier and rank.
fn map_node_to_line(
    node: &NodeInfo,
    all_nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> Option<usize> {
    if node.identifier == BRANCH_IDENTIFIER {
        let rank = node_rank(node, all_nodes)?;
        return find_nth_identifier_line(BRANCH_IDENTIFIER, rank, bytecode_lines);
    }

    let rank = node_rank(node, all_nodes)?;

    // VariableSet: only match assignment lines to prevent matching read-only
    // references in other events' bytecode. Try member access (`self.X = ...`)
    // first, then local variable assignment (`X = ...`) for function locals.
    if node.is_variable_set {
        let member_pattern = format!("self.{} = ", node.identifier);
        if let Some(line) = find_nth_pattern_line(&member_pattern, rank, bytecode_lines) {
            return Some(line);
        }
        let local_pattern = format!("{} = ", node.identifier);
        return find_nth_pattern_line(&local_pattern, rank, bytecode_lines);
    }

    find_nth_identifier_line(&node.identifier, rank, bytecode_lines)
}

/// Find the Nth line containing a specific pattern string (0-based rank).
fn find_nth_pattern_line(pattern: &str, rank: usize, bytecode_lines: &[String]) -> Option<usize> {
    let mut count = 0;
    for (i, line) in bytecode_lines.iter().enumerate() {
        if line.contains(pattern) {
            if count == rank {
                return Some(i);
            }
            count += 1;
        }
    }
    None
}

/// Walk backward from a line to find the start of its enclosing structure.
/// Skips over preceding guard blocks (`if (...) { return }`) to find the
/// actual entry point, since guards are often generated by macro expansions
/// whose bubble comments describe the whole sequence.
fn find_enclosing_structure(bytecode_lines: &[String], line_idx: usize) -> usize {
    if line_idx == 0 {
        return 0;
    }
    let target_indent = indent_of(&bytecode_lines[line_idx]);
    let mut best = line_idx;
    for i in (0..line_idx).rev() {
        let line = &bytecode_lines[i];
        let trimmed = line.trim_start();
        let indent = indent_of(line);
        if indent < target_indent {
            return best;
        }
        if indent == target_indent {
            if trimmed.starts_with("// sequence")
                || trimmed.starts_with("// sub-sequence")
                || trimmed.starts_with("if (")
                || trimmed.starts_with("} else")
            {
                best = i;
            } else if trimmed == "}" {
                // Closing brace of a preceding block at the same indent,
                // continue walking to find the block's opening `if`
                continue;
            } else if !is_comment_or_empty(trimmed) {
                // Non-structure line at the same indent, stop here
                return best;
            }
        }
    }
    best
}

/// Find identifiable nodes associated with a comment.
///
/// For bubble comments: uses the owner export for direct lookup, falling back to
/// spatial proximity. For box comments: returns all same-page nodes inside the box.
fn resolve_comment_nodes<'a>(comment: &CommentBox, nodes: &'a [NodeInfo]) -> Vec<&'a NodeInfo> {
    if comment.is_bubble {
        if comment.owner_export > 0 {
            if let Some(owner) = nodes
                .iter()
                .find(|n| n.export_index == comment.owner_export)
            {
                return vec![owner];
            }
        }
        // Bubble without identifiable owner: spatial proximity fallback
        let right = nearest_nodes(comment, nodes, true);
        if !right.is_empty() {
            right
        } else {
            nearest_nodes(comment, nodes, false)
        }
    } else {
        nodes
            .iter()
            .filter(|n| n.graph_page == comment.graph_page && comment.contains_point(n.x, n.y))
            .collect()
    }
}

/// Find the closest identifiable nodes to a bubble comment (same graph page only).
fn nearest_nodes<'a>(
    comment: &CommentBox,
    nodes: &'a [NodeInfo],
    right_only: bool,
) -> Vec<&'a NodeInfo> {
    let mut candidates: Vec<(&NodeInfo, i64)> = nodes
        .iter()
        .filter(|n| n.graph_page == comment.graph_page && (!right_only || n.x >= comment.x))
        .map(|n| {
            let dx = (n.x - comment.x) as i64;
            let dy = (n.y - comment.y) as i64;
            (n, dx * dx + dy * dy)
        })
        .filter(|&(_, d)| d < MAX_BUBBLE_DISTANCE_SQ)
        .collect();
    candidates.sort_by_key(|&(n, d)| (d, n.y, n.x));
    candidates.truncate(5);
    candidates.into_iter().map(|(n, _)| n).collect()
}

fn line_contains_identifier(line: &str, identifier: &str) -> bool {
    if identifier == BRANCH_IDENTIFIER {
        let trimmed = line.trim_start();
        return trimmed.starts_with("if (") || trimmed.starts_with("} else if (");
    }
    let mut start = 0;
    while start + identifier.len() <= line.len() {
        if let Some(pos) = line[start..].find(identifier) {
            let abs_pos = start + pos;
            let is_start = abs_pos == 0 || !is_ident_char(line.as_bytes()[abs_pos - 1]);
            let end = abs_pos + identifier.len();
            let is_end = end >= line.len() || !is_ident_char(line.as_bytes()[end]);
            if is_start && is_end {
                return true;
            }
            start = abs_pos + 1;
        } else {
            break;
        }
    }
    false
}

/// Find the Nth occurrence of `identifier` in bytecode lines (0-based rank).
fn find_nth_identifier_line(
    identifier: &str,
    rank: usize,
    bytecode_lines: &[String],
) -> Option<usize> {
    let mut count = 0;
    for (i, line) in bytecode_lines.iter().enumerate() {
        if line_contains_identifier(line, identifier) {
            if count == rank {
                return Some(i);
            }
            count += 1;
        }
    }
    None
}

/// Determine a node's rank among all nodes sharing its identifier.
/// Uses (Y, X) sort order; graphs branch vertically (true=up, false=down),
/// which generally matches bytecode order (true branches processed first).
fn node_rank(node: &NodeInfo, all_nodes: &[NodeInfo]) -> Option<usize> {
    let mut same_id: Vec<(i32, i32)> = all_nodes
        .iter()
        .filter(|n| n.identifier == node.identifier && n.graph_page == node.graph_page)
        .map(|n| (n.y, n.x))
        .collect();
    same_id.sort();
    same_id
        .iter()
        .position(|&(y, x)| y == node.y && x == node.x)
}

/// Walk backward from `anchor_line` to find the nearest `if` at a shallower indent.
fn find_enclosing_if(bytecode_lines: &[String], anchor_line: usize) -> Option<usize> {
    let anchor_indent = indent_of(&bytecode_lines[anchor_line]);
    for i in (0..anchor_line).rev() {
        let line = &bytecode_lines[i];
        let trimmed = line.trim_start();
        let indent = indent_of(line);
        if indent < anchor_indent
            && (trimmed.starts_with("if (") || trimmed.starts_with("} else if ("))
        {
            return Some(i);
        }
    }
    None
}

pub(super) fn find_comment_line(
    comment: &CommentBox,
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> Option<usize> {
    let contained = resolve_comment_nodes(comment, nodes);
    if contained.is_empty() {
        return None;
    }

    // When a comment covers both Branch nodes and regular identifiable nodes,
    // anchor on the regular nodes and walk backward to the enclosing `if`.
    let has_branch = contained.iter().any(|n| n.identifier == BRANCH_IDENTIFIER);
    if has_branch {
        let regular: Vec<&&NodeInfo> = contained
            .iter()
            .filter(|n| n.identifier != BRANCH_IDENTIFIER)
            .collect();
        if !regular.is_empty() {
            let mut anchor_line: Option<usize> = None;
            for node in &regular {
                let rank = match node_rank(node, nodes) {
                    Some(r) => r,
                    None => continue,
                };
                if let Some(line_idx) =
                    find_nth_identifier_line(&node.identifier, rank, bytecode_lines)
                {
                    anchor_line = Some(anchor_line.map_or(line_idx, |m: usize| m.min(line_idx)));
                    if comment.is_bubble {
                        break;
                    }
                }
            }
            if let Some(anchor) = anchor_line {
                return Some(find_enclosing_if(bytecode_lines, anchor).unwrap_or(anchor));
            }
        }
    }

    // For box comments, prefer execution nodes (CallFunction, VariableSet)
    // over pure nodes (VariableGet). Pure nodes produce expressions inlined
    // at multiple bytecode locations, so rank-based matching is unreliable
    // and can pull the comment to an unrelated outer line.
    let has_execution = !comment.is_bubble && contained.iter().any(|n| !n.is_pure);

    let mut min_line: Option<usize> = None;
    for node in &contained {
        if has_execution && node.is_pure {
            continue;
        }
        let rank = match node_rank(node, nodes) {
            Some(r) => r,
            None => continue,
        };
        if let Some(line_idx) = find_nth_identifier_line(&node.identifier, rank, bytecode_lines) {
            min_line = Some(min_line.map_or(line_idx, |m: usize| m.min(line_idx)));
            // For bubbles, use the first match (closest node) rather than minimum line
            if comment.is_bubble {
                return min_line;
            }
        }
    }

    min_line
}

/// Maximum bytecode line span for a cluster match.
const MAX_CLUSTER_SPAN: usize = 30;

/// Weight multiplier for function call identifiers in cluster scoring.
/// Calls are primary execution targets of a comment, while variable accesses
/// from adjacent events are supporting data flow.
const CALL_WEIGHT: usize = 3;

/// Cluster-based comment matching for ubergraph bytecode.
///
/// Unlike `find_comment_line` (rank-based, designed for single-function graphs),
/// this finds the tightest window of bytecode lines where multiple identifiers
/// from the comment box appear near each other. This handles cross-event
/// matching where rank ordering (graph Y-sort) doesn't match bytecode order.
///
/// Function calls (identifier followed by `(`) get an extra CALL_WEIGHT bonus
/// since they're the primary execution targets of a comment, while variable
/// accesses from adjacent events are supporting data flow.
pub(super) fn find_comment_line_clustered(
    comment: &CommentBox,
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
) -> Option<usize> {
    let contained = resolve_comment_nodes(comment, nodes);
    if contained.is_empty() {
        return None;
    }

    // Collect unique identifiers, excluding __branch__ (matches every `if`).
    let mut all_ids: HashSet<&str> = HashSet::new();
    for node in &contained {
        if node.identifier != BRANCH_IDENTIFIER {
            all_ids.insert(&node.identifier);
        }
    }

    // Build occurrence list: every bytecode line where a candidate id appears.
    let mut occurrences: Vec<(usize, &str)> = Vec::new();
    for &id in &all_ids {
        for (line_idx, line) in bytecode_lines.iter().enumerate() {
            if line_contains_identifier(line, id) {
                occurrences.push((line_idx, id));
            }
        }
    }
    occurrences.sort_by_key(|&(idx, _)| idx);

    if occurrences.is_empty() {
        return None;
    }

    // Pre-build call patterns to avoid allocations in the sliding window loop
    let call_patterns: HashMap<&str, String> =
        all_ids.iter().map(|&id| (id, format!("{id}("))).collect();

    // Slide a window to find the best cluster. Each identifier contributes
    // 1 to the weighted count; function calls contribute an extra CALL_WEIGHT.
    // Score = weighted / (span + 1). Tiebreak by higher raw count.
    let mut best_score: f64 = 0.0;
    let mut best_count: usize = 0;
    let mut best_start: usize = 0;

    for (anchor_pos, &(anchor_line, _)) in occurrences.iter().enumerate() {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut call_ids: HashSet<&str> = HashSet::new();
        let mut last_line = anchor_line;

        for &(line_idx, id) in &occurrences[anchor_pos..] {
            if line_idx > anchor_line + MAX_CLUSTER_SPAN {
                break;
            }
            if seen.insert(id) {
                let line = &bytecode_lines[line_idx];
                if line.contains(call_patterns[id].as_str()) {
                    call_ids.insert(id);
                }
            }
            last_line = line_idx;
        }

        let count = seen.len();
        let weighted = count + CALL_WEIGHT * call_ids.len();
        let span = last_line - anchor_line;
        let score = weighted as f64 / (span + 1) as f64;

        let is_better = score > best_score || (score == best_score && count > best_count);
        if is_better {
            best_score = score;
            best_count = count;
            best_start = anchor_line;
        }
    }

    if best_score > 0.0 {
        Some(best_start)
    } else {
        None
    }
}

pub(super) fn classify_comments<'a>(
    comments: &'a [CommentBox],
    nodes: &[NodeInfo],
    bytecode_lines: &[String],
    pin_data: &HashMap<usize, NodePinData>,
    all_positions: &HashMap<String, HashMap<usize, (i32, i32)>>,
) -> (Vec<&'a CommentBox>, Vec<(usize, &'a CommentBox)>) {
    let total_nodes = nodes.len();
    let node_index = build_node_index(nodes);
    let mut top_level: Vec<&CommentBox> = Vec::new();
    let mut inline: Vec<(usize, &CommentBox)> = Vec::new();

    for comment in comments {
        if comment.is_bubble {
            if comment.owner_export > 0 {
                if let Some(line_idx) = map_export_to_line(
                    comment.owner_export,
                    nodes,
                    &node_index,
                    pin_data,
                    bytecode_lines,
                ) {
                    inline.push((line_idx, comment));
                    continue;
                }
            }
            if let Some(line_idx) = find_comment_line(comment, nodes, bytecode_lines) {
                inline.push((line_idx, comment));
            } else {
                top_level.push(comment);
            }
            continue;
        }

        let contained_count = resolve_comment_nodes(comment, nodes).len();

        if total_nodes > 0
            && contained_count > 0
            && contained_count * 100 / total_nodes > COVERAGE_THRESHOLD_PERCENT
        {
            top_level.push(comment);
            continue;
        }

        // Pin-based: find exec entry point into the box, map to a bytecode line
        let contained_exports = find_contained_exports(comment, all_positions);
        let entries = find_exec_entry_points(&contained_exports, pin_data, all_positions);
        if let Some(&entry) = entries.first() {
            if let Some(line_idx) =
                map_export_to_line(entry, nodes, &node_index, pin_data, bytecode_lines)
            {
                inline.push((line_idx, comment));
                continue;
            }
        }

        // Spatial fallback
        if let Some(line_idx) = find_comment_line(comment, nodes, bytecode_lines) {
            inline.push((line_idx, comment));
        } else {
            top_level.push(comment);
        }
    }

    inline.sort_by_key(|(idx, _)| *idx);
    // Deduplicate when multiple nodes produce the same comment at the same line.
    // Common with Select-based left/right branching where the compiler merges paths.
    inline.dedup_by(|b, a| a.0 == b.0 && a.1.text == b.1.text);

    (top_level, inline)
}
