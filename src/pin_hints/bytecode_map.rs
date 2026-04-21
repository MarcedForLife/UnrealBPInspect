//! Map bytecode if-statement offsets to their corresponding `K2Node_IfThenElse`
//! export.
//!
//! For each Branch node, extract the condition identity from the node that
//! feeds its `Condition` input pin, then match that identity against the
//! condition text of every `if !(...) jump 0xHEX` in the relevant bytecode
//! stream. A unique match produces an offset -> branch-export entry; any
//! other outcome puts the branch in `unmatched_branches`.

use std::collections::{BTreeMap, BTreeSet};

use crate::prop_query::{find_prop_str_items_any, find_struct_field_str};
use crate::resolve::{resolve_index, short_class};
use crate::types::{ParsedAsset, Property};

use super::types::BranchHints;

/// Mapping from bytecode if-statement offsets to the `K2Node_IfThenElse`
/// (Branch) node they correspond to, grouped by owning function key.
#[derive(Debug, Clone, Default)]
pub struct BytecodeBranchMap {
    /// Maps `(owning_function_key, bytecode_offset_of_if_statement)` to the
    /// 1-based `K2Node_IfThenElse` export index. Only entries where the
    /// condition identity unambiguously matches a single bytecode if.
    pub offset_to_branch: BTreeMap<(String, u32), usize>,
    /// Branches that couldn't be mapped (condition unreadable, no match, or
    /// multiple matches). Keyed by `(owning_function_key, branch_export_idx)`.
    /// Diagnostic only; empty is good.
    pub unmatched_branches: BTreeSet<(String, usize)>,
}

/// Condition identity used to match a Branch node to a bytecode if-statement.
#[derive(Debug, Clone)]
pub(super) enum ConditionIdentity {
    /// Produced by a `K2Node_CallFunction`. The bytecode temp variable name
    /// will be `<prefix>_ReturnValue` (optionally with a `_N` suffix).
    CallFunction { prefix: String },
    /// Produced by a `K2Node_VariableGet`. The bytecode condition will
    /// reference the variable name, usually as `self.<name>` or just `<name>`.
    VariableGet { var_name: String },
}

/// Info about the UberGraph function: its name and sorted entry offsets.
struct UberGraphInfo {
    /// 1-based export index of the UberGraph Function export.
    export_idx: usize,
    /// Sorted list of event entry offsets discovered by scanning non-UberGraph
    /// stubs for `<UbergraphName>(N)` calls.
    entry_offsets: Vec<u32>,
}

/// Build a bytecode-offset to Branch-export mapping from per-function branch
/// hints and bytecode stored on Function exports.
pub fn build_bytecode_branch_map(asset: &ParsedAsset, hints: &BranchHints) -> BytecodeBranchMap {
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(hdr, _)| hdr.object_name.clone())
        .collect();

    let ubergraph = find_ubergraph_function(asset, &export_names);
    let function_by_name: BTreeMap<String, usize> = asset
        .exports
        .iter()
        .enumerate()
        .filter_map(|(idx, (hdr, _))| {
            let class = resolve_index(&asset.imports, &export_names, hdr.class_index);
            class
                .ends_with(".Function")
                .then(|| (hdr.object_name.clone(), idx + 1))
        })
        .collect();

    let mut map = BytecodeBranchMap::default();

    // Pre-compute the UberGraph's full if-statement list once; each event
    // slices the same list by its own entry range inside the loop below.
    let ug_ifs: Option<Vec<(u32, String)>> = ubergraph.as_ref().and_then(|ug| {
        let ug_props = &asset.exports.get(ug.export_idx - 1)?.1;
        Some(extract_if_statements(ug_props))
    });

    for (function_key, branches) in &hints.by_function {
        let Some(if_stmts) = collect_if_statements_for_key(
            asset,
            function_key,
            &function_by_name,
            ubergraph.as_ref(),
            ug_ifs.as_deref(),
        ) else {
            // No bytecode visible for this key; every branch is unmatched.
            for info in branches {
                map.unmatched_branches
                    .insert((function_key.clone(), info.branch_export_idx));
            }
            continue;
        };

        for info in branches {
            let Some(identity) = branch_condition_identity(asset, info.branch_export_idx) else {
                map.unmatched_branches
                    .insert((function_key.clone(), info.branch_export_idx));
                continue;
            };

            let matches: Vec<u32> = if_stmts
                .iter()
                .filter(|(_, cond)| condition_matches(&identity, cond))
                .map(|(offset, _)| *offset)
                .collect();

            if matches.len() == 1 {
                map.offset_to_branch
                    .insert((function_key.clone(), matches[0]), info.branch_export_idx);
            } else {
                map.unmatched_branches
                    .insert((function_key.clone(), info.branch_export_idx));
            }
        }
    }

    map
}

fn find_ubergraph_function(asset: &ParsedAsset, export_names: &[String]) -> Option<UberGraphInfo> {
    let (ug_idx, ug_name) = asset
        .exports
        .iter()
        .enumerate()
        .find_map(|(idx, (hdr, _))| {
            let class = resolve_index(&asset.imports, export_names, hdr.class_index);
            (class.ends_with(".Function") && hdr.object_name.starts_with("ExecuteUbergraph_"))
                .then(|| (idx + 1, hdr.object_name.clone()))
        })?;

    let call_prefix = format!("{}(", ug_name);
    let mut entry_offsets: BTreeSet<u32> = BTreeSet::new();
    for (hdr, props) in &asset.exports {
        let class = resolve_index(&asset.imports, export_names, hdr.class_index);
        if !class.ends_with(".Function") || hdr.object_name.starts_with("ExecuteUbergraph_") {
            continue;
        }
        for line in find_prop_str_items_any(props, &["BytecodeSummary", "Bytecode"]) {
            if let Some(offset) = parse_ubergraph_entry_call(line, &call_prefix) {
                entry_offsets.insert(offset);
            }
        }
    }

    Some(UberGraphInfo {
        export_idx: ug_idx,
        entry_offsets: entry_offsets.into_iter().collect(),
    })
}

/// Parse a bytecode line for `<UberGraphName>(N)` and return the numeric
/// argument as a `u32` offset.
fn parse_ubergraph_entry_call(line: &str, call_prefix: &str) -> Option<u32> {
    let start = line.find(call_prefix)?;
    let after = &line[start + call_prefix.len()..];
    let end = after.find(')')?;
    after[..end].trim().parse::<u32>().ok()
}

/// Collect `(offset, condition_text)` for every `if !(COND) jump` in the
/// bytecode stream relevant to `function_key`. For event stubs, this returns
/// if-statements from the UberGraph function sliced to the event's offset
/// range; for regular functions, it returns the function's own if-statements.
fn collect_if_statements_for_key(
    asset: &ParsedAsset,
    function_key: &str,
    function_by_name: &BTreeMap<String, usize>,
    ubergraph: Option<&UberGraphInfo>,
    all_ug_ifs: Option<&[(u32, String)]>,
) -> Option<Vec<(u32, String)>> {
    let target_export = *function_by_name.get(function_key)?;

    // Try the named function first. If it has if-statements in its own
    // bytecode, use those.
    let (_hdr, props) = asset.exports.get(target_export - 1)?;
    let own_ifs = extract_if_statements(props);
    if !own_ifs.is_empty() {
        return Some(own_ifs);
    }

    // Fall back to the UberGraph slice for this event's entry offset.
    let ug = ubergraph?;
    let entry_offset = find_stub_entry_offset(props, asset, ug)?;
    let all_ug_ifs = all_ug_ifs?;

    let next_entry = ug
        .entry_offsets
        .iter()
        .copied()
        .find(|o| *o > entry_offset)
        .unwrap_or(u32::MAX);

    Some(
        all_ug_ifs
            .iter()
            .filter(|(offset, _)| *offset >= entry_offset && *offset < next_entry)
            .cloned()
            .collect(),
    )
}

/// Scan a stub function's bytecode for its `<UberGraphName>(N)` call and
/// return the entry offset `N`.
fn find_stub_entry_offset(
    stub_props: &[Property],
    asset: &ParsedAsset,
    ug: &UberGraphInfo,
) -> Option<u32> {
    let ug_name = &asset.exports.get(ug.export_idx - 1)?.0.object_name;
    let call_prefix = format!("{}(", ug_name);
    for line in find_prop_str_items_any(stub_props, &["BytecodeSummary", "Bytecode"]) {
        if let Some(offset) = parse_ubergraph_entry_call(line, &call_prefix) {
            return Some(offset);
        }
    }
    None
}

/// Extract `(offset, condition_text)` for every `if !(COND) jump 0xHEX` in a
/// Function export's `Bytecode` / `BytecodeSummary` property.
fn extract_if_statements(props: &[Property]) -> Vec<(u32, String)> {
    let mut out = Vec::new();
    for line in find_prop_str_items_any(props, &["Bytecode", "BytecodeSummary"]) {
        if let Some((offset, body)) = split_bytecode_line(line) {
            if let Some(cond) = parse_if_jump_cond(body) {
                out.push((offset, cond.to_string()));
            }
        }
    }
    out
}

/// Split a stored bytecode line of the form `"XXXX: text"` into `(offset, body)`.
pub(super) fn split_bytecode_line(line: &str) -> Option<(u32, &str)> {
    let hex_len = 4;
    let separator = ": ";
    let prefix_len = hex_len + separator.len();
    if line.len() <= prefix_len || line.as_bytes().get(hex_len) != Some(&b':') {
        return None;
    }
    let offset = u32::from_str_radix(&line[..hex_len], 16).ok()?;
    Some((offset, &line[prefix_len..]))
}

/// Return the condition text inside `if !(COND) jump 0xHEX`, or `None` if
/// the line is not an if-jump.
pub(super) fn parse_if_jump_cond(text: &str) -> Option<&str> {
    let rest = text.strip_prefix("if !(")?;
    let jump_pos = rest.rfind(") jump 0x")?;
    Some(&rest[..jump_pos])
}

/// Follow the `Condition` input pin of a `K2Node_IfThenElse` to its
/// producer and extract an identity usable for bytecode matching.
fn branch_condition_identity(
    asset: &ParsedAsset,
    branch_export: usize,
) -> Option<ConditionIdentity> {
    let pin_data = asset.pin_data.get(&branch_export)?;
    let cond_pin = pin_data
        .pins
        .iter()
        .find(|p| p.name == "Condition" && p.is_data_input())?;
    let producer = cond_pin.linked_to.first()?.node;
    let zero_based = producer.checked_sub(1)?;
    let (hdr, props) = asset.exports.get(zero_based)?;
    let export_names: Vec<String> = asset
        .exports
        .iter()
        .map(|(h, _)| h.object_name.clone())
        .collect();
    let short = short_class(&resolve_index(
        &asset.imports,
        &export_names,
        hdr.class_index,
    ));
    match short.as_str() {
        "K2Node_CallFunction" => find_struct_field_str(props, "FunctionReference", "MemberName")
            .map(|prefix| ConditionIdentity::CallFunction { prefix }),
        "K2Node_VariableGet" => find_struct_field_str(props, "VariableReference", "MemberName")
            .map(|var_name| ConditionIdentity::VariableGet { var_name }),
        _ => None,
    }
}

/// Determine whether a bytecode condition text matches a Branch identity.
pub(super) fn condition_matches(identity: &ConditionIdentity, cond_text: &str) -> bool {
    let trimmed = cond_text.trim();
    match identity {
        ConditionIdentity::CallFunction { prefix } => {
            // Bytecode temp vars look like `$<prefix>_ReturnValue` or
            // `$<prefix>_ReturnValue_N`. Match on the stripped prefix so
            // version/index suffixes don't foil the match.
            let base = trimmed.strip_prefix('$').unwrap_or(trimmed);
            let marker = format!("{}_ReturnValue", prefix);
            base == marker || base.starts_with(&(marker + "_"))
        }
        ConditionIdentity::VariableGet { var_name } => {
            // Accept "self.Name", "Name", "!self.Name", "!Name" forms.
            let positive = trimmed.strip_prefix('!').unwrap_or(trimmed);
            let bare = positive.strip_prefix("self.").unwrap_or(positive);
            bare == var_name
        }
    }
}
