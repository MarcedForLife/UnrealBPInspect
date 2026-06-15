//! Call / variable-set / dynamic-cast offset indexing and attribution.
//!
//! Builds the member-name and target-class indices, walks the bytecode
//! for `EX_LET*` and cast opcodes, and writes the matching
//! `K2Node_CallFunction` / `K2Node_VariableSet` / `K2Node_DynamicCast`
//! attributions into `partitions` and `byte_to_node`.

use std::collections::{BTreeMap, HashMap};

use crate::bytecode::decode::walker::{walk_opcode, FieldPath, OpcodeVisitor, WalkCtx};
use crate::bytecode::opcodes::{
    EX_DYNAMIC_CAST, EX_LET, EX_LET_BOOL, EX_LET_DELEGATE, EX_LET_MULTICAST_DELEGATE, EX_LET_OBJ,
    EX_LET_VALUE_ON_PERSISTENT_FRAME, EX_LET_WEAK_OBJ_PTR, EX_META_CAST, EX_RETURN,
};
use crate::bytecode::pin_attribution::{build_callfunc_member_index, collect_call_sites};
use crate::bytecode::resolve::resolve_bc_obj;
use crate::prop_query::{find_prop, find_struct_field_str};
use crate::resolve::{enclosing_graph_name, resolve_index, short_class};
use crate::types::{ParsedAsset, PropValue};

use super::{
    extend_owner_events, node_class, normalise_member_name, owner_events_for_node, push_range,
    resolve_member_group, AttributionMode, GraphScope, K2NodeByteMapInputs, K2NodePartition,
};

/// Resolve a batch of `(disk_offset, member_key)` sites to their owning
/// K2Node ids and record the attribution. Shared by the call /
/// variable-set / dynamic-cast passes, which differ only in how they
/// build `index` and collect `sites`; the per-member group resolution
/// and the partition / `byte_to_node` insert are identical.
fn attribute_member_sites(
    sites: &[(usize, String)],
    index: &HashMap<String, Vec<usize>>,
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let mut offsets_by_member: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (disk_offset, member) in sites {
        if index.contains_key(member.as_str()) {
            offsets_by_member
                .entry(member.as_str())
                .or_default()
                .push(*disk_offset);
        }
    }
    for (member, offsets) in offsets_by_member {
        let candidates = &index[member];
        for (disk_offset, node_id) in resolve_member_group(candidates, &offsets, inputs, mode) {
            let owners = owner_events_for_node(node_id, inputs);
            let partition = partitions.entry(node_id).or_insert_with(|| {
                K2NodePartition::new(node_id, owners.clone(), node_class(inputs, node_id), None)
            });
            extend_owner_events(partition, owners);
            // Conservative single-byte range at the opcode start.
            // The macro-scaffold pass expands to full opcode extents.
            push_range(&mut partition.ranges, disk_offset..disk_offset + 1);
            byte_to_node.entry(disk_offset).or_default().push(node_id);
        }
    }
}

/// Attribute every call opcode to its K2Node_CallFunction node(s)
/// via short-member-name lookup. Multiple K2Node_CallFunction exports
/// may share a member name; the group resolver assigns each site.
pub(super) fn attribute_calls(
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let callfunc_by_member = build_callfunc_member_index(inputs.asset, inputs.export_names);
    let call_sites = collect_call_sites(
        inputs.bytecode,
        inputs.name_table,
        inputs.ue5,
        inputs.asset,
        inputs.export_names,
    );
    attribute_member_sites(
        &call_sites,
        &callfunc_by_member,
        inputs,
        mode,
        partitions,
        byte_to_node,
    );
}

/// Attribute member-var `EX_LET*` opcodes to matching
/// `K2Node_VariableSet` export(s) via last-segment FieldPath compared
/// against `VariableReference.MemberName`.
pub(super) fn attribute_variable_sets(
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let varset_by_member = build_variableset_member_index(inputs.asset, inputs.export_names);
    if varset_by_member.is_empty() {
        return;
    }
    let walk_ctx = WalkCtx::new(inputs.bytecode, inputs.name_table, inputs.ue5);
    let mut visitor = LetTargetVisitor {
        recorded: Vec::new(),
    };
    let mut cursor = 0usize;
    while cursor < inputs.bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    attribute_member_sites(
        &visitor.recorded,
        &varset_by_member,
        inputs,
        mode,
        partitions,
        byte_to_node,
    );
}

/// Attribute `EX_DynamicCast` / `EX_MetaCast` opcodes to matching
/// `K2Node_DynamicCast` export(s). Match key is the resolved class
/// reference operand compared against the K2Node's `TargetType`.
pub(super) fn attribute_dynamic_casts(
    inputs: &K2NodeByteMapInputs<'_>,
    mode: AttributionMode,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let cast_by_target = build_dynamic_cast_index(inputs.asset, inputs.export_names);
    if cast_by_target.is_empty() {
        return;
    }
    let walk_ctx = WalkCtx::new(inputs.bytecode, inputs.name_table, inputs.ue5);
    let mut visitor = CastSiteVisitor {
        imports: &inputs.asset.imports,
        export_names: inputs.export_names,
        recorded: Vec::new(),
    };
    let mut cursor = 0usize;
    while cursor < inputs.bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    attribute_member_sites(
        &visitor.recorded,
        &cast_by_target,
        inputs,
        mode,
        partitions,
        byte_to_node,
    );
}

/// Attribute the page's `K2Node_FunctionResult` node to the function's
/// `EX_Return` site(s). Function-map scope only (the ubergraph has no Result
/// nodes); skipped when the page has zero or several Result nodes (each
/// compiles its own return and the sites cannot be told apart by name).
///
/// A pure function's graph is pure expression nodes feeding the Result node,
/// so without this partition nothing on the page resolves and every comment
/// on it drops. The covering statement for a return site is the function's
/// tail statement (the decoded body strips the implicit trailing Return),
/// which is where the output computation lands.
pub(super) fn attribute_function_results(
    inputs: &K2NodeByteMapInputs<'_>,
    partitions: &mut BTreeMap<usize, K2NodePartition>,
    byte_to_node: &mut BTreeMap<usize, Vec<usize>>,
) {
    let GraphScope::FunctionPage(page) = inputs.scope else {
        return;
    };
    let result_nodes: Vec<usize> = inputs
        .asset
        .exports
        .iter()
        .enumerate()
        .filter_map(|(zero_based, (hdr, _))| {
            let one_based = zero_based + 1;
            let class = short_class(&resolve_index(
                &inputs.asset.imports,
                inputs.export_names,
                hdr.class_index,
            ));
            (class == "K2Node_FunctionResult"
                && enclosing_graph_name(inputs.asset, inputs.export_names, one_based).as_deref()
                    == Some(page))
            .then_some(one_based)
        })
        .collect();
    let [result_node] = result_nodes[..] else {
        return;
    };
    let walk_ctx = WalkCtx::new(inputs.bytecode, inputs.name_table, inputs.ue5);
    let mut visitor = ReturnSiteVisitor {
        offsets: Vec::new(),
    };
    let mut cursor = 0usize;
    while cursor < inputs.bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    if visitor.offsets.is_empty() {
        return;
    }
    let owners = owner_events_for_node(result_node, inputs);
    let partition = partitions.entry(result_node).or_insert_with(|| {
        K2NodePartition::new(
            result_node,
            owners.clone(),
            node_class(inputs, result_node),
            None,
        )
    });
    extend_owner_events(partition, owners);
    for offset in visitor.offsets {
        push_range(&mut partition.ranges, offset..offset + 1);
        byte_to_node.entry(offset).or_default().push(result_node);
    }
}

/// Records the disk offset of every `EX_Return` opcode.
struct ReturnSiteVisitor {
    offsets: Vec<usize>,
}

impl OpcodeVisitor for ReturnSiteVisitor {
    type Result = ();

    fn enter_opcode(&mut self, opcode: u8, start_offset: usize) {
        if opcode == EX_RETURN {
            self.offsets.push(start_offset);
        }
    }

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) -> Self::Result {}
}

/// Reverse the call-site list to a per-node-id offset list so the
/// downstream BFS unions offsets in O(1) per step.
pub(super) fn build_offsets_by_callfunc_node(
    inputs: &K2NodeByteMapInputs<'_>,
) -> HashMap<usize, Vec<usize>> {
    let callfunc_by_member = build_callfunc_member_index(inputs.asset, inputs.export_names);
    let call_sites = collect_call_sites(
        inputs.bytecode,
        inputs.name_table,
        inputs.ue5,
        inputs.asset,
        inputs.export_names,
    );
    let mut offsets: HashMap<usize, Vec<usize>> = HashMap::new();
    for (disk_offset, callee_short) in &call_sites {
        if let Some(nodes) = callfunc_by_member.get(callee_short) {
            for &node_id in nodes {
                offsets.entry(node_id).or_default().push(*disk_offset);
            }
        }
    }
    offsets
}

/// Per-node offset list for every `K2Node_VariableSet`, derived from
/// the same `EX_LET*` walk that `attribute_variable_sets` runs. Used
/// by macro-instance attribution so FlipFlop pin A / pin B downstream
/// VariableSets contribute offsets to the macro's range.
pub(super) fn build_offsets_by_varset_node(
    inputs: &K2NodeByteMapInputs<'_>,
) -> HashMap<usize, Vec<usize>> {
    let varset_by_member = build_variableset_member_index(inputs.asset, inputs.export_names);
    if varset_by_member.is_empty() {
        return HashMap::new();
    }
    let walk_ctx = WalkCtx::new(inputs.bytecode, inputs.name_table, inputs.ue5);
    let mut visitor = LetTargetVisitor {
        recorded: Vec::new(),
    };
    let mut cursor = 0usize;
    while cursor < inputs.bytecode.len() {
        walk_opcode(&walk_ctx, &mut cursor, &mut visitor);
    }
    let mut offsets: HashMap<usize, Vec<usize>> = HashMap::new();
    for (disk_offset, member_name) in visitor.recorded {
        if let Some(nodes) = varset_by_member.get(&member_name) {
            for &node_id in nodes {
                offsets.entry(node_id).or_default().push(disk_offset);
            }
        }
    }
    offsets
}

/// Member-name to node-id index for every `K2Node_VariableSet` with
/// a resolvable `VariableReference.MemberName`.
fn build_variableset_member_index(
    asset: &ParsedAsset,
    export_names: &[String],
) -> HashMap<String, Vec<usize>> {
    let mut index: HashMap<String, Vec<usize>> = HashMap::new();
    for (zero_based, (hdr, props)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = resolve_index(&asset.imports, export_names, hdr.class_index);
        if short_class(&class_full) != "K2Node_VariableSet" {
            continue;
        }
        let Some(member_name) = find_struct_field_str(props, "VariableReference", "MemberName")
        else {
            continue;
        };
        index
            .entry(normalise_member_name(&member_name))
            .or_default()
            .push(one_based);
    }
    index
}

/// Target-class to node-id index for every `K2Node_DynamicCast` with
/// a `TargetType` property. `TargetType` is an ObjectProperty package
/// index (verified at runtime on a UE 4.27 fixture; a string-rendered
/// object path is also accepted). Both forms key on the same short
/// class name [`CastSiteVisitor`] records for the cast operand via
/// `resolve_bc_obj`.
fn build_dynamic_cast_index(
    asset: &ParsedAsset,
    export_names: &[String],
) -> HashMap<String, Vec<usize>> {
    let mut index: HashMap<String, Vec<usize>> = HashMap::new();
    for (zero_based, (hdr, props)) in asset.exports.iter().enumerate() {
        let one_based = zero_based + 1;
        let class_full = resolve_index(&asset.imports, export_names, hdr.class_index);
        if short_class(&class_full) != "K2Node_DynamicCast" {
            continue;
        }
        let target_short = match find_prop(props, "TargetType").map(|prop| &prop.value) {
            Some(PropValue::Object(obj_idx)) => {
                resolve_bc_obj(*obj_idx, &asset.imports, export_names)
            }
            Some(PropValue::Str(path) | PropValue::Name(path)) => short_class(path),
            _ => continue,
        };
        index.entry(target_short).or_default().push(one_based);
    }
    index
}

/// Visitor that records `EX_LET*` target offsets and the target's
/// member-variable name. `EX_Let` / delegate LETs carry the name as a
/// field-path operand; the no-path variants (`EX_LetBool`, `EX_LetObj`,
/// `EX_LetWeakObjPtr`) carry it inside the destination expression, so
/// the variable-access hook hands its leaf one level up through the
/// walk result. All other opcodes fall through to the default `None`.
struct LetTargetVisitor {
    recorded: Vec<(usize, String)>,
}

impl LetTargetVisitor {
    fn leaf_member(path: &FieldPath) -> Option<String> {
        if path.is_null() || path.display.is_empty() {
            return None;
        }
        let leaf = path.display.rsplit("::").next().unwrap_or(&path.display);
        Some(normalise_member_name(leaf))
    }

    fn push_path(&mut self, start_offset: usize, path: &FieldPath) {
        if let Some(member) = Self::leaf_member(path) {
            self.recorded.push((start_offset, member));
        }
    }
}

impl OpcodeVisitor for LetTargetVisitor {
    /// Leaf member name of a variable-access expression, carried one
    /// level up so the no-path LET hooks can read their destination.
    type Result = Option<String>;

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) -> Self::Result {
        None
    }

    fn on_field_path_var(
        &mut self,
        _opcode: u8,
        path: FieldPath,
        _start_offset: usize,
    ) -> Self::Result {
        Self::leaf_member(&path)
    }

    fn on_let_with_path(
        &mut self,
        opcode: u8,
        path: FieldPath,
        _lhs: Self::Result,
        _rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(
            opcode == EX_LET || opcode == EX_LET_MULTICAST_DELEGATE || opcode == EX_LET_DELEGATE
        );
        self.push_path(start_offset, &path);
        None
    }

    fn on_let_no_path(
        &mut self,
        opcode: u8,
        lhs: Self::Result,
        _rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        debug_assert!(
            opcode == EX_LET_BOOL || opcode == EX_LET_OBJ || opcode == EX_LET_WEAK_OBJ_PTR
        );
        if let Some(member) = lhs {
            self.recorded.push((start_offset, member));
        }
        None
    }

    fn on_let_value_on_persistent_frame(
        &mut self,
        path: FieldPath,
        _value: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = EX_LET_VALUE_ON_PERSISTENT_FRAME;
        self.push_path(start_offset, &path);
        None
    }
}

/// Visitor that records `EX_DynamicCast` / `EX_MetaCast` opcode offsets
/// paired with their resolved class reference operand.
struct CastSiteVisitor<'a> {
    imports: &'a [crate::types::ImportEntry],
    export_names: &'a [String],
    recorded: Vec<(usize, String)>,
}

impl OpcodeVisitor for CastSiteVisitor<'_> {
    type Result = ();

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) -> Self::Result {}

    fn on_obj_cast(
        &mut self,
        opcode: u8,
        class_obj_idx: i32,
        _inner: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        if opcode != EX_DYNAMIC_CAST && opcode != EX_META_CAST {
            return;
        }
        let class_ref = resolve_bc_obj(class_obj_idx, self.imports, self.export_names);
        self.recorded.push((start_offset, class_ref));
    }
}
