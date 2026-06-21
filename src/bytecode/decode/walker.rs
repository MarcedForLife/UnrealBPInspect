//! Generic opcode walker driving an `OpcodeVisitor` trait.
//!
//! Single source of truth for the ~85-arm Kismet opcode dispatch: which
//! operand bytes each opcode consumes and how sub-expressions are arranged.
//! Boundary scan, drift accumulation, and expression decode all share this
//! walker; per-consumer semantics live in `OpcodeVisitor` impls rather than
//! parallel match arms.
//!
//! Each visit method receives pre-parsed operand values (literals,
//! resolved FNames, field-path strings) plus already-walked sub-expression
//! results. The walker itself owns the `pos` cursor and recursion.
//!
//! Adding a new opcode means adding one arm here. Each visitor decides
//! whether to override the relevant visit hook or accept the default
//! (typically a unit/no-op result).

use crate::binary::NameTable;
use crate::bytecode::opcodes::*;
use crate::bytecode::readers::{
    read_bc_f32, read_bc_f64, read_bc_fname, read_bc_i32, read_bc_i64, read_bc_string, read_bc_u16,
    read_bc_u32, read_bc_u64, read_bc_u8, read_bc_xyz, read_bc_xyzw,
};
use crate::types::VER_UE5_LARGE_WORLD_COORDINATES;

/// One arm of a `EX_SwitchValue` instruction as exposed to a visitor.
pub struct SwitchValueCase<R> {
    pub case_value: R,
    pub next_offset: u32,
    pub case_result: R,
}

/// Resolved FFieldPath operand. The walker exposes both the rendered
/// path (segment names joined by `"."`) and the segment count, so
/// visitors that need to compute disk/memory drift can do so without
/// re-parsing the byte stream.
#[derive(Clone, Default)]
pub struct FieldPath {
    /// Rendered path (`Path0.Path1...`), `"null"` for a null path
    /// (`path_num <= 0`), or `"???"` for a corrupt/over-deep operand.
    pub display: String,
    /// Number of name segments. Zero for null paths. Useful for drift
    /// arithmetic: disk size of a non-null path is `4 + segments*8 + 4`.
    pub segments: u32,
}

impl FieldPath {
    /// True for the null-path encoding (`path_num <= 0` on disk).
    pub fn is_null(&self) -> bool {
        self.segments == 0
    }

    /// The member leaf: the segment after the last `::`, or the whole
    /// display when there is no `::`. `None` for null/corrupt paths
    /// (`is_null`) and empty-display operands. Raw and un-normalised;
    /// callers apply their own canonicalisation (e.g. `normalise_member_name`).
    pub fn leaf_member(&self) -> Option<&str> {
        if self.is_null() || self.display.is_empty() {
            return None;
        }
        Some(self.display.rsplit("::").next().unwrap_or(&self.display))
    }
}

/// `EX_TextConst` payload variants. The text-const opcode prefixes a
/// 1-byte type tag, then operand layout depends on the tag. Several
/// variant fields (`Localised.namespace` / `.key`, `StringTable.
/// table_obj_idx`) are parsed for byte-stream advancement but not read
/// by any visitor, so the type carries a dead-code allow.
#[allow(dead_code)]
pub enum TextConstPayload<R> {
    /// Empty (tag 0) or sentinel (0xFF), no further operands.
    Empty,
    /// Localised text (tag 1): namespace + key + value sub-expressions.
    Localised { namespace: R, key: R, value: R },
    /// Invariant text (tag 2): single value sub-expression.
    Invariant { value: R },
    /// Literal text (tag 3): single value sub-expression.
    Literal { value: R },
    /// String table reference (tag 4): 4-byte object reference (the
    /// table) followed by a key sub-expression. The walker does not
    /// resolve the object reference; consumers that need to display
    /// it can re-read from the bytecode if necessary.
    StringTable { table_obj_idx: i32, key: R },
    /// Tag value the walker did not recognise; no further operands
    /// are consumed.
    Unknown(u8),
}

/// Visitor driven by `walk_opcode`. Each method receives a pre-parsed
/// operand bundle for one opcode. Default implementations return
/// `default_result()`, which most visitors implement once to suit
/// their result type.
///
/// The walker calls one visit method per opcode encountered and
/// returns whatever the visitor returns. Sub-expression results
/// are already-walked `Self::Result` values produced by recursive
/// calls into `walk_opcode`.
pub trait OpcodeVisitor {
    type Result;

    /// Called by the walker before reading any operand bytes for an
    /// opcode. Visitors that care about top-level vs nested context
    /// (e.g. recording control-flow successors only at depth 0)
    /// override this to maintain a depth counter. Default no-op.
    fn enter_opcode(&mut self, _opcode: u8, _start_offset: usize) {}

    /// Called by the walker after the visit method for the opcode
    /// returns, before propagating the result up. Pairs with
    /// [`enter_opcode`].
    fn exit_opcode(&mut self, _opcode: u8, _start_offset: usize) {}

    /// Default result returned for opcodes the visitor does not
    /// override. For length/drift visitors this is the unit value;
    /// for expression decoding this is a placeholder `Expr::Unknown`.
    fn default_result(&mut self, opcode: u8, start_offset: usize) -> Self::Result;

    fn on_zero_operand(&mut self, opcode: u8, start_offset: usize) -> Self::Result {
        self.default_result(opcode, start_offset)
    }

    fn on_jump(&mut self, opcode: u8, target: u32, start_offset: usize) -> Self::Result {
        let _ = (opcode, target);
        self.default_result(opcode, start_offset)
    }

    fn on_jump_if_not(
        &mut self,
        target: u32,
        condition: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (target, condition);
        self.default_result(EX_JUMP_IF_NOT, start_offset)
    }

    fn on_push_execution_flow(&mut self, target: u32, start_offset: usize) -> Self::Result {
        let _ = target;
        self.default_result(EX_PUSH_EXECUTION_FLOW, start_offset)
    }

    fn on_return(&mut self, value: Self::Result, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_RETURN, start_offset)
    }

    fn on_byte_const(&mut self, opcode: u8, value: u8, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(opcode, start_offset)
    }

    fn on_int_const(&mut self, value: i32, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_INT_CONST, start_offset)
    }

    fn on_int_const_passthrough(
        &mut self,
        opcode: u8,
        raw_bytes: [u8; 4],
        start_offset: usize,
    ) -> Self::Result {
        let _ = raw_bytes;
        self.default_result(opcode, start_offset)
    }

    fn on_float_const(&mut self, value: f32, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_FLOAT_CONST, start_offset)
    }

    fn on_int64_const(&mut self, value: i64, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_INT64_CONST, start_offset)
    }

    fn on_uint64_const(&mut self, value: u64, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_UINT64_CONST, start_offset)
    }

    fn on_double_const(&mut self, value: f64, start_offset: usize) -> Self::Result {
        let _ = value;
        self.default_result(EX_DOUBLE_CONST, start_offset)
    }

    fn on_string_const(&mut self, text: String, start_offset: usize) -> Self::Result {
        let _ = text;
        self.default_result(EX_STRING_CONST, start_offset)
    }

    fn on_unicode_string_const(&mut self, raw: Vec<u16>, start_offset: usize) -> Self::Result {
        let _ = raw;
        self.default_result(EX_UNICODE_STRING_CONST, start_offset)
    }

    fn on_object_const(&mut self, opcode: u8, obj_idx: i32, start_offset: usize) -> Self::Result {
        let _ = obj_idx;
        self.default_result(opcode, start_offset)
    }

    fn on_name_const(&mut self, name: String, start_offset: usize) -> Self::Result {
        let _ = name;
        self.default_result(EX_NAME_CONST, start_offset)
    }

    fn on_rotation_const(
        &mut self,
        pitch: f64,
        yaw: f64,
        roll: f64,
        lwc: bool,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (pitch, yaw, roll, lwc);
        self.default_result(EX_ROTATION_CONST, start_offset)
    }

    fn on_vector_const(
        &mut self,
        x: f64,
        y: f64,
        z: f64,
        lwc: bool,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (x, y, z, lwc);
        self.default_result(EX_VECTOR_CONST, start_offset)
    }

    fn on_vector3f_const_lwc(
        &mut self,
        x: f32,
        y: f32,
        z: f32,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (x, y, z);
        self.default_result(EX_VECTOR3F_CONST, start_offset)
    }

    /// UE4 fallback layout for `EX_VECTOR3F_CONST`: field-path + sub-expression,
    /// matching `EX_StructMemberContext`.
    fn on_vector3f_const_ue4(
        &mut self,
        path: FieldPath,
        struct_expr: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (path, struct_expr);
        self.default_result(EX_VECTOR3F_CONST, start_offset)
    }

    fn on_transform_const(
        &mut self,
        rotation: (f64, f64, f64, f64),
        translation: (f64, f64, f64),
        scale: (f64, f64, f64),
        lwc: bool,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (rotation, translation, scale, lwc);
        self.default_result(EX_TRANSFORM_CONST, start_offset)
    }

    fn on_bitfield_const(
        &mut self,
        path: FieldPath,
        value: u8,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (path, value);
        self.default_result(EX_BITFIELD_CONST, start_offset)
    }

    fn on_property_const(&mut self, path: FieldPath, start_offset: usize) -> Self::Result {
        let _ = path;
        self.default_result(EX_PROPERTY_CONST, start_offset)
    }

    fn on_text_const(
        &mut self,
        payload: TextConstPayload<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = payload;
        self.default_result(EX_TEXT_CONST, start_offset)
    }

    fn on_struct_const(
        &mut self,
        struct_obj_idx: i32,
        serial_size: i32,
        items: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (struct_obj_idx, serial_size, items);
        self.default_result(EX_STRUCT_CONST, start_offset)
    }

    fn on_array_const(
        &mut self,
        inner_obj_idx: i32,
        count: i32,
        items: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (inner_obj_idx, count, items);
        self.default_result(EX_ARRAY_CONST, start_offset)
    }

    fn on_set_const(
        &mut self,
        inner_obj_idx: i32,
        count: i32,
        items: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (inner_obj_idx, count, items);
        self.default_result(EX_SET_CONST, start_offset)
    }

    fn on_map_const(
        &mut self,
        key_obj_idx: i32,
        value_obj_idx: i32,
        count: i32,
        items: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (key_obj_idx, value_obj_idx, count, items);
        self.default_result(EX_MAP_CONST, start_offset)
    }

    /// Field-path-only variable references: `EX_LocalVariable`,
    /// `EX_InstanceVariable`, `EX_DefaultVariable`, `EX_LocalOutVariable`,
    /// `EX_ClassSparseDataVariable`.
    fn on_field_path_var(
        &mut self,
        opcode: u8,
        path: FieldPath,
        start_offset: usize,
    ) -> Self::Result {
        let _ = path;
        self.default_result(opcode, start_offset)
    }

    /// Object-reference + sub-expression cast opcodes:
    /// `EX_MetaCast`, `EX_DynamicCast`, `EX_ObjToInterfaceCast`,
    /// `EX_CrossInterfaceCast`, `EX_InterfaceToObjCast`.
    fn on_obj_cast(
        &mut self,
        opcode: u8,
        class_obj_idx: i32,
        inner: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (class_obj_idx, inner);
        self.default_result(opcode, start_offset)
    }

    fn on_interface_context(&mut self, inner: Self::Result, start_offset: usize) -> Self::Result {
        let _ = inner;
        self.default_result(EX_INTERFACE_CONTEXT, start_offset)
    }

    /// Member-access opcodes (`EX_Context`, `EX_ContextFailSilent`, `EX_ClassContext`).
    fn on_context(
        &mut self,
        opcode: u8,
        receiver: Self::Result,
        rvalue_skip: u32,
        rvalue_path: FieldPath,
        member: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (receiver, rvalue_skip, rvalue_path, member);
        self.default_result(opcode, start_offset)
    }

    fn on_struct_member_context(
        &mut self,
        path: FieldPath,
        struct_expr: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (path, struct_expr);
        self.default_result(EX_STRUCT_MEMBER_CONTEXT, start_offset)
    }

    /// Assignments with a leading field-path operand: `EX_Let`,
    /// `EX_LetMulticastDelegate`, `EX_LetDelegate`.
    fn on_let_with_path(
        &mut self,
        opcode: u8,
        path: FieldPath,
        lhs: Self::Result,
        rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (path, lhs, rhs);
        self.default_result(opcode, start_offset)
    }

    /// Assignments without a leading path operand: `EX_LetBool`,
    /// `EX_LetObj`, `EX_LetWeakObjPtr`.
    fn on_let_no_path(
        &mut self,
        opcode: u8,
        lhs: Self::Result,
        rhs: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (lhs, rhs);
        self.default_result(opcode, start_offset)
    }

    fn on_let_value_on_persistent_frame(
        &mut self,
        path: FieldPath,
        value: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (path, value);
        self.default_result(EX_LET_VALUE_ON_PERSISTENT_FRAME, start_offset)
    }

    /// `EX_VirtualFunction` / `EX_LocalVirtualFunction`. Function name is an FName.
    fn on_virtual_function(
        &mut self,
        opcode: u8,
        function_name: String,
        args: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (function_name, args);
        self.default_result(opcode, start_offset)
    }

    /// `EX_FinalFunction`, `EX_LocalFinalFunction`, `EX_CallMath`. Callee is an FPackageIndex.
    fn on_final_function(
        &mut self,
        opcode: u8,
        callee_obj_idx: i32,
        args: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (callee_obj_idx, args);
        self.default_result(opcode, start_offset)
    }

    fn on_primitive_cast(
        &mut self,
        cast_byte: u8,
        inner: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (cast_byte, inner);
        self.default_result(EX_PRIMITIVE_CAST, start_offset)
    }

    fn on_skip(&mut self, target: u32, inner: Self::Result, start_offset: usize) -> Self::Result {
        let _ = (target, inner);
        self.default_result(EX_SKIP, start_offset)
    }

    fn on_skip_offset_const(&mut self, target: u32, start_offset: usize) -> Self::Result {
        let _ = target;
        self.default_result(EX_SKIP_OFFSET_CONST, start_offset)
    }

    fn on_assert(
        &mut self,
        line_number: u16,
        debug_only: u8,
        condition: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (line_number, debug_only, condition);
        self.default_result(EX_ASSERT, start_offset)
    }

    /// Container mutation: `EX_SetArray`, `EX_SetSet`, `EX_SetMap`.
    fn on_set_container(
        &mut self,
        opcode: u8,
        target: Self::Result,
        items: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (target, items);
        self.default_result(opcode, start_offset)
    }

    fn on_instance_delegate(&mut self, name: String, start_offset: usize) -> Self::Result {
        let _ = name;
        self.default_result(EX_INSTANCE_DELEGATE, start_offset)
    }

    fn on_bind_delegate(
        &mut self,
        function_name: String,
        delegate: Self::Result,
        target: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (function_name, delegate, target);
        self.default_result(EX_BIND_DELEGATE, start_offset)
    }

    /// `EX_AddMulticastDelegate`, `EX_ClearMulticastDelegate`,
    /// `EX_RemoveMulticastDelegate`.
    fn on_multicast_delegate_op(
        &mut self,
        opcode: u8,
        delegate: Self::Result,
        target: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (delegate, target);
        self.default_result(opcode, start_offset)
    }

    fn on_call_multicast_delegate(
        &mut self,
        signature_obj_idx: i32,
        delegate: Self::Result,
        target: Self::Result,
        args: Vec<Self::Result>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (signature_obj_idx, delegate, target, args);
        self.default_result(EX_CALL_MULTICAST_DELEGATE, start_offset)
    }

    fn on_computed_jump(
        &mut self,
        target_expression: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = target_expression;
        self.default_result(EX_COMPUTED_JUMP, start_offset)
    }

    fn on_pop_flow_if_not(&mut self, condition: Self::Result, start_offset: usize) -> Self::Result {
        let _ = condition;
        self.default_result(EX_POP_FLOW_IF_NOT, start_offset)
    }

    fn on_switch_value(
        &mut self,
        end_offset: u32,
        index: Self::Result,
        cases: Vec<SwitchValueCase<Self::Result>>,
        default: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (end_offset, index, cases, default);
        self.default_result(EX_SWITCH_VALUE, start_offset)
    }

    fn on_instrumentation_event(
        &mut self,
        event_type: u8,
        event_name: Option<String>,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (event_type, event_name);
        self.default_result(EX_INSTRUMENTATION_EVENT, start_offset)
    }

    fn on_auto_rtfm_transact(
        &mut self,
        target_offset: u32,
        body: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (target_offset, body);
        self.default_result(EX_AUTO_RTFM_TRANSACT, start_offset)
    }

    fn on_auto_rtfm_stop_transact(&mut self, abort_flag: u8, start_offset: usize) -> Self::Result {
        let _ = abort_flag;
        self.default_result(EX_AUTO_RTFM_STOP_TRANSACT, start_offset)
    }

    fn on_field_path_const(&mut self, path: FieldPath, start_offset: usize) -> Self::Result {
        let _ = path;
        self.default_result(EX_FIELD_PATH_CONST, start_offset)
    }

    /// `EX_ArrayGetByRef`: array subscript. Two sub-expressions, array first.
    fn on_array_get_by_ref(
        &mut self,
        array: Self::Result,
        index: Self::Result,
        start_offset: usize,
    ) -> Self::Result {
        let _ = (array, index);
        self.default_result(EX_ARRAY_GET_BY_REF, start_offset)
    }

    /// Opcode the walker did not recognise. The opcode byte is already
    /// consumed; visitors typically emit a placeholder and rely on the
    /// caller's failsafe to advance `pos` if it stalls.
    fn on_unknown(&mut self, opcode: u8, start_offset: usize) -> Self::Result {
        self.default_result(opcode, start_offset)
    }
}

/// Inputs threaded through the walker. Consumers construct one and
/// pass it alongside their visitor.
pub struct WalkCtx<'a> {
    pub bytecode: &'a [u8],
    pub name_table: &'a NameTable,
    pub ue5: i32,
}

impl<'a> WalkCtx<'a> {
    /// Convenience constructor.
    pub fn new(bytecode: &'a [u8], name_table: &'a NameTable, ue5: i32) -> Self {
        Self {
            bytecode,
            name_table,
            ue5,
        }
    }

    fn lwc(&self) -> bool {
        self.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES
    }
}

/// Walk one opcode at `*pos`, advance past it, and return the visitor's
/// result. The visitor owns all consumer-specific behaviour. The walker
/// is the single source of truth for operand layouts.
pub fn walk_opcode<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
) -> V::Result {
    let start = *pos;
    if start >= ctx.bytecode.len() {
        return visitor.on_unknown(0, start);
    }

    let opcode = read_bc_u8(ctx.bytecode, pos);
    visitor.enter_opcode(opcode, start);
    let result = walk_opcode_dispatch(ctx, pos, visitor, opcode, start);
    visitor.exit_opcode(opcode, start);
    result
}

/// Body of the opcode dispatch, factored out so [`walk_opcode`] can wrap
/// it with `enter_opcode` / `exit_opcode` hook calls.
fn walk_opcode_dispatch<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> V::Result {
    let lwc = ctx.lwc();

    // Each category handler matches a disjoint opcode set and returns `Some`
    // for opcodes it owns. Opcodes never overlap across categories, so the
    // chaining order doesn't affect dispatch; each handler preserves the
    // exact operand layout of its original match arm.
    if let Some(result) = dispatch_const_literal(ctx, pos, visitor, opcode, lwc, start) {
        return result;
    }
    if let Some(result) = dispatch_var_field(ctx, pos, visitor, opcode, start) {
        return result;
    }
    if let Some(result) = dispatch_call(ctx, pos, visitor, opcode, start) {
        return result;
    }
    if let Some(result) = dispatch_cast(ctx, pos, visitor, opcode, start) {
        return result;
    }
    if let Some(result) = dispatch_container(ctx, pos, visitor, opcode, start) {
        return result;
    }
    if let Some(result) = dispatch_flow(ctx, pos, visitor, opcode, start) {
        return result;
    }
    // Anything else: opcode byte already consumed; emit unknown without
    // further advance. Callers rely on a stall failsafe.
    visitor.on_unknown(opcode, start)
}

/// Constant/literal opcodes (zero-operand sentinels, int/float/string/name,
/// vector/rotator/transform, bitfield/property, text, field-path,
/// instrumentation-event).
fn dispatch_const_literal<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    lwc: bool,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        // Zero-operand literals and sentinels.
        EX_INT_ZERO
        | EX_INT_ONE
        | EX_TRUE
        | EX_FALSE
        | EX_NO_OBJECT
        | EX_NO_INTERFACE
        | EX_SELF
        | EX_END_PARM_VALUE
        | EX_NOTHING
        | EX_POP_EXECUTION_FLOW
        | EX_BREAKPOINT
        | EX_WIRE_TRACEPOINT
        | EX_TRACEPOINT
        | EX_END_OF_SCRIPT
        | EX_END_FUNCTION_PARMS
        | EX_END_STRUCT_CONST
        | EX_END_ARRAY_CONST
        | EX_END_SET_CONST
        | EX_END_MAP_CONST
        | EX_END_ARRAY
        | EX_END_SET
        | EX_END_MAP => visitor.on_zero_operand(opcode, start),

        EX_BYTE_CONST | EX_INT_CONST_BYTE => {
            let value = read_bc_u8(ctx.bytecode, pos);
            visitor.on_byte_const(opcode, value, start)
        }
        EX_INT_CONST => {
            let value = read_bc_i32(ctx.bytecode, pos);
            visitor.on_int_const(value, start)
        }
        EX_NOTHING_INT32 => {
            // 4-byte payload, semantics opaque to the walker. Pass raw bytes through.
            let bytes_start = *pos;
            *pos += 4;
            let mut buffer = [0u8; 4];
            if bytes_start + 4 <= ctx.bytecode.len() {
                buffer.copy_from_slice(&ctx.bytecode[bytes_start..bytes_start + 4]);
            }
            visitor.on_int_const_passthrough(opcode, buffer, start)
        }
        EX_FLOAT_CONST => {
            let value = read_bc_f32(ctx.bytecode, pos);
            visitor.on_float_const(value, start)
        }
        EX_INT64_CONST => {
            let value = read_bc_i64(ctx.bytecode, pos);
            visitor.on_int64_const(value, start)
        }
        EX_UINT64_CONST => {
            let value = read_bc_u64(ctx.bytecode, pos);
            visitor.on_uint64_const(value, start)
        }
        EX_DOUBLE_CONST => {
            let value = read_bc_f64(ctx.bytecode, pos);
            visitor.on_double_const(value, start)
        }
        EX_STRING_CONST => {
            let text = read_bc_string(ctx.bytecode, pos);
            visitor.on_string_const(text, start)
        }
        EX_UNICODE_STRING_CONST => {
            let raw = read_unicode_string(ctx.bytecode, pos);
            visitor.on_unicode_string_const(raw, start)
        }

        EX_OBJECT_CONST | EX_SOFT_OBJECT_CONST => {
            let obj_idx = read_bc_i32(ctx.bytecode, pos);
            visitor.on_object_const(opcode, obj_idx, start)
        }
        EX_NAME_CONST => {
            let name = read_bc_fname(ctx.bytecode, pos, ctx.name_table);
            visitor.on_name_const(name, start)
        }

        EX_ROTATION_CONST => {
            let (pitch, yaw, roll) = read_bc_xyz(ctx.bytecode, pos, lwc);
            visitor.on_rotation_const(pitch, yaw, roll, lwc, start)
        }
        EX_VECTOR_CONST => {
            let (x, y, z) = read_bc_xyz(ctx.bytecode, pos, lwc);
            visitor.on_vector_const(x, y, z, lwc, start)
        }
        EX_VECTOR3F_CONST => {
            if lwc {
                let x = read_bc_f32(ctx.bytecode, pos);
                let y = read_bc_f32(ctx.bytecode, pos);
                let z = read_bc_f32(ctx.bytecode, pos);
                visitor.on_vector3f_const_lwc(x, y, z, start)
            } else {
                let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
                let struct_expr = walk_opcode(ctx, pos, visitor);
                visitor.on_vector3f_const_ue4(path, struct_expr, start)
            }
        }
        EX_TRANSFORM_CONST => {
            let rotation = read_bc_xyzw(ctx.bytecode, pos, lwc);
            let translation = read_bc_xyz(ctx.bytecode, pos, lwc);
            let scale = read_bc_xyz(ctx.bytecode, pos, lwc);
            visitor.on_transform_const(rotation, translation, scale, lwc, start)
        }

        EX_BITFIELD_CONST => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            let value = read_bc_u8(ctx.bytecode, pos);
            visitor.on_bitfield_const(path, value, start)
        }
        EX_PROPERTY_CONST => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            visitor.on_property_const(path, start)
        }

        EX_TEXT_CONST => {
            let payload = walk_text_const(ctx, pos, visitor);
            visitor.on_text_const(payload, start)
        }

        EX_INSTRUMENTATION_EVENT => {
            let event_type = read_bc_u8(ctx.bytecode, pos);
            let event_name = if event_type == 4 {
                Some(read_bc_fname(ctx.bytecode, pos, ctx.name_table))
            } else {
                None
            };
            visitor.on_instrumentation_event(event_type, event_name, start)
        }

        EX_FIELD_PATH_CONST => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            visitor.on_field_path_const(path, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Variable/field access, member contexts, assignments (EX_LET family),
/// array element-by-ref, and delegate binding/instance opcodes.
fn dispatch_var_field<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        EX_LOCAL_VARIABLE
        | EX_INSTANCE_VARIABLE
        | EX_DEFAULT_VARIABLE
        | EX_LOCAL_OUT_VARIABLE
        | EX_CLASS_SPARSE_DATA_VARIABLE => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            visitor.on_field_path_var(opcode, path, start)
        }

        EX_INTERFACE_CONTEXT => {
            let inner = walk_opcode(ctx, pos, visitor);
            visitor.on_interface_context(inner, start)
        }

        EX_CLASS_CONTEXT | EX_CONTEXT | EX_CONTEXT_FAIL_SILENT => {
            let receiver = walk_opcode(ctx, pos, visitor);
            let rvalue_skip = read_bc_u32(ctx.bytecode, pos);
            let rvalue_path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            let member = walk_opcode(ctx, pos, visitor);
            visitor.on_context(opcode, receiver, rvalue_skip, rvalue_path, member, start)
        }

        EX_STRUCT_MEMBER_CONTEXT => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            let struct_expr = walk_opcode(ctx, pos, visitor);
            visitor.on_struct_member_context(path, struct_expr, start)
        }

        EX_LET | EX_LET_MULTICAST_DELEGATE | EX_LET_DELEGATE => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            let lhs = walk_opcode(ctx, pos, visitor);
            let rhs = walk_opcode(ctx, pos, visitor);
            visitor.on_let_with_path(opcode, path, lhs, rhs, start)
        }
        EX_LET_BOOL | EX_LET_OBJ | EX_LET_WEAK_OBJ_PTR => {
            let lhs = walk_opcode(ctx, pos, visitor);
            let rhs = walk_opcode(ctx, pos, visitor);
            visitor.on_let_no_path(opcode, lhs, rhs, start)
        }
        EX_LET_VALUE_ON_PERSISTENT_FRAME => {
            let path = read_field_path(ctx.bytecode, pos, ctx.name_table);
            let value = walk_opcode(ctx, pos, visitor);
            visitor.on_let_value_on_persistent_frame(path, value, start)
        }

        EX_ARRAY_GET_BY_REF => {
            let array = walk_opcode(ctx, pos, visitor);
            let index = walk_opcode(ctx, pos, visitor);
            visitor.on_array_get_by_ref(array, index, start)
        }

        EX_INSTANCE_DELEGATE => {
            let name = read_bc_fname(ctx.bytecode, pos, ctx.name_table);
            visitor.on_instance_delegate(name, start)
        }
        EX_BIND_DELEGATE => {
            let function_name = read_bc_fname(ctx.bytecode, pos, ctx.name_table);
            let delegate = walk_opcode(ctx, pos, visitor);
            let target = walk_opcode(ctx, pos, visitor);
            visitor.on_bind_delegate(function_name, delegate, target, start)
        }
        EX_ADD_MULTICAST_DELEGATE | EX_CLEAR_MULTICAST_DELEGATE | EX_REMOVE_MULTICAST_DELEGATE => {
            let delegate = walk_opcode(ctx, pos, visitor);
            let target = walk_opcode(ctx, pos, visitor);
            visitor.on_multicast_delegate_op(opcode, delegate, target, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Function-call opcodes (virtual/final/math) and multicast-delegate calls.
fn dispatch_call<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        EX_VIRTUAL_FUNCTION | EX_LOCAL_VIRTUAL_FUNCTION => {
            let function_name = read_bc_fname(ctx.bytecode, pos, ctx.name_table);
            let args = walk_until(ctx, pos, visitor, EX_END_FUNCTION_PARMS);
            visitor.on_virtual_function(opcode, function_name, args, start)
        }
        EX_FINAL_FUNCTION | EX_LOCAL_FINAL_FUNCTION | EX_CALL_MATH => {
            let callee_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let args = walk_until(ctx, pos, visitor, EX_END_FUNCTION_PARMS);
            visitor.on_final_function(opcode, callee_obj_idx, args, start)
        }
        EX_CALL_MULTICAST_DELEGATE => {
            let signature_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let delegate = walk_opcode(ctx, pos, visitor);
            let target = walk_opcode(ctx, pos, visitor);
            let args = walk_until(ctx, pos, visitor, EX_END_FUNCTION_PARMS);
            visitor.on_call_multicast_delegate(signature_obj_idx, delegate, target, args, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Cast opcodes (object/interface casts plus the primitive numeric cast).
fn dispatch_cast<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        EX_META_CAST | EX_DYNAMIC_CAST | EX_OBJ_TO_IFACE_CAST | EX_CROSS_IFACE_CAST
        | EX_IFACE_TO_OBJ_CAST => {
            let class_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let inner = walk_opcode(ctx, pos, visitor);
            visitor.on_obj_cast(opcode, class_obj_idx, inner, start)
        }
        EX_PRIMITIVE_CAST => {
            let cast_byte = read_bc_u8(ctx.bytecode, pos);
            let inner = walk_opcode(ctx, pos, visitor);
            visitor.on_primitive_cast(cast_byte, inner, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Container literal opcodes (struct/array/set/map const) and the
/// in-place container assignment opcodes (EX_SetArray/Set/Map).
fn dispatch_container<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        EX_STRUCT_CONST => {
            let struct_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let serial_size = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_STRUCT_CONST);
            visitor.on_struct_const(struct_obj_idx, serial_size, items, start)
        }
        EX_ARRAY_CONST => {
            let inner_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let count = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_ARRAY_CONST);
            visitor.on_array_const(inner_obj_idx, count, items, start)
        }
        EX_SET_CONST => {
            let inner_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let count = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_SET_CONST);
            visitor.on_set_const(inner_obj_idx, count, items, start)
        }
        EX_MAP_CONST => {
            let key_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let value_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let count = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_MAP_CONST);
            visitor.on_map_const(key_obj_idx, value_obj_idx, count, items, start)
        }

        EX_SET_ARRAY => {
            let target = walk_opcode(ctx, pos, visitor);
            let items = walk_until(ctx, pos, visitor, EX_END_ARRAY);
            visitor.on_set_container(opcode, target, items, start)
        }
        EX_SET_SET => {
            let target = walk_opcode(ctx, pos, visitor);
            let _count = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_SET);
            visitor.on_set_container(opcode, target, items, start)
        }
        EX_SET_MAP => {
            let target = walk_opcode(ctx, pos, visitor);
            let _count = read_bc_i32(ctx.bytecode, pos);
            let items = walk_until(ctx, pos, visitor, EX_END_MAP);
            visitor.on_set_container(opcode, target, items, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Flow-control opcodes (return, jump, conditional jump, flow stack push/pop,
/// skip, assert, computed jump, switch-value, AutoRTFM transact).
fn dispatch_flow<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    opcode: u8,
    start: usize,
) -> Option<V::Result> {
    let result = match opcode {
        EX_RETURN => {
            let value = walk_opcode(ctx, pos, visitor);
            visitor.on_return(value, start)
        }
        EX_JUMP => {
            let target = read_bc_u32(ctx.bytecode, pos);
            visitor.on_jump(opcode, target, start)
        }
        EX_JUMP_IF_NOT => {
            let target = read_bc_u32(ctx.bytecode, pos);
            let condition = walk_opcode(ctx, pos, visitor);
            visitor.on_jump_if_not(target, condition, start)
        }
        EX_PUSH_EXECUTION_FLOW => {
            let target = read_bc_u32(ctx.bytecode, pos);
            visitor.on_push_execution_flow(target, start)
        }

        EX_SKIP => {
            let target = read_bc_u32(ctx.bytecode, pos);
            let inner = walk_opcode(ctx, pos, visitor);
            visitor.on_skip(target, inner, start)
        }
        EX_SKIP_OFFSET_CONST => {
            let target = read_bc_u32(ctx.bytecode, pos);
            visitor.on_skip_offset_const(target, start)
        }
        EX_ASSERT => {
            let line_number = read_bc_u16(ctx.bytecode, pos);
            let debug_only = read_bc_u8(ctx.bytecode, pos);
            let condition = walk_opcode(ctx, pos, visitor);
            visitor.on_assert(line_number, debug_only, condition, start)
        }

        EX_COMPUTED_JUMP => {
            let target_expression = walk_opcode(ctx, pos, visitor);
            visitor.on_computed_jump(target_expression, start)
        }
        EX_POP_FLOW_IF_NOT => {
            let condition = walk_opcode(ctx, pos, visitor);
            visitor.on_pop_flow_if_not(condition, start)
        }

        EX_SWITCH_VALUE => {
            let num_cases = read_bc_u16(ctx.bytecode, pos) as usize;
            let end_offset = read_bc_u32(ctx.bytecode, pos);
            let index = walk_opcode(ctx, pos, visitor);
            let mut cases = Vec::with_capacity(num_cases);
            for _ in 0..num_cases {
                let case_value = walk_opcode(ctx, pos, visitor);
                let next_offset = read_bc_u32(ctx.bytecode, pos);
                let case_result = walk_opcode(ctx, pos, visitor);
                cases.push(SwitchValueCase {
                    case_value,
                    next_offset,
                    case_result,
                });
            }
            let default = walk_opcode(ctx, pos, visitor);
            visitor.on_switch_value(end_offset, index, cases, default, start)
        }

        EX_AUTO_RTFM_TRANSACT => {
            let target_offset = read_bc_u32(ctx.bytecode, pos);
            let body = walk_opcode(ctx, pos, visitor);
            visitor.on_auto_rtfm_transact(target_offset, body, start)
        }
        EX_AUTO_RTFM_STOP_TRANSACT => {
            let abort_flag = read_bc_u8(ctx.bytecode, pos);
            visitor.on_auto_rtfm_stop_transact(abort_flag, start)
        }

        _ => return None,
    };
    Some(result)
}

/// Walk sub-expressions until the `terminator` opcode byte is seen.
/// The terminator byte is consumed.
fn walk_until<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
    terminator: u8,
) -> Vec<V::Result> {
    let mut items: Vec<V::Result> = Vec::new();
    loop {
        if *pos >= ctx.bytecode.len() {
            break;
        }
        if ctx.bytecode[*pos] == terminator {
            *pos += 1;
            break;
        }
        let before = *pos;
        items.push(walk_opcode(ctx, pos, visitor));
        if *pos == before {
            // Stall on unrecognised opcode: skip one byte to avoid an
            // infinite loop, the walker failsafe.
            *pos += 1;
        }
    }
    items
}

/// Walk an `EX_TextConst` payload after the opcode byte is consumed.
fn walk_text_const<V: OpcodeVisitor>(
    ctx: &WalkCtx<'_>,
    pos: &mut usize,
    visitor: &mut V,
) -> TextConstPayload<V::Result> {
    if *pos >= ctx.bytecode.len() {
        return TextConstPayload::Empty;
    }
    let text_type = read_bc_u8(ctx.bytecode, pos);
    match text_type {
        0 | 0xFF => TextConstPayload::Empty,
        1 => {
            let namespace = walk_opcode(ctx, pos, visitor);
            let key = walk_opcode(ctx, pos, visitor);
            let value = walk_opcode(ctx, pos, visitor);
            TextConstPayload::Localised {
                namespace,
                key,
                value,
            }
        }
        2 => {
            let value = walk_opcode(ctx, pos, visitor);
            TextConstPayload::Invariant { value }
        }
        3 => {
            let value = walk_opcode(ctx, pos, visitor);
            TextConstPayload::Literal { value }
        }
        4 => {
            let table_obj_idx = read_bc_i32(ctx.bytecode, pos);
            let key = walk_opcode(ctx, pos, visitor);
            TextConstPayload::StringTable { table_obj_idx, key }
        }
        other => TextConstPayload::Unknown(other),
    }
}

/// Read an FFieldPath operand. Disk format: `i32 path_num + path_num
/// FNames + i32 owner`. Returns the rendered display form (segments
/// joined by `"."`) plus the segment count for drift arithmetic.
/// Bounds-checked against `MAX_FIELD_PATH_DEPTH` so corrupt streams
/// don't trigger unbounded reads.
fn read_field_path(bytecode: &[u8], pos: &mut usize, name_table: &NameTable) -> FieldPath {
    /// Maximum FFieldPath depth. UE field paths are typically 1-3 levels
    /// deep; 16 is generous enough for any real asset while catching
    /// corrupt operands that would otherwise read garbage FNames.
    const MAX_FIELD_PATH_DEPTH: i32 = 16;

    let path_num = read_bc_i32(bytecode, pos);
    if path_num <= 0 {
        let _owner = read_bc_i32(bytecode, pos);
        return FieldPath {
            display: "null".into(),
            segments: 0,
        };
    }
    let needed = path_num as usize * 8 + 4;
    if path_num > MAX_FIELD_PATH_DEPTH || *pos + needed > bytecode.len() {
        let _owner = read_bc_i32(bytecode, pos);
        return FieldPath {
            display: "???".into(),
            segments: 0,
        };
    }
    let mut names: Vec<String> = Vec::with_capacity(path_num as usize);
    for _ in 0..path_num {
        let raw = read_bc_fname(bytecode, pos, name_table);
        names.push(crate::bytecode::names::clean_bc_name(&raw));
    }
    let _owner = read_bc_i32(bytecode, pos);
    FieldPath {
        display: names.join("."),
        segments: path_num as u32,
    }
}

/// Read a null-terminated UCS-2 (wide) string and return its raw u16
/// code units. Visitors can lossily decode to UTF-8 if needed.
fn read_unicode_string(bytecode: &[u8], pos: &mut usize) -> Vec<u16> {
    let mut units: Vec<u16> = Vec::new();
    while *pos + 1 < bytecode.len() {
        let low = bytecode[*pos];
        let high = bytecode[*pos + 1];
        *pos += 2;
        if low == 0 && high == 0 {
            break;
        }
        units.push(u16::from_le_bytes([low, high]));
    }
    units
}
