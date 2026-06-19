//! Expression decoder: Kismet opcodes into [`Expr`] nodes.
//!
//! `decode_expr` is a thin wrapper that drives the shared
//! [`walk_opcode`] dispatcher with an [`ExprVisitor`]. The visitor
//! converts each pre-parsed operand bundle into an `Expr` variant,
//! reusing the walker's recursion to assemble nested expression
//! trees. Out-of-scope opcodes surface as `Expr::Unknown` with the
//! original byte range so diagnostics can identify the gap.

use crate::bytecode::decode::walker::{
    walk_opcode, FieldPath, OpcodeVisitor, SwitchValueCase, TextConstPayload, WalkCtx,
};
use crate::bytecode::expr::{CastKind, Expr, SwitchExprCase};
use crate::bytecode::names::{clean_bc_name, normalize_lwc_name};
use crate::bytecode::opcodes::*;
use crate::bytecode::partition::opcode_length_at;
use crate::bytecode::resolve::resolve_bc_obj;
use crate::types::{ImportEntry, VER_UE5_LARGE_WORLD_COORDINATES};

use super::ctx::DecodeCtx;

/// Decode one expression starting at `*pos`, advancing `pos` past every
/// consumed byte. Returns an `Expr::Unknown` for opcodes the visitor does
/// not handle, with the raw bytes preserved for diagnostics.
pub(crate) fn decode_expr(pos: &mut usize, ctx: &DecodeCtx) -> Expr {
    let walk_ctx = WalkCtx::new(ctx.bytecode, ctx.name_table, ctx.ue5);
    let mut visitor = ExprVisitor {
        imports: ctx._imports,
        export_names: ctx._export_names,
        ue5: ctx.ue5,
        bytecode: ctx.bytecode,
        name_table: ctx.name_table,
    };
    walk_opcode(&walk_ctx, pos, &mut visitor)
}

/// Visitor that materialises an [`Expr`] tree from the walker's
/// per-opcode operand bundles. Holds borrowed references to the
/// import / export tables so it can resolve `FPackageIndex` operands
/// to display names without re-walking the asset.
struct ExprVisitor<'a> {
    imports: &'a [ImportEntry],
    export_names: &'a [String],
    ue5: i32,
    /// Raw bytecode slice, only consulted for the `Unknown` fallback
    /// (it copies a few bytes into the diagnostic blob).
    bytecode: &'a [u8],
    /// Name table, kept for symmetry with `WalkCtx` though the visitor
    /// does not currently re-read FNames after the walker has produced
    /// them.
    name_table: &'a crate::binary::NameTable,
}

impl ExprVisitor<'_> {
    /// Resolve a 4-byte FPackageIndex object reference to its display name.
    /// Uses [`resolve_bc_obj`] (not the wider `resolve_index`) so imports
    /// collapse through `short_class` and the `"Default__"` prefix is stripped.
    fn obj_name(&self, obj_idx: i32) -> String {
        let _ = self.name_table; // kept for future mem_adj symmetry
        resolve_bc_obj(obj_idx, self.imports, self.export_names)
    }

    /// Apply LWC normalisation and `clean_bc_name` to a raw function name.
    fn normalise_call_name(&self, raw: &str) -> String {
        clean_bc_name(&normalize_lwc_name(raw))
    }

    fn lwc(&self) -> bool {
        self.ue5 >= VER_UE5_LARGE_WORLD_COORDINATES
    }

    /// Map an `EX_PrimitiveCast` byte to a `CastKind`. Returns `None` for
    /// transparent casts (Large World Coordinates double/float conversions
    /// and the opaque obj-to-iface cast in UE5 slot 0) that should be
    /// elided at this level.
    fn map_primitive_cast(&self, cast_byte: u8) -> Option<CastKind> {
        if self.lwc() {
            match cast_byte {
                0x00 => None,                   // CST_ObjectToInterface, transparent
                0x01 => Some(CastKind::ToBool), // CST_ObjectToBool
                0x02 => Some(CastKind::ToBool), // CST_InterfaceToBool
                0x03 => None,                   // CST_DoubleToFloat, implicit narrowing
                0x04 => None,                   // CST_FloatToDouble, implicit widening
                other => Some(CastKind::Other(other)),
            }
        } else {
            // UE4 primitive cast 0x46 (CST_ObjectToInterface) has no
            // target class at this site, so it falls through to
            // `Other(0x46)` and renders as `(x as cast_0x46)`. Object-
            // cast opcodes (`EX_ObjToInterfaceCast`, etc.) carry a
            // class index and produce `ToInterface { target }`
            // through `on_obj_cast`.
            match cast_byte {
                0x41 => Some(CastKind::ToObject), // CST_InterfaceToObject
                0x47 => Some(CastKind::ToBool),   // CST_ObjectToBool
                0x49 => Some(CastKind::ToBool),   // CST_InterfaceToBool
                other => Some(CastKind::Other(other)),
            }
        }
    }

    /// Build an `Expr::Unknown` for an opcode the visitor does not
    /// recognise. The walker has already consumed the operand bytes,
    /// so we use `opcode_length_at` to figure out how many bytes to
    /// preserve for diagnostics.
    fn unknown_for(&self, opcode: u8, start_offset: usize) -> Expr {
        let length = opcode_length_at(start_offset, self.bytecode, self.ue5, self.name_table);
        let end = (start_offset + length).min(self.bytecode.len());
        let raw_bytes = self.bytecode[start_offset..end].to_vec();
        Expr::Unknown {
            reason: format!("opcode 0x{:02x} not decoded", opcode),
            raw_bytes,
            offset: start_offset,
        }
    }

    /// Format an `Expr` for inline use inside `Literal` text (text
    /// constants, field-name fallbacks). Diagnostic-only; not used for
    /// full pseudocode emission.
    fn expr_display(expr: &Expr) -> String {
        match expr {
            Expr::Literal(text) => text.clone(),
            Expr::Var(name) => name.clone(),
            Expr::Call { name, args } => {
                let arg_strs: Vec<String> = args.iter().map(Self::expr_display).collect();
                format!("{}({})", name, arg_strs.join(", "))
            }
            Expr::Unknown { reason, offset, .. } => {
                format!("?[0x{:x}: {}]", offset, reason)
            }
            _ => "?".into(),
        }
    }

    /// Extract the field-name string for `Expr::FieldAccess` when the
    /// member side of a context decoded as something other than a call.
    fn expr_to_field_name(expr: &Expr) -> String {
        match expr {
            Expr::Var(name) => name.clone(),
            Expr::Literal(val) => val.clone(),
            _ => Self::expr_display(expr),
        }
    }
}

impl OpcodeVisitor for ExprVisitor<'_> {
    type Result = Expr;

    fn default_result(&mut self, opcode: u8, start_offset: usize) -> Expr {
        self.unknown_for(opcode, start_offset)
    }

    fn on_zero_operand(&mut self, opcode: u8, start_offset: usize) -> Expr {
        match opcode {
            EX_TRUE => Expr::Literal("true".into()),
            EX_FALSE => Expr::Literal("false".into()),
            EX_SELF => Expr::Literal("self".into()),
            EX_NO_OBJECT | EX_NO_INTERFACE => Expr::Literal("None".into()),
            EX_INT_ZERO => Expr::Literal("0".into()),
            EX_INT_ONE => Expr::Literal("1".into()),
            EX_BREAKPOINT => Expr::Literal("BreakPoint".into()),
            EX_TRACEPOINT => Expr::Literal("Tracepoint".into()),
            EX_WIRE_TRACEPOINT => Expr::Literal("WireTracepoint".into()),
            _ => self.unknown_for(opcode, start_offset),
        }
    }

    fn on_int_const(&mut self, value: i32, _start_offset: usize) -> Expr {
        Expr::Literal(value.to_string())
    }

    fn on_int64_const(&mut self, value: i64, _start_offset: usize) -> Expr {
        Expr::Literal(format!("{}L", value))
    }

    fn on_uint64_const(&mut self, value: u64, _start_offset: usize) -> Expr {
        Expr::Literal(format!("{}UL", value))
    }

    fn on_byte_const(&mut self, _opcode: u8, value: u8, _start_offset: usize) -> Expr {
        Expr::Literal(value.to_string())
    }

    fn on_float_const(&mut self, value: f32, _start_offset: usize) -> Expr {
        Expr::Literal(format!("{:.4}", value))
    }

    fn on_double_const(&mut self, value: f64, _start_offset: usize) -> Expr {
        Expr::Literal(format!("{:.4}", value))
    }

    fn on_string_const(&mut self, text: String, _start_offset: usize) -> Expr {
        Expr::Literal(format!("\"{}\"", text))
    }

    fn on_unicode_string_const(&mut self, raw: Vec<u16>, _start_offset: usize) -> Expr {
        let text = String::from_utf16_lossy(&raw);
        Expr::Literal(format!("\"{}\"", text))
    }

    fn on_object_const(&mut self, _opcode: u8, obj_idx: i32, _start_offset: usize) -> Expr {
        Expr::Literal(self.obj_name(obj_idx))
    }

    fn on_name_const(&mut self, name: String, _start_offset: usize) -> Expr {
        Expr::Literal(format!("'{}'", name))
    }

    fn on_rotation_const(
        &mut self,
        pitch: f64,
        yaw: f64,
        roll: f64,
        _lwc: bool,
        _start_offset: usize,
    ) -> Expr {
        Expr::Literal(format!("Rot({:.4},{:.4},{:.4})", pitch, yaw, roll))
    }

    fn on_vector_const(
        &mut self,
        x: f64,
        y: f64,
        z: f64,
        _lwc: bool,
        _start_offset: usize,
    ) -> Expr {
        Expr::Literal(format!("Vec({:.4},{:.4},{:.4})", x, y, z))
    }

    fn on_vector3f_const_lwc(&mut self, x: f32, y: f32, z: f32, _start_offset: usize) -> Expr {
        Expr::Literal(format!("Vec3f({:.4},{:.4},{:.4})", x, y, z))
    }

    fn on_vector3f_const_ue4(
        &mut self,
        _path: FieldPath,
        _struct_expr: Expr,
        start_offset: usize,
    ) -> Expr {
        // UE4 fallback layout for `EX_VECTOR3F_CONST` is the
        // `EX_StructMemberContext` shape, emitted as a placeholder rather
        // than surfaced as a literal.
        self.unknown_for(EX_VECTOR3F_CONST, start_offset)
    }

    fn on_transform_const(
        &mut self,
        rotation: (f64, f64, f64, f64),
        translation: (f64, f64, f64),
        scale: (f64, f64, f64),
        _lwc: bool,
        _start_offset: usize,
    ) -> Expr {
        let (rx, ry, rz, rw) = rotation;
        let (tx, ty, tz) = translation;
        let (sx, sy, sz) = scale;
        Expr::Literal(format!(
            "Transform(Rot({:.4},{:.4},{:.4},{:.4}),Pos({:.4},{:.4},{:.4}),Scale({:.4},{:.4},{:.4}))",
            rx, ry, rz, rw, tx, ty, tz, sx, sy, sz
        ))
    }

    fn on_text_const(&mut self, payload: TextConstPayload<Expr>, _start_offset: usize) -> Expr {
        let text = match payload {
            TextConstPayload::Empty => "\"\"".into(),
            TextConstPayload::Localised { value, .. } => {
                format!("LOCTEXT({})", Self::expr_display(&value))
            }
            TextConstPayload::Invariant { value } => Self::expr_display(&value),
            TextConstPayload::Literal { value } => Self::expr_display(&value),
            TextConstPayload::StringTable { key, .. } => {
                format!("STRTABLE({})", Self::expr_display(&key))
            }
            TextConstPayload::Unknown(other) => format!("text(type={})", other),
        };
        Expr::Literal(text)
    }

    fn on_field_path_var(&mut self, opcode: u8, path: FieldPath, _start_offset: usize) -> Expr {
        // Prefix table: instance/default/sparse variables get a qualifying
        // receiver baked into the rendered name, local variables and
        // out-parameters do not.
        let prefix = match opcode {
            EX_INSTANCE_VARIABLE => "self.",
            EX_DEFAULT_VARIABLE => "default.",
            EX_CLASS_SPARSE_DATA_VARIABLE => "sparse.",
            _ => "",
        };
        let display = if prefix.is_empty() {
            path.display
        } else {
            format!("{}{}", prefix, path.display)
        };
        let var = Expr::Var(display);
        if opcode == EX_LOCAL_OUT_VARIABLE {
            // The outer function declared this slot as an OUT parameter.
            // Preserve that ABI distinction; downstream transforms peel
            // through Out where they need the bare Var.
            Expr::Out(Box::new(var))
        } else {
            var
        }
    }

    fn on_virtual_function(
        &mut self,
        _opcode: u8,
        function_name: String,
        args: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        Expr::Call {
            name: self.normalise_call_name(&function_name),
            args,
        }
    }

    fn on_final_function(
        &mut self,
        _opcode: u8,
        callee_obj_idx: i32,
        args: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        let raw_name = self.obj_name(callee_obj_idx);
        Expr::Call {
            name: self.normalise_call_name(&raw_name),
            args,
        }
    }

    fn on_context(
        &mut self,
        _opcode: u8,
        receiver: Expr,
        _rvalue_skip: u32,
        _rvalue_path: FieldPath,
        member: Expr,
        _start_offset: usize,
    ) -> Expr {
        match member {
            Expr::Call { name, args } => Expr::MethodCall {
                recv: Box::new(receiver),
                name,
                args,
            },
            Expr::Unknown { .. } => member,
            other => {
                // The member side already qualified itself with `self.`
                // when it was an EX_INSTANCE_VARIABLE. With an explicit
                // receiver in scope that prefix would double up, so peel
                // it off here.
                let raw_field = Self::expr_to_field_name(&other);
                let field = raw_field
                    .strip_prefix("self.")
                    .map(|stripped| stripped.to_string())
                    .unwrap_or(raw_field);
                Expr::FieldAccess {
                    recv: Box::new(receiver),
                    field,
                }
            }
        }
    }

    fn on_obj_cast(
        &mut self,
        opcode: u8,
        class_obj_idx: i32,
        inner: Expr,
        _start_offset: usize,
    ) -> Expr {
        // Resolve the target class once; variants that don't need it
        // (`ToObject`, `Other`) ignore the result.
        let target = self.obj_name(class_obj_idx);
        let kind = match opcode {
            EX_DYNAMIC_CAST | EX_META_CAST => CastKind::Class { target },
            EX_OBJ_TO_IFACE_CAST | EX_CROSS_IFACE_CAST => CastKind::ToInterface { target },
            EX_IFACE_TO_OBJ_CAST => CastKind::ToObject,
            _ => CastKind::Other(opcode),
        };
        Expr::Cast {
            kind,
            inner: Box::new(inner),
        }
    }

    fn on_interface_context(&mut self, inner: Expr, _start_offset: usize) -> Expr {
        Expr::Interface(Box::new(inner))
    }

    fn on_primitive_cast(&mut self, cast_byte: u8, inner: Expr, _start_offset: usize) -> Expr {
        match self.map_primitive_cast(cast_byte) {
            None => inner,
            Some(kind) => Expr::Cast {
                kind,
                inner: Box::new(inner),
            },
        }
    }

    fn on_struct_const(
        &mut self,
        struct_obj_idx: i32,
        _serial_size: i32,
        items: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        let raw_name = self.obj_name(struct_obj_idx);
        Expr::Call {
            name: format!("Make{}", raw_name),
            args: items,
        }
    }

    fn on_array_const(
        &mut self,
        _inner_obj_idx: i32,
        _count: i32,
        items: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        Expr::ArrayLit(items)
    }

    fn on_set_const(
        &mut self,
        _inner_obj_idx: i32,
        _count: i32,
        items: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        Expr::Call {
            name: "SetConst".into(),
            args: items,
        }
    }

    fn on_map_const(
        &mut self,
        _key_obj_idx: i32,
        _value_obj_idx: i32,
        _count: i32,
        items: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        Expr::Call {
            name: "MapConst".into(),
            args: items,
        }
    }

    fn on_set_container(
        &mut self,
        opcode: u8,
        target: Expr,
        items: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        let name = match opcode {
            EX_SET_ARRAY => "SetArray",
            EX_SET_SET => "SetSet",
            EX_SET_MAP => "SetMap",
            _ => "SetContainer",
        };
        let mut args = Vec::with_capacity(1 + items.len());
        args.push(target);
        args.extend(items);
        Expr::Call {
            name: name.into(),
            args,
        }
    }

    fn on_instance_delegate(&mut self, name: String, _start_offset: usize) -> Expr {
        Expr::Literal(format!("'{}'", name))
    }

    fn on_bind_delegate(
        &mut self,
        function_name: String,
        delegate: Expr,
        target: Expr,
        _start_offset: usize,
    ) -> Expr {
        Expr::Call {
            name: format!("BindDelegate<{}>", function_name),
            args: vec![delegate, target],
        }
    }

    fn on_multicast_delegate_op(
        &mut self,
        opcode: u8,
        delegate: Expr,
        target: Expr,
        _start_offset: usize,
    ) -> Expr {
        let name = match opcode {
            EX_ADD_MULTICAST_DELEGATE => "AddMulticastDelegate",
            EX_REMOVE_MULTICAST_DELEGATE => "RemoveMulticastDelegate",
            EX_CLEAR_MULTICAST_DELEGATE => "ClearMulticastDelegate",
            _ => "MulticastDelegateOp",
        };
        Expr::Call {
            name: name.into(),
            args: vec![delegate, target],
        }
    }

    fn on_call_multicast_delegate(
        &mut self,
        _signature_obj_idx: i32,
        delegate: Expr,
        target: Expr,
        args: Vec<Expr>,
        _start_offset: usize,
    ) -> Expr {
        let mut all_args = vec![delegate, target];
        all_args.extend(args);
        Expr::Call {
            name: "CallMulticastDelegate".into(),
            args: all_args,
        }
    }

    fn on_bitfield_const(&mut self, path: FieldPath, value: u8, _start_offset: usize) -> Expr {
        Expr::Literal(format!("BitFieldConst('{}', {})", path.display, value))
    }

    fn on_property_const(&mut self, path: FieldPath, _start_offset: usize) -> Expr {
        Expr::Literal(format!("PropertyConst('{}')", path.display))
    }

    fn on_struct_member_context(
        &mut self,
        path: FieldPath,
        struct_expr: Expr,
        _start_offset: usize,
    ) -> Expr {
        Expr::FieldAccess {
            recv: Box::new(struct_expr),
            field: path.display,
        }
    }

    fn on_field_path_const(&mut self, path: FieldPath, _start_offset: usize) -> Expr {
        Expr::Literal(format!("FieldPath('{}')", path.display))
    }

    fn on_instrumentation_event(
        &mut self,
        event_type: u8,
        event_name: Option<String>,
        _start_offset: usize,
    ) -> Expr {
        let label = match event_name {
            Some(name) => name,
            None => format!("{}", event_type),
        };
        Expr::Literal(format!("InstrumentationEvent({})", label))
    }

    fn on_auto_rtfm_transact(
        &mut self,
        _target_offset: u32,
        body: Expr,
        _start_offset: usize,
    ) -> Expr {
        Expr::Call {
            name: "AutoRtfmTransact".into(),
            args: vec![body],
        }
    }

    fn on_auto_rtfm_stop_transact(&mut self, _abort_flag: u8, _start_offset: usize) -> Expr {
        Expr::Literal("AutoRtfmStopTransact".into())
    }

    fn on_array_get_by_ref(&mut self, array: Expr, index: Expr, _start_offset: usize) -> Expr {
        Expr::Index {
            recv: Box::new(array),
            idx: Box::new(index),
        }
    }

    /// `EX_SkipOffsetConst` (0x5b) in expression position. The walker
    /// has already consumed the 4-byte linkage offset; render it as a
    /// `skip_offset(0xHEX)` literal.
    fn on_skip_offset_const(&mut self, target: u32, _start_offset: usize) -> Expr {
        Expr::Literal(format!("skip_offset(0x{:x})", target))
    }

    /// `EX_SwitchValue` (0x69) at expression position. The walker has
    /// already decoded the index, each case's value/body pair, and the
    /// default expression; map them straight into `Expr::Switch`. The
    /// per-case `next_offset` jump targets are walker-internal metadata,
    /// the IR has no place for them.
    fn on_switch_value(
        &mut self,
        _end_offset: u32,
        index: Expr,
        cases: Vec<SwitchValueCase<Expr>>,
        default: Expr,
        _start_offset: usize,
    ) -> Expr {
        let cases = cases
            .into_iter()
            .map(|case| SwitchExprCase {
                value: case.case_value,
                body: case.case_result,
            })
            .collect();
        Expr::Switch {
            index: Box::new(index),
            cases,
            default: Box::new(default),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::NameTable;
    use crate::bytecode::decode::ctx::DecodeCtx;

    fn make_name_table(names: &[&str]) -> NameTable {
        NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
    }

    fn make_ctx<'a>(
        stream: &'a [u8],
        name_table: &'a NameTable,
        imports: &'a [crate::types::ImportEntry],
        export_names: &'a [String],
        ue5: i32,
    ) -> DecodeCtx<'a> {
        DecodeCtx::new(stream, name_table, imports, export_names, ue5)
    }

    use super::super::test_fixtures::{put_field_path, put_fname, put_i32};

    #[test]
    fn decodes_local_variable() {
        let name_table = make_name_table(&["MyVar"]);
        let mut stream = vec![EX_LOCAL_VARIABLE];
        put_field_path(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Var("MyVar".into()));
        assert_eq!(pos, stream.len());
    }

    #[test]
    fn local_out_variable_wraps_in_expr_out() {
        let name_table = make_name_table(&["OutSlot"]);
        let mut stream = vec![EX_LOCAL_OUT_VARIABLE];
        put_field_path(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Out(Box::new(Expr::Var("OutSlot".into()))));
        assert_eq!(pos, stream.len());
    }

    #[test]
    fn decodes_int_const() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_INT_CONST];
        put_i32(&mut stream, 42);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("42".into()));
        assert_eq!(pos, stream.len());
    }

    #[test]
    fn decodes_string_const() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_STRING_CONST];
        stream.extend_from_slice(b"hello");
        stream.push(0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("\"hello\"".into()));
    }

    #[test]
    fn decodes_name_const() {
        let name_table = make_name_table(&["MyName"]);
        let mut stream = vec![EX_NAME_CONST];
        put_fname(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("'MyName'".into()));
    }

    #[test]
    fn decodes_true_false_self() {
        let name_table = make_name_table(&[]);
        let stream_true = [EX_TRUE];
        let stream_false = [EX_FALSE];
        let stream_self = [EX_SELF];

        let ctx = make_ctx(&stream_true, &name_table, &[], &[], 0);
        let mut pos = 0;
        assert_eq!(decode_expr(&mut pos, &ctx), Expr::Literal("true".into()));

        let ctx = make_ctx(&stream_false, &name_table, &[], &[], 0);
        pos = 0;
        assert_eq!(decode_expr(&mut pos, &ctx), Expr::Literal("false".into()));

        let ctx = make_ctx(&stream_self, &name_table, &[], &[], 0);
        pos = 0;
        assert_eq!(decode_expr(&mut pos, &ctx), Expr::Literal("self".into()));
    }

    #[test]
    fn decodes_no_object_no_interface_to_none() {
        let name_table = make_name_table(&[]);
        let stream_no_obj = [EX_NO_OBJECT];
        let ctx = make_ctx(&stream_no_obj, &name_table, &[], &[], 0);
        let mut pos = 0;
        assert_eq!(decode_expr(&mut pos, &ctx), Expr::Literal("None".into()));

        let stream_no_iface = [EX_NO_INTERFACE];
        let ctx = make_ctx(&stream_no_iface, &name_table, &[], &[], 0);
        pos = 0;
        assert_eq!(decode_expr(&mut pos, &ctx), Expr::Literal("None".into()));
    }

    #[test]
    fn decodes_virtual_function_call() {
        let name_table = make_name_table(&["DoThing"]);
        let mut stream = vec![EX_VIRTUAL_FUNCTION];
        put_fname(&mut stream, 0);
        stream.push(EX_INT_ZERO);
        stream.push(EX_END_FUNCTION_PARMS);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        match result {
            Expr::Call { name, args } => {
                assert!(name.contains("DoThing"));
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], Expr::Literal("0".into()));
            }
            other => panic!("expected Call, got {:?}", other),
        }
    }

    #[test]
    fn decodes_final_function_call_no_args() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_FINAL_FUNCTION];
        put_i32(&mut stream, 0);
        stream.push(EX_END_FUNCTION_PARMS);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Call { args, .. } = result {
            assert_eq!(args.len(), 0);
        } else {
            panic!("expected Call");
        }
    }

    #[test]
    fn decodes_primitive_cast_transparent_lwc() {
        // UE5 LWC primitive cast 0x03 = CST_DoubleToFloat (transparent).
        let name_table = make_name_table(&[]);
        let stream = [EX_PRIMITIVE_CAST, 0x03, EX_SELF];
        let ctx = make_ctx(
            &stream,
            &name_table,
            &[],
            &[],
            VER_UE5_LARGE_WORLD_COORDINATES,
        );
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("self".into()));
    }

    #[test]
    fn decodes_interface_context() {
        let name_table = make_name_table(&[]);
        let stream = [EX_INTERFACE_CONTEXT, EX_SELF];
        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Interface(inner) = result {
            assert_eq!(*inner, Expr::Literal("self".into()));
        } else {
            panic!("expected Interface, got {:?}", result);
        }
    }

    #[test]
    fn decodes_context_to_methodcall() {
        let name_table = make_name_table(&["FieldProp", "Foo"]);
        let mut stream = vec![EX_CONTEXT];
        stream.push(EX_SELF);
        put_i32(&mut stream, 0);
        put_field_path(&mut stream, 0);
        stream.push(EX_VIRTUAL_FUNCTION);
        put_fname(&mut stream, 1);
        stream.push(EX_END_FUNCTION_PARMS);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::MethodCall { recv, name, args } = result {
            assert_eq!(*recv, Expr::Literal("self".into()));
            assert!(name.contains("Foo"));
            assert_eq!(args.len(), 0);
        } else {
            panic!("expected MethodCall, got {:?}", result);
        }
    }

    #[test]
    fn decodes_text_const_empty() {
        let name_table = make_name_table(&[]);
        let stream = [EX_TEXT_CONST, 0];

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("\"\"".into()));
    }

    #[test]
    fn decodes_text_const_literal() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_TEXT_CONST, 3];
        stream.push(EX_STRING_CONST);
        stream.extend_from_slice(b"hi\0");

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Literal(text) = result {
            assert!(text.contains("hi"));
        } else {
            panic!("expected Literal");
        }
    }

    #[test]
    fn decodes_vector_const_ue4() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_VECTOR_CONST];
        stream.extend_from_slice(&f32::to_le_bytes(1.0));
        stream.extend_from_slice(&f32::to_le_bytes(2.0));
        stream.extend_from_slice(&f32::to_le_bytes(3.0));

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Literal(text) = result {
            assert!(text.starts_with("Vec("), "got: {}", text);
        } else {
            panic!("expected Literal");
        }
    }

    #[test]
    fn decodes_breakpoint_tracepoint_wiretracepoint() {
        let name_table = make_name_table(&[]);

        let stream_bp = [EX_BREAKPOINT];
        let ctx = make_ctx(&stream_bp, &name_table, &[], &[], 0);
        let mut pos = 0;
        assert_eq!(
            decode_expr(&mut pos, &ctx),
            Expr::Literal("BreakPoint".into())
        );

        let stream_tp = [EX_TRACEPOINT];
        let ctx = make_ctx(&stream_tp, &name_table, &[], &[], 0);
        pos = 0;
        assert_eq!(
            decode_expr(&mut pos, &ctx),
            Expr::Literal("Tracepoint".into())
        );

        let stream_wt = [EX_WIRE_TRACEPOINT];
        let ctx = make_ctx(&stream_wt, &name_table, &[], &[], 0);
        pos = 0;
        assert_eq!(
            decode_expr(&mut pos, &ctx),
            Expr::Literal("WireTracepoint".into())
        );
    }

    #[test]
    fn decodes_field_path_const() {
        let name_table = make_name_table(&["MyField"]);
        let mut stream = vec![EX_FIELD_PATH_CONST];
        put_field_path(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Literal(text) = result {
            assert!(text.contains("MyField"), "got: {}", text);
            assert!(text.starts_with("FieldPath("), "got: {}", text);
        } else {
            panic!("expected Literal, got {:?}", result);
        }
    }

    #[test]
    fn decodes_property_const() {
        let name_table = make_name_table(&["SomeProp"]);
        let mut stream = vec![EX_PROPERTY_CONST];
        put_field_path(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Literal(text) = result {
            assert!(text.contains("SomeProp"), "got: {}", text);
            assert!(text.starts_with("PropertyConst("), "got: {}", text);
        } else {
            panic!("expected Literal, got {:?}", result);
        }
    }

    #[test]
    fn decodes_struct_member_context() {
        let name_table = make_name_table(&["XField"]);
        let mut stream = vec![EX_STRUCT_MEMBER_CONTEXT];
        put_field_path(&mut stream, 0);
        stream.push(EX_SELF);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::FieldAccess { recv, field } = result {
            assert_eq!(*recv, Expr::Literal("self".into()));
            assert_eq!(field, "XField");
        } else {
            panic!("expected FieldAccess, got {:?}", result);
        }
    }

    #[test]
    fn decodes_instrumentation_event_no_name() {
        let name_table = make_name_table(&[]);
        let stream = [EX_INSTRUMENTATION_EVENT, 2];

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("InstrumentationEvent(2)".into()));
    }

    #[test]
    fn decodes_instrumentation_event_with_name() {
        let name_table = make_name_table(&["BeginEvent"]);
        let mut stream = vec![EX_INSTRUMENTATION_EVENT, 4];
        put_fname(&mut stream, 0);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        if let Expr::Literal(text) = result {
            assert!(text.contains("BeginEvent"), "got: {}", text);
        } else {
            panic!("expected Literal, got {:?}", result);
        }
    }

    #[test]
    fn decodes_object_const_resolves_export_name() {
        // EX_ObjectConst (0x20) with a positive FPackageIndex resolves to
        // the matching export name. Previously fell through to Expr::Unknown.
        let name_table = make_name_table(&[]);
        let export_names = vec!["MyActor".to_string()];
        let mut stream = vec![EX_OBJECT_CONST];
        put_i32(&mut stream, 1); // FPackageIndex 1 => export_names[0]

        let ctx = make_ctx(&stream, &name_table, &[], &export_names, 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("MyActor".into()));
        assert_eq!(pos, stream.len());
    }

    #[test]
    fn decodes_soft_object_const_resolves_export_name() {
        // EX_SoftObjectConst shares the same walker arm as EX_ObjectConst.
        let name_table = make_name_table(&[]);
        let export_names = vec!["SoftRef".to_string()];
        let mut stream = vec![EX_SOFT_OBJECT_CONST];
        put_i32(&mut stream, 1);

        let ctx = make_ctx(&stream, &name_table, &[], &export_names, 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(result, Expr::Literal("SoftRef".into()));
        assert_eq!(pos, stream.len());
    }

    /// `EX_SwitchValue` (0x69) at expression position decodes to
    /// `Expr::Switch` with one `SwitchExprCase` per arm and the default
    /// expression boxed at the end.
    #[test]
    fn decodes_switch_value_to_expr_switch() {
        let name_table = make_name_table(&[]);
        let mut stream = vec![EX_SWITCH_VALUE];
        // num_cases = 2, end_offset = 0xFE.
        stream.extend_from_slice(&2u16.to_le_bytes());
        put_i32(&mut stream, 0xFE);
        // index expression.
        stream.push(EX_INT_ZERO);
        // Case 0: value = IntConst(0), next_offset = 0x10, body = INT_ZERO.
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 0);
        put_i32(&mut stream, 0x10);
        stream.push(EX_INT_ZERO);
        // Case 1: value = IntConst(1), next_offset = 0x20, body = INT_ONE.
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 1);
        put_i32(&mut stream, 0x20);
        stream.push(EX_INT_ONE);
        // default = INT_ZERO.
        stream.push(EX_INT_ZERO);

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        assert_eq!(pos, stream.len());
        match result {
            Expr::Switch {
                index,
                cases,
                default,
            } => {
                assert_eq!(*index, Expr::Literal("0".into()));
                assert_eq!(cases.len(), 2);
                assert_eq!(cases[0].value, Expr::Literal("0".into()));
                assert_eq!(cases[0].body, Expr::Literal("0".into()));
                assert_eq!(cases[1].value, Expr::Literal("1".into()));
                assert_eq!(cases[1].body, Expr::Literal("1".into()));
                assert_eq!(*default, Expr::Literal("0".into()));
            }
            other => panic!("expected Expr::Switch, got {:?}", other),
        }
    }

    /// `EX_ARRAY_GET_BY_REF` (0x6B) decodes to `Expr::Index { recv, idx }`
    /// with the array operand first, index second.
    #[test]
    fn decodes_array_get_by_ref_to_index() {
        let name_table = make_name_table(&["Items"]);
        let mut stream = vec![EX_ARRAY_GET_BY_REF, EX_LOCAL_VARIABLE];
        put_field_path(&mut stream, 0); // recv = Var("Items")
        stream.push(EX_INT_ZERO); // idx = literal 0

        let ctx = make_ctx(&stream, &name_table, &[], &[], 0);
        let mut pos = 0;
        let result = decode_expr(&mut pos, &ctx);
        match result {
            Expr::Index { recv, idx } => {
                assert_eq!(*recv, Expr::Var("Items".into()));
                assert_eq!(*idx, Expr::Literal("0".into()));
            }
            other => panic!("expected Expr::Index, got {:?}", other),
        }
        assert_eq!(pos, stream.len());
    }
}
