//! Memory-to-disk offset translation for bytecode entry points.
//!
//! Unreal Engine serialises some operand types at smaller sizes on disk than
//! they occupy in memory at runtime. Bytecode instructions reference each
//! other by memory offset (the runtime's view), but our decode pipeline
//! operates on the disk byte slice. Event entry offsets we collect from
//! `ExecuteUbergraph_Name(N)` call sites are memory coordinates, while
//! [`partition_ubergraph`] builds disk-coordinate boundaries from the raw
//! `&[u8]`. Drift accumulates each time an operand-with-drift is consumed,
//! so an entry that was a valid opcode boundary in memory falls mid-instruction
//! on disk.
//!
//! Drift sources (size on disk vs runtime memory):
//!
//! - **FName**: 8 disk (index i32 + number i32), 12 mem (adds DisplayIndex
//!   under `WITH_CASE_PRESERVING_NAME`, the build flag uncooked editor assets
//!   use). Drift +4 per occurrence.
//! - **Object reference (FPackageIndex)**: 4 disk (one i32), 8 mem (a
//!   pointer). Drift +4 per occurrence.
//! - **FFieldPath**: variable on disk (`4 + N*8 + 4` for path length, N FNames,
//!   and an owner i32), 8 mem (a single pointer). Drift `8 - (4 + N*8 + 4) =
//!   -4 - N*8` per occurrence; for the common N=1 path this is `-12`.
//!
//! Large World Coordinates (LWC) is NOT a drift source: UE5's wider doubles
//! produce a different disk size from UE4 floats, but the runtime reads the
//! same number of bytes that were written.
//!
//! [`partition_ubergraph`]: crate::bytecode::partition::partition_ubergraph
//!
//! [`build_mem_to_disk_map`] walks the bytecode once and produces a
//! `BTreeMap<usize, usize>` mapping memory offset to disk offset for every
//! opcode boundary. Callers translate event entries through the map before
//! handing them to the partitioner.

use std::collections::BTreeMap;

use crate::binary::NameTable;
use crate::bytecode::decode::walker::{
    walk_opcode, FieldPath, OpcodeVisitor, SwitchValueCase, TextConstPayload, WalkCtx,
};

/// Disk size of an FName operand (two i32s: name index + instance number).
const FNAME_DISK: usize = 8;
/// Memory size of an FName operand under `WITH_CASE_PRESERVING_NAME`
/// (adds a third i32 for DisplayIndex).
const FNAME_MEM: usize = 12;
/// Drift introduced per FName operand consumed.
const FNAME_DRIFT: i64 = (FNAME_MEM - FNAME_DISK) as i64;

/// Disk size of an FPackageIndex object reference (one i32).
const OBJREF_DISK: usize = 4;
/// Memory size of a UObject pointer.
const OBJREF_MEM: usize = 8;
/// Drift introduced per object reference operand consumed.
const OBJREF_DRIFT: i64 = (OBJREF_MEM - OBJREF_DISK) as i64;

/// Memory size of an FFieldPath (a single resolved pointer at runtime).
const FIELDPATH_MEM: i64 = 8;

/// Errors from [`build_mem_to_disk_map`].
///
/// All variants are non-fatal at the call site: the converter signals
/// progress by returning whatever boundaries it managed to walk, and the
/// caller decides whether to abort or fall back. The variants exist mainly
/// to surface diagnostics for misaligned opcode streams.
#[derive(Debug)]
pub enum ConvertError {
    /// `pos` would advance past the end of the bytecode while reading
    /// operands for the opcode that started at `disk_offset`.
    Truncated { disk_offset: usize },
    /// The walker stalled (a malformed opcode left `pos` unchanged).
    /// `disk_offset` is where the stall happened.
    Stalled { disk_offset: usize },
}

impl std::fmt::Display for ConvertError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConvertError::Truncated { disk_offset } => write!(
                formatter,
                "mem-to-disk converter: truncated bytecode at disk offset 0x{:x}",
                disk_offset
            ),
            ConvertError::Stalled { disk_offset } => write!(
                formatter,
                "mem-to-disk converter: walker stalled at disk offset 0x{:x}",
                disk_offset
            ),
        }
    }
}

impl std::error::Error for ConvertError {}

/// Walk the bytecode once and produce a memory-to-disk offset map for every
/// opcode boundary.
///
/// At each opcode boundary the memory position equals
/// `disk_position + accumulated_drift`. The returned map is keyed by
/// memory offset to mirror the coordinate space of event entries, and the
/// values are disk offsets suitable for indexing into `bytecode`.
///
/// The walker is intentionally permissive: if a nested operand walk would
/// truncate, it stops advancing and continues from the next byte rather
/// than aborting the whole map.
///
/// On a clean walk, every opcode start in the stream has an entry. The
/// returned `Option<ConvertError>` reports the first non-fatal anomaly the
/// walker observed; callers may log it for diagnostics.
pub(crate) fn build_mem_to_disk_map(
    bytecode: &[u8],
    name_table: &NameTable,
    ue5: i32,
) -> (BTreeMap<usize, usize>, Option<ConvertError>) {
    let mut map: BTreeMap<usize, usize> = BTreeMap::new();
    let mut pos = 0usize;
    let mut drift: i64 = 0;
    let mut first_anomaly: Option<ConvertError> = None;
    let ctx = WalkCtx::new(bytecode, name_table, ue5);

    while pos < bytecode.len() {
        let disk_start = pos;
        let mem_start = (disk_start as i64 + drift) as usize;
        map.insert(mem_start, disk_start);

        let mut visitor = DriftVisitor::new();
        walk_opcode(&ctx, &mut pos, &mut visitor);
        drift += visitor.drift;

        if pos > bytecode.len() {
            pos = bytecode.len();
            if first_anomaly.is_none() {
                first_anomaly = Some(ConvertError::Truncated {
                    disk_offset: disk_start,
                });
            }
        }

        if pos == disk_start {
            // Stall: opcode at disk_start is unrecognised; force a 1-byte
            // advance so we can keep walking, matching the wider walker
            // failsafe behaviour.
            pos += 1;
            if first_anomaly.is_none() {
                first_anomaly = Some(ConvertError::Stalled {
                    disk_offset: disk_start,
                });
            }
        }
    }

    (map, first_anomaly)
}

/// Visitor that accumulates the disk-to-memory drift contributed by one
/// opcode (and its sub-expressions). Each visit method maps the
/// already-parsed operand values onto their drift contribution: FNames
/// add `FNAME_DRIFT`, object references add `OBJREF_DRIFT`, and field
/// paths use the formula `mem - disk = 8 - (4 + N*8 + 4) = -N*8` for
/// non-null paths (zero for null paths).
///
/// The walker handles all the byte-cursor movement; the visitor's only
/// responsibility is to fold drift contributions into a running total.
struct DriftVisitor {
    drift: i64,
}

impl DriftVisitor {
    fn new() -> Self {
        Self { drift: 0 }
    }

    /// Drift contribution for one FFieldPath operand. Null paths
    /// (`segments == 0`) have zero net drift; non-null paths drift by
    /// `-segments * 8`.
    fn field_path_drift(path: &FieldPath) -> i64 {
        if path.is_null() {
            0
        } else {
            FIELDPATH_MEM - (4 + path.segments as i64 * 8 + 4)
        }
    }

    fn add_fname(&mut self) {
        self.drift += FNAME_DRIFT;
    }

    fn add_obj_ref(&mut self) {
        self.drift += OBJREF_DRIFT;
    }

    fn add_field_path(&mut self, path: &FieldPath) {
        self.drift += Self::field_path_drift(path);
    }
}

impl OpcodeVisitor for DriftVisitor {
    type Result = ();

    fn default_result(&mut self, _opcode: u8, _start_offset: usize) {}

    fn on_object_const(&mut self, _opcode: u8, _obj_idx: i32, _start_offset: usize) {
        // EX_ObjectConst, EX_SoftObjectConst: 4-byte FPackageIndex.
        self.add_obj_ref();
    }

    fn on_name_const(&mut self, _name: String, _start_offset: usize) {
        // EX_NameConst: 8 bytes on disk, 12 in memory.
        self.add_fname();
    }

    fn on_bitfield_const(&mut self, path: FieldPath, _value: u8, _start_offset: usize) {
        self.add_field_path(&path);
    }

    fn on_property_const(&mut self, path: FieldPath, _start_offset: usize) {
        self.add_field_path(&path);
    }

    fn on_struct_const(
        &mut self,
        _struct_obj_idx: i32,
        _serial_size: i32,
        _items: Vec<()>,
        _start_offset: usize,
    ) {
        // 4-byte struct object reference (the i32 serial size carries no drift).
        self.add_obj_ref();
    }

    fn on_array_const(
        &mut self,
        _inner_obj_idx: i32,
        _count: i32,
        _items: Vec<()>,
        _start_offset: usize,
    ) {
        self.add_obj_ref();
    }

    fn on_set_const(
        &mut self,
        _inner_obj_idx: i32,
        _count: i32,
        _items: Vec<()>,
        _start_offset: usize,
    ) {
        self.add_obj_ref();
    }

    fn on_map_const(
        &mut self,
        _key_obj_idx: i32,
        _value_obj_idx: i32,
        _count: i32,
        _items: Vec<()>,
        _start_offset: usize,
    ) {
        // Two FPackageIndex operands (key and value property types).
        self.drift += OBJREF_DRIFT * 2;
    }

    fn on_field_path_var(&mut self, _opcode: u8, path: FieldPath, _start_offset: usize) {
        // EX_LocalVariable / EX_InstanceVariable / EX_DefaultVariable /
        // EX_LocalOutVariable / EX_ClassSparseDataVariable.
        self.add_field_path(&path);
    }

    fn on_obj_cast(&mut self, _opcode: u8, _class_obj_idx: i32, _inner: (), _start_offset: usize) {
        // EX_MetaCast / EX_DynamicCast / EX_ObjToInterfaceCast /
        // EX_CrossInterfaceCast / EX_InterfaceToObjCast each take a
        // 4-byte class FPackageIndex.
        self.add_obj_ref();
    }

    fn on_context(
        &mut self,
        _opcode: u8,
        _receiver: (),
        _rvalue_skip: u32,
        rvalue_path: FieldPath,
        _member: (),
        _start_offset: usize,
    ) {
        self.add_field_path(&rvalue_path);
    }

    fn on_struct_member_context(
        &mut self,
        path: FieldPath,
        _struct_expr: (),
        _start_offset: usize,
    ) {
        self.add_field_path(&path);
    }

    fn on_let_with_path(
        &mut self,
        _opcode: u8,
        path: FieldPath,
        _lhs: (),
        _rhs: (),
        _start_offset: usize,
    ) {
        // EX_Let / EX_LetMulticastDelegate / EX_LetDelegate.
        self.add_field_path(&path);
    }

    fn on_let_value_on_persistent_frame(
        &mut self,
        path: FieldPath,
        _value: (),
        _start_offset: usize,
    ) {
        self.add_field_path(&path);
    }

    fn on_virtual_function(
        &mut self,
        _opcode: u8,
        _function_name: String,
        _args: Vec<()>,
        _start_offset: usize,
    ) {
        // FName operand for the function name.
        self.add_fname();
    }

    fn on_final_function(
        &mut self,
        _opcode: u8,
        _callee_obj_idx: i32,
        _args: Vec<()>,
        _start_offset: usize,
    ) {
        self.add_obj_ref();
    }

    fn on_instance_delegate(&mut self, _name: String, _start_offset: usize) {
        // EX_InstanceDelegate carries an FName.
        self.add_fname();
    }

    fn on_bind_delegate(
        &mut self,
        _function_name: String,
        _delegate: (),
        _target: (),
        _start_offset: usize,
    ) {
        self.add_fname();
    }

    fn on_call_multicast_delegate(
        &mut self,
        _signature_obj_idx: i32,
        _delegate: (),
        _target: (),
        _args: Vec<()>,
        _start_offset: usize,
    ) {
        // EX_CallMulticastDelegate has a 4-byte FPackageIndex signature.
        self.add_obj_ref();
    }

    fn on_instrumentation_event(
        &mut self,
        _event_type: u8,
        event_name: Option<String>,
        _start_offset: usize,
    ) {
        // Type 4 carries an FName payload.
        if event_name.is_some() {
            self.add_fname();
        }
    }

    fn on_field_path_const(&mut self, path: FieldPath, _start_offset: usize) {
        self.add_field_path(&path);
    }

    fn on_text_const(&mut self, _payload: TextConstPayload<()>, _start_offset: usize) {
        // EX_TextConst carries no FName / object-ref / field-path of its
        // own beyond what its sub-expressions already report. The 4-byte
        // string-table reference in the StringTable variant is not an
        // FPackageIndex but a plain i32 ID, so it does not contribute drift.
    }

    fn on_switch_value(
        &mut self,
        _end_offset: u32,
        _index: (),
        _cases: Vec<SwitchValueCase<()>>,
        _default: (),
        _start_offset: usize,
    ) {
        // No drift-contributing operands of its own.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::decode::test_fixtures::empty_name_table;
    use crate::bytecode::opcodes::*;

    fn write_u32(buffer: &mut Vec<u8>, value: u32) {
        buffer.extend_from_slice(&value.to_le_bytes());
    }

    #[test]
    fn empty_bytecode_no_drift() {
        let bytecode: Vec<u8> = Vec::new();
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(map.is_empty());
        assert!(err.is_none());
    }

    #[test]
    fn no_drift_opcodes_match_disk_offsets() {
        // Two terminators back to back. No drift introduced.
        let bytecode = vec![EX_NOTHING, EX_END_OF_SCRIPT];
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&0), Some(&0));
        assert_eq!(map.get(&1), Some(&1));
    }

    #[test]
    fn object_const_drift_4_per_occurrence() {
        // EX_OBJECT_CONST consumes 4 bytes of obj-ref. Mem offset of the
        // next opcode should be disk_start + 1 + 4 + 4 = +9.
        let mut bytecode = vec![EX_OBJECT_CONST];
        write_u32(&mut bytecode, 0); // 4-byte obj ref
        bytecode.push(EX_END_OF_SCRIPT);
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&9), Some(&5));
    }

    #[test]
    fn fname_drift_per_occurrence() {
        // EX_NAME_CONST + 8-byte FName + EX_END_OF_SCRIPT (1 byte).
        // Disk len = 1 + 8 = 9 bytes for EX_NAME_CONST; mem offset of
        // EX_END_OF_SCRIPT = 9 + 4 = 13.
        let mut bytecode = vec![EX_NAME_CONST];
        bytecode.extend_from_slice(&[0u8; 8]);
        bytecode.push(EX_END_OF_SCRIPT);
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&13), Some(&9));
    }

    #[test]
    fn virtual_function_drift_includes_fname_only() {
        // EX_VIRTUAL_FUNCTION + 8-byte FName + immediate EX_END_FUNCTION_PARMS,
        // then EX_END_OF_SCRIPT. FName drift = +4. Disk len = 1+8+1 = 10,
        // mem offset of EX_END_OF_SCRIPT = 10 + 4 = 14.
        let mut bytecode = vec![EX_VIRTUAL_FUNCTION];
        bytecode.extend_from_slice(&[0u8; 8]);
        bytecode.push(EX_END_FUNCTION_PARMS);
        bytecode.push(EX_END_OF_SCRIPT);
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&14), Some(&10));
    }

    #[test]
    fn local_variable_drift_negative_for_single_path() {
        // EX_LOCAL_VARIABLE with path_num=1 + one FName + owner. Disk size
        // = 4 + 8 + 4 = 16 bytes of operand. Mem size = 8. Drift = -8.
        // After the opcode (1 byte) plus 16 bytes operand, pos = 17. Mem
        // offset of next opcode = 17 - 8 = 9.
        let mut bytecode = vec![EX_LOCAL_VARIABLE];
        write_u32(&mut bytecode, 1); // path_num
        write_u32(&mut bytecode, 0); // FName index
        write_u32(&mut bytecode, 0); // FName instance number
        write_u32(&mut bytecode, 0); // owner
        bytecode.push(EX_END_OF_SCRIPT);
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&9), Some(&17));
    }

    #[test]
    fn null_field_path_no_net_drift() {
        // EX_LOCAL_VARIABLE with path_num=0 (null path). Disk = 4 + 4 = 8.
        // Mem = 8. Drift = 0. Next opcode at disk 9 = mem 9.
        let mut bytecode = vec![EX_LOCAL_VARIABLE];
        write_u32(&mut bytecode, 0); // path_num = 0 (null path)
        write_u32(&mut bytecode, 0); // owner
        bytecode.push(EX_END_OF_SCRIPT);
        let nt = empty_name_table();
        let (map, err) = build_mem_to_disk_map(&bytecode, &nt, 0);
        assert!(err.is_none(), "unexpected error {:?}", err);
        assert_eq!(map.get(&9), Some(&9));
    }
}
