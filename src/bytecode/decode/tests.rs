// Inline tests: these test private functions (try_rewrite_array_call, decode_expr, etc.)
// that aren't accessible from tests/. Integration tests cover the public API end-to-end.

use super::entry::decode_bytecode;
use super::expr::decode_expr;
use super::types::DecodeCtx;
use crate::binary::NameTable;
use crate::bytecode::format::try_rewrite_array_call;

// Helper: build a NameTable with given names (index 0 = first name)
fn name_table(names: &[&str]) -> NameTable {
    NameTable::from_names(names.iter().map(|s| s.to_string()).collect())
}

// Helper: append little-endian i32
fn push_i32(bytecode: &mut Vec<u8>, v: i32) {
    bytecode.extend_from_slice(&v.to_le_bytes());
}
fn push_f32(bytecode: &mut Vec<u8>, v: f32) {
    bytecode.extend_from_slice(&v.to_le_bytes());
}
fn push_f64(bytecode: &mut Vec<u8>, v: f64) {
    bytecode.extend_from_slice(&v.to_le_bytes());
}

// Helper: append a single-name FFieldPath (16 bytes)
// FName = name_index(i32) + instance_number(i32), then owner(i32)
fn push_field_path(bytecode: &mut Vec<u8>, name_idx: i32) {
    push_i32(bytecode, 1); // path_num = 1
    push_i32(bytecode, name_idx); // FName index
    push_i32(bytecode, 0); // FName instance number
    push_i32(bytecode, 0); // owner
}

// Helper: decode a single expression from bytes
fn expr(bytecode: &[u8], ue5: i32) -> (Option<String>, i32) {
    let names = name_table(&["TestVar", "TestFunc", "None"]);
    let imports = vec![];
    let export_names = vec![];
    let ctx = DecodeCtx {
        bytecode,
        name_table: &names,
        imports: &imports,
        export_names: &export_names,
        ue5,
    };
    let mut pos = 0;
    let mut mem_adj = 0;
    let result = decode_expr(&ctx, &mut pos, &mut mem_adj);
    (result, mem_adj)
}

// Helper: decode with custom name table
fn expr_with_names(bytecode: &[u8], names: &NameTable, ue5: i32) -> Option<String> {
    let imports = vec![];
    let export_names = vec![];
    let ctx = DecodeCtx {
        bytecode,
        name_table: names,
        imports: &imports,
        export_names: &export_names,
        ue5,
    };
    let mut pos = 0;
    let mut mem_adj = 0;
    decode_expr(&ctx, &mut pos, &mut mem_adj)
}

// LWC opcodes: float vs double branching

#[test]
fn rotation_const_ue4_reads_floats() {
    let mut bytecode = vec![0x22];
    push_f32(&mut bytecode, 1.0);
    push_f32(&mut bytecode, 2.0);
    push_f32(&mut bytecode, 3.0);
    let (result, _) = expr(&bytecode, 0);
    assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
}

#[test]
fn rotation_const_ue5_lwc_reads_doubles() {
    let mut bytecode = vec![0x22];
    push_f64(&mut bytecode, 1.0);
    push_f64(&mut bytecode, 2.0);
    push_f64(&mut bytecode, 3.0);
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "Rot(1.0,2.0,3.0)");
}

#[test]
fn vector_const_ue4_reads_floats() {
    let mut bytecode = vec![0x23];
    push_f32(&mut bytecode, 10.0);
    push_f32(&mut bytecode, 20.0);
    push_f32(&mut bytecode, 30.0);
    let (result, _) = expr(&bytecode, 0);
    assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
}

#[test]
fn vector_const_ue5_lwc_reads_doubles() {
    let mut bytecode = vec![0x23];
    push_f64(&mut bytecode, 10.0);
    push_f64(&mut bytecode, 20.0);
    push_f64(&mut bytecode, 30.0);
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "Vec(10.0,20.0,30.0)");
}

#[test]
fn transform_const_ue4_reads_floats() {
    let mut bytecode = vec![0x2B];
    for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
        push_f32(&mut bytecode, v);
    }
    let (result, _) = expr(&bytecode, 0);
    assert!(result.unwrap().starts_with("Transform("));
}

#[test]
fn transform_const_ue5_lwc_reads_doubles() {
    let mut bytecode = vec![0x2B];
    for v in [0.0, 0.0, 0.0, 1.0, 5.0, 10.0, 15.0, 1.0, 1.0, 1.0] {
        push_f64(&mut bytecode, v);
    }
    let (result, _) = expr(&bytecode, 1004);
    assert!(result.unwrap().starts_with("Transform("));
}

// 0x41: UE5 = Vector3fConst, UE4 = StructMemberContext fallback

#[test]
fn vector3f_const_ue5() {
    let mut bytecode = vec![0x41];
    push_f32(&mut bytecode, 1.0);
    push_f32(&mut bytecode, 2.0);
    push_f32(&mut bytecode, 3.0);
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "Vec3f(1.0,2.0,3.0)");
}

// 0x37: EX_DoubleConst

#[test]
fn double_const() {
    let mut bytecode = vec![0x37];
    push_f64(&mut bytecode, 1.2345);
    let (result, _) = expr(&bytecode, 0);
    assert_eq!(result.unwrap(), "1.2345");
}

// 0x0C: EX_NothingInt32

#[test]
fn nothing_int32_returns_nop() {
    let mut bytecode = vec![0x0C];
    push_i32(&mut bytecode, 42);
    let (result, _) = expr(&bytecode, 0);
    assert_eq!(result.unwrap(), "nop");
}

// 0x11: EX_BitFieldConst

#[test]
fn bitfield_const() {
    let mut bytecode = vec![0x11];
    push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
    bytecode.push(0x01); // uint8 value = true
    let names = name_table(&["TestVar"]);
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "true");
}

// 0x33: EX_PropertyConst

#[test]
fn property_const() {
    let mut bytecode = vec![0x33];
    push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
    let names = name_table(&["TestVar"]);
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "prop(TestVar)");
}

// 0x6C: EX_ClassSparseDataVariable

#[test]
fn class_sparse_data_variable() {
    let mut bytecode = vec![0x6C];
    push_field_path(&mut bytecode, 0); // FFieldPath ->"TestVar"
    let names = name_table(&["TestVar"]);
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "sparse.TestVar");
}

// 0x70-0x72: RTFM opcodes

#[test]
fn rtfm_transact() {
    let mut bytecode = vec![0x70];
    bytecode.push(0x27); // EX_True as inner expression
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "rtfm_transact(true)");
}

#[test]
fn rtfm_stop_transact() {
    let bytecode = vec![0x71, 0x01]; // opcode + mode byte
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "rtfm_stop");
}

#[test]
fn rtfm_abort_if_not() {
    let mut bytecode = vec![0x72];
    bytecode.push(0x28); // EX_False as condition
    let (result, _) = expr(&bytecode, 1004);
    assert_eq!(result.unwrap(), "rtfm_abort_if_not(false)");
}

// 0x43/0x44: EX_LetMulticastDelegate/EX_LetDelegate (with FFieldPath)

#[test]
fn let_multicast_delegate() {
    let names = name_table(&["MyDelegate", "Target", "Value"]);
    let mut bytecode = vec![0x43];
    push_field_path(&mut bytecode, 0); // FFieldPath ->"MyDelegate"
                                       // var: EX_LocalVariable with FFieldPath -> "Target"
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 1);
    // val: EX_LocalVariable with FFieldPath -> "Value"
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 2);
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "Target = Value");
}

#[test]
fn let_delegate() {
    let names = name_table(&["MyDelegate", "Target", "Value"]);
    let mut bytecode = vec![0x44];
    push_field_path(&mut bytecode, 0); // FFieldPath ->"MyDelegate"
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 1); // var
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 2); // val
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "Target = Value");
}

// 0x39/0x3B: EX_SetSet/EX_SetMap (with element count)

#[test]
fn set_set_reads_element_count() {
    let names = name_table(&["MySet"]);
    let mut bytecode = vec![0x39];
    // target: EX_LocalVariable
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 0);
    // element count (int32)
    push_i32(&mut bytecode, 2);
    // two elements: EX_IntConst(1), EX_IntConst(2), then EX_EndSet
    bytecode.push(0x1D);
    push_i32(&mut bytecode, 1);
    bytecode.push(0x1D);
    push_i32(&mut bytecode, 2);
    bytecode.push(0x3A); // EX_EndSet
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "MySet = set{1, 2}");
}

#[test]
fn set_map_reads_element_count() {
    let names = name_table(&["MyMap"]);
    let mut bytecode = vec![0x3B];
    bytecode.push(0x00);
    push_field_path(&mut bytecode, 0); // target
    push_i32(&mut bytecode, 1); // element count
    bytecode.push(0x1D);
    push_i32(&mut bytecode, 10); // key
    bytecode.push(0x1D);
    push_i32(&mut bytecode, 20); // value
    bytecode.push(0x3C); // EX_EndMap
    let result = expr_with_names(&bytecode, &names, 0);
    assert_eq!(result.unwrap(), "MyMap = map{10, 20}");
}

// LWC pre-1004: still uses floats

#[test]
fn vector_const_ue5_pre_lwc_reads_floats() {
    let mut bytecode = vec![0x23];
    push_f32(&mut bytecode, 1.0);
    push_f32(&mut bytecode, 2.0);
    push_f32(&mut bytecode, 3.0);
    let (result, _) = expr(&bytecode, 1003); // pre-LWC UE5
    assert_eq!(result.unwrap(), "Vec(1.0,2.0,3.0)");
}

// decode_bytecode filters nop

#[test]
fn decode_bytecode_filters_nothing_int32() {
    let names = name_table(&["None"]);
    let imports = vec![];
    let export_names = vec![];
    let mut bytecode = vec![0x0C]; // EX_NothingInt32
    push_i32(&mut bytecode, 0);
    bytecode.push(0x53); // EX_EndOfScript
    let (stmts, _) = decode_bytecode(&bytecode, &names, &imports, &export_names, 0);
    assert!(stmts.is_empty(), "NothingInt32 should be filtered as nop");
}

// Array rewrite tests

fn owned(val: &str) -> String {
    val.to_string()
}

#[test]
fn array_get_rewrite() {
    let result = try_rewrite_array_call("Array_Get", &[owned("arr"), owned("0"), owned("$item")]);
    assert_eq!(result.unwrap(), "$item = arr[0]");
}

#[test]
fn array_set_rewrite() {
    let result = try_rewrite_array_call(
        "Array_Set",
        &[owned("arr"), owned("0"), owned("val"), owned("false")],
    );
    assert_eq!(result.unwrap(), "arr[0] = val");
}

#[test]
fn array_set_size_to_fit_keeps_method_call() {
    let result = try_rewrite_array_call(
        "Array_Set",
        &[owned("arr"), owned("0"), owned("val"), owned("true")],
    );
    assert_eq!(result.unwrap(), "arr.Set(0, val, true)");
}

#[test]
fn array_length_rewrite() {
    let result = try_rewrite_array_call("Array_Length", &[owned("arr")]);
    assert_eq!(result.unwrap(), "arr.Length()");
}

#[test]
fn array_add_rewrite() {
    let result = try_rewrite_array_call("Array_Add", &[owned("arr"), owned("item")]);
    assert_eq!(result.unwrap(), "arr.Add(item)");
}

#[test]
fn array_contains_rewrite() {
    let result = try_rewrite_array_call("Array_Contains", &[owned("arr"), owned("item")]);
    assert_eq!(result.unwrap(), "arr.Contains(item)");
}

#[test]
fn array_remove_rewrite() {
    let result = try_rewrite_array_call("Array_Remove", &[owned("arr"), owned("2")]);
    assert_eq!(result.unwrap(), "arr.Remove(2)");
}

#[test]
fn array_remove_item_rewrite() {
    let result = try_rewrite_array_call("Array_RemoveItem", &[owned("arr"), owned("item")]);
    assert_eq!(result.unwrap(), "arr.RemoveItem(item)");
}

#[test]
fn array_find_rewrite() {
    let result =
        try_rewrite_array_call("Array_Find", &[owned("arr"), owned("item"), owned("$idx")]);
    assert_eq!(result.unwrap(), "$idx = arr.Find(item)");
}

#[test]
fn array_last_rewrite() {
    let result = try_rewrite_array_call("Array_Last", &[owned("arr"), owned("$item")]);
    assert_eq!(result.unwrap(), "$item = arr.Last()");
}

#[test]
fn array_clear_rewrite() {
    let result = try_rewrite_array_call("Array_Clear", &[owned("arr")]);
    assert_eq!(result.unwrap(), "arr.Clear()");
}

#[test]
fn array_insert_rewrite() {
    let result = try_rewrite_array_call("Array_Insert", &[owned("arr"), owned("item"), owned("2")]);
    assert_eq!(result.unwrap(), "arr.Insert(item, 2)");
}

#[test]
fn non_array_passthrough() {
    let result = try_rewrite_array_call("SomeFunc", &[owned("a"), owned("b")]);
    assert!(result.is_none());
}
