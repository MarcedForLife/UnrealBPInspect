//! Tests for the opcode walker. Extracted from the production module so
//! the dispatch table doesn't share a file with several hundred lines of
//! synthetic-byte-stream fixtures.

#[cfg(test)]
mod tests {
    use super::super::walker::{walk_opcode, FieldPath, OpcodeVisitor, SwitchValueCase, WalkCtx};
    use crate::binary::NameTable;
    use crate::bytecode::opcodes::*;

    fn name_table(entries: &[&str]) -> NameTable {
        NameTable::from_names(entries.iter().map(|s| s.to_string()).collect())
    }

    /// Counts how many times each visitor hook fires; useful for verifying
    /// the walker's recursion shape independent of any consumer impl.
    #[derive(Default)]
    struct CountingVisitor {
        zero_operand: u32,
        return_count: u32,
        jump: u32,
        jump_if_not: u32,
        push_exec: u32,
        let_with_path: u32,
        final_function: u32,
        virtual_function: u32,
        switch_value: u32,
        instance_delegate: u32,
        bind_delegate: u32,
        multicast_delegate_op: u32,
        call_multicast_delegate: u32,
        set_container: u32,
        array_const: u32,
        set_const: u32,
        map_const: u32,
        unknown: u32,
    }

    impl OpcodeVisitor for CountingVisitor {
        type Result = ();
        fn default_result(&mut self, _opcode: u8, _start_offset: usize) {}
        fn on_zero_operand(&mut self, _opcode: u8, _start_offset: usize) {
            self.zero_operand += 1;
        }
        fn on_return(&mut self, _value: (), _start_offset: usize) {
            self.return_count += 1;
        }
        fn on_jump(&mut self, _opcode: u8, _target: u32, _start_offset: usize) {
            self.jump += 1;
        }
        fn on_jump_if_not(&mut self, _target: u32, _condition: (), _start_offset: usize) {
            self.jump_if_not += 1;
        }
        fn on_push_execution_flow(&mut self, _target: u32, _start_offset: usize) {
            self.push_exec += 1;
        }
        fn on_let_with_path(
            &mut self,
            _opcode: u8,
            _path: FieldPath,
            _lhs: (),
            _rhs: (),
            _start_offset: usize,
        ) {
            self.let_with_path += 1;
        }
        fn on_final_function(
            &mut self,
            _opcode: u8,
            _callee_obj_idx: i32,
            _args: Vec<()>,
            _start_offset: usize,
        ) {
            self.final_function += 1;
        }
        fn on_virtual_function(
            &mut self,
            _opcode: u8,
            _function_name: String,
            _args: Vec<()>,
            _start_offset: usize,
        ) {
            self.virtual_function += 1;
        }
        fn on_switch_value(
            &mut self,
            _end_offset: u32,
            _index: (),
            _cases: Vec<SwitchValueCase<()>>,
            _default: (),
            _start_offset: usize,
        ) {
            self.switch_value += 1;
        }
        fn on_instance_delegate(&mut self, _name: String, _start_offset: usize) {
            self.instance_delegate += 1;
        }
        fn on_bind_delegate(
            &mut self,
            _function_name: String,
            _delegate: (),
            _target: (),
            _start_offset: usize,
        ) {
            self.bind_delegate += 1;
        }
        fn on_multicast_delegate_op(
            &mut self,
            _opcode: u8,
            _delegate: (),
            _target: (),
            _start_offset: usize,
        ) {
            self.multicast_delegate_op += 1;
        }
        fn on_call_multicast_delegate(
            &mut self,
            _signature_obj_idx: i32,
            _delegate: (),
            _target: (),
            _args: Vec<()>,
            _start_offset: usize,
        ) {
            self.call_multicast_delegate += 1;
        }
        fn on_set_container(
            &mut self,
            _opcode: u8,
            _target: (),
            _items: Vec<()>,
            _start_offset: usize,
        ) {
            self.set_container += 1;
        }
        fn on_array_const(
            &mut self,
            _inner_obj_idx: i32,
            _count: i32,
            _items: Vec<()>,
            _start_offset: usize,
        ) {
            self.array_const += 1;
        }
        fn on_set_const(
            &mut self,
            _inner_obj_idx: i32,
            _count: i32,
            _items: Vec<()>,
            _start_offset: usize,
        ) {
            self.set_const += 1;
        }
        fn on_map_const(
            &mut self,
            _key_obj_idx: i32,
            _value_obj_idx: i32,
            _count: i32,
            _items: Vec<()>,
            _start_offset: usize,
        ) {
            self.map_const += 1;
        }
        fn on_unknown(&mut self, _opcode: u8, _start_offset: usize) {
            self.unknown += 1;
        }
    }

    use super::super::test_fixtures::{put_field_path, put_fname, put_i32, put_u32};

    #[test]
    fn walks_zero_operand() {
        let names = name_table(&[]);
        let stream = vec![EX_TRUE];
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, 1);
        assert_eq!(visitor.zero_operand, 1);
    }

    #[test]
    fn walks_let_recurses_into_subexprs() {
        let names = name_table(&["MyVar"]);
        let mut stream = vec![EX_LET];
        put_field_path(&mut stream, 0);
        stream.push(EX_LOCAL_VARIABLE);
        put_field_path(&mut stream, 0);
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 7);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.let_with_path, 1);
    }

    #[test]
    fn walks_final_function_with_args_terminator() {
        let names = name_table(&[]);
        let mut stream = vec![EX_FINAL_FUNCTION];
        put_i32(&mut stream, 5);
        stream.push(EX_INT_ZERO);
        stream.push(EX_INT_ONE);
        stream.push(EX_END_FUNCTION_PARMS);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.final_function, 1);
        assert_eq!(visitor.zero_operand, 2);
    }

    #[test]
    fn walks_virtual_function_reads_fname() {
        let names = name_table(&["DoThing"]);
        let mut stream = vec![EX_VIRTUAL_FUNCTION];
        put_fname(&mut stream, 0);
        stream.push(EX_END_FUNCTION_PARMS);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.virtual_function, 1);
    }

    #[test]
    fn walks_jump_if_not_consumes_condition() {
        let names = name_table(&[]);
        let mut stream = vec![EX_JUMP_IF_NOT];
        put_u32(&mut stream, 0x42);
        stream.push(EX_TRUE);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.jump_if_not, 1);
        assert_eq!(visitor.zero_operand, 1);
    }

    #[test]
    fn walks_switch_value_with_two_cases() {
        let names = name_table(&[]);
        let mut stream = vec![EX_SWITCH_VALUE];
        stream.extend_from_slice(&2u16.to_le_bytes());
        put_u32(&mut stream, 0xFE);
        stream.push(EX_INT_ZERO); // index
                                  // Case 0
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 0);
        put_u32(&mut stream, 0x10);
        stream.push(EX_INT_ZERO); // result
                                  // Case 1
        stream.push(EX_INT_CONST);
        put_i32(&mut stream, 1);
        put_u32(&mut stream, 0x20);
        stream.push(EX_INT_ONE); // result
        stream.push(EX_INT_ZERO); // default
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.switch_value, 1);
    }

    #[test]
    fn walks_unknown_opcode_without_consuming_more() {
        let names = name_table(&[]);
        let stream = vec![0xEE]; // opcode the walker does not recognise
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, 1);
        assert_eq!(visitor.unknown, 1);
    }

    #[test]
    fn walks_instance_delegate_reads_fname() {
        let names = name_table(&["OnFired"]);
        let mut stream = vec![EX_INSTANCE_DELEGATE];
        put_fname(&mut stream, 0);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.instance_delegate, 1);
    }

    #[test]
    fn walks_bind_delegate_reads_fname_and_two_subexprs() {
        let names = name_table(&["OnFired"]);
        let mut stream = vec![EX_BIND_DELEGATE];
        put_fname(&mut stream, 0); // function_name
        stream.push(EX_TRUE); // delegate sub-expr
        stream.push(EX_FALSE); // target sub-expr
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.bind_delegate, 1);
        assert_eq!(visitor.zero_operand, 2);
    }

    #[test]
    fn walks_add_multicast_delegate_reads_two_subexprs() {
        let names = name_table(&[]);
        let mut stream = vec![EX_ADD_MULTICAST_DELEGATE];
        stream.push(EX_TRUE); // delegate
        stream.push(EX_FALSE); // target
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.multicast_delegate_op, 1);
        assert_eq!(visitor.zero_operand, 2);
    }

    #[test]
    fn walks_remove_multicast_delegate_routes_same_hook() {
        let names = name_table(&[]);
        let mut stream = vec![EX_REMOVE_MULTICAST_DELEGATE];
        stream.push(EX_TRUE);
        stream.push(EX_FALSE);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.multicast_delegate_op, 1);
    }

    #[test]
    fn walks_call_multicast_delegate_with_args() {
        let names = name_table(&[]);
        let mut stream = vec![EX_CALL_MULTICAST_DELEGATE];
        put_i32(&mut stream, 7); // signature obj idx
        stream.push(EX_TRUE); // delegate sub-expr
        stream.push(EX_FALSE); // target sub-expr
        stream.push(EX_INT_ZERO); // arg 1
        stream.push(EX_INT_ONE); // arg 2
        stream.push(EX_END_FUNCTION_PARMS);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.call_multicast_delegate, 1);
        assert_eq!(visitor.zero_operand, 4);
    }

    #[test]
    fn walks_set_array_with_items() {
        // EX_SET_ARRAY: target sub-expr + item list terminated by EX_END_ARRAY (no size hint).
        let names = name_table(&[]);
        let mut stream = vec![EX_SET_ARRAY];
        stream.push(EX_TRUE); // target
        stream.push(EX_INT_ZERO); // item 0
        stream.push(EX_INT_ONE); // item 1
        stream.push(EX_END_ARRAY);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.set_container, 1);
        assert_eq!(visitor.zero_operand, 3); // EX_TRUE + EX_INT_ZERO + EX_INT_ONE
    }

    #[test]
    fn walks_set_set_with_count_and_items() {
        // EX_SET_SET: target sub-expr + i32 size hint + item list terminated by EX_END_SET.
        let names = name_table(&[]);
        let mut stream = vec![EX_SET_SET];
        stream.push(EX_FALSE); // target
        put_i32(&mut stream, 2); // size hint
        stream.push(EX_INT_ZERO); // item 0
        stream.push(EX_INT_ONE); // item 1
        stream.push(EX_END_SET);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.set_container, 1);
        assert_eq!(visitor.zero_operand, 3); // EX_FALSE + EX_INT_ZERO + EX_INT_ONE
    }

    #[test]
    fn walks_set_map_with_count_and_pairs() {
        // EX_SET_MAP: target sub-expr + i32 size hint + key/value pairs terminated by EX_END_MAP.
        let names = name_table(&[]);
        let mut stream = vec![EX_SET_MAP];
        stream.push(EX_TRUE); // target
        put_i32(&mut stream, 1); // size hint
        stream.push(EX_INT_ZERO); // key 0
        stream.push(EX_INT_ONE); // value 0
        stream.push(EX_END_MAP);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.set_container, 1);
        assert_eq!(visitor.zero_operand, 3); // EX_TRUE + EX_INT_ZERO + EX_INT_ONE
    }

    #[test]
    fn walks_array_const_with_items() {
        // EX_ARRAY_CONST: i32 inner_obj_idx + i32 count + items terminated by EX_END_ARRAY_CONST.
        let names = name_table(&[]);
        let mut stream = vec![EX_ARRAY_CONST];
        put_i32(&mut stream, 0); // inner obj idx
        put_i32(&mut stream, 2); // count hint
        stream.push(EX_INT_ZERO); // item 0
        stream.push(EX_INT_ONE); // item 1
        stream.push(EX_END_ARRAY_CONST);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.array_const, 1);
        assert_eq!(visitor.zero_operand, 2); // EX_INT_ZERO + EX_INT_ONE
    }

    #[test]
    fn walks_set_const_with_items() {
        // EX_SET_CONST: i32 inner_obj_idx + i32 count + items terminated by EX_END_SET_CONST.
        let names = name_table(&[]);
        let mut stream = vec![EX_SET_CONST];
        put_i32(&mut stream, 5); // inner obj idx
        put_i32(&mut stream, 1); // count hint
        stream.push(EX_INT_ONE); // item 0
        stream.push(EX_END_SET_CONST);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.set_const, 1);
        assert_eq!(visitor.zero_operand, 1);
    }

    #[test]
    fn walks_map_const_with_pairs() {
        // EX_MAP_CONST: i32 key_obj_idx + i32 value_obj_idx + i32 count + pairs terminated by EX_END_MAP_CONST.
        let names = name_table(&[]);
        let mut stream = vec![EX_MAP_CONST];
        put_i32(&mut stream, 3); // key obj idx
        put_i32(&mut stream, 4); // value obj idx
        put_i32(&mut stream, 1); // count hint
        stream.push(EX_INT_ZERO); // key 0
        stream.push(EX_INT_ONE); // value 0
        stream.push(EX_END_MAP_CONST);
        let ctx = WalkCtx::new(&stream, &names, 0);
        let mut visitor = CountingVisitor::default();
        let mut pos = 0;
        walk_opcode(&ctx, &mut pos, &mut visitor);
        assert_eq!(pos, stream.len());
        assert_eq!(visitor.map_const, 1);
        assert_eq!(visitor.zero_operand, 2); // EX_INT_ZERO + EX_INT_ONE
    }
}
