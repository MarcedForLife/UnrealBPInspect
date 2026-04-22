# unreal-bp-inspect

Standalone Rust CLI that parses Unreal Engine Blueprint `.uasset` files into readable text or JSON. Binary name is `bp-inspect`.

## Project structure

```
src/
  main.rs              CLI entry point
  lib.rs               Module declarations
  types.rs             Core data types (ImportEntry, ExportHeader, PropValue, Property, ParsedAsset)
  binary.rs            Binary reading helpers (Reader<'a>, read_*, NameTable)
  resolve.rs           Index resolution, property lookup helpers, format_func_flags
  enums.rs             Common UE4 enum argument resolution (ECollisionEnabled, EAttachmentRule, etc.)
  properties.rs        Tagged property deserialiser
  ffield.rs            FField type resolution, function signatures
  helpers.rs           Shared text utilities (indent_of, find_matching_paren, split_args, is_loop_header)
  parser.rs            Asset parser orchestrator (parse_asset, ParseCtx)
  pins.rs              EdGraph pin parsing (K2Node pin connections, LinkedTo, SubPins)
  prop_query.rs        Typed property lookup helpers (find_prop, find_struct_field_str, etc.)
  pin_hints/
    mod.rs             Module declarations + public re-exports
    types.rs           BranchSide, BranchInfo, BranchHints
    collect.rs         BFS over pins to build BranchHints from entry points
    routing.rs         Per-class exec-successor rules (Branch, Sequence, DoOnce)
    bytecode_map.rs    Map bytecode if-offsets to K2Node_IfThenElse exports
    detect.rs          Pin-aware else-branch classifier (scoped + explicit variants)
  pin_hints_scope.rs   Thread-local scope holding current BranchHints + BytecodeBranchMap
  output_text.rs       Dump output mode (--dump)
  output_json.rs       JSON output mode (--json)
  output_summary/
    mod.rs             Shared types (CommentBox, NodeInfo, UbergraphSection), re-exports
    comments.rs        EdGraph comment/bubble matching: rank-based, cluster-based, classification
    edgraph.rs         EdGraph data collection: comments, node positions, event positions, pin-based ownership BFS
    call_graph.rs      Call graph construction, ubergraph context, local function collection
    ubergraph/
      mod.rs           Public entry: emit_ubergraph_events, scan_structured_calls, is_ubergraph_stub, helpers
      linearize.rs     Event-stream linearization (split, linearize-from-entry, offset renumbering, jump-chain collapse)
      events.rs        Event-name and section-name resolution (InpAxisEvt_*, InpActEvt_* normalization)
      comment_placement.rs  Pin-classified + fallback comment placement within ubergraph sections
      emit.rs          Section-boundary build, delay-resume map, section-body emission
      tests.rs         Unit tests
    format.rs          Summary formatting: component tree, variables, functions, inline comments
    filter.rs          Post-processing filter for summary output (--filter)
    relocate/
      mod.rs           Entry point + orchestration for orphan DoOnce relocation via pin hints
      if_block.rs      IfBlock struct, find/parse if-blocks in the flat line list
      matching.rs      Match block body against BranchInfo pin-only sets
      rewrite.rs       Splice captured orphans into the matched branch, un-invert if needed
  output_diff.rs       Diff output mode (--diff: unified diff of two summaries)
  bytecode/
    mod.rs             OffsetMap, sub-module re-exports
    opcodes.rs         EExprToken opcode constants (EX_*)
    readers.rs         Bytecode binary stream readers (read_bc_*)
    names.rs           GUID stripping, name cleanup
    resolve.rs         Bytecode reference resolution (obj refs, field paths)
    decode/
      mod.rs           Re-exports decode_bytecode, decode_expr, BcStatement, DecodeCtx
      types.rs         BcStatement + DecodeCtx
      helpers.rs       Constant/list/delegate/container/table_op decode subroutines
      expr.rs          decode_expr top-level dispatcher (~20 arms)
      match_op.rs      decode_match_op (Switch/MatchOp handler, monolithic)
      funcs.rs         decode_func_args, primitive_cast_name
      entry.rs         decode_bytecode (public entry, drives the decode loop)
      tests.rs         Unit tests (34)
    cfg/
      mod.rs           Re-exports StmtCfg + BlockCfg public API
      stmt.rs          Statement-level CFG (StmtCfg) for event partitioning by reachability
      block/
        mod.rs         Re-exports BlockCfg, BlockExit, BlockId, ReturnKind, linearize_blocks
        types.rs       Block-level CFG types (BlockCfg, Block, BlockExit, BlockMetadata, ReturnKind, BlockCfgConfig)
        build.rs       Basic-block construction, edge wiring, latch-body range detection
        collapse.rs    Latch-body annotation and Sequence super-block collapse
        analysis.rs    In-degree, predecessors, convergence detection, reachability helpers
        linearize.rs   DFS linearization of the block CFG
        tests.rs       Unit tests
    flow/
      mod.rs           Re-exports parsers, reorder_flow_patterns, reorder_convergence, strip_latch_boilerplate, detect_sequence_spans
      parsers.rs       Statement-text parsers (parse_push_flow, parse_jump, etc.) + flow depth helpers
      sequence.rs      SequenceSpan + detect_sequence_spans
      loops.rs         ForLoop / ForEach detection (grouped and interleaved Sequence variants)
      emit.rs          SequenceEmitter, loop body emission
      latch_strip.rs   Pre-structuring latch boilerplate removal (distinct from latch/ which does the final rewrite)
      reorder.rs       Top-level reorder_flow_patterns + reorder_convergence pipeline
      tests.rs         Unit tests
    latch/
      mod.rs           Public entry: transform_latch_patterns, precompute_flipflop_names; shared gate/init var prefixes
      doonce.rs        DoOnce init-block detection, name derivation, library-function prefix list
      flipflop.rs      FlipFlop toggle detection, name derivation, convergence collapse
      transform.rs     Shared body-entry resolution and the monolithic transform_latches pass
      tests.rs         Unit tests
    structure/
      mod.rs           Public entry: structure_bytecode + apply_indentation; negate_cond helper
      region.rs        Region / RegionKind / IfBlock / BlockType types + tree mutation primitives
      detect.rs        if-block / else-branch / displaced-else detection
      build.rs         Region tree construction (build_region_tree, insert_* helpers)
      emit.rs          Region-tree to pseudocode emission
      postprocess.rs   Goto->break conversion, convergence extraction, double-else collapse
      tests.rs         Unit tests
    transforms/
      mod.rs           Shared helpers (parse_temp_assignment, substitute_var, etc.), re-exports
      temps.rs         Temp variable inlining, constant folding, dead assignment removal
      cleanup.rs       Line cleanup, bool switch rewriting, brace/goto cleanup, loop var renaming
      loops.rs         Loop pattern rewriting: ForEach (confirmed/unconfirmed), ForLoopWithBreak
      structs.rs       Break/Make struct folding, struct construction, Make* rename
      switch.rs        Switch/enum cascade folding
      pipeline.rs      Summary pipeline orchestration, delegates, casts, ternaries, section temps
      fold.rs          Line folding for long pseudocode lines (120-char target)
  update.rs            Self-update from GitHub releases (--update)
install.sh             macOS/Linux install script (curl | sh)
install.ps1            Windows install script (irm | iex)
skill/SKILL.md         Claude Code skill instructions
skill/README.md        Skill install guide
samples/
  ue_4.27/           UE4.27 test assets
  ue_5.3/            UE5.3 test assets
  ue_5.5/            UE5.5 test assets
tests/
  common/mod.rs      Test utilities (fixture loading, snapshot comparison)
  integration.rs     Snapshot and structural tests
snapshots/         Expected output files for regression detection
```

## Building and testing

```bash
cargo build                                    # dev build
cargo fmt                                      # format all code (required before committing)
cargo clippy --all-targets -- -D warnings      # lint check (must pass clean)
cargo test                                     # run all tests
cargo test -- --nocapture                      # run with stdout visible
UPDATE_SNAPSHOTS=1 cargo test                  # update snapshot files after intentional changes
cargo run -- samples/<file>.uasset             # test summary output (default)
cargo run -- samples/<file>.uasset --dump      # test full dump output
cargo run -- samples/<file>.uasset --json      # test JSON output
cargo run -- --diff samples/A.uasset samples/B.uasset  # test diff output
cargo run -- samples/                          # test batch/directory mode
cargo build --release                          # release build
```

CI enforces `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings` on every push and PR.

### Test structure
- `src/**/*.rs` — inline `#[cfg(test)]` unit tests for private helpers
- `tests/integration.rs` — snapshot and structural tests using committed fixtures
- `tests/snapshots/` — expected output for regression detection
- `tests/snapshots/private/` — branch-local snapshots for regression coverage, pruned before merge (see `tests/snapshots/README.md`)
- `tests/common/mod.rs` — test utilities (fixture loading, snapshot comparison)

JSON mode should always produce valid JSON. When validating, redirect stderr so cargo build output doesn't pollute stdout:

```bash
cargo run -- samples/<file>.uasset --json 2>/dev/null | python3 -m json.tool
```

## Architecture

The parser reads the binary format sequentially through these modules:

1. **binary.rs** — Low-level I/O helpers and NameTable
2. **properties.rs** — Tagged property deserialisation (recursive)
3. **ffield.rs** — FField child property parsing, type resolution, function signatures
4. **bytecode/** — Kismet bytecode: expression decoding (~85 opcodes, UE5 LWC support), flow pattern detection (sequences, ForEach via `foreach (COND) {` markers, ForLoopWithBreak, convergence reordering/duplication, FlipFlop/DoOnce latch stripping), if/else/loop structuring via region tree with guard-to-nested-if conversion, single-pass indentation
5. **parser.rs** — Orchestrates all parsing: header, name/import/export tables, export data, bytecode, EdGraph pin connections
6. **output_*.rs** — Three output modes: summary (default), dump, JSON. Summary mode places EdGraph comments inline near corresponding bytecode using: (a) pin-based event ownership via BFS through execution pins to assign comments to the correct event section, falling back to (b) cluster-based spatial matching against bytecode identifiers.

Key dependency flow: `types` + `binary` → `resolve` → `properties` + `ffield` → `bytecode` → `parser` → `output_*`

## Binary format notes

Key things to know:

- **FField metadata** has a `HasMetadata` gate: int32 = 1 means metadata block follows (MetadataCount + entries), 0 means nothing. Class members have metadata, function params don't.
- **UStruct::Children** is `int32 count + int32[count]` (array of package indices), not a single pointer.
- All FName references on disk are 8 bytes (int32 index + int32 instance number). In memory with `WITH_CASE_PRESERVING_NAME` (typical for uncooked), FName is 12 bytes (adds DisplayIndex). This +4 difference affects mem_adj for bytecode FName operands.
- Uncooked assets have everything in one `.uasset` file. Cooked assets split into `.uasset` header + `.uexp` data (not yet supported).
- **UE5 versioning**: `AssetVersion { file_ver, file_ver_ue5 }` is threaded through parsing. `file_ver_ue5` is 0 for UE4 assets, 1000+ for UE5. Key gates: 1003 (OptionalResources), 1004 (LWC -- double vectors/rotators), 1005 (remove export GUID), 1007 (SoftObjectPaths), 1010 (ScriptSerializationOffset), 1011 (PropertyTagExtension -- extension byte before tagged properties; UE source gates on `bIsUClass` but uncooked assets emit it for all exports), 1012 (PROPERTY_TAG_COMPLETE_TYPE_NAME -- new FPropertyTag format with recursive FPropertyTypeName and Flags byte). The `ue5: i32` parameter is threaded through bytecode decoding for LWC opcode branching.
- **UE5.2+ tagged properties** (ue5 >= 1012): FPropertyTag uses `FPropertyTypeName` (recursive: `FName + i32 innerCount + children`) instead of separate Type FName + type-specific fields. A `Flags` byte replaces `ArrayIndex` + `HasPropertyGuid`. All exports have a 1-byte `EClassSerializationControlExtension` before the property stream (0x00 = NoExtension). The extension byte gate and complete type name gate are both checked as `>= 1012` in the code; version 1011 (extension without new tag format) is untested.
- **LWC display normalization**: UE5 renames float math functions to double variants (`Add_FloatFloat` → `Add_DoubleDouble`, `SelectFloat` → `SelectDouble`) and promotes `float` properties to `double`. For output consistency and clean cross-version diffs, all display names are normalized back to their UE4 equivalents (`float`, `_FloatFloat`, `SelectFloat`). Actual data is always parsed at full f64 precision. Normalization happens in `bytecode/names.rs`, `bytecode/decode.rs`, and `ffield.rs`.

## Conventions

- Minimal dependencies: `clap`, `serde_json`, `anyhow`, `similar`, `ureq` (for self-update)
- Modular architecture: `lib.rs` + `main.rs` pattern with focused modules
- Default output is the summary mode (human-readable, designed for AI assistant use)
- `--json` is for programmatic access and should always be valid JSON
- Sample files in `samples/` are organized into `ue_4.27/`, `ue_5.3/`, and `ue_5.5/` subdirectories. Small fixtures are committed; larger samples are gitignored for local testing only
- **Deterministic output**: All output must be identical across runs for the same input. Never iterate a `HashMap`/`HashSet` when the order affects output or substitution results — use `BTreeMap`, `BTreeSet`, or collect-and-sort instead.
- Always check if the `README.md`, `CLAUDE.md`, and other documentation files need updating

## Release process

Run the Release workflow from GitHub Actions with a version bump type (patch/minor/major):

**Actions > Release > Run workflow > select bump type**

The workflow automatically bumps `Cargo.toml`, commits, tags, builds binaries for linux-x86_64, macos-x86_64, macos-aarch64, windows-x86_64 with SHA-256 checksums, and creates a GitHub release. Run `git pull` locally after the release to pick up the version bump commit.

Install scripts (`install.sh` / `install.ps1`) download from GitHub releases. `cargo install unreal-bp-inspect` works once published to crates.io.
