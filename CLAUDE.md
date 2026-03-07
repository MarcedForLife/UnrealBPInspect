# unreal-bp-inspect

Standalone Rust CLI that parses Unreal Engine Blueprint `.uasset` files into readable text or JSON. Binary name is `bp-inspect`.

## Project structure

```
src/
  main.rs              CLI entry point (~60 lines)
  lib.rs               Module declarations
  types.rs             Core data types (ImportEntry, ExportHeader, PropValue, Property, ParsedAsset)
  binary.rs            Binary reading helpers (R<'a>, read_*, NameTable)
  resolve.rs           Index resolution, property lookup helpers, format_func_flags
  enums.rs             Common UE4 enum argument resolution (ECollisionEnabled, EAttachmentRule, etc.)
  properties.rs        Tagged property deserialiser
  ffield.rs            FField type resolution, function signatures
  parser.rs            Asset parser orchestrator (parse_asset)
  output_text.rs       Text output mode
  output_json.rs       JSON output mode
  output_summary.rs    Summary output mode (component tree, variables, functions)
  bytecode/
    mod.rs             Sub-module re-exports
    readers.rs         Bytecode binary stream readers (read_bc_*)
    names.rs           GUID stripping, name cleanup
    resolve.rs         Bytecode reference resolution (obj refs, field paths)
    decode.rs          Expression decoder (~77 opcodes), BcStatement, decode_bytecode
    flow.rs            Flow pattern detection (sequences, for-loops, ForEach, convergence reorder)
    structure.rs       If/else block structuring, false-block truncation
    inline.rs          Temp inlining, ForEach rewriting, delegate folding, summary pattern folding
skill/SKILL.md       Claude Code skill instructions
skill/README.md      Skill install guide
samples/             Test .uasset files (UE4.27, uncooked)
```

## Building and testing

```bash
cargo build                                    # dev build
cargo run -- samples/<file>.uasset --summary  # test summary output
cargo run -- samples/<file>.uasset --json     # test JSON output
cargo build --release                          # release build
```

No test suite yet. Validate changes by running against sample files and checking output makes sense. JSON mode should always produce valid JSON (`| python3 -m json.tool`).

## Architecture

The parser reads the binary format sequentially through these modules:

1. **binary.rs** — Low-level I/O helpers and NameTable
2. **properties.rs** — Tagged property deserialisation (recursive)
3. **ffield.rs** — FField child property parsing, type resolution, function signatures
4. **bytecode/** — Kismet bytecode: expression decoding (~77 opcodes), flow pattern detection, if/else structuring
5. **parser.rs** — Orchestrates all parsing: header, name/import/export tables, export data, bytecode
6. **output_*.rs** — Three output modes: text, JSON, summary

Key dependency flow: `types` + `binary` → `resolve` → `properties` + `ffield` → `bytecode` → `parser` → `output_*`

## Binary format notes

Key things to know:

- **FField metadata** has a `HasMetadata` gate: int32 = 1 means metadata block follows (MetadataCount + entries), 0 means nothing. Class members have metadata, function params don't.
- **UStruct::Children** is `int32 count + int32[count]` (array of package indices), not a single pointer.
- All FName references on disk are 8 bytes (int32 index + int32 instance number). In memory with `WITH_CASE_PRESERVING_NAME` (typical for uncooked), FName is 12 bytes (adds DisplayIndex). This +4 difference affects mem_adj for bytecode FName operands.
- Uncooked assets have everything in one `.uasset` file. Cooked assets split into `.uasset` header + `.uexp` data (not yet supported).

## Conventions

- No external dependencies beyond `clap`, `serde_json`, and `anyhow`
- Modular architecture: `lib.rs` + `main.rs` pattern with focused modules
- `--summary` is the primary output mode for AI assistant use
- `--json` is for programmatic access and should always be valid JSON
- Sample files in `samples/` are from a UE4.27 project called "LastResort" (gitignored, not in repo)
- Always check if the `README.md`, `CLAUDE.md`, and other documentation files need updating

## Release process

Push a version tag to trigger GitHub Actions:

```bash
git tag v0.1.0
git push --tags
```

Builds binaries for linux-x86_64, macos-x86_64, macos-aarch64, windows-x86_64 and creates a GitHub release.
