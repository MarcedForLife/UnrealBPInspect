# unreal-bp-inspect

Standalone Rust CLI that parses Unreal Engine Blueprint `.uasset` files into readable text or JSON. Binary name is `bp-inspect`.

## Project structure

```
src/main.rs          Single-file parser (~2400 lines)
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

Everything is in `src/main.rs`. The parser reads the binary format sequentially:

1. **Package header** — magic, version, name/import/export table offsets
2. **Name table** — FString entries used as keys throughout
3. **Import table** — external class/object references with outer_index chain
4. **Export table** — headers with serial offset/size, then per-export data
5. **Export data** — tagged properties, then type-specific: UStruct children, FField metadata, bytecode
6. **Output** — text (default), `--json`, or `--summary`

Key functions:
- `read_properties()` — recursive tagged property deserialiser
- `decode_expr()` — Kismet bytecode decoder (recursive, ~40 opcodes)
- `resolve_ffield_type()` — maps FField class names to readable types
- `print_summary()` — the summary view (component tree, variables, functions)
- `skip_ffield_child()` — skips FField data in exports we don't fully parse

## Binary format notes

Key things to know:

- **FField metadata** has a `HasMetadata` gate: int32 = 1 means metadata block follows (MetadataCount + entries), 0 means nothing. Class members have metadata, function params don't.
- **UStruct::Children** is `int32 count + int32[count]` (array of package indices), not a single pointer.
- All FName references on disk are 8 bytes (int32 index + int32 instance number).
- Uncooked assets have everything in one `.uasset` file. Cooked assets split into `.uasset` header + `.uexp` data (not yet supported).

## Conventions

- No external dependencies beyond `clap` and `serde_json`
- Single-file architecture — don't split into modules unless it gets unmanageable
- `--summary` is the primary output mode for AI assistant use
- `--json` is for programmatic access and should always be valid JSON
- Sample files in `samples/` are from a UE4.27 project called "LastResort" (gitignored, not in repo)

## Release process

Push a version tag to trigger GitHub Actions:

```bash
git tag v0.1.0
git push --tags
```

Builds binaries for linux-x86_64, macos-x86_64, macos-aarch64, windows-x86_64 and creates a GitHub release.
