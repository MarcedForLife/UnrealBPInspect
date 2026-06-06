# unreal-bp-inspect

Standalone Rust CLI that parses Unreal Engine Blueprint `.uasset` files into readable text or JSON. Binary name is `bp-inspect`.

## Building and testing

```bash
cargo build
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
cargo build --release
```

CI enforces `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings` on every push and PR.

### Test structure
- `src/**/*.rs` — inline `#[cfg(test)]` unit tests for private helpers
- `tests/integration.rs` — snapshot and structural tests using committed fixtures
- `tests/snapshots/` — expected output for regression detection
- `tests/common/mod.rs` — test utilities (fixture loading, snapshot comparison)
- `tests/v2_baseline.rs` — byte-identity over-fire gate for the decoder; `tests/decodertest_known_bugs.rs` — synthetic-fixture trackers (all green); `tests/v2_partition_helm.rs` — ubergraph partition checks

JSON mode should always produce valid JSON. When validating, redirect stderr so cargo build output doesn't pollute stdout:

```bash
cargo run -- samples/<file>.uasset --json 2>/dev/null | python3 -m json.tool
```

## Architecture

The parser reads the binary format sequentially through these modules:

1. **binary.rs** — Low-level I/O helpers and NameTable
2. **properties.rs** — Tagged property deserialisation (recursive)
3. **ffield.rs** — FField child property parsing, type resolution, function signatures
4. **bytecode/** — Kismet bytecode: ~85 opcodes (UE5 LWC support) decoded into a typed statement IR, then a control-flow graph and single-entry/single-exit region tree (IfThen/IfThenElse/Loop/SequenceChain/DoOnceGate) for if/else/loop structuring, plus IR transforms (loop refinement, latch/DoOnce recognition, convergence folds, name synthesis)
5. **parser.rs** — Orchestrates all parsing: header, name/import/export tables, export data, bytecode, EdGraph pin connections
6. **output_summary/** (default), **output_text.rs** (`--dump`), **output_json.rs** (`--json`), **output_diff.rs** (`--diff`) — the four output modes. Summary places EdGraph comments inline near the matching bytecode via pin-based BFS event ownership, with spatial cluster matching as fallback.

Key dependency flow: `types` + `binary` → `resolve` → `properties` + `ffield` → `bytecode` → `parser` → `output_*`

## Binary format notes

Key things to know:

- **FField metadata** has a `HasMetadata` gate: int32 = 1 means metadata block follows (MetadataCount + entries), 0 means nothing. Class members have metadata, function params don't.
- **UStruct::Children** is `int32 count + int32[count]` (array of package indices), not a single pointer.
- All FName references on disk are 8 bytes (int32 index + int32 instance number). In memory with `WITH_CASE_PRESERVING_NAME` (typical for uncooked), FName is 12 bytes (adds DisplayIndex). This +4 difference affects mem_adj for bytecode FName operands.
- Uncooked assets have everything in one `.uasset` file. Cooked assets split into `.uasset` header + `.uexp` data (not yet supported).
- **UE5 versioning**: `AssetVersion { file_ver, file_ver_ue5 }` is threaded through parsing. `file_ver_ue5` is 0 for UE4 assets, 1000+ for UE5. Key gates: 1003 (OptionalResources), 1004 (LWC -- double vectors/rotators), 1005 (remove export GUID), 1007 (SoftObjectPaths), 1010 (ScriptSerializationOffset), 1011 (PropertyTagExtension -- extension byte before tagged properties; UE source gates on `bIsUClass` but uncooked assets emit it for all exports), 1012 (PROPERTY_TAG_COMPLETE_TYPE_NAME -- new FPropertyTag format with recursive FPropertyTypeName and Flags byte). The `ue5: i32` parameter is threaded through bytecode decoding for LWC opcode branching.
- **UE5.2+ tagged properties** (ue5 >= 1012): FPropertyTag uses `FPropertyTypeName` (recursive: `FName + i32 innerCount + children`) instead of separate Type FName + type-specific fields. A `Flags` byte replaces `ArrayIndex` + `HasPropertyGuid`. All exports have a 1-byte `EClassSerializationControlExtension` before the property stream (0x00 = NoExtension). The extension byte gate and complete type name gate are both checked as `>= 1012` in the code; version 1011 (extension without new tag format) is untested.
- **LWC display normalization**: UE5 renames float math functions to double variants (`Add_FloatFloat` → `Add_DoubleDouble`, `SelectFloat` → `SelectDouble`) and promotes `float` properties to `double`. For output consistency and clean cross-version diffs, all display names are normalized back to their UE4 equivalents (`float`, `_FloatFloat`, `SelectFloat`). Actual data is always parsed at full f64 precision. Normalization happens in `bytecode/names.rs`, `bytecode/decode/expr_decode.rs`, and `ffield.rs`.

## Conventions

- Minimal dependencies: `clap`, `serde_json`, `anyhow`, `similar`, `ureq` (for self-update)
- Modular architecture: `lib.rs` + `main.rs` pattern with focused modules
- Default output is the summary mode (human-readable, designed for AI assistant use)
- `--json` is for programmatic access and should always be valid JSON
- Sample files in `samples/` are organized into `ue_4.27/`, `ue_5.3/`, and `ue_5.5/` subdirectories. Small fixtures are committed; larger samples are gitignored for local testing only
- **Deterministic output**: All output must be identical across runs for the same input. Never iterate a `HashMap`/`HashSet` when the order affects output or substitution results — use `BTreeMap`, `BTreeSet`, or collect-and-sort instead.
- **Naming in human-readable contexts**: in prose, doc comments, error messages, log lines, and plan documents, expand non-obvious acronyms on first use and prefer full words thereafter. Code identifiers may stay short. Universally-known acronyms (HTTP, JSON, URL, CPU) don't need expansion.
    + "statement" in prose, `Stmt` in code identifiers
    + "intermediate representation" on first mention, `IR` thereafter
    + "Blueprint" in prose, `BP` only after first use
    + "Large World Coordinates" on first mention, `LWC` thereafter
    + "bytecode" in prose, `Bc`/`bc` in code identifiers ok

## Release process

Run the Release workflow from GitHub Actions with a version bump type (patch/minor/major):

**Actions > Release > Run workflow > select bump type**

The workflow automatically bumps `Cargo.toml`, commits, tags, builds binaries for linux-x86_64, macos-x86_64, macos-aarch64, windows-x86_64 with SHA-256 checksums, and creates a GitHub release. Run `git pull` locally after the release to pick up the version bump commit.

Install scripts (`install.sh` / `install.ps1`) download from GitHub releases. `cargo install unreal-bp-inspect` works once published to crates.io.
