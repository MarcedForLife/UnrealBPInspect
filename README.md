# Unreal Blueprint Inspect

A standalone CLI that makes Unreal Engine Blueprint `.uasset` files readable outside the editor — in terminals, AI assistants, code review, CI pipelines, and documentation.

Parses the binary format directly and outputs component trees, variable declarations, function signatures, decoded bytecode pseudo-code, and graph node summaries. No editor, no project context, no dependencies.

## Usage

```sh
bp-inspect [OPTIONS] <PATH>
```

### Options

| Flag               | Description                                                                                   |
| ------------------ | --------------------------------------------------------------------------------------------- |
| `--summary`        | Concise logical structure: class hierarchy, components, variables, functions with pseudo-code |
| `--json`           | Full structured output as JSON                                                                |
| `--filter <name>`  | Filter exports by name (substring match, comma-separated)                                     |
| `--debug`          | Dump raw table data for format investigation                                                  |
| `-V` / `--version` | Print version                                                                                 |

### Summary mode

The default debugging view. Shows the Blueprint as a single readable document.

```sh
$ bp-inspect Helm_BP.uasset --summary

Blueprint: Helm_BP (extends Actor)

Components:
  Scene (SceneComponent)
    Stand (StaticMeshComponent)
      StaticMesh: helm_elemnt_02
      BodyInstance: CollisionProfileName: Custom, PhysMaterialOverride: 11_Wood_Physic_Mat
    Wheel (GrippableStaticMeshComponent)
      StaticMesh: helm_elemnt_01
      BodyInstance: ObjectType: ECC_PhysicsBody, CollisionProfileName: PhysicsActor, ...
      RelativeLocation: (-0.0000, 0.0000, 146.6086)
    WheelConstraint (ChildActorComponent)
      ChildActorClass: WinchConstraint_BP_C
      [template: WinchConstraint_BP_C]
        WinchMesh: helm_elemnt_01
        WinchComponentName: "Wheel"
        InitialRotationAlpha: 0.5000
  DefaultSceneRoot (SceneComponent)

Variables:
  WinchConstraintInstance: WinchConstraint_BP_C*

Functions:
  GetSteeringAngle(out SteeringAngle: float) [Public|HasOutParms|BlueprintPure|Const]
    self.WinchConstraintInstance.GetRotationAlpha($GetRotationAlpha_RotationAlpha)
    out SteeringAngle = ($GetRotationAlpha_RotationAlpha * 2.0000) - 1.0000
  UserConstructionScript() [Event|Public|BlueprintPure]
    $Cast_AsWinch_Constraint_BP = cast<WinchConstraint_BP_C>(self.WheelConstraint.ChildActor)
    if ($Cast_AsWinch_Constraint_BP) {
        self.WinchConstraintInstance = $Cast_AsWinch_Constraint_BP
    }
```

### Filtering

Drill into a specific function while keeping class context:

```sh
bp-inspect Helm_BP.uasset --summary --filter GetSteeringAngle
```

### JSON mode

Full structured output for programmatic use:

```sh
bp-inspect Helm_BP.uasset --json | jq '.exports[] | select(.name == "GetSteeringAngle")'
```

## Why bp-inspect

Blueprint `.uasset` files are binary — opaque to git diff, code review, CI pipelines, AI assistants, and every other text-based tool. The editor is the only way to read them. bp-inspect changes that.

**How it compares to existing tools:**

- **UAssetAPI** is a serialisation library for modding tools. It round-trips the binary format faithfully but doesn't interpret it — you get raw property trees and bytecode as byte arrays. No disassembly, no signature reconstruction, no readable output.
- **UE commandlets** (`DumpBlueprintInfo`, etc.) require a full editor instance with the project loaded, all dependencies resolved, game module DLLs compiled. They can't work on standalone `.uasset` files.
- **[NodeToCode](https://github.com/protospatial/NodeToCode)** is an editor plugin that translates Blueprint visual graphs to C++ via LLM. Great for interactive code migration inside the editor, but requires the editor running and an AI API key. It reads the live graph through the editor API, not the binary file — so it can't work in terminals, CI, or code review. The two tools are complementary: NodeToCode for editor-based interactive work, bp-inspect for everything outside the editor.

bp-inspect takes a different approach: it reads the compiled bytecode from the binary file directly, with zero UE dependency. A 1MB Blueprint with 18 functions parses in ~15ms — the entire Blueprint (all functions, components, variables), not one graph at a time. No API calls, no editor, no network.

The raw bytecode is not the hard part — making it *readable* is. bp-inspect reconstructs function signatures from parameter properties, disassembles Kismet bytecode into structured pseudo-code, detects and structures control flow (if/else, while/for loops, ForEach, sequence nodes), reorders displaced convergence blocks from the UE4 compiler, inlines single-use temporaries and operators, resolves enum arguments to readable names, dynamically infers and folds struct Break/Make patterns, strips serialisation noise (GUID suffixes, K2Node prefixes, library prefixes), splits ubergraph functions into labelled event handlers, and inlines latent resume blocks after their corresponding Delay() calls. The goal is output that reads like hand-written pseudocode, not a bytecode dump.

The `--summary` output is designed to be handed directly to an AI assistant and asked "what does this Blueprint do?".

## What it parses

- **Package header** and name/import/export tables
- **Tagged properties** (Bool, Int, Float, Struct, Array, Map, Enum, Object refs, Text, etc.)
- **UStruct serialisation** (super struct, children array, FField child properties with metadata)
- **FField types** (FloatProperty, ObjectProperty, BoolProperty, StructProperty, ArrayProperty, etc.)
- **Kismet bytecode** decoded to structured pseudo-code with nested if/else blocks, while loops, ForEach loops, and sequence nodes (arithmetic, casts, context calls, conditionals, local/instance variables). Convergence reordering handles displaced branches from the UE4 compiler. Accurate memory-space offset tracking for jump target resolution.
- **EdGraph nodes** (K2Node_CallFunction, VariableGet/Set, DynamicCast, FunctionEntry/Result, events, etc.)
- **SCS component tree** with sub-object properties and child actor templates

## Supported formats

- UE4 uncooked `.uasset` files (UE4.14–4.27, file versions 459–522)
- UE5 uncooked `.uasset` files (UE5.0–5.5) with Large World Coordinates support
- Animation Blueprints and Widget Blueprints partially work (event graphs and functions parse correctly; AnimGraph state machines and widget hierarchy display are planned)
- Cooked assets (split `.uasset`/`.uexp`) and UE5 IoStore format are not yet supported

## Install

### From releases

Download a prebuilt binary from [Releases](../../releases) for your platform.

### From source

Requires [Rust](https://rustup.rs/) 1.70+.

```sh
cargo install --path .
```

Or build directly:

```sh
cargo build --release
# Binary at target/release/bp-inspect
```

## Claude Code skill

The `skill/` directory contains a Claude Code skill that teaches Claude how to use `bp-inspect` for Blueprint debugging, logic review, and BP-to-C++ migration. See [skill/README.md](skill/README.md) for install instructions.

## Development

### Building

```sh
cargo build                        # dev build
cargo build --release              # optimised build → target/release/bp-inspect
```

### Running locally

Use `cargo run --` to pass arguments to the CLI during development:

```sh
cargo run -- samples/Helm_BP.uasset --summary           # human-readable summary
cargo run -- samples/Helm_BP.uasset --json               # full JSON output
cargo run -- samples/Helm_BP.uasset --json | python3 -m json.tool   # validate JSON
cargo run -- samples/Helm_BP.uasset --summary --filter GetSteeringAngle  # single function
cargo run -- samples/Helm_BP.uasset --debug              # raw table dump for format investigation
```

### Testing

```sh
cargo test                         # run all tests
cargo test -- --nocapture          # run with stdout visible
cargo test inline                  # run tests matching "inline"
UPDATE_SNAPSHOTS=1 cargo test      # update snapshot files after intentional output changes
```

The test suite has two layers. **Unit tests** live inline in source files (`#[cfg(test)]`) because they test private helper functions (expression decoding, temp inlining, control flow structuring, name cleanup) that aren't accessible from outside their module. **Integration tests** in `tests/` exercise the public API end-to-end with snapshot regression for summary/text/JSON output and structural assertions.

**Snapshot tests**: expected outputs live in `tests/snapshots/`. When you intentionally change output format, run with `UPDATE_SNAPSHOTS=1` to regenerate them, then review the diffs before committing.

**Adding test fixtures**: place `.uasset` files in `samples/`. The committed fixture `Helm_BP.uasset` is used by integration tests. Additional files are gitignored and used by `tests/extended.rs`, which auto-skips when they're absent.

## Limitations

- Cooked (split `.uasset`/`.uexp`) files are not yet supported
- Bytecode decoder covers ~85 of ~120+ Kismet opcodes; uncommon expressions may show as `??(0xNN)`
- Animation Blueprint state machines (AnimGraph) and Material expression trees are not yet interpreted — only standard Blueprint logic (event graphs, functions)
- Unversioned properties (UE5 IoStore) require `.usmap` mappings, which are not implemented

## License

Apache-2.0
