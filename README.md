# Unreal Blueprint Inspect

A CLI tool that extracts readable structure and logic from Unreal Engine Blueprint `.uasset` files without requiring the UE editor.

Parses the binary format directly and outputs component trees, variable declarations, function signatures, decoded bytecode pseudo-code, and graph node summaries.

Built primarily for use with AI coding assistants (Claude Code, etc.) to enable Blueprint debugging, logic review, and BP-to-C++ migration from the command line.

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

Existing tools solve different problems:

- **UAssetAPI** is a serialisation library. It round-trips the binary format faithfully but doesn't interpret it -- you get raw property trees and bytecode as byte arrays. No disassembly, no signature reconstruction. Built for modding tools that patch values and re-save, not for reading comprehension.
- **UE4 commandlets** (`DumpBlueprintInfo`, etc.) require a full editor instance with the project loaded, all dependencies resolved, game module DLLs compiled. They can't work on standalone `.uasset` files and their output is verbose internal reflection data.
- **NodeToCode** runs inside the editor as a plugin, translating graphs to C++ via LLM. Not usable from the command line or CI.

bp-inspect works on bare `.uasset` files with zero UE4 dependency. It reconstructs function signatures from parameter properties, disassembles Kismet bytecode into readable pseudo-code, structures control flow (if/else, while/for loops, ForEach, sequence nodes), inlines single-use temporaries and operators, resolves enum arguments to readable names, folds struct Break/Make patterns, strips serialisation noise (GUID suffixes, K2Node prefixes, library prefixes), and splits ubergraph functions into labelled event handlers with latent resume inlining. The `--summary` output is designed to be handed directly to an AI and asked "what does this Blueprint do?".

## What it parses

- **Package header** and name/import/export tables
- **Tagged properties** (Bool, Int, Float, Struct, Array, Map, Enum, Object refs, Text, etc.)
- **UStruct serialisation** (super struct, children array, FField child properties with metadata)
- **FField types** (FloatProperty, ObjectProperty, BoolProperty, StructProperty, ArrayProperty, etc.)
- **Kismet bytecode** decoded to structured pseudo-code with nested if/else blocks, while loops, ForEach loops, and sequence nodes (arithmetic, casts, context calls, conditionals, local/instance variables). Convergence reordering handles displaced branches from the UE4 compiler. Accurate memory-space offset tracking for jump target resolution.
- **EdGraph nodes** (K2Node_CallFunction, VariableGet/Set, DynamicCast, FunctionEntry/Result, events, etc.)
- **SCS component tree** with sub-object properties and child actor templates

## Supported formats

- UE4 uncooked `.uasset` files (single-file, not split `.uasset`/`.uexp`)
- Tested against UE4.27 (file version 522)
- UE5 and cooked asset support is planned

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

## Limitations

- UE5 assets and cooked (split `.uasset`/`.uexp`) files are not yet supported
- Bytecode decoder covers common opcodes but some complex expressions may show as `??(0xNN)`
- Unversioned properties (UE5 IoStore) require `.usmap` mappings, which are not implemented

## License

Apache-2.0
