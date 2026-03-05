# unreal-bp-inspect

A CLI tool that extracts readable structure and logic from Unreal Engine Blueprint `.uasset` files without requiring the UE editor.

Parses the binary format directly and outputs component trees, variable declarations, function signatures, decoded bytecode pseudo-code, and graph node summaries.

Built primarily for use with AI coding assistants (Claude Code, etc.) to enable Blueprint debugging, logic review, and BP-to-C++ migration from the command line.

## Usage

```
bp-inspect [OPTIONS] <PATH>
```

### Options

| Flag                     | Description                                                                                   |
| ------------------------ | --------------------------------------------------------------------------------------------- |
| `--summary`              | Concise logical structure: class hierarchy, components, variables, functions with pseudo-code |
| `--json`                 | Full structured output as JSON                                                                |
| `--filter <name>`        | Filter exports by name (substring match, comma-separated)                                     |
| `--debug`                | Dump raw table data for format investigation                                                  |
| `-V` / `--version`       | Print version                                                                                 |

### Summary mode

The default debugging view. Shows the Blueprint as a single readable document.

```
$ bp-inspect Helm_BP.uasset --summary

Blueprint: Helm_BP (extends Actor)

Components:
  DefaultSceneRoot (SceneComponent)
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

Variables:
  WinchConstraintInstance: WinchConstraint_BP_C*

Functions:
  GetSteeringAngle(out SteeringAngle: float) [Public|HasOutParms|BlueprintPure|Const]
    self.WinchConstraintInstance.GetRotationAlpha($GetRotationAlpha_RotationAlpha)
    $Multiply_FloatFloat = Multiply_FloatFloat($GetRotationAlpha_RotationAlpha, 2.0000)
    $Subtract_FloatFloat = Subtract_FloatFloat($Multiply_FloatFloat, 1.0000)
    out SteeringAngle = $Subtract_FloatFloat
    return nop
  UserConstructionScript() [Event|Public|BlueprintPure]
    $Cast_AsWinch_Constraint_BP = cast<WinchConstraint_BP_C>(self.WheelConstraint.ChildActor)
    ...
```

### Filtering

Drill into a specific function while keeping class context:

```
$ bp-inspect Helm_BP.uasset --summary --filter GetSteeringAngle
```

### JSON mode

Full structured output for programmatic use:

```
$ bp-inspect Helm_BP.uasset --json | jq '.exports[] | select(.name == "GetSteeringAngle")'
```

## What it parses

- **Package header** and name/import/export tables
- **Tagged properties** (Bool, Int, Float, Struct, Array, Map, Enum, Object refs, Text, etc.)
- **UStruct serialisation** (super struct, children array, FField child properties with metadata)
- **FField types** (FloatProperty, ObjectProperty, BoolProperty, StructProperty, ArrayProperty, etc.)
- **Kismet bytecode** decoded to pseudo-code (arithmetic, casts, context calls, conditionals, local/instance variables)
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

```
cargo install --path .
```

Or build directly:

```
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

MIT
