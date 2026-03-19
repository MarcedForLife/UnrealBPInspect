# Unreal Blueprint Inspect

A standalone CLI that makes Unreal Engine Blueprint `.uasset` files readable outside the editor: in terminals, AI assistants, code review, CI pipelines, and documentation.

Parses the binary format directly and outputs component trees, variable declarations, function signatures, decoded bytecode pseudo-code, and graph node summaries. No editor, no project context, no dependencies.

> [!NOTE]
> This project is in early development. Core parsing works well for uncooked assets, but expect rough edges, missing opcodes, and breaking changes.
>
> This started as a personal prototype to see if Blueprint bytecode could be made readable outside the editor. AI-assisted development made it practical to explore as a solo side project.

## Install

### Windows (PowerShell)

```powershell
irm https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.ps1 | iex
```

### macOS / Linux

```sh
curl -fsSL https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.sh | sh
```

### With Cargo

```sh
cargo install unreal-bp-inspect
```

The install scripts download the latest binary, add it to your PATH, and configure Git to show readable Blueprint diffs. See [Git integration](#git-integration) for details.

### Install options

| Option                 | Shell                                       | PowerShell                           |
| ---------------------- | ------------------------------------------- | ------------------------------------ |
| Specific version       | `BP_INSPECT_VERSION=v0.1.0 curl ... \| sh`  | `.\install.ps1 -Version v0.1.0`      |
| Custom directory       | `INSTALL_DIR=/usr/local/bin curl ... \| sh` | `.\install.ps1 -InstallDir C:\Tools` |
| With Claude Code skill | `curl ... \| sh -s -- --with-skill`         | `.\install.ps1 -WithSkill`           |

### From source

```sh
git clone https://github.com/MarcedForLife/unreal-bp-inspect.git
cd unreal-bp-inspect
cargo install --path .
```

## Usage

```sh
bp-inspect [OPTIONS] <PATH>...
```

Accepts one or more `.uasset` files or directories. Directories are scanned recursively.

| Flag               | Description                                                |
| ------------------ | ---------------------------------------------------------- |
| `--dump`           | Full import/export/property dump (verbose diagnostic view) |
| `--json`           | Full structured output as JSON                             |
| `--diff`           | Compare two `.uasset` files (unified diff of summaries)    |
| `--filter <name>`  | Filter exports by name (substring match, comma-separated)  |
| `--update`         | Update bp-inspect to the latest release                    |
| `--context <N>`    | Context lines in diff output (default: 3)                  |
| `--debug`          | Dump raw table data for format investigation               |
| `-V` / `--version` | Print version                                              |

### Default output

Shows the Blueprint as a single readable document with components, variables, and decoded functions:

```sh
$ bp-inspect Helm_BP.uasset

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
bp-inspect MyBlueprint.uasset --filter MyFunction
```

### Batch / directory mode

```sh
bp-inspect Content/Blueprints/                          # all .uasset files under directory
bp-inspect A_BP.uasset B_BP.uasset                      # multiple files
bp-inspect Content/ --json | jq '.[].functions[].name'   # multi-file JSON array
```

### Comparing Blueprints

```sh
bp-inspect --diff Old_BP.uasset New_BP.uasset
```

Outputs a unified diff of the decoded summaries. Exit code 0 means identical, 1 means differences found. Combine with `--filter` to compare specific functions.

### JSON mode

Full structured output for programmatic use. Includes top-level `imports`, `exports`, and `functions` arrays. Functions have pre-extracted signatures, flags, and structured bytecode:

```sh
bp-inspect MyBlueprint.uasset --json | jq '.functions[] | {name, signature, flags}'
```

## Git integration

bp-inspect can act as a Git [textconv](https://git-scm.com/docs/gitattributes#_performing_text_diffs_of_binary_files) filter, making `git diff`, `git log -p`, and GUI tools show readable Blueprint diffs instead of "Binary files differ".

### Setup

**1. `.gitattributes`** - add to your UE project repo (committed, shared with teammates):

```
*.uasset diff=bp-inspect
```

**2. Git config** - run once (globally, so it applies to all repos):

```sh
git config --global diff.bp-inspect.textconv bp-inspect
git config --global diff.bp-inspect.cachetextconv true
```

If bp-inspect isn't on PATH, use the full path instead:

```sh
# macOS / Linux
git config --global diff.bp-inspect.textconv /path/to/bp-inspect

# Windows - use forward slashes
git config --global diff.bp-inspect.textconv C:/Tools/bp-inspect.exe
```

### What it looks like

```diff
$ git diff Content/Blueprints/MyBlueprint.uasset

-  GripStrength: float = 0.8
+  GripStrength: float = 1.2

   OnGripReleased():
-    Delay(0.5000)
+    Delay(1.0000)
```

### Notes

- **Read-only** - textconv only affects diff display. Git still treats `.uasset` as binary for merge/conflict resolution.
- **`cachetextconv = true`** caches converted text per blob SHA, so repeated diffs are fast.
- Works with `git log -p`, `git show`, `git diff --cached`, and any tool that uses Git's diff machinery.

## Claude Code skill

bp-inspect includes a [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill that teaches Claude to read, debug, and explain Blueprint files.

Install it alongside bp-inspect using `--with-skill` (see [Install options](#install-options)), or copy manually:

```sh
cp -r skill/ ~/.claude/skills/unreal-bp/
```

Once installed, Claude can read any `.uasset` file you point it at. Ask it to explain what a Blueprint does, debug a specific function, or plan a Blueprint-to-C++ migration.

## How it works

bp-inspect reads the compiled bytecode from the binary file directly, with zero UE dependency. A 1MB Blueprint with 18 functions parses in ~15ms, the entire Blueprint, not one graph at a time.

The hard part is making bytecode *readable*. bp-inspect:

- Reconstructs function signatures from parameter properties
- Disassembles Kismet bytecode into structured pseudo-code with if/else, while/for, ForEach, and sequence nodes
- Reorders displaced convergence blocks from the UE4 compiler
- Inlines single-use temporaries and folds struct Break/Make patterns
- Strips serialisation noise (GUID suffixes, K2Node prefixes, library prefixes)
- Splits ubergraph functions into labelled event handlers
- Inlines latent resume blocks after their corresponding Delay() calls
- Places Blueprint comment boxes and bubble comments inline near the code they annotate (via 2D spatial matching between graph nodes and bytecode)

The goal is output that reads like hand-written pseudocode, not a bytecode dump.

**How it compares to existing tools:**

| Tool                                                         | Approach                                    | Limitations                                                                           |
| ------------------------------------------------------------ | ------------------------------------------- | ------------------------------------------------------------------------------------- |
| **UAssetAPI**                                                | .NET serialisation library for modding      | Raw property trees and byte arrays, no disassembly or readable output                 |
| **UE commandlets**                                           | Editor-based dump tools                     | Requires full editor instance with project loaded and all dependencies compiled       |
| **[NodeToCode](https://github.com/protospatial/NodeToCode)** | Editor plugin, BP→C++ via LLM               | Requires running editor + AI API key; reads live graph, not binary files              |
| **bp-inspect**                                               | Standalone binary, reads `.uasset` directly | No editor, no project context, no network. Works in terminals, CI, and AI assistants  |

## Supported formats

- **UE4** uncooked `.uasset` files (4.14-4.27, file versions 459-522)
- **UE5** uncooked `.uasset` files (5.0-5.5) with Large World Coordinates support
- Tested with UE 4.27 (version 522), 5.3 (version 1009), and 5.5 (version 1012+). Other UE5 versions should work but are unverified.
- Animation Blueprints and Widget Blueprints partially work (event graphs and functions parse correctly; AnimGraph state machines and widget hierarchy display are planned)
- Cooked assets (split `.uasset`/`.uexp`) and UE5 IoStore format are not yet supported

## Development

### Building

```sh
cargo build                        # dev build
cargo build --release              # optimised build → target/release/bp-inspect
```

### Running locally

```sh
cargo run -- samples/ue_4.27/MyBlueprint.uasset                       # human-readable summary (default)
cargo run -- samples/ue_4.27/MyBlueprint.uasset --dump                # full import/export/property dump
cargo run -- samples/ue_4.27/MyBlueprint.uasset --json                # full JSON output
cargo run -- samples/ue_4.27/MyBlueprint.uasset --filter MyFunction   # single function
cargo run -- --diff samples/ue_4.27/A.uasset samples/ue_5.5/A.uasset # compare two files
cargo run -- samples/                                                 # all .uasset files in directory
```

### Testing

```sh
cargo test                         # run all tests
cargo test -- --nocapture          # run with stdout visible
cargo test inline                  # run tests matching "inline"
UPDATE_SNAPSHOTS=1 cargo test      # update snapshot files after intentional output changes
```

**Unit tests** live inline in source files (`#[cfg(test)]`). They test private helpers that aren't accessible from outside their module. **Integration tests** in `tests/` exercise the public API end-to-end with snapshot regression and structural assertions.

**Snapshot tests**: expected outputs live in `tests/snapshots/`. After intentional output changes, run with `UPDATE_SNAPSHOTS=1` to regenerate, then review diffs before committing.

**Test fixtures**: place `.uasset` files in `samples/ue_4.27/` or `samples/ue_5.5/`. Small committed fixtures are used by integration tests; larger files are gitignored for local testing.

### Contributing

Branch from `main` and open a pull request when ready.

| Convention        | Details                                                                        |
| ----------------- | ------------------------------------------------------------------------------ |
| Branch naming     | `feature/short-description` or `bugfix/short-description`                      |
| Commit hygiene    | Squash fixups and WIP commits; keep logically distinct changes separate        |
| Before submitting | `cargo fmt`, `cargo clippy --all-targets -- -D warnings`, `cargo test`         |
| Merge strategy    | Merge commit when history is curated, squash merge for single-concern branches |

Bug reports and sample `.uasset` files are also welcome as issues.

## License

Apache-2.0
