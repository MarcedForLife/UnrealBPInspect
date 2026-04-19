# Unreal Blueprint Inspect

A standalone CLI that makes Unreal Engine Blueprint `.uasset` files readable outside the editor: in terminals, AI assistants, code review, CI pipelines, and documentation.

Parses the binary format directly and outputs component trees, variable declarations, function signatures, decoded bytecode pseudo-code, and graph node summaries. No editor, no project context, no dependencies.

> [!NOTE]
> This project is in early development. Core parsing works well, but expect rough edges and breaking changes.
>
> This started as a personal prototype to see if Blueprint bytecode could be made readable outside the editor. AI-assisted development made it practical to explore as a solo side project.

## Install

### Windows (PowerShell)

```powershell
irm https://raw.githubusercontent.com/MarcedForLife/UnrealBPInspect/main/install.ps1 | iex
```

### macOS / Linux

```sh
curl -fsSL https://raw.githubusercontent.com/MarcedForLife/UnrealBPInspect/main/install.sh | sh
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
git clone https://github.com/MarcedForLife/UnrealBPInspect.git
cd UnrealBPInspect
cargo install --path .
```

## Usage

```sh
bp-inspect [OPTIONS] <PATH>...
```

Accepts one or more `.uasset` files or directories. Directories are scanned recursively.

| Flag                       | Description                                             |
| -------------------------- | ------------------------------------------------------- |
| `-f` / `--filter <term>`   | Filter output by substring (comma-separated, see below) |
| `-j` / `--json`            | Full structured output as JSON                          |
| `-d` / `--diff`            | Compare two `.uasset` files (unified diff of summaries) |
| `--context <N>`            | Context lines in diff output (default: 3)               |
| `--update [version]`       | Update to the latest (or specified) release             |
| `--dump`                   | Full import/export/property dump (verbose diagnostic)   |
| `--debug`                  | Dump raw table data for format investigation            |
| `-V` / `--version`         | Print version                                           |

### Default output

Shows the Blueprint as a single readable document with components, variables, call graph, and decoded functions with inline comments:

```sh
$ bp-inspect Helm_BP.uasset
```

```
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
```

Larger Blueprints include call graphs and decoded functions:

```
Call graph:
  InitialiseHandPhysics → EnableHandPhysics
  OnComponentGripped → DisableHandPhysics, ResolveFingerPoses
  OnGripReleased → EnableHandPhysics
  ReceiveBeginPlay → InitialiseHandPhysics, ScaleHandToPlayer
  ReceiveTick → TeleportHandToController
  ResolveFingerPoses → ResolveFingerPose
  ...
```

Functions are decompiled into structured pseudocode with Blueprint comments placed inline:

```
  ReceiveBeginPlay():
    // "Resize the hand based on the players height (breaks physical animation)"
    ScaleHandToPlayer(self.PlayerHeight)
    // "Do first time setup and enable physics for the hand"
    InitialiseHandPhysics()
    // "Bind on player teleported events"
    $Cast_AsVRPlayer_BP = cast<VRPlayer_BP_C>(self.MotionController.GetOwner())
    if ($Cast_AsVRPlayer_BP) {
        $Cast_AsVRPlayer_BP.OnCharacterTeleported_Bind += self.OnOwnerTeleported
        // "Bind player status updates to update the player state widget"
        if (IsValid(self.PlayerStateWidget)) {
            $Cast_AsVRPlayer_BP.PlayerStatusesUpdated += self.OnPlayerStatusesUpdated
        }
    }
```

Latent actions (Delay, MoveTo) show their resume continuation inline:

```
  // "On grip released"
  OnGripReleased():
    self.SkeletalMeshComponent.DetachFromComponent(KeepWorld, KeepWorld, KeepWorld, true)
    EnableHandPhysics()
    self.GrippingActor = false
    // "Since we simulate gravity on gripped components, wait a little bit
    //  before restoring the hands mass. This stops the gripped component
    //  from being launched when held from the bottom"
    Delay(0.5000)
    self.SkeletalMeshComponent.SetMassOverrideInKg(self.RootBoneName, self.OriginalHandMass, true)
```

### Filtering

`--filter` searches across all sections of the output, case-insensitive. It shows matching components, variables, functions (by name or body content), and the related call graph entries.

Filter by a function or event name:

```sh
bp-inspect MyBlueprint.uasset --filter ReceiveTick
```

```
Blueprint: VRHand_BP (extends SkeletalMeshActor)

Call graph:
  ReceiveTick → TeleportHandToController

Functions:
  ReceiveTick():
    ...
    if ((!self.GrippingActor) && ($VSize >= self.MaxHandDistance)) {
        TeleportHandToController()
    }

  TeleportHandToController() [Public|BlueprintPure]
    ...
```

Filter by a variable name to see its definition and every function that references it:

```sh
bp-inspect MyBlueprint.uasset --filter GrippingActor
```

```
Blueprint: VRHand_BP (extends SkeletalMeshActor)

Variables:
  GrippingActor: bool

Call graph:
  OnComponentGripped → DisableHandPhysics, ResolveFingerPoses
  OnGripReleased → EnableHandPhysics
  ...

Functions:
  OnGripReleased():
    ...
    self.GrippingActor = false
    ...

  OnComponentGripped(GrippedActor: GrippedComponent_Struct) [Public|BlueprintPure]
    ...
    self.GrippingActor = true
    ...
```

Multiple terms can be comma-separated: `--filter health,mana`.

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

```diff
 Variables:
-  MaxHandDistance: float = 50.0000
+  MaxHandDistance: float = 75.0000
 ...
@@ -290,8 +290,8 @@
   UserConstructionScript() [Event|Public|BlueprintPure]
     // "Set the appropriate mesh"
-    self.SkeletalMeshComponent.SetSkeletalMesh(switch(self.Hand) { ... }, true)
+    self.SkeletalMeshComponent.SetSkinnedAssetAndUpdate(switch(self.Hand) { ... }, true)
     // "Set the appropriate animation blueprint"
-    self.SkeletalMeshComponent.SetAnimClass(switch(self.Hand) { ... })
+    self.SkeletalMeshComponent.SetAnimInstanceClass(switch(self.Hand) { ... })
```

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

bp-inspect reads the compiled bytecode from the binary file directly, with zero UE dependency. A large Blueprint with 90 functions parses in under 100ms.

The hard part is making bytecode *readable*. bp-inspect:

- Reconstructs function signatures from parameter properties
- Disassembles Kismet bytecode into structured pseudo-code with if/else, while/for, ForEach, and sequence nodes
- Reorders displaced convergence blocks from the UE4 compiler
- Inlines single-use temporaries and folds struct Break/Make patterns
- Strips serialisation noise (GUID suffixes, K2Node prefixes, library prefixes)
- Splits ubergraph functions into labelled event handlers
- Inlines latent resume blocks after their corresponding Delay() calls
- Places Blueprint comment boxes and bubble comments inline near the code they annotate (via 2D spatial matching between graph nodes and bytecode)
- Detects DoOnce and FlipFlop macro patterns and emits them as structured pseudocode

The goal is output that reads like hand-written pseudocode, not a bytecode dump.

> [!NOTE]
> DoOnce and FlipFlop macro instances carry no user-set label in the compiled asset, so their names in output are derived heuristically from the first meaningful call in the body (e.g. `DoOnce(AttemptGrip)`). These names are stable per gate but won't match the node titles you might remember from the editor.

**How it compares to existing tools:**

| Tool                                                         | Approach                                    | Limitations                                                                           |
| ------------------------------------------------------------ | ------------------------------------------- | ------------------------------------------------------------------------------------- |
| **UAssetAPI**                                                | .NET serialisation library for modding      | Raw property trees and byte arrays, no disassembly or readable output                 |
| **UE commandlets**                                           | Editor-based dump tools                     | Requires full editor instance with project loaded and all dependencies compiled       |
| **[NodeToCode](https://github.com/protospatial/NodeToCode)** | Editor plugin, translates graphs via LLM    | Requires running editor and LLM service (cloud or local); reads live graph, not files |
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
cargo build             # dev build
cargo build --release   # optimised build → target/release/bp-inspect
```

### Running locally

```sh
cargo run -- samples/<file>.uasset                        # summary (default)
cargo run -- samples/<file>.uasset --filter ReceiveTick   # filter by event
cargo run -- --diff samples/A.uasset samples/B.uasset     # compare two files
cargo run -- samples/                                     # all files in directory
```

### Testing

```sh
cargo test                      # run all tests
cargo test -- --nocapture       # run with stdout visible
cargo test inline               # run tests matching "inline"
UPDATE_SNAPSHOTS=1 cargo test   # update snapshot files after intentional output changes
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
