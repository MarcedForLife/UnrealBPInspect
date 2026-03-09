# Unreal Blueprint Debugging Skill

Use `bp-inspect` to read and understand Unreal Engine Blueprint `.uasset` files from the command line.

## When to use this

- User asks about Blueprint logic, behaviour, or bugs
- User wants to understand what a Blueprint does without opening the editor
- User needs to migrate Blueprint logic to C++
- User is debugging physics, collision, component setup, or variable state in a Blueprint
- User references a `.uasset` file in their project

## Prerequisites

`bp-inspect` must be installed and available on PATH. If it's not installed, run:

```bash
# macOS / Linux
curl -fsSL https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.sh | sh

# Windows PowerShell
irm https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.ps1 | iex
```

To update to the latest version:

```bash
bp-inspect --update
```

## Commands

### Get a full overview

```bash
bp-inspect <path>.uasset
```

Returns: class hierarchy, component tree with properties (meshes, physics, transforms), variable declarations with types, function signatures with structured bytecode pseudo-code (if/else blocks, indented), and graph node summaries for graphs not already shown as functions.

Start here. This gives you everything you need for most questions.

### Drill into a specific function

```bash
bp-inspect <path>.uasset --filter <FunctionName>
```

Filters functions and graphs to the named export while keeping class context (components, variables). Use when the full summary is too noisy or you need to focus on one function.

Multiple names can be comma-separated: `--filter GetSteeringAngle,UserConstructionScript`

### Scan a directory

```bash
bp-inspect <directory>/
```

Recursively finds and processes all `.uasset` files. Each file gets a header. Multiple files and directories can be mixed. Works with all output modes.

### Get structured data

```bash
bp-inspect <path>.uasset --json
```

Full structured data as JSON with top-level `imports`, `exports`, and `functions` arrays. Functions have pre-extracted signatures, flags, and structured bytecode. Use when you need to programmatically inspect properties, or when the default view doesn't show a specific detail you need.

### Compare two Blueprints

```bash
bp-inspect --diff <before>.uasset <after>.uasset
```

Outputs a unified diff of the decoded summaries. Exit code 0 means identical, 1 means differences found. Use `--filter` to compare specific functions, and `--context N` to control surrounding lines.

### Find Blueprint files

```bash
find <ProjectRoot>/Content -name "*.uasset" | head -20
```

UE4 Blueprint `.uasset` files live under the `Content/` directory. Not all `.uasset` files are Blueprints -- some are meshes, textures, etc. `bp-inspect` will parse what it can and skip non-Blueprint data.

## Reading the output

### Components section

Indentation shows the scene graph hierarchy (parent-child attachment). Each component shows:
- Type in parentheses: `Stand (StaticMeshComponent)`
- Sub-object properties: meshes, transforms, physics config, collision profiles
- Child actor templates: configured defaults for spawned child actors

### Variables section

Class member variables with resolved types. Components are filtered out (shown in Components section). Default values from the CDO are shown inline when present: `MyVar: float = 0.5`

### Functions section

Each function shows:
- Signature: `FunctionName(params) [Flags]`
- Decoded bytecode as pseudo-code, indented below

Pseudo-code conventions:
- `self.VarName` -- instance variable access
- `$Name` -- compiler-generated temporary (shortened from verbose Blueprint names)
- `cast<Type>(expr)` -- dynamic cast
- `ClassName::FunctionName(args)` -- static/library function call
- `obj.FunctionName(args)` -- context call on an object
- `if (cond) { ... }` / `if (cond) { ... } else { ... }` -- structured control flow (conditions are inverted from the raw `JumpIfNot` for readability)
- `while (cond) { body; increment; }` -- for/ForEach loops (reordered from scattered bytecode into logical order)
- `// sequence [N]:` -- sequence node pins in execution order
- `// "Comment text"` -- Blueprint comment boxes and node bubble comments, placed inline near the code they describe

### Graph section

EdGraph node list showing the visual Blueprint graph structure. Graphs that already appear as functions with bytecode are suppressed to avoid redundancy. The EventGraph (which has no matching function) still shows. Less detailed than bytecode but shows node types (pure calls, events, variable gets/sets, casts).

## Common workflows

### Understanding what a Blueprint does

1. Run `bp-inspect` to get the full picture
2. Read the Components section for the physical structure
3. Read the Variables section for state
4. Read the Functions section for logic -- the pseudo-code reads like simplified code

### Debugging a specific function

1. Run with `--filter FunctionName`
2. Read the pseudo-code line by line
3. Cross-reference variable types from the Variables/Components sections
4. Check component properties for physics/collision configuration if relevant

### Blueprint to C++ migration

1. Run `bp-inspect` to understand the full Blueprint
2. Components section maps to `CreateDefaultSubobject<T>()` calls in the constructor
3. Component properties map to constructor defaults (`SetRelativeLocation`, `SetCollisionProfileName`, etc.)
4. Variables section maps to `UPROPERTY()` declarations
5. Function pseudo-code maps to the C++ implementation -- the operations translate directly
6. Function flags indicate `UFUNCTION()` specifiers: `BlueprintPure` -> `BlueprintPure`, `BlueprintCallable` -> `BlueprintCallable`, `Const` -> `const`

### Comparing two Blueprints

```bash
bp-inspect --diff A.uasset B.uasset
```

Use `--filter FunctionName` to focus the diff on a specific function. Exit code 0 means no changes, 1 means differences found.

## Limitations

- UE4 uncooked `.uasset` files fully supported; UE5 uncooked assets have basic support
- Cooked assets (split `.uasset`/`.uexp`) are not yet supported
- Some complex bytecode expressions may show as `??(0xNN)` -- the common opcodes are covered
- Default property values only show non-null values from the CDO
