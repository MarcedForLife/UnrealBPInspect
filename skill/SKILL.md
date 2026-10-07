---
name: unreal-bp
description: Inspect, compare, and debug Unreal Engine Blueprint .uasset files with bp-inspect. Use for questions about Blueprint logic, components, defaults, or Blueprint-to-C++ migration based on local assets.
---

# Unreal Blueprint inspection

Use `bp-inspect` to inspect saved Blueprint assets without opening Unreal Editor. It reads files and emits pseudocode, properties, or JSON. It does not edit Blueprints or inspect a running game.

## Start with the asset

Check `bp-inspect --version`. If the binary is missing, use the project's [installation instructions](https://github.com/MarcedForLife/UnrealBPInspect#install) within the user's installation preferences. Inspection does not require a network connection. Do not update the binary as part of routine inspection.

Use the supplied asset path. If the file is unknown, search the relevant Content folder with the agent's file search or `rg --files Content -g '*.uasset'`. Not every `.uasset` is a Blueprint. Narrow the selection before decoding a whole project.

```sh
bp-inspect "Content/Blueprints/Enemy_BP.uasset"
bp-inspect "Content/Blueprints/Enemy_BP.uasset" --filter ApplyDamage
bp-inspect "Content/Blueprints/Enemy_BP.uasset" --filter health,armor
```

Start with the summary, or a filter when the user names a function or variable. Summary filtering uses case-insensitive substrings across names and bodies, with comma-separated alternatives. It can include callers and omit non-matching variables or components. Return to the unfiltered summary when those defaults or relationships matter.

## Read the result

- Components show attachment hierarchy and saved properties, including child actor templates where available.
- Variables show declared types and available defaults from the class default object. These are not runtime values. A missing default does not establish that the value is zero or unset.
- The call graph helps trace calls within the decoded Blueprint. Inspect referenced assets separately when behaviour depends on another Blueprint.
- Functions and events contain reconstructed pseudocode. It can include branches, switch cases, ForEach, counted and while loops, breaks, Sequence pins, DoOnce, FlipFlop, and latent continuations.
- `self.Name` refers to instance state. `$Name` is usually a compiler-generated temporary. `// "..."` carries an editor comment. DoOnce and FlipFlop labels are inferred and need not match editor titles.

Treat pseudocode as an interpretation of compiled data. `UNKNOWN` diagnostics, unresolved expressions, or an unexpectedly empty body are reasons to qualify the explanation and inspect further. Do not invent missing logic or assume a displayed construct is a literal C++ implementation.

## Inspect properties and JSON

```sh
bp-inspect "Content/Blueprints/Enemy_BP.uasset" --json
bp-inspect "Content/Blueprints/Enemy_BP.uasset" --dump
```

Use JSON for property queries and `--dump` for diagnostic import, export, and property details. JSON contains `imports`, `exports`, and `functions`. Each function has `name`, `signature`, `flags`, and `bytecode`, an array of rendered lines rather than an abstract syntax tree. Editor comments are summary-only. In JSON and dump modes, filters match export names, not the summary's body-text matches.

One resolved input file produces a JSON object. Multiple files produce an array with a `file` field on each successful result. Directory inputs are recursive. Batch parsing keeps successful results but returns exit code 2 if any file fails. Inspect stderr for the failed paths before claiming the whole batch parsed. Older releases can return 0 on partial failure, so check stderr with those versions too.

## Compare revisions

```sh
bp-inspect --diff "Old_Enemy_BP.uasset" "New_Enemy_BP.uasset"
bp-inspect --diff "Old_Enemy_BP.uasset" "New_Enemy_BP.uasset" --filter ApplyDamage --context 5
```

Pass the older file first. Exit code 0 means the summaries match. Exit code 1 means differences and 2 means an error. Errors are written to stderr. Older releases also use 1 for errors, so check stderr when using those versions. A decoded diff can omit binary changes that do not affect the summary.

For Git revisions, use an existing textconv setup or extract each revision to a separate temporary file. Preserve the binary bytes when extracting and leave the working asset intact.

## Explain or migrate

Ground findings in the asset path, function or event, and relevant output. Separate observed control flow from suspected bugs. For behaviour that depends on runtime state, inherited defaults, missing assets, or unsupported decoding, state what still needs checking in Unreal Editor.

For C++ migration, use the output to identify components, properties, functions, and event flow. Verify engine API signatures, ownership, reflection flags, replication, and latent behaviour against the project before translating. Pseudocode and displayed flags are not a compilable implementation.

## Format limits

Uncooked UE4 and UE5 assets have partial support, with committed fixtures for 4.27, 5.3, and 5.5. Other versions are unverified. Animation and Widget Blueprint functions and events may decode, but animation state machines and widget hierarchies are not displayed. Cooked `.uasset`/`.uexp` pairs and IoStore are unsupported.
