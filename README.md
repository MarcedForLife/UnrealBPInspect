<picture>
  <source media="(prefers-color-scheme: dark)" srcset="brand/lockup-dark.svg">
  <img src="brand/lockup-light.svg" alt="bp-inspect" width="260">
</picture>

`bp-inspect` reads Unreal Engine Blueprint `.uasset` files and outputs readable pseudocode, component trees, variables, and function signatures. It runs without Unreal Editor or the original project, and supports JSON output and Git diffs.

Support is incomplete. Expect rough edges in decoded output and verify it against the editor when needed.

## Install

Download a binary from [Releases](https://github.com/MarcedForLife/UnrealBPInspect/releases), or use an install script.

Windows PowerShell

```powershell
irm https://raw.githubusercontent.com/MarcedForLife/UnrealBPInspect/main/install.ps1 | iex
```

macOS and Linux

```sh
curl -fsSL https://raw.githubusercontent.com/MarcedForLife/UnrealBPInspect/main/install.sh | sh
```

Binaries are available for Windows x86_64, Linux x86_64, and macOS Intel and Apple Silicon. The scripts verify the release SHA-256 checksum before replacing an existing installation and configure Git text conversion. Windows also adds the install directory to your user PATH. On macOS and Linux, add `~/.local/bin` to PATH if needed.

To customise a downloaded installer, use `BP_INSPECT_VERSION` and `INSTALL_DIR` with `install.sh`, or `-Version` and `-InstallDir` with `install.ps1`.

```sh
BP_INSPECT_VERSION=v1.0.0 INSTALL_DIR="$HOME/.local/bin" sh install.sh
```

To build from source, install [Rust](https://www.rust-lang.org/tools/install), then run

```sh
git clone https://github.com/MarcedForLife/UnrealBPInspect.git
cd UnrealBPInspect
cargo install --locked --path .
```

## Usage

```sh
bp-inspect MyBlueprint.uasset
bp-inspect Content/Blueprints/
bp-inspect MyBlueprint.uasset --filter health,mana
bp-inspect MyBlueprint.uasset --json
bp-inspect --diff Old_BP.uasset New_BP.uasset
```

Directories are scanned recursively. Filtering is case-insensitive and matches component, variable, and function names as well as function bodies. Multiple files produce a JSON array, while a single file produces an object. Failures are reported on stderr and in a JSON `diagnostics` list. Partial results are kept, but the exit code is 2 if any file fails or reports diagnostics.

Use `--dump` for the full import, export, and property output, `--debug` for raw table diagnostics, and `--help` for all options. `bp-inspect --update` installs the latest release, or use `--update v1.0.0` for a specific version.

### Reading a Blueprint

```sh
bp-inspect Enemy_BP.uasset
```

Illustrative output, shortened to show the components, variables, call graph, and damage logic

```text
Blueprint: Enemy_BP (extends Character)

Components:
  CapsuleComponent (CapsuleComponent)
    Mesh (SkeletalMeshComponent)

Variables:
  Health: float = 100.0000

Call graph:
  ApplyDamage → Die

Functions:
  ApplyDamage(Amount: float) [Public]
    // "Reduce health and check for death"
    self.Health = (self.Health - Amount)
    if (self.Health <= 0.0000) {
        Die()
    }
```

### Control flow

```sh
bp-inspect Enemy_BP.uasset --filter UpdateNearbyEnemies
```

Illustrative function with a ForEach loop, nested branch, and switch cases

```text
  UpdateNearbyEnemies() [Public]
    // "Choose a behaviour for each nearby enemy"
    for (Enemy in self.NearbyEnemies) {
        if (IsValid(Enemy)) {
            switch (Enemy.AlertLevel) {
                case 0:
                    Enemy.Patrol()
                case 1:
                    Enemy.Investigate(self.LastKnownPosition)
                default:
                    Enemy.Attack(self.Target)
            }
        }
    }
```

The decoder also recognises counted and while loops, loop breaks, Sequence pins, DoOnce and FlipFlop patterns, and continuations after latent actions such as Delay, including engine and project latent functions. Recovery depends on the compiled bytecode pattern. A continuation that resumes in code already shown in an event, such as a Delay looping back to an earlier node, is marked `UNKNOWN` with the event's name. A continuation that can't be located is marked the same way and reported as an incomplete result. Temporary variables are kept where removing them could change evaluation order.

### Comparing Blueprints

`--diff` compares summaries in the supplied order. Exit code 0 means identical, 1 means differences, and 2 means an error or incomplete parse/decode result. Errors are written to stderr. Use `--context <N>` to change the number of context lines, or `--filter` to narrow the comparison.

```sh
bp-inspect --diff Old_Enemy_BP.uasset New_Enemy_BP.uasset
```

Illustrative diff adding armour to the damage calculation

```diff
--- Old_Enemy_BP.uasset
+++ New_Enemy_BP.uasset
@@ -7,4 +7,5 @@
 Variables:
   Health: float = 100.0000
+  Armor: float = 10.0000

 Call graph:
@@ -14,5 +15,5 @@
   ApplyDamage(Amount: float) [Public]
     // "Reduce health and check for death"
-    self.Health = (self.Health - Amount)
+    self.Health = (self.Health - FMax((Amount - self.Armor), 0.0000))
     if (self.Health <= 0.0000) {
         Die()
```

## Git integration

Add this to your Unreal project's `.gitattributes`

```gitattributes
*.uasset diff=bp-inspect
```

The install scripts configure the text converter. For a manual or source installation, run

```sh
git config --global diff.bp-inspect.textconv bp-inspect
git config --global diff.bp-inspect.cachetextconv true
```

With `bp-inspect` on PATH, `git diff`, `git show`, and `git log -p` display readable Blueprint summaries. This only changes diff display, not the stored assets or binary merge behaviour.

SmartGit shows the summaries in its diff view. Rider and other JetBrains IDEs show them after enabling `git.read.content.with.textconv` under Help > Find Action > Registry. VS Code shows them for committed and staged changes but not unstaged ones. GitKraken, Sublime Merge, and GitHub's web diffs don't support text conversion.

An optional [agent skill](skill/README.md) helps coding agents inspect, compare, and debug Blueprints with the CLI. It uses the Agent Skills format and works with agents that can run local commands.

## Supported formats

- Uncooked UE4 `.uasset` files from 4.14 to 4.27 and UE5 files from 5.0 to 5.5. Committed test fixtures cover 4.27, 5.3, and 5.5. Other versions are unverified.
- Animation and Widget Blueprints have partial support for event graphs and functions. Animation state machines and widget hierarchies are not displayed.
- Cooked assets split across `.uasset` and `.uexp`, and UE5 IoStore files, are not supported.

Numbers keep their stored precision, and summaries include array, map and struct contents, so diffs show small value changes and changes within collections. Unsupported property payloads are marked as unknown with a `payload_sha256`, so equal-size changes still show in diffs. DoOnce and FlipFlop names are inferred and may differ from editor node titles.

Blueprint comments appear above the statements they annotate. Comments that can't be placed reliably are listed in a separate graph-comments section.

## Development

```sh
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-features
cargo build --locked --release
python tests/installers.py
cargo run --locked -- samples/ue_4.27/Helm_BP.uasset
```

Rust integrations call `decode_asset(&parsed)` after `parse_asset`. Both parsed and decoded assets expose diagnostics.

Tests use the committed assets in `samples/` and don't need private assets. See [test snapshots](tests/snapshots/README.md) for updating expected output after intentional changes.

Open a pull request for changes, or an issue for bugs and sample assets that fail to parse.

To publish a release, run the Release workflow on `main` with a patch, minor, or major version bump. If `main` changes during the build, the workflow stops before pushing and must be rerun. Pull `main` afterwards to pick up the version commit.

## License

[Apache-2.0](LICENSE)
