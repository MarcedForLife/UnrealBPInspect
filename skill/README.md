# Unreal Blueprint inspection skill

The `unreal-bp` skill helps coding agents use `bp-inspect` to explain Blueprint logic, investigate bugs, compare revisions, and plan C++ migrations. It follows the [Agent Skills format](https://agentskills.io/specification) and requires an agent that can run local commands.

Install [bp-inspect](../README.md#install) first and make it available on PATH.

## Install the skill

Copy [SKILL.md](SKILL.md) into a folder named `unreal-bp` in your agent's skills directory. Only that file is needed.

| Agent | Personal installation | Project installation |
| --- | --- | --- |
| [Codex](https://learn.chatgpt.com/docs/build-skills#where-codex-loads-local-skills) | `~/.agents/skills/unreal-bp/SKILL.md` | `.agents/skills/unreal-bp/SKILL.md` |
| [Claude Code](https://code.claude.com/docs/en/skills#where-skills-live) | `~/.claude/skills/unreal-bp/SKILL.md` | `.claude/skills/unreal-bp/SKILL.md` |
| Other Agent Skills clients | Use the client's configured skills directory | Use the client's project skills directory |

For example, from this repository, install for Codex on macOS or Linux

```sh
mkdir -p "$HOME/.agents/skills/unreal-bp"
cp skill/SKILL.md "$HOME/.agents/skills/unreal-bp/SKILL.md"
```

Or in PowerShell

```powershell
New-Item -ItemType Directory -Force "$HOME/.agents/skills/unreal-bp" | Out-Null
Copy-Item skill/SKILL.md "$HOME/.agents/skills/unreal-bp/SKILL.md"
```

For a project installation, create the matching directory inside your Unreal project and copy the same file there.

The binary installers can also install the skill. `--skill-dir` or `-SkillDir` selects the final directory containing `SKILL.md` and enables skill installation.

```sh
sh install.sh --skill-dir "$HOME/.agents/skills/unreal-bp"
```

```powershell
.\install.ps1 -SkillDir "$HOME/.agents/skills/unreal-bp"
```

Without a custom directory, `--with-skill` and `-WithSkill` retain the Claude Code personal location. The installer downloads the skill from the same release tag as the binary. Older releases may contain the earlier Claude-specific skill instructions.

## Use it

Ask your agent to use `unreal-bp` with an asset path, for example

- Explain what `Content/Blueprints/Enemy_BP.uasset` does.
- Trace how `ApplyDamage` changes health and calls other functions.
- Compare these two Blueprint revisions and explain the behavioural changes.
- Use this Blueprint to plan a C++ implementation, noting anything the decoder cannot establish.
