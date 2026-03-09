# Claude Code Skill: Unreal Blueprint Debugging

This skill teaches Claude Code how to use `bp-inspect` to read, debug, and explain Unreal Engine Blueprint files.

## Install

Install alongside bp-inspect using the `--with-skill` flag:

```bash
# macOS / Linux
curl -fsSL https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.sh | sh -s -- --with-skill

# Windows PowerShell
.\install.ps1 -WithSkill
```

Or copy manually:

```bash
# Global (available in all projects)
cp -r skill/ ~/.claude/skills/unreal-bp/

# Project-scoped
cp skill/SKILL.md your-ue-project/.claude/skills/unreal-bp/SKILL.md
```

## Requirements

The `bp-inspect` binary must be installed and available on PATH. See the [main README](../README.md) for install options.
