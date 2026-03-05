# Claude Code Skill: Unreal Blueprint Debugging

This skill teaches Claude Code how to use `bp-inspect` to read, debug, and explain Unreal Engine Blueprint files.

## Install

### Option 1: Copy to your skills directory

```bash
cp -r skill/ ~/.claude/skills/unreal-bp/
```

### Option 2: Add to a project

Copy `SKILL.md` into your UE project's `.claude/skills/unreal-bp/` directory for project-scoped use.

### Option 3: Use with npx skills (when published)

```bash
npx skills add <owner>/unreal-bp-inspect@skill
```

## Requirements

The `bp-inspect` binary must be installed and available on PATH. See the [main README](../README.md) for install options.
