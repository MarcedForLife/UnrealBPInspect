#!/bin/sh
# Install bp-inspect from a checksummed GitHub release.
# INSTALL_DIR defaults to ~/.local/bin. BP_INSPECT_VERSION defaults to latest.
set -eu

REPO="MarcedForLife/UnrealBPInspect"
BINARY="bp-inspect"
INSTALL_DIR="${INSTALL_DIR:-$HOME/.local/bin}"
VERSION="${BP_INSPECT_VERSION:-latest}"
WITH_SKILL=false
SKILL_DIR="$HOME/.claude/skills/unreal-bp"

while [ "$#" -gt 0 ]; do
    case "$1" in
        --with-skill) WITH_SKILL=true ;;
        --skill-dir)
            if [ "$#" -lt 2 ] || [ -z "$2" ]; then
                echo "Error: --skill-dir requires a directory." >&2
                exit 1
            fi
            SKILL_DIR="$2"
            WITH_SKILL=true
            shift
            ;;
        --help|-h)
            echo "Usage: install.sh [--with-skill] [--skill-dir DIRECTORY]"
            echo "  --with-skill  Install to ~/.claude/skills/unreal-bp (legacy default)"
            echo "  --skill-dir   Install the skill to a chosen directory"
            echo "Environment: INSTALL_DIR, BP_INSPECT_VERSION (default: latest)"
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
    shift
done

case "$(uname -s)" in
    Linux) PLATFORM="linux" ;;
    Darwin) PLATFORM="macos" ;;
    *) echo "Error: Unsupported OS." >&2; exit 1 ;;
esac
case "$(uname -m)" in
    x86_64|amd64) ARCH="x86_64" ;;
    aarch64|arm64) ARCH="aarch64" ;;
    *) echo "Error: Unsupported architecture." >&2; exit 1 ;;
esac
if [ "$PLATFORM-$ARCH" = "linux-aarch64" ]; then
    echo "Linux ARM64 binaries are unavailable. Install from source:" >&2
    echo "cargo install --locked --git https://github.com/${REPO}.git" >&2
    exit 1
fi
ASSET="${BINARY}-${PLATFORM}-${ARCH}"

# Every failed transfer is fatal, even if a partial file was written.
download() {
    if command -v curl >/dev/null 2>&1; then
        curl -fsSL --retry 3 -o "$2" "$1"
    elif command -v wget >/dev/null 2>&1; then
        wget -q -O "$2" "$1"
    else
        echo "Error: curl or wget required." >&2
        return 1
    fi
}

mkdir -p "$INSTALL_DIR"
INSTALL_DIR=$(cd "$INSTALL_DIR" && pwd)
TARGET="$INSTALL_DIR/$BINARY"
TEMP_DIR=$(mktemp -d "$INSTALL_DIR/.bp-inspect.XXXXXX")
SKILL_TEMP=""
trap 'rm -rf "$TEMP_DIR"; if [ -n "$SKILL_TEMP" ]; then rm -f "$SKILL_TEMP"; fi' 0
trap 'exit 1' HUP INT TERM

# Resolve latest once so the binary, checksums, and skill use the same tag.
if [ "$VERSION" = "latest" ]; then
    download "https://api.github.com/repos/${REPO}/releases/latest" "$TEMP_DIR/release.json"
    VERSION=$(sed -n 's/.*"tag_name"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$TEMP_DIR/release.json" | head -n 1)
fi
case "$VERSION" in v*) ;; *) VERSION="v$VERSION" ;; esac
if ! printf '%s\n' "$VERSION" | grep -Eq '^v[0-9]+\.[0-9]+\.[0-9]+([.-][0-9A-Za-z.-]+)?$'; then
    echo "Error: Invalid release version: $VERSION" >&2
    exit 1
fi
URL="https://github.com/${REPO}/releases/download/${VERSION}"
echo "Installing bp-inspect $VERSION..."
download "$URL/$ASSET" "$TEMP_DIR/$ASSET"
download "$URL/checksums.txt" "$TEMP_DIR/checksums.txt"
EXPECTED=$(awk -v asset="$ASSET" '$2 == asset || $2 == "*" asset { print $1 }' "$TEMP_DIR/checksums.txt")
if command -v sha256sum >/dev/null 2>&1; then
    ACTUAL=$(sha256sum "$TEMP_DIR/$ASSET" | awk '{print $1}')
elif command -v shasum >/dev/null 2>&1; then
    ACTUAL=$(shasum -a 256 "$TEMP_DIR/$ASSET" | awk '{print $1}')
else
    echo "Error: sha256sum or shasum required." >&2
    exit 1
fi
if [ "$EXPECTED" != "$ACTUAL" ]; then
    echo "Error: Missing, duplicate, or mismatched SHA-256 checksum for $ASSET." >&2
    exit 1
fi
chmod +x "$TEMP_DIR/$ASSET"
INSTALLED_VERSION=$("$TEMP_DIR/$ASSET" --version)

if [ "$WITH_SKILL" = true ]; then
    mkdir -p "$SKILL_DIR"
    SKILL_TEMP=$(mktemp "$SKILL_DIR/.SKILL.XXXXXX")
    download "https://raw.githubusercontent.com/${REPO}/${VERSION}/skill/SKILL.md" "$SKILL_TEMP"
    if [ ! -s "$SKILL_TEMP" ]; then
        echo "Error: Downloaded skill is empty." >&2
        exit 1
    fi
    chmod 644 "$SKILL_TEMP"
fi

mv -f "$TEMP_DIR/$ASSET" "$TARGET"
if [ "$WITH_SKILL" = true ]; then
    mv -f "$SKILL_TEMP" "$SKILL_DIR/SKILL.md"
    echo "  Installed skill to $SKILL_DIR"
fi

if command -v git >/dev/null 2>&1; then
    # textconv is a shell command, so retain quoting inside the config value.
    QUOTED_TARGET=$(printf '%s' "$TARGET" | sed "s/'/'\\\\''/g")
    git config --global diff.bp-inspect.textconv "'$QUOTED_TARGET'"
    git config --global diff.bp-inspect.cachetextconv true
fi

echo "  $INSTALLED_VERSION"
echo "  Installed to: $TARGET"
case ":${PATH}:" in
    *":${INSTALL_DIR}:"*) ;;
    *) echo "  Add $INSTALL_DIR to your PATH." ;;
esac
echo "To enable Git diffs, add this to your Unreal project's .gitattributes:"
echo "  *.uasset diff=bp-inspect"
