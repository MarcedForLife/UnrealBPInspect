#!/bin/sh
# Install bp-inspect (Unreal Blueprint Inspector)
#
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/MarcedForLife/unreal-bp-inspect/main/install.sh | sh
#   curl -fsSL .../install.sh | sh -s -- --with-skill
#
# Environment variables:
#   INSTALL_DIR         Override install directory (default: ~/.local/bin)
#   BP_INSPECT_VERSION  Pin to a specific version (default: latest)

set -eu

REPO="MarcedForLife/unreal-bp-inspect"
BINARY="bp-inspect"
INSTALL_DIR="${INSTALL_DIR:-$HOME/.local/bin}"
VERSION="${BP_INSPECT_VERSION:-latest}"
WITH_SKILL=false

# Parse arguments
for arg in "$@"; do
    case "$arg" in
        --with-skill) WITH_SKILL=true ;;
        --help|-h)
            echo "Usage: install.sh [--with-skill]"
            echo ""
            echo "Environment variables:"
            echo "  INSTALL_DIR         Install directory (default: ~/.local/bin)"
            echo "  BP_INSPECT_VERSION  Version to install (default: latest)"
            exit 0
            ;;
        *) echo "Unknown option: $arg"; exit 1 ;;
    esac
done

# Detect platform
detect_platform() {
    OS="$(uname -s)"
    ARCH="$(uname -m)"

    case "$OS" in
        Linux)  PLATFORM="linux" ;;
        Darwin) PLATFORM="macos" ;;
        *)
            echo "Error: Unsupported OS: $OS"
            echo "Install via: cargo install unreal-bp-inspect"
            exit 1
            ;;
    esac

    case "$ARCH" in
        x86_64|amd64)   ARCH="x86_64" ;;
        aarch64|arm64)   ARCH="aarch64" ;;
        *)
            echo "Error: Unsupported architecture: $ARCH"
            echo "Install via: cargo install unreal-bp-inspect"
            exit 1
            ;;
    esac

    # Linux arm64 not in release matrix
    if [ "$PLATFORM" = "linux" ] && [ "$ARCH" = "aarch64" ]; then
        echo "Error: Linux ARM64 binaries are not available yet."
        echo "Install via: cargo install unreal-bp-inspect"
        exit 1
    fi

    ASSET="${BINARY}-${PLATFORM}-${ARCH}"
}

detect_platform

# Resolve download URL
if [ "$VERSION" = "latest" ]; then
    URL="https://github.com/${REPO}/releases/latest/download/${ASSET}"
else
    URL="https://github.com/${REPO}/releases/download/${VERSION}/${ASSET}"
fi

echo "Installing bp-inspect..."

# Create install directory
mkdir -p "$INSTALL_DIR"

TARGET="$INSTALL_DIR/$BINARY"

# Download (try curl, fall back to wget)
echo "  Downloading from GitHub releases..."
if command -v curl >/dev/null 2>&1; then
    HTTP_CODE=$(curl -fsSL -w "%{http_code}" -o "$TARGET" "$URL" 2>/dev/null) || true
    if [ ! -f "$TARGET" ] || [ "$(wc -c < "$TARGET" | tr -d ' ')" -lt 1000 ]; then
        rm -f "$TARGET"
        echo "Error: Failed to download bp-inspect."
        if [ "$VERSION" != "latest" ]; then
            echo "  Check that version '$VERSION' exists at:"
        else
            echo "  Check that a release exists at:"
        fi
        echo "  https://github.com/${REPO}/releases"
        exit 1
    fi
elif command -v wget >/dev/null 2>&1; then
    if ! wget -q -O "$TARGET" "$URL" 2>/dev/null; then
        rm -f "$TARGET"
        echo "Error: Failed to download bp-inspect."
        echo "  https://github.com/${REPO}/releases"
        exit 1
    fi
else
    echo "Error: curl or wget required."
    exit 1
fi

chmod +x "$TARGET"

# Configure Git textconv
if command -v git >/dev/null 2>&1; then
    git config --global diff.bp-inspect.textconv "$TARGET"
    git config --global diff.bp-inspect.cachetextconv true
    echo "  Configured Git textconv for .uasset diffs."
else
    echo "  Git not found -- skipping textconv setup."
    echo "  Run these after installing Git:"
    echo "    git config --global diff.bp-inspect.textconv \"$TARGET\""
    echo "    git config --global diff.bp-inspect.cachetextconv true"
fi

# Install Claude Code skill
if [ "$WITH_SKILL" = true ]; then
    SKILL_DIR="$HOME/.claude/skills/unreal-bp"
    mkdir -p "$SKILL_DIR"
    SKILL_URL="https://raw.githubusercontent.com/${REPO}/main/skill/SKILL.md"
    if command -v curl >/dev/null 2>&1; then
        curl -fsSL -o "$SKILL_DIR/SKILL.md" "$SKILL_URL" 2>/dev/null && \
            echo "  Installed Claude Code skill to $SKILL_DIR" || \
            echo "  Warning: Failed to download Claude Code skill."
    elif command -v wget >/dev/null 2>&1; then
        wget -q -O "$SKILL_DIR/SKILL.md" "$SKILL_URL" 2>/dev/null && \
            echo "  Installed Claude Code skill to $SKILL_DIR" || \
            echo "  Warning: Failed to download Claude Code skill."
    fi
fi

# Verify
INSTALLED_VERSION=$("$TARGET" --version 2>/dev/null || echo "bp-inspect (version unknown)")
echo ""
echo "  $INSTALLED_VERSION"
echo "  Installed to: $TARGET"

# Check PATH
case ":${PATH}:" in
    *":${INSTALL_DIR}:"*) ;;
    *)
        echo ""
        echo "  Warning: $INSTALL_DIR is not on your PATH."
        echo "  Add this to your shell profile (~/.bashrc, ~/.zshrc, etc.):"
        echo "    export PATH=\"$INSTALL_DIR:\$PATH\""
        ;;
esac

# Remind about .gitattributes
echo ""
echo "To enable Git diff support, add this to your UE project's .gitattributes:"
echo "  *.uasset diff=bp-inspect"
echo ""
