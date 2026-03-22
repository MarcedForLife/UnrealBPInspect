<#
.SYNOPSIS
    Install bp-inspect (Unreal Blueprint Inspector)
.DESCRIPTION
    Downloads the latest bp-inspect binary from GitHub releases and installs it.
    Automatically configures Git textconv for .uasset diff support.
.PARAMETER Version
    Specific version to install (e.g. "v0.1.0"). Defaults to latest.
.PARAMETER InstallDir
    Directory to install into. Defaults to $env:LOCALAPPDATA\bp-inspect
.PARAMETER WithSkill
    Also install the Claude Code skill for Blueprint debugging.
.EXAMPLE
    irm https://raw.githubusercontent.com/MarcedForLife/UnrealBPInspect/main/install.ps1 | iex
.EXAMPLE
    .\install.ps1 -WithSkill
.EXAMPLE
    .\install.ps1 -Version v0.1.0 -InstallDir C:\Tools
#>
param(
    [string]$Version = "latest",
    [string]$InstallDir = "$env:LOCALAPPDATA\bp-inspect",
    [switch]$WithSkill
)

$ErrorActionPreference = "Stop"
$Repo = "MarcedForLife/UnrealBPInspect"
$BinaryName = "bp-inspect.exe"
$Asset = "bp-inspect-windows-x86_64.exe"

# Resolve download URL
if ($Version -eq "latest") {
    $Url = "https://github.com/$Repo/releases/latest/download/$Asset"
} else {
    $Url = "https://github.com/$Repo/releases/download/$Version/$Asset"
}

Write-Host "Installing bp-inspect..." -ForegroundColor Cyan

# Create install directory
if (-not (Test-Path $InstallDir)) {
    New-Item -ItemType Directory -Path $InstallDir -Force | Out-Null
}

$BinaryPath = Join-Path $InstallDir $BinaryName

# Download
Write-Host "  Downloading from GitHub releases..."
try {
    Invoke-WebRequest -Uri $Url -OutFile $BinaryPath -UseBasicParsing
} catch {
    Write-Host "Error: Failed to download bp-inspect." -ForegroundColor Red
    if ($Version -ne "latest") {
        Write-Host "  Check that version '$Version' exists at:" -ForegroundColor Yellow
    } else {
        Write-Host "  Check that a release exists at:" -ForegroundColor Yellow
    }
    Write-Host "  https://github.com/$Repo/releases" -ForegroundColor Yellow
    exit 1
}

# Add to user PATH if not already present
$UserPath = [Environment]::GetEnvironmentVariable("Path", "User")
if ($UserPath -notlike "*$InstallDir*") {
    [Environment]::SetEnvironmentVariable("Path", "$UserPath;$InstallDir", "User")
    $env:Path = "$env:Path;$InstallDir"
    Write-Host "  Added $InstallDir to user PATH." -ForegroundColor Green
}

# Configure Git textconv
$GitAvailable = Get-Command git -ErrorAction SilentlyContinue
if ($GitAvailable) {
    # Use forward slashes for git config (works on all platforms)
    $GitBinaryPath = $BinaryPath -replace '\\', '/'
    git config --global diff.bp-inspect.textconv $GitBinaryPath
    git config --global diff.bp-inspect.cachetextconv true
    Write-Host "  Configured Git textconv for .uasset diffs." -ForegroundColor Green
} else {
    Write-Host "  Git not found -- skipping textconv setup." -ForegroundColor Yellow
    Write-Host "  Run these after installing Git:" -ForegroundColor Yellow
    Write-Host "    git config --global diff.bp-inspect.textconv `"$($BinaryPath -replace '\\', '/')`""
    Write-Host "    git config --global diff.bp-inspect.cachetextconv true"
}

# Install Claude Code skill
if ($WithSkill) {
    $SkillDir = Join-Path $env:USERPROFILE ".claude\skills\unreal-bp"
    if (-not (Test-Path $SkillDir)) {
        New-Item -ItemType Directory -Path $SkillDir -Force | Out-Null
    }
    $SkillUrl = "https://raw.githubusercontent.com/$Repo/main/skill/SKILL.md"
    $SkillPath = Join-Path $SkillDir "SKILL.md"
    try {
        Invoke-WebRequest -Uri $SkillUrl -OutFile $SkillPath -UseBasicParsing
        Write-Host "  Installed Claude Code skill to $SkillDir" -ForegroundColor Green
    } catch {
        Write-Host "  Warning: Failed to download Claude Code skill." -ForegroundColor Yellow
    }
}

# Verify
try {
    $InstalledVersion = & $BinaryPath --version 2>&1
    Write-Host ""
    Write-Host "  $InstalledVersion" -ForegroundColor Green
    Write-Host "  Installed to: $BinaryPath" -ForegroundColor Green
} catch {
    Write-Host ""
    Write-Host "  Installed to: $BinaryPath" -ForegroundColor Green
}

# Remind about .gitattributes
Write-Host ""
Write-Host "To enable Git diff support, add this to your UE project's .gitattributes:" -ForegroundColor Cyan
Write-Host "  *.uasset diff=bp-inspect"
Write-Host ""
