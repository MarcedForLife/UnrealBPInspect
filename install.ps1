<#
.SYNOPSIS
    Install bp-inspect from a checksummed GitHub release.
.PARAMETER Version
    Release version, such as v1.0.0. Defaults to latest.
.PARAMETER InstallDir
    Binary directory. Defaults to $env:LOCALAPPDATA\bp-inspect.
.PARAMETER WithSkill
    Also install the skill to the legacy Claude Code personal directory.
.PARAMETER SkillDir
    Final skill directory containing SKILL.md. Implies WithSkill.
#>
param(
    [string]$Version = "latest",
    [string]$InstallDir = "$env:LOCALAPPDATA\bp-inspect",
    [switch]$WithSkill,
    [string]$SkillDir
)

$ErrorActionPreference = "Stop"
$Repo = "MarcedForLife/UnrealBPInspect"
$Asset = "bp-inspect-windows-x86_64.exe"
$SkillRequested = $WithSkill -or $PSBoundParameters.ContainsKey("SkillDir")
if ($PSBoundParameters.ContainsKey("SkillDir") -and [string]::IsNullOrWhiteSpace($SkillDir)) {
    throw "SkillDir must be a non-empty directory."
}
if (-not $SkillDir) {
    $SkillDir = Join-Path $env:USERPROFILE ".claude\skills\unreal-bp"
}

New-Item -ItemType Directory -Path $InstallDir -Force | Out-Null
$InstallDir = (Resolve-Path $InstallDir).Path
$BinaryPath = Join-Path $InstallDir "bp-inspect.exe"
$TemporaryDir = Join-Path $InstallDir (".bp-inspect-" + [guid]::NewGuid())
New-Item -ItemType Directory -Path $TemporaryDir | Out-Null
$SkillTemporary = $null
try {
    if ($Version -eq "latest") {
        $ReleasePath = Join-Path $TemporaryDir "release.json"
        Invoke-WebRequest -Uri "https://api.github.com/repos/$Repo/releases/latest" -OutFile $ReleasePath -UseBasicParsing
        $Version = (Get-Content -Raw $ReleasePath | ConvertFrom-Json).tag_name
    }
    if (-not $Version.StartsWith("v")) { $Version = "v$Version" }
    if ($Version -notmatch '^v[0-9]+\.[0-9]+\.[0-9]+([.-][0-9A-Za-z.-]+)?$') {
        throw "Invalid release version: $Version"
    }
    $Url = "https://github.com/$Repo/releases/download/$Version"
    $TemporaryBinary = Join-Path $TemporaryDir $Asset
    $ChecksumPath = Join-Path $TemporaryDir "checksums.txt"
    Write-Host "Installing bp-inspect $Version..."
    Invoke-WebRequest -Uri "$Url/$Asset" -OutFile $TemporaryBinary -UseBasicParsing
    Invoke-WebRequest -Uri "$Url/checksums.txt" -OutFile $ChecksumPath -UseBasicParsing
    $Checksums = @(Get-Content $ChecksumPath | ForEach-Object {
        $Fields = $_.Trim() -split '\s+'
        if ($Fields.Count -eq 2 -and $Fields[1].TrimStart('*') -ceq $Asset) { $Fields[0] }
    })
    $Actual = (Get-FileHash -Algorithm SHA256 $TemporaryBinary).Hash
    if ($Checksums.Count -ne 1 -or $Checksums[0] -ine $Actual) {
        throw "Missing, duplicate, or mismatched SHA-256 checksum for $Asset."
    }
    $InstalledVersion = & $TemporaryBinary --version
    if ($LASTEXITCODE -ne 0) { throw "Downloaded binary failed its version check." }

    if ($SkillRequested) {
        New-Item -ItemType Directory -Path $SkillDir -Force | Out-Null
        $SkillTemporary = Join-Path $SkillDir (".SKILL-" + [guid]::NewGuid())
        Invoke-WebRequest -Uri "https://raw.githubusercontent.com/$Repo/$Version/skill/SKILL.md" -OutFile $SkillTemporary -UseBasicParsing
        if ((Get-Item $SkillTemporary).Length -eq 0) { throw "Downloaded skill is empty." }
    }

    # Replace preserves the existing file if Windows has it locked.
    if (Test-Path $BinaryPath) {
        [System.IO.File]::Replace($TemporaryBinary, $BinaryPath, [NullString]::Value)
    } else {
        [System.IO.File]::Move($TemporaryBinary, $BinaryPath)
    }
    if ($SkillRequested) {
        $SkillPath = Join-Path $SkillDir "SKILL.md"
        if (Test-Path $SkillPath) {
            [System.IO.File]::Replace($SkillTemporary, $SkillPath, [NullString]::Value)
        } else {
            [System.IO.File]::Move($SkillTemporary, $SkillPath)
        }
        Write-Host "  Installed skill to $SkillDir"
    }
} finally {
    Remove-Item -Recurse -Force $TemporaryDir -ErrorAction SilentlyContinue
    if ($SkillTemporary -and (Test-Path $SkillTemporary)) {
        Remove-Item -Force $SkillTemporary -ErrorAction SilentlyContinue
    }
}

$UserPath = [Environment]::GetEnvironmentVariable("Path", "User")
if (($UserPath -split ';') -notcontains $InstallDir) {
    [Environment]::SetEnvironmentVariable("Path", "$UserPath;$InstallDir", "User")
}
if (($env:Path -split ';') -notcontains $InstallDir) { $env:Path = "$env:Path;$InstallDir" }
if (Get-Command git -ErrorAction SilentlyContinue) {
    $GitBinaryPath = ($BinaryPath -replace '\\', '/').Replace("'", "'\''")
    git config --global diff.bp-inspect.textconv "'$GitBinaryPath'"
    if ($LASTEXITCODE -ne 0) { throw "Failed to configure Git textconv." }
    git config --global diff.bp-inspect.cachetextconv true
    if ($LASTEXITCODE -ne 0) { throw "Failed to configure Git textconv caching." }
}
Write-Host "  $InstalledVersion"
Write-Host "  Installed to: $BinaryPath"
Write-Host "To enable Git diffs, add this to your Unreal project's .gitattributes:"
Write-Host "  *.uasset diff=bp-inspect"
