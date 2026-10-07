"""Exercise installers with local downloads and an isolated Git config.

Run after cargo build --release. Windows tests use PowerShell, Unix tests use sh.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import unittest

REPOSITORY = Path(__file__).resolve().parents[1]
WINDOWS = os.name == "nt"
BINARY = Path(os.environ.get(
    "BP_INSPECT_TEST_BINARY",
    REPOSITORY / "target" / "release" / ("bp-inspect.exe" if WINDOWS else "bp-inspect"),
)).resolve()

DOWNLOAD_MOCK = r'''
import os
from pathlib import Path
import shutil
import sys

arguments = sys.argv[1:]
output_flag = "-o" if "-o" in arguments else "-O"
destination = Path(arguments[arguments.index(output_flag) + 1])
url = arguments[-1]
fixtures = Path(os.environ["INSTALLER_FIXTURES"])
with (fixtures / "requests.txt").open("a") as requests:
    requests.write(url + "\n")
name = url.rsplit("/", 1)[-1]
if name == "latest":
    name = "release.json"
if os.environ.get("INSTALLER_FAILURE") == "network" and name.startswith("bp-inspect-"):
    destination.write_bytes(b"partial download" * 200)
    sys.exit(22)
if os.environ.get("INSTALLER_FAILURE") == "skill" and name == "SKILL.md":
    sys.exit(22)
shutil.copyfile(fixtures / name, destination)
'''

POWERSHELL_MOCK = r'''
function Invoke-WebRequest {
    param($Uri, $OutFile, [switch]$UseBasicParsing)
    Add-Content -Path (Join-Path $env:INSTALLER_FIXTURES "requests.txt") -Value $Uri
    $Name = ($Uri -split '/')[-1]
    if ($Name -eq "latest") { $Name = "release.json" }
    if ($env:INSTALLER_FAILURE -eq "network" -and $Name.StartsWith("bp-inspect-")) {
        Set-Content -Path $OutFile -Value ('partial download' * 200)
        throw "Simulated interrupted download"
    }
    if ($env:INSTALLER_FAILURE -eq "skill" -and $Name -eq "SKILL.md") {
        throw "Simulated missing skill"
    }
    Copy-Item (Join-Path $env:INSTALLER_FIXTURES $Name) $OutFile
}
$OriginalPath = [Environment]::GetEnvironmentVariable("Path", "User")
try {
    & $env:INSTALLER_SCRIPT -Version $env:INSTALLER_VERSION -InstallDir $env:INSTALL_DIR -SkillDir $env:INSTALLER_SKILL_DIR
} catch {
    Write-Error $_ -ErrorAction Continue
    exit 1
} finally {
    [Environment]::SetEnvironmentVariable("Path", $OriginalPath, "User")
}
'''


class InstallerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.fixtures = self.directory / "fixtures"
        self.fixtures.mkdir()
        # Exercise both whitespace and shell quoting in the textconv command.
        self.install_dir = self.directory / "tools with space's"
        self.install_dir.mkdir()
        self.target = self.install_dir / ("bp-inspect.exe" if WINDOWS else "bp-inspect")
        self.target.write_bytes(b"previous binary")
        self.skill_dir = self.directory / "skills with spaces" / "unreal-bp"
        self.skill_dir.mkdir(parents=True)
        (self.skill_dir / "SKILL.md").write_text("previous skill")
        if WINDOWS:
            self.asset = "bp-inspect-windows-x86_64.exe"
        else:
            system = "macos" if platform.system() == "Darwin" else "linux"
            architecture = "aarch64" if platform.machine() in ("arm64", "aarch64") else "x86_64"
            self.asset = f"bp-inspect-{system}-{architecture}"
        shutil.copyfile(BINARY, self.fixtures / self.asset)
        self.digest = hashlib.sha256(BINARY.read_bytes()).hexdigest()
        (self.fixtures / "checksums.txt").write_text(f"{self.digest}  {self.asset}\n")
        (self.fixtures / "release.json").write_text(json.dumps({"tag_name": "v1.2.3"}))
        (self.fixtures / "SKILL.md").write_text("released skill")
        self.environment = os.environ.copy()
        self.environment.update({
            "INSTALL_DIR": str(self.install_dir),
            "BP_INSPECT_VERSION": "v1.2.3",
            "INSTALLER_VERSION": "v1.2.3",
            "INSTALLER_SKILL_DIR": str(self.skill_dir),
            "INSTALLER_FIXTURES": str(self.fixtures),
            "INSTALLER_FAILURE": "",
            "GIT_CONFIG_GLOBAL": str(self.directory / "gitconfig"),
            "GIT_CONFIG_NOSYSTEM": "1",
        })
        if WINDOWS:
            self.environment["INSTALLER_SCRIPT"] = str(REPOSITORY / "install.ps1")
            wrapper = self.directory / "test.ps1"
            wrapper.write_text(POWERSHELL_MOCK)
            self.command = ["pwsh", "-NoProfile", "-File", str(wrapper)]
        else:
            mock_bin = self.directory / "bin"
            mock_bin.mkdir()
            for name in ("curl", "wget"):
                executable = mock_bin / name
                executable.write_text("#!/usr/bin/env python3\n" + DOWNLOAD_MOCK)
                executable.chmod(0o755)
            self.environment["PATH"] = str(mock_bin) + os.pathsep + self.environment["PATH"]
            self.command = ["sh", str(REPOSITORY / "install.sh"), "--skill-dir", str(self.skill_dir)]

    def run_installer(self):
        return subprocess.run(self.command, env=self.environment, capture_output=True, text=True)

    def assert_preserved(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.target.read_bytes(), b"previous binary")
        self.assertEqual((self.skill_dir / "SKILL.md").read_text(), "previous skill")
        self.assertEqual(list(self.install_dir.iterdir()), [self.target])
        self.assertEqual(list(self.skill_dir.iterdir()), [self.skill_dir / "SKILL.md"])
        self.assertFalse((self.directory / "gitconfig").exists())

    def test_success_pins_skill_and_configures_working_textconv(self):
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.target.read_bytes(), BINARY.read_bytes())
        self.assertEqual((self.skill_dir / "SKILL.md").read_text(), "released skill")
        requests = (self.fixtures / "requests.txt").read_text()
        self.assertIn("/v1.2.3/skill/SKILL.md", requests)
        self.assertNotIn("/main/", requests)
        repository = self.directory / "git project"
        repository.mkdir()
        subprocess.run(["git", "init", "-q", str(repository)], check=True, env=self.environment)
        for key, value in [("user.name", "Installer test"), ("user.email", "installer@example.invalid")]:
            subprocess.run(["git", "config", key, value], cwd=repository, env=self.environment, check=True)
        fixture = REPOSITORY / "samples" / "ue_4.27" / "Helm_BP.uasset"
        shutil.copyfile(fixture, repository / "sample.uasset")
        (repository / ".gitattributes").write_text("*.uasset diff=bp-inspect\n")
        subprocess.run(["git", "add", "."], cwd=repository, env=self.environment, check=True)
        converted = subprocess.run(
            ["git", "cat-file", "--textconv", ":sample.uasset"],
            cwd=repository, env=self.environment, capture_output=True,
        )
        self.assertEqual(converted.returncode, 0, converted.stderr.decode())
        self.assertIn(b"Blueprint:", converted.stdout)

    def test_fresh_installation(self):
        self.target.unlink()
        (self.skill_dir / "SKILL.md").unlink()
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.target.read_bytes(), BINARY.read_bytes())
        self.assertEqual((self.skill_dir / "SKILL.md").read_text(), "released skill")

    @unittest.skipIf(WINDOWS, "wget fallback belongs to the shell installer")
    def test_wget_fallback(self):
        mock_bin = self.directory / "bin"
        (mock_bin / "curl").unlink()
        for command in ("uname", "mkdir", "mktemp", "sed", "head", "grep", "awk",
                        "sha256sum", "shasum", "chmod", "mv", "rm", "git", "python3"):
            executable = shutil.which(command)
            if executable:
                (mock_bin / command).symlink_to(executable)
        self.environment["PATH"] = str(mock_bin)
        self.command[0] = shutil.which("sh")
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.target.read_bytes(), BINARY.read_bytes())

    def test_latest_is_resolved_once(self):
        self.environment["BP_INSPECT_VERSION"] = "latest"
        self.environment["INSTALLER_VERSION"] = "latest"
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        requests = (self.fixtures / "requests.txt").read_text().splitlines()
        self.assertEqual(sum(url.endswith("/latest") for url in requests), 1)
        self.assertTrue(all("v1.2.3" in url for url in requests[1:]))

    def test_interrupted_download_preserves_existing_installation(self):
        self.environment["INSTALLER_FAILURE"] = "network"
        self.assert_preserved(self.run_installer())

    def test_bad_checksum_preserves_existing_installation(self):
        (self.fixtures / "checksums.txt").write_text(f"{'0' * 64}  {self.asset}\n")
        self.assert_preserved(self.run_installer())

    def test_missing_checksum_preserves_existing_installation(self):
        (self.fixtures / "checksums.txt").write_text(f"{self.digest}  different-binary\n")
        self.assert_preserved(self.run_installer())

    def test_duplicate_checksum_preserves_existing_installation(self):
        (self.fixtures / "checksums.txt").write_text(f"{self.digest}  {self.asset}\n" * 2)
        self.assert_preserved(self.run_installer())

    def test_missing_skill_preserves_existing_installation(self):
        self.environment["INSTALLER_FAILURE"] = "skill"
        self.assert_preserved(self.run_installer())


if __name__ == "__main__":
    if not BINARY.is_file():
        raise SystemExit(f"Build the release binary first: {BINARY}")
    unittest.main()
