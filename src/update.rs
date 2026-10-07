//! Self-update from GitHub releases (`--update`).

use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::path::Path;

const REPO: &str = "MarcedForLife/UnrealBPInspect";
const CURRENT_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Update bp-inspect from GitHub releases.
pub fn run_update(target_version: Option<&str>) -> Result<()> {
    eprintln!("Checking for updates...");

    // Normalize version tag (ensure "v" prefix for API lookup)
    let api_url = match target_version {
        Some(v) => {
            let tag = if v.starts_with('v') {
                v.to_string()
            } else {
                format!("v{}", v)
            };
            format!(
                "https://api.github.com/repos/{}/releases/tags/{}",
                REPO, tag
            )
        }
        None => format!("https://api.github.com/repos/{}/releases/latest", REPO),
    };

    let mut response = match ureq::get(&api_url)
        .header("User-Agent", "bp-inspect")
        .call()
    {
        Ok(resp) => resp,
        Err(ureq::Error::StatusCode(404)) => {
            if let Some(v) = target_version {
                bail!(
                    "Version '{}' not found. Check https://github.com/{}/releases",
                    v,
                    REPO
                );
            }
            bail!(
                "No releases found. Check https://github.com/{}/releases",
                REPO
            );
        }
        Err(e) => {
            return Err(anyhow::anyhow!(e).context("Failed to check for updates (network error)"));
        }
    };
    let resp: serde_json::Value = response
        .body_mut()
        .read_json()
        .context("Failed to parse release info")?;

    let release_tag = resp["tag_name"]
        .as_str()
        .context("No tag_name in release response")?;
    let release_version = release_tag.strip_prefix('v').unwrap_or(release_tag);

    if release_version == CURRENT_VERSION {
        eprintln!("Already on v{}", CURRENT_VERSION);
        return Ok(());
    }

    eprintln!("Updating v{} → v{}...", CURRENT_VERSION, release_version);

    // Determine asset name for current platform
    let asset_name = platform_asset()?;

    let assets = resp["assets"].as_array().context("No assets in release")?;
    eprintln!("  Downloading {}...", asset_name);
    let bytes = download_asset(assets, asset_name)?;
    let checksums = download_asset(assets, "checksums.txt")?;
    validate_checksum(&bytes, asset_name, std::str::from_utf8(&checksums)?)?;
    validate_binary(&bytes)?;

    // Replace current binary
    let current_exe =
        std::env::current_exe().context("Cannot determine current executable path")?;
    self_replace(&current_exe, &bytes)?;

    eprintln!("Updated to v{}", release_version);
    Ok(())
}

fn download_asset(assets: &[serde_json::Value], name: &str) -> Result<Vec<u8>> {
    let asset = assets
        .iter()
        .find(|asset| asset["name"].as_str() == Some(name))
        .with_context(|| format!("Missing release asset: {name}"))?;
    let url = asset["browser_download_url"]
        .as_str()
        .context("No download URL for asset")?;
    let mut bytes = Vec::new();
    ureq::get(url)
        .header("User-Agent", "bp-inspect")
        .call()
        .with_context(|| format!("Failed to download {name}"))?
        .body_mut()
        .as_reader()
        .read_to_end(&mut bytes)
        .with_context(|| format!("Failed to read {name}"))?;
    Ok(bytes)
}

fn validate_checksum(bytes: &[u8], name: &str, checksums: &str) -> Result<()> {
    let matches: Vec<&str> = checksums
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace();
            let checksum = fields.next()?;
            let filename = fields.next()?.trim_start_matches('*');
            (filename == name && fields.next().is_none()).then_some(checksum)
        })
        .collect();
    let [expected] = matches.as_slice() else {
        bail!("Expected exactly one checksum for {name}");
    };
    let actual = Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    if !actual.eq_ignore_ascii_case(expected) {
        bail!("SHA-256 checksum mismatch for {name}");
    }
    Ok(())
}

fn validate_binary(bytes: &[u8]) -> Result<()> {
    if bytes.len() < 1024 {
        bail!("Downloaded file too small ({} bytes)", bytes.len());
    }
    let valid_magic = if cfg!(target_os = "linux") {
        bytes.starts_with(b"\x7fELF")
    } else if cfg!(target_os = "macos") {
        // Mach-O 64-bit magic (little-endian on disk) or universal binary
        bytes.starts_with(&[0xCF, 0xFA, 0xED, 0xFE]) || bytes.starts_with(&[0xCA, 0xFE, 0xBA, 0xBE])
    } else if cfg!(target_os = "windows") {
        bytes.starts_with(b"MZ")
    } else {
        true
    };
    if !valid_magic {
        bail!("Downloaded file is not a valid executable");
    }
    Ok(())
}

fn platform_asset() -> Result<&'static str> {
    if cfg!(target_os = "windows") && cfg!(target_arch = "x86_64") {
        Ok("bp-inspect-windows-x86_64.exe")
    } else if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
        Ok("bp-inspect-macos-aarch64")
    } else if cfg!(target_os = "macos") && cfg!(target_arch = "x86_64") {
        Ok("bp-inspect-macos-x86_64")
    } else if cfg!(target_os = "linux") && cfg!(target_arch = "x86_64") {
        Ok("bp-inspect-linux-x86_64")
    } else {
        bail!(
            "Self-update not available for this platform. \
             Download manually from https://github.com/{}/releases",
            REPO
        )
    }
}

fn self_replace(exe_path: &Path, new_bytes: &[u8]) -> Result<()> {
    let dir = exe_path
        .parent()
        .context("Cannot determine executable directory")?;
    let mut temporary =
        tempfile::NamedTempFile::new_in(dir).context("Failed to create update file")?;
    temporary
        .write_all(new_bytes)
        .context("Failed to write update file")?;
    temporary.as_file().sync_all()?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        temporary
            .as_file()
            .set_permissions(std::fs::Permissions::from_mode(0o755))?;
    }
    let temporary = temporary.into_temp_path();

    #[cfg(windows)]
    {
        let old_path = dir.join("bp-inspect.old.exe");
        if old_path.exists() {
            std::fs::remove_file(&old_path).context("Failed to remove previous backup")?;
        }
        std::fs::rename(exe_path, &old_path).context("Failed to move old binary")?;
        if let Err(error) = temporary.persist(exe_path) {
            std::fs::rename(&old_path, exe_path)
                .context("Failed to restore old binary after update failure")?;
            return Err(error).context("Failed to install new binary; old binary restored");
        }
        // A running Windows executable can remain locked until this process exits.
        let _ = std::fs::remove_file(old_path);
    }
    #[cfg(not(windows))]
    temporary
        .persist(exe_path)
        .context("Failed to replace binary")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checksum_requires_matching_content_and_unique_asset() {
        let checksum = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        let manifest = format!("{checksum}  bp-inspect-linux-x86_64\n");
        assert!(validate_checksum(b"abc", "bp-inspect-linux-x86_64", &manifest).is_ok());
        assert!(validate_checksum(b"abd", "bp-inspect-linux-x86_64", &manifest).is_err());
        assert!(validate_checksum(b"abc", "bp-inspect-macos-aarch64", &manifest).is_err());
        assert!(validate_checksum(b"abc", "bp-inspect-linux-x86_64", &manifest.repeat(2)).is_err());
        assert!(validate_checksum(b"abc", "bp-inspect-linux-x86_64", "malformed").is_err());
    }

    #[test]
    fn replacement_installs_bytes_and_cleans_temporary_files() {
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("bp-inspect");
        std::fs::write(&executable, b"old executable").unwrap();
        self_replace(&executable, b"new executable").unwrap();
        assert_eq!(std::fs::read(&executable).unwrap(), b"new executable");
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 1);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                std::fs::metadata(executable).unwrap().permissions().mode() & 0o777,
                0o755
            );
        }
    }

    #[test]
    fn replacement_failure_preserves_existing_destination() {
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("bp-inspect");
        std::fs::create_dir(&executable).unwrap();
        std::fs::write(executable.join("keep"), b"untouched").unwrap();
        // Windows can rename a directory aside, so use a missing parent there.
        #[cfg(not(windows))]
        assert!(self_replace(&executable, b"new executable").is_err());
        #[cfg(windows)]
        assert!(self_replace(
            &directory.path().join("missing/bp-inspect"),
            b"new executable"
        )
        .is_err());
        assert_eq!(
            std::fs::read(executable.join("keep")).unwrap(),
            b"untouched"
        );
        assert_eq!(std::fs::read_dir(directory.path()).unwrap().count(), 1);
    }
}
