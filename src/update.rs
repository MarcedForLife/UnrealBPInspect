use anyhow::{bail, Context, Result};
use std::io::Read;
use std::path::Path;

const REPO: &str = "MarcedForLife/UnrealBPInspect";
const CURRENT_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Update bp-inspect to the latest (or a specific) version from GitHub releases.
/// Pass `None` for latest, or `Some("v0.2.0")` for a pinned version.
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

    // Compare versions (skip check when pinning to a specific version)
    if target_version.is_none() && release_version == CURRENT_VERSION {
        eprintln!("Already up to date (v{})", CURRENT_VERSION);
        return Ok(());
    }

    if release_version == CURRENT_VERSION {
        eprintln!("Already on v{}", CURRENT_VERSION);
        return Ok(());
    }

    eprintln!("Updating v{} → v{}...", CURRENT_VERSION, release_version);

    // Determine asset name for current platform
    let asset_name = platform_asset()?;

    // Find download URL from release assets
    let assets = resp["assets"].as_array().context("No assets in release")?;
    let asset = assets
        .iter()
        .find(|a| a["name"].as_str() == Some(asset_name))
        .with_context(|| format!("No release binary for this platform: {}", asset_name))?;
    let download_url = asset["browser_download_url"]
        .as_str()
        .context("No download URL for asset")?;

    // Download the new binary
    eprintln!("  Downloading {}...", asset_name);
    let mut bytes = Vec::new();
    ureq::get(download_url)
        .header("User-Agent", "bp-inspect")
        .call()
        .context("Failed to download update")?
        .body_mut()
        .as_reader()
        .read_to_end(&mut bytes)
        .context("Failed to read update data")?;

    if bytes.len() < 1000 {
        bail!("Downloaded file too small — possible error");
    }

    // Replace current binary
    let current_exe =
        std::env::current_exe().context("Cannot determine current executable path")?;
    self_replace(&current_exe, &bytes)?;

    eprintln!("Updated to v{}", release_version);
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
    let tmp_path = dir.join(".bp-inspect-update.tmp");

    std::fs::write(&tmp_path, new_bytes).context("Failed to write update file")?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&tmp_path, std::fs::Permissions::from_mode(0o755))?;
        std::fs::rename(&tmp_path, exe_path).context("Failed to replace binary")?;
    }

    #[cfg(windows)]
    {
        let old_path = dir.join("bp-inspect.old.exe");
        let _ = std::fs::remove_file(&old_path);
        std::fs::rename(exe_path, &old_path).context("Failed to move old binary")?;
        std::fs::rename(&tmp_path, exe_path).context("Failed to install new binary")?;
    }

    Ok(())
}
