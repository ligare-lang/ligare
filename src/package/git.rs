use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::diagnostic::Diagnostic;

pub fn ensure_git_checkout(url: &str, version: &str, cache: &Path) -> Result<(), Diagnostic> {
    if cache.join(".git").exists() {
        run_git(cache, &["fetch", "--tags", "--force"])?;
    } else {
        if let Some(parent) = cache.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Diagnostic::new(format!("cannot create dependency cache: {e}")))?;
        }
        let cache_str = cache.to_string_lossy().into_owned();
        run_cmd(None, "git", &["clone", url, &cache_str])?;
    }
    run_git(cache, &["checkout", version])?;
    Ok(())
}

pub fn latest_git_tag(url: &str) -> Result<String, Diagnostic> {
    let out = Command::new("git")
        .args(["ls-remote", "--tags", "--refs", url])
        .output()
        .map_err(|e| Diagnostic::new(format!("cannot run git: {e}")))?;
    if !out.status.success() {
        return Err(Diagnostic::new("git ls-remote failed"));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .filter_map(|line| {
            line.split_once("refs/tags/")
                .map(|(_, tag)| tag.to_string())
        })
        .max()
        .ok_or_else(|| Diagnostic::new(format!("no git tags found for `{url}`")))
}

pub fn git_commit(root: &Path) -> Result<String, Diagnostic> {
    let out = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .output()
        .map_err(|e| Diagnostic::new(format!("cannot run git in `{}`: {e}", root.display())))?;
    if !out.status.success() {
        return Err(Diagnostic::new(format!(
            "git rev-parse failed in `{}`",
            root.display()
        )));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

pub fn dep_cache_dir(name: &str, version: &str) -> Result<PathBuf, Diagnostic> {
    let home = env::var_os("LIGARE_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|home| PathBuf::from(home).join(".ligare")))
        .ok_or_else(|| Diagnostic::new("HOME is not set; cannot locate dependency cache"))?;
    Ok(home.join("deps").join(name).join(version))
}

fn run_git(root: &Path, args: &[&str]) -> Result<(), Diagnostic> {
    run_cmd(Some(root), "git", args)
}

fn run_cmd(root: Option<&Path>, bin: &str, args: &[&str]) -> Result<(), Diagnostic> {
    let mut cmd = Command::new(bin);
    cmd.args(args);
    if let Some(root) = root {
        cmd.current_dir(root);
    }
    let status = cmd
        .status()
        .map_err(|e| Diagnostic::new(format!("cannot run `{bin}`: {e}")))?;
    if status.success() {
        Ok(())
    } else {
        Err(Diagnostic::new(format!(
            "`{bin} {}` failed",
            args.join(" ")
        )))
    }
}
