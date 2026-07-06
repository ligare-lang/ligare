use std::cmp::Ordering;
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
    let mut semver_tags = Vec::new();
    let mut fallback_tags = Vec::new();
    for tag in stdout.lines().filter_map(parse_tag_name) {
        if let Some(version) = SemVerTag::parse(&tag) {
            semver_tags.push((version, tag));
        } else {
            fallback_tags.push(tag);
        }
    }
    if let Some((_, tag)) = semver_tags.into_iter().max_by(|lhs, rhs| lhs.0.cmp(&rhs.0)) {
        return Ok(tag);
    }
    fallback_tags
        .into_iter()
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

fn parse_tag_name(line: &str) -> Option<String> {
    line.split_once("refs/tags/")
        .map(|(_, tag)| tag.trim().to_string())
        .filter(|tag| !tag.is_empty())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SemVerTag {
    core: Vec<u64>,
    pre: Vec<PreReleaseId>,
}

impl SemVerTag {
    fn parse(tag: &str) -> Option<Self> {
        let version = tag
            .strip_prefix('v')
            .or_else(|| tag.strip_prefix('V'))
            .unwrap_or(tag);
        let (version, _) = version.split_once('+').unwrap_or((version, ""));
        let (core, pre) = version
            .split_once('-')
            .map_or((version, None), |(core, pre)| (core, Some(pre)));
        let core = parse_numeric_identifiers(core, '.')?;
        if core.is_empty() {
            return None;
        }
        let pre = match pre {
            Some(ids) if !ids.is_empty() => ids
                .split('.')
                .map(PreReleaseId::parse)
                .collect::<Option<Vec<_>>>()?,
            Some(_) => return None,
            None => Vec::new(),
        };
        Some(Self { core, pre })
    }
}

impl Ord for SemVerTag {
    fn cmp(&self, other: &Self) -> Ordering {
        let len = self.core.len().max(other.core.len());
        for idx in 0..len {
            let lhs = *self.core.get(idx).unwrap_or(&0);
            let rhs = *other.core.get(idx).unwrap_or(&0);
            match lhs.cmp(&rhs) {
                Ordering::Equal => {}
                ord => return ord,
            }
        }
        match (self.pre.is_empty(), other.pre.is_empty()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => compare_pre_release(&self.pre, &other.pre),
        }
    }
}

impl PartialOrd for SemVerTag {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PreReleaseId {
    Numeric(u64),
    Text(String),
}

impl PreReleaseId {
    fn parse(id: &str) -> Option<Self> {
        if id.is_empty() {
            return None;
        }
        if let Ok(value) = id.parse::<u64>() {
            return Some(Self::Numeric(value));
        }
        Some(Self::Text(id.to_string()))
    }
}

fn compare_pre_release(lhs: &[PreReleaseId], rhs: &[PreReleaseId]) -> Ordering {
    let len = lhs.len().max(rhs.len());
    for idx in 0..len {
        match (lhs.get(idx), rhs.get(idx)) {
            (Some(lhs), Some(rhs)) => match compare_pre_release_id(lhs, rhs) {
                Ordering::Equal => {}
                ord => return ord,
            },
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (None, None) => return Ordering::Equal,
        }
    }
    Ordering::Equal
}

fn compare_pre_release_id(lhs: &PreReleaseId, rhs: &PreReleaseId) -> Ordering {
    match (lhs, rhs) {
        (PreReleaseId::Numeric(lhs), PreReleaseId::Numeric(rhs)) => lhs.cmp(rhs),
        (PreReleaseId::Numeric(_), PreReleaseId::Text(_)) => Ordering::Less,
        (PreReleaseId::Text(_), PreReleaseId::Numeric(_)) => Ordering::Greater,
        (PreReleaseId::Text(lhs), PreReleaseId::Text(rhs)) => lhs.cmp(rhs),
    }
}

fn parse_numeric_identifiers(input: &str, delimiter: char) -> Option<Vec<u64>> {
    input
        .split(delimiter)
        .map(|part| {
            (!part.is_empty())
                .then(|| part.parse::<u64>().ok())
                .flatten()
        })
        .collect()
}
