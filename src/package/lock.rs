use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::diagnostic::Diagnostic;

use super::manifest::manifest_error;

pub const LOCK_FILE_NAME: &str = "ligare.lock";

#[derive(Clone, Debug, Default)]
pub struct LockFile {
    pub deps: BTreeMap<String, LockedDependency>,
}

#[derive(Clone, Debug)]
pub struct LockedDependency {
    pub source: String,
    pub version: String,
    pub commit: String,
    pub path: PathBuf,
}

pub fn read_lock(root: &Path) -> Result<LockFile, Diagnostic> {
    let path = root.join(LOCK_FILE_NAME);
    if !path.exists() {
        return Ok(LockFile::default());
    }
    let content = fs::read_to_string(&path)
        .map_err(|e| Diagnostic::new(format!("cannot read `{}`: {e}", path.display())))?;
    parse_lock(&content, &path)
}

pub fn write_lock(root: &Path, lock: &LockFile) -> Result<(), Diagnostic> {
    let mut out = String::new();
    for (name, dep) in &lock.deps {
        out.push_str(&format!("[[dep]]\nname = \"{}\"\n", escape(name)));
        out.push_str(&format!("source = \"{}\"\n", escape(&dep.source)));
        out.push_str(&format!("version = \"{}\"\n", escape(&dep.version)));
        out.push_str(&format!("commit = \"{}\"\n", escape(&dep.commit)));
        out.push_str(&format!(
            "path = \"{}\"\n\n",
            escape(&dep.path.to_string_lossy())
        ));
    }
    fs::write(root.join(LOCK_FILE_NAME), out)
        .map_err(|e| Diagnostic::new(format!("cannot write `{LOCK_FILE_NAME}`: {e}")))
}

fn parse_lock(content: &str, path: &Path) -> Result<LockFile, Diagnostic> {
    let mut lock = LockFile::default();
    let mut current = BTreeMap::new();
    for (idx, raw) in content.lines().enumerate() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if line == "[[dep]]" {
            flush_lock_dep(&mut lock, &mut current, path, idx)?;
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(manifest_error(path, idx, "expected `key = value`"));
        };
        current.insert(
            key.trim().to_string(),
            parse_string(value.trim(), path, idx)?,
        );
    }
    flush_lock_dep(&mut lock, &mut current, path, content.lines().count())?;
    Ok(lock)
}

fn flush_lock_dep(
    lock: &mut LockFile,
    current: &mut BTreeMap<String, String>,
    path: &Path,
    line: usize,
) -> Result<(), Diagnostic> {
    if current.is_empty() {
        return Ok(());
    }
    let name = current
        .remove("name")
        .ok_or_else(|| manifest_error(path, line, "lock dep requires `name`"))?;
    let dep = LockedDependency {
        source: current
            .remove("source")
            .ok_or_else(|| manifest_error(path, line, "lock dep requires `source`"))?,
        version: current
            .remove("version")
            .ok_or_else(|| manifest_error(path, line, "lock dep requires `version`"))?,
        commit: current
            .remove("commit")
            .ok_or_else(|| manifest_error(path, line, "lock dep requires `commit`"))?,
        path: PathBuf::from(
            current
                .remove("path")
                .ok_or_else(|| manifest_error(path, line, "lock dep requires `path`"))?,
        ),
    };
    lock.deps.insert(name, dep);
    current.clear();
    Ok(())
}

fn parse_string(value: &str, path: &Path, line: usize) -> Result<String, Diagnostic> {
    let value = value.trim();
    if value.len() >= 2 && value.starts_with('"') && value.ends_with('"') {
        return Ok(value[1..value.len() - 1].replace("\\\"", "\""));
    }
    Err(manifest_error(path, line, "expected quoted string"))
}

fn escape(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}
