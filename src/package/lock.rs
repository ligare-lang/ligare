use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::diagnostic::Diagnostic;

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
    let out = toml::to_string(&LockToml::from(lock))
        .map_err(|e| Diagnostic::new(format!("cannot serialize `{LOCK_FILE_NAME}`: {e}")))?;
    fs::write(root.join(LOCK_FILE_NAME), out)
        .map_err(|e| Diagnostic::new(format!("cannot write `{LOCK_FILE_NAME}`: {e}")))
}

fn parse_lock(content: &str, path: &Path) -> Result<LockFile, Diagnostic> {
    toml::from_str::<LockToml>(content)
        .map(LockFile::from)
        .map_err(|e| invalid_lock(path, content, &e))
}

fn invalid_lock(path: &Path, content: &str, error: &toml::de::Error) -> Diagnostic {
    let line = error.span().map(|span| line_number(content, span.start));
    match line {
        Some(line) => Diagnostic::new(format!(
            "{}:{line}: invalid lock file: {error}",
            path.display()
        )),
        None => Diagnostic::new(format!("{}: invalid lock file: {error}", path.display())),
    }
}

fn line_number(content: &str, byte: usize) -> usize {
    content[..byte.min(content.len())]
        .bytes()
        .filter(|b| *b == b'\n')
        .count()
        + 1
}

#[derive(Serialize, Deserialize)]
struct LockToml {
    #[serde(default)]
    dep: Vec<LockedDependencyToml>,
}

#[derive(Serialize, Deserialize)]
struct LockedDependencyToml {
    name: String,
    source: String,
    version: String,
    commit: String,
    path: PathBuf,
}

impl From<&LockFile> for LockToml {
    fn from(lock: &LockFile) -> Self {
        Self {
            dep: lock
                .deps
                .iter()
                .map(|(name, dep)| LockedDependencyToml {
                    name: name.clone(),
                    source: dep.source.clone(),
                    version: dep.version.clone(),
                    commit: dep.commit.clone(),
                    path: dep.path.clone(),
                })
                .collect(),
        }
    }
}

impl From<LockToml> for LockFile {
    fn from(lock: LockToml) -> Self {
        Self {
            deps: lock
                .dep
                .into_iter()
                .map(|dep| {
                    (
                        dep.name,
                        LockedDependency {
                            source: dep.source,
                            version: dep.version,
                            commit: dep.commit,
                            path: dep.path,
                        },
                    )
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    fn temp_root() -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "ligare_lock_{}_{}_{}",
            std::process::id(),
            nanos,
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn lock_round_trips_escaped_values() {
        let root = temp_root();
        let mut lock = LockFile::default();
        lock.deps.insert(
            "pkg#1".to_string(),
            LockedDependency {
                source: "file:///tmp/repo#fragment".to_string(),
                version: "v1.2.3".to_string(),
                commit: "abc\\def".to_string(),
                path: PathBuf::from(r"C:\deps\pkg#1"),
            },
        );

        write_lock(&root, &lock).unwrap();
        let parsed = read_lock(&root).unwrap();
        let dep = &parsed.deps["pkg#1"];

        assert_eq!(dep.source, "file:///tmp/repo#fragment");
        assert_eq!(dep.version, "v1.2.3");
        assert_eq!(dep.commit, "abc\\def");
        assert_eq!(dep.path, PathBuf::from(r"C:\deps\pkg#1"));
    }
}
