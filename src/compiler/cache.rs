use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use crate::diagnostic::Diagnostic;
use crate::package::find_manifest_root;

const CACHE_VERSION: u32 = 2;
const CACHE_DIR: &str = "target";
const CACHE_SUBDIR: &str = "ligare";
pub const FALLBACK_ROOT_PACKAGE: &str = "root";

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FileCompilerCache {
    pub version: u32,
    pub files: HashMap<String, CachedFile>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CachedFile {
    pub package: Option<String>,
    pub module_path: Vec<String>,
    pub source_hash: u64,
    pub imports: Vec<Vec<String>>,
    pub exports: Vec<String>,
    pub checked_ok: bool,
    pub updated_at_ms: u128,
}

#[derive(Clone, Debug)]
pub struct PackageCompilerCache {
    target_root: PathBuf,
    package_root: PathBuf,
    package: String,
    cache: FileCompilerCache,
}

impl PackageCompilerCache {
    pub fn load(target_root: &Path, package_root: &Path, package: &str) -> Self {
        let path = cache_file_path(target_root, package);
        let cache = fs::read(&path)
            .ok()
            .and_then(|content| rmp_serde::from_slice::<FileCompilerCache>(&content).ok())
            .filter(|cache| cache.version == CACHE_VERSION)
            .unwrap_or_else(|| FileCompilerCache {
                version: CACHE_VERSION,
                files: HashMap::new(),
            });
        Self {
            target_root: target_root.to_path_buf(),
            package_root: package_root.to_path_buf(),
            package: package.to_string(),
            cache,
        }
    }

    pub fn lookup(&self, file: &Path) -> Option<&CachedFile> {
        let key = cache_key(&self.package_root, file);
        self.cache.files.get(&key)
    }

    pub fn is_fresh(&self, file: &Path, source_hash: u64) -> bool {
        self.lookup(file)
            .is_some_and(|entry| entry.checked_ok && entry.source_hash == source_hash)
    }

    pub fn update(&mut self, file: &Path, entry: CachedFile) {
        let key = cache_key(&self.package_root, file);
        self.cache.files.insert(key, entry);
    }

    pub fn retain_files<'a>(&mut self, files: impl IntoIterator<Item = &'a PathBuf>) {
        let keys = files
            .into_iter()
            .map(|file| cache_key(&self.package_root, file))
            .collect::<HashSet<_>>();
        self.cache.files.retain(|path, _| keys.contains(path));
    }

    pub fn save(&self) -> Result<(), Diagnostic> {
        let path = cache_file_path(&self.target_root, &self.package);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                Diagnostic::new(format!(
                    "cannot create compiler cache directory `{}`: {e}",
                    parent.display()
                ))
            })?;
        }
        let content = rmp_serde::to_vec(&self.cache).map_err(|e| {
            Diagnostic::new(format!(
                "cannot encode compiler cache `{}`: {e}",
                path.display()
            ))
        })?;
        fs::write(&path, content).map_err(|e| {
            Diagnostic::new(format!(
                "cannot write compiler cache `{}`: {e}",
                path.display()
            ))
        })
    }
}

pub fn cache_file_path(target_root: &Path, package: &str) -> PathBuf {
    target_root
        .join(CACHE_DIR)
        .join(CACHE_SUBDIR)
        .join(format!("{}.bin", cache_file_stem(package)))
}

pub fn source_hash(source: &str) -> u64 {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    source.bytes().fold(OFFSET, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(PRIME)
    })
}

pub fn now_ms() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or_default()
}

pub fn package_root_for_file(file: &Path) -> Option<PathBuf> {
    find_manifest_root(file).ok()
}

pub fn cache_file_stem(package: &str) -> String {
    let stem = package
        .chars()
        .map(|ch| match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' => ch,
            _ => '_',
        })
        .collect::<String>();
    if stem.is_empty() {
        FALLBACK_ROOT_PACKAGE.to_string()
    } else {
        stem
    }
}

fn cache_key(root: &Path, file: &Path) -> String {
    let relative = file.strip_prefix(root).unwrap_or(file);
    relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}
