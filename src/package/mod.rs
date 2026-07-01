mod git;
mod lock;
mod manifest;
mod resolver;

pub use lock::{LOCK_FILE_NAME, LockFile, LockedDependency, write_lock};
pub use manifest::{
    DepSource, Dependency, MANIFEST_NAMES, Manifest, find_manifest_root, manifest_path,
    read_manifest,
};
pub use resolver::{ResolvedProject, UpdateMode, resolve_project};
