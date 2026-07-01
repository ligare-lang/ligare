use std::fs;
use std::path::{Path, PathBuf};

use toml::{Table, Value};

use crate::diagnostic::Diagnostic;

pub const MANIFEST_NAMES: &[&str] = &["ligare.toml"];

#[derive(Clone, Debug)]
pub struct Manifest {
    pub name: String,
    pub entry: PathBuf,
    pub public_modules: Vec<Vec<String>>,
    pub dependencies: Vec<Dependency>,
}

#[derive(Clone, Debug)]
pub struct Dependency {
    pub name: String,
    pub source: DepSource,
    pub version: Option<String>,
}

#[derive(Clone, Debug)]
pub enum DepSource {
    Git(String),
    Path(PathBuf),
}

pub fn find_manifest_root(start: &Path) -> Result<PathBuf, Diagnostic> {
    let mut cur = if start.is_file() {
        start.parent().unwrap_or(start).to_path_buf()
    } else {
        start.to_path_buf()
    };
    loop {
        if manifest_path(&cur).is_some() {
            return Ok(cur);
        }
        if !cur.pop() {
            return Err(Diagnostic::new(format!(
                "no build manifest found from `{}`",
                start.display()
            )));
        }
    }
}

pub fn read_manifest(root: &Path) -> Result<Manifest, Diagnostic> {
    let path = manifest_path(root).ok_or_else(|| {
        Diagnostic::new(format!("no build manifest found in `{}`", root.display()))
    })?;
    let content = fs::read_to_string(&path)
        .map_err(|e| Diagnostic::new(format!("cannot read `{}`: {e}", path.display())))?;
    parse_manifest(&content, &path)
}

pub fn manifest_path(root: &Path) -> Option<PathBuf> {
    MANIFEST_NAMES
        .iter()
        .map(|name| root.join(name))
        .find(|path| path.exists())
}

fn parse_manifest(content: &str, path: &Path) -> Result<Manifest, Diagnostic> {
    let root = content.parse::<Table>().map_err(|e| {
        Diagnostic::new(format!(
            "{}:{}: invalid TOML: {e}",
            path.display(),
            e.span()
                .map(|span| line_number(content, span.start))
                .unwrap_or(1)
        ))
    })?;
    let package = root
        .get("package")
        .and_then(Value::as_table)
        .ok_or_else(|| manifest_error(path, 0, "manifest requires `[package]`"))?;
    let name = required_string(package, "name", path)?;
    let entry = optional_string(package, "entry")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("src/main.lig"));

    let mut public_modules = Vec::new();
    if let Some(exports) = root.get("exports") {
        let exports = exports
            .as_table()
            .ok_or_else(|| manifest_error(path, 0, "`exports` must be a table"))?;
        if let Some(modules) = exports.get("modules") {
            let modules = modules
                .as_array()
                .ok_or_else(|| manifest_error(path, 0, "`exports.modules` must be an array"))?;
            for module in modules {
                let module = module.as_str().ok_or_else(|| {
                    manifest_error(path, 0, "`exports.modules` entries must be strings")
                })?;
                public_modules.push(parse_module_path(module, path, 0)?);
            }
        }
        for key in exports.keys() {
            if key != "modules" {
                return Err(manifest_error(
                    path,
                    0,
                    &format!("unknown exports field `{key}`"),
                ));
            }
        }
    }
    if public_modules.is_empty() {
        public_modules.push(vec!["main".to_string()]);
    }
    let dependencies = parse_dependencies(root.get("dependencies"), path)?;
    Ok(Manifest {
        name,
        entry,
        public_modules,
        dependencies,
    })
}

fn parse_dependencies(value: Option<&Value>, path: &Path) -> Result<Vec<Dependency>, Diagnostic> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    let table = value
        .as_table()
        .ok_or_else(|| manifest_error(path, 0, "`dependencies` must be a table"))?;
    table
        .iter()
        .map(|(name, spec)| parse_dependency(name, spec, path))
        .collect()
}

fn parse_dependency(name: &str, value: &Value, path: &Path) -> Result<Dependency, Diagnostic> {
    let mut git = None;
    let mut local_path = None;
    let mut version = None;
    match value {
        Value::String(version_value) => {
            version = Some(version_value.clone());
        }
        Value::Table(fields) => {
            for (key, field) in fields {
                let value = field
                    .as_str()
                    .ok_or_else(|| manifest_error(path, 0, "dependency fields must be strings"))?;
                match key.as_str() {
                    "git" => git = Some(value.to_string()),
                    "path" => local_path = Some(PathBuf::from(value)),
                    "version" => version = Some(value.to_string()),
                    other => {
                        return Err(manifest_error(
                            path,
                            0,
                            &format!("unknown dependency field `{other}`"),
                        ));
                    }
                }
            }
        }
        _ => {
            return Err(manifest_error(
                path,
                0,
                "dependency must be a version string or inline table",
            ));
        }
    }
    let source = match (git, local_path) {
        (Some(url), None) => DepSource::Git(url),
        (None, Some(path)) => DepSource::Path(path),
        (None, None) if version.is_some() => {
            return Err(manifest_error(
                path,
                0,
                &format!("dependency `{name}` requires `git` or `path`"),
            ));
        }
        _ => {
            return Err(manifest_error(
                path,
                0,
                &format!("dependency `{name}` requires exactly one of `git` or `path`"),
            ));
        }
    };
    Ok(Dependency {
        name: name.to_string(),
        source,
        version,
    })
}

fn required_string(
    table: &toml::map::Map<String, Value>,
    key: &str,
    path: &Path,
) -> Result<String, Diagnostic> {
    table
        .get(key)
        .and_then(Value::as_str)
        .map(ToString::to_string)
        .ok_or_else(|| manifest_error(path, 0, &format!("`package.{key}` must be a string")))
}

fn optional_string(table: &toml::map::Map<String, Value>, key: &str) -> Option<String> {
    table
        .get(key)
        .and_then(Value::as_str)
        .map(ToString::to_string)
}

fn parse_module_path(value: &str, path: &Path, line: usize) -> Result<Vec<String>, Diagnostic> {
    let parts = value
        .split("::")
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(str::to_string)
        .collect::<Vec<_>>();
    if parts.is_empty() {
        return Err(manifest_error(path, line, "`pub` requires a module path"));
    }
    Ok(parts)
}

fn line_number(content: &str, byte: usize) -> usize {
    content[..byte.min(content.len())]
        .bytes()
        .filter(|b| *b == b'\n')
        .count()
        + 1
}

pub(super) fn manifest_error(path: &Path, line: usize, message: &str) -> Diagnostic {
    Diagnostic::new(format!("{}:{}: {message}", path.display(), line + 1))
}
