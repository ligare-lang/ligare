//! Invoke external compilers to produce native executables
//! from generated source code.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Errors that can occur during compilation.
#[derive(Debug)]
pub enum CompileError {
    Io(std::io::Error),
    CompilerNotFound,
    CompileFailed {
        status: std::process::ExitStatus,
        stderr: String,
    },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Io(e) => write!(f, "I/O error: {}", e),
            CompileError::CompilerNotFound => write!(f, "compiler not found in PATH"),
            CompileError::CompileFailed { status, stderr } => {
                write!(f, "compilation failed ({}): {}", status, stderr)
            }
        }
    }
}

impl std::error::Error for CompileError {}

impl From<std::io::Error> for CompileError {
    fn from(e: std::io::Error) -> Self {
        CompileError::Io(e)
    }
}

/// Compile C source code into a native executable using `cc`.
/// Respects the `CC` environment variable.
pub fn compile_c(c_source: &str, output_path: &Path) -> Result<PathBuf, CompileError> {
    let output_abs = resolve_output(output_path)?;
    let tmp_file = temp_file(&output_abs, "c");

    write_temp(&tmp_file, c_source)?;

    let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let status = Command::new(&compiler)
        .arg("-o")
        .arg(&output_abs)
        .arg(&tmp_file)
        .output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                CompileError::CompilerNotFound
            } else {
                CompileError::Io(e)
            }
        })?;

    let _ = std::fs::remove_file(&tmp_file);

    if !status.status.success() {
        return Err(CompileError::CompileFailed {
            status: status.status,
            stderr: String::from_utf8_lossy(&status.stderr).into_owned(),
        });
    }

    let actual = find_output(&output_abs);
    print_diag(&status.stdout);
    Ok(actual)
}

// ── helpers ──

fn resolve_output(output_path: &Path) -> Result<PathBuf, std::io::Error> {
    let abs = if output_path.is_absolute() {
        output_path.to_path_buf()
    } else {
        std::env::current_dir()?.join(output_path)
    };
    if let Some(parent) = abs.parent() {
        std::fs::create_dir_all(parent)?;
    }
    Ok(abs)
}

fn temp_file(output: &Path, ext: &str) -> PathBuf {
    let stem = output
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("ligare_out");
    let dir = output.parent().unwrap_or_else(|| Path::new("."));
    dir.join(format!(".{stem}.tmp.{ext}"))
}

fn write_temp(path: &Path, source: &str) -> Result<(), CompileError> {
    let mut f = std::fs::File::create(path)?;
    f.write_all(source.as_bytes())?;
    Ok(())
}

fn print_diag(stdout: &[u8]) {
    let s = String::from_utf8_lossy(stdout);
    if !s.trim().is_empty() {
        eprintln!("{}", s.trim());
    }
}

/// Find the actual output file (handles .exe on Windows).
fn find_output(expected: &Path) -> PathBuf {
    if expected.exists() {
        return expected.to_path_buf();
    }
    #[cfg(target_os = "windows")]
    {
        let with_exe = expected.with_extension("exe");
        if with_exe.exists() {
            return with_exe;
        }
    }
    expected.to_path_buf()
}
