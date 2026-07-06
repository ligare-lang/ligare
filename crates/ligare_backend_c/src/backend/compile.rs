//! Invoke external compilers to produce native executables
//! from generated source code.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

pub use ligare_backend::CompileError;

static TEMP_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Compile C source code into a native executable using `cc`.
/// Respects the `CC` environment variable.
pub fn compile_c(c_source: &str, output_path: &Path) -> Result<PathBuf, CompileError> {
    let output_abs = resolve_output(output_path)?;
    let tmp_file = temp_file("c")?;
    let _guard = TempGuard(tmp_file.clone());

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

/// Compile C source into a temporary executable, run it, and return stdout.
pub fn compile_and_run_c(c_source: &str) -> Result<String, CompileError> {
    let exe = temp_file("eval")?;
    let _guard = TempGuard(exe.clone());
    let actual = compile_c(c_source, &exe)?;
    let output = Command::new(&actual).output().map_err(CompileError::Io)?;
    if !output.status.success() {
        return Err(CompileError::RunFailed {
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.trim().is_empty() {
        eprintln!("{}", stderr.trim());
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
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

/// Create a unique temporary file in the system temp directory.
fn temp_file(ext: &str) -> Result<PathBuf, CompileError> {
    let mut dir = std::env::temp_dir();
    let pid = std::process::id();
    loop {
        let counter = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let name = format!("ligare_{pid}_{counter}.{ext}");
        let path = dir.join(&name);
        if !path.exists() {
            return Ok(path);
        }
        if counter == u32::MAX {
            dir = std::env::current_dir().map_err(CompileError::Io)?;
        }
    }
}

/// RAII guard that deletes the temp file on drop (best-effort).
struct TempGuard(PathBuf);
impl Drop for TempGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
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
