//! Publish completed artifacts atomically without overwriting source inputs.

use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

pub(super) fn write_text(path: &Path, content: &str, inputs: &[PathBuf]) -> Result<(), String> {
    write_bytes(path, content.as_bytes(), inputs, Mode::Text)
}

pub(super) fn write_binary(path: &Path, content: &[u8], inputs: &[PathBuf]) -> Result<(), String> {
    write_bytes(path, content, inputs, Mode::Text)
}

pub(super) fn write_executable(
    path: &Path,
    content: &[u8],
    inputs: &[PathBuf],
) -> Result<(), String> {
    write_bytes(path, content, inputs, Mode::Executable)
}

pub(super) fn replace_source(path: &Path, content: &str) -> Result<(), String> {
    write_bytes(path, content.as_bytes(), &[], Mode::Source)
}

enum Mode {
    Text,
    Executable,
    Source,
}

fn write_bytes(path: &Path, content: &[u8], inputs: &[PathBuf], mode: Mode) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let name = path.file_name().ok_or("output must be a file path")?;
    let parent = parent.canonicalize().map_err(|e| e.to_string())?;
    let destination = path.canonicalize().unwrap_or_else(|_| parent.join(name));
    for input in inputs {
        if input.canonicalize().map_err(|e| e.to_string())? == destination {
            return Err("output must not overwrite a source input".into());
        }
    }
    let temp = parent.join(format!(".evg-output-{}.tmp", super::temporary_id()?));
    let result = (|| {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)
            .map_err(|e| e.to_string())?;
        file.write_all(content).map_err(|e| e.to_string())?;
        if matches!(mode, Mode::Source) {
            let metadata = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
            if !metadata.is_file() {
                return Err("format input must be a regular file".into());
            }
            file.set_permissions(metadata.permissions())
                .map_err(|e| e.to_string())?;
        }
        if matches!(mode, Mode::Executable) {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(fs::Permissions::from_mode(0o755))
                    .map_err(|e| e.to_string())?;
            }

            #[cfg(not(unix))]
            return Err("native executable output currently requires a Unix host".into());
        }
        file.sync_all().map_err(|e| e.to_string())?;
        fs::rename(&temp, path).map_err(|e| e.to_string())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result
}
