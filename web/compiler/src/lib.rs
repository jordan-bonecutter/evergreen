//! Small, dependency-free browser ABI. The input and output buffers belong to
//! this instance; JS reacquires views after calls that can grow Wasm memory.

use evergreen::{
    compiler::{verify::verify, wasm},
    syntax::Type,
};
use std::cell::RefCell;

const MAX_SOURCE: usize = 100_000;

#[derive(Default)]
struct Buffers {
    source: Vec<u8>,
    metadata: Vec<u8>,
    module: Vec<u8>,
}

thread_local! { static BUFFERS: RefCell<Buffers> = RefCell::new(Buffers::default()); }

fn quote(text: &str) -> String {
    let mut output = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            ch if ch < ' ' => output.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => output.push(ch),
        }
    }
    output.push('"');
    output
}

fn compile(source: &str) -> (String, Vec<u8>) {
    let program = match verify(source) {
        Ok(program) => program,
        Err(error) => {
            return (
                format!(
                    "{{\"ok\":false,\"stage\":\"verify\",\"error\":{}}}",
                    quote(&error)
                ),
                Vec::new(),
            )
        }
    };
    let module = match wasm::emit(&program) {
        Ok(module) => module,
        Err(error) => {
            return (
                format!(
                    "{{\"ok\":false,\"stage\":\"compile\",\"error\":{}}}",
                    quote(&error)
                ),
                Vec::new(),
            )
        }
    };
    let result_kind = match program.entry_result_type() {
        Some(Type::Machine(integer)) if integer.signed => "signed",
        Some(Type::Machine(_)) => "unsigned",
        Some(Type::Bool) => "bool",
        _ => "unit",
    };
    let assumptions = program
        .trusted_assumptions()
        .iter()
        .map(|item| format!("{{\"line\":{},\"goal\":{}}}", item.line, quote(&item.goal)))
        .collect::<Vec<_>>()
        .join(",");
    (
        format!(
            "{{\"ok\":true,\"obligations\":{},\"resultKind\":{},\"assumptions\":[{}]}}",
            program.obligations,
            quote(result_kind),
            assumptions
        ),
        module,
    )
}

/// Resize the instance's UTF-8 input buffer and return its writable address.
/// Zero means the size exceeds the playground limit.
#[no_mangle]
pub extern "C" fn evg_source_resize(length: u32) -> *mut u8 {
    if length as usize > MAX_SOURCE {
        return std::ptr::null_mut();
    }
    BUFFERS.with_borrow_mut(|buffers| {
        buffers.source.resize(length as usize, 0);
        buffers.source.as_mut_ptr()
    })
}

/// Compile input, replacing both output buffers (including after failures).
#[no_mangle]
pub extern "C" fn evg_compile() {
    BUFFERS.with_borrow_mut(|buffers| {
        let (metadata, module) = match std::str::from_utf8(&buffers.source) {
            Ok(source) => compile(source),
            Err(_) => (
                "{\"ok\":false,\"stage\":\"verify\",\"error\":\"Source must be valid UTF-8\"}"
                    .into(),
                Vec::new(),
            ),
        };
        buffers.metadata = metadata.into_bytes();
        buffers.module = module;
    });
}

#[no_mangle]
pub extern "C" fn evg_metadata_ptr() -> *const u8 {
    BUFFERS.with_borrow(|buffers| buffers.metadata.as_ptr())
}
#[no_mangle]
pub extern "C" fn evg_metadata_len() -> u32 {
    BUFFERS.with_borrow(|buffers| buffers.metadata.len() as u32)
}
#[no_mangle]
pub extern "C" fn evg_module_ptr() -> *const u8 {
    BUFFERS.with_borrow(|buffers| buffers.module.as_ptr())
}
#[no_mangle]
pub extern "C" fn evg_module_len() -> u32 {
    BUFFERS.with_borrow(|buffers| buffers.module.len() as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiler_returns_metadata_and_real_wasm_and_clears_failed_outputs() {
        let (metadata, module) = compile(include_str!("../../../examples/console.evg"));
        assert!(metadata.contains("\"ok\":true"), "{metadata}");
        assert!(metadata.contains("external contract for console::print"));
        assert_eq!(&module[..4], b"\0asm");
        let (metadata, module) = compile("fn main() -> usize {usize::MAX + 1}");
        assert!(metadata.contains("\"ok\":false"));
        assert!(module.is_empty());
        assert_eq!(quote("\"\\\n\0"), "\"\\\"\\\\\\n\\u0000\"");
        assert!(evg_source_resize(100_001).is_null());
    }
}
