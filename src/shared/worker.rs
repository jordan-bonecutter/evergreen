//! Run recursive operations on a worker thread with a 16 MiB stack.
//! This keeps stack capacity consistent across CLI, tests, and library callers.
//! Each operation still enforces its own recursion-depth and work limits.

pub(crate) fn run<T: Send>(
    name: &str,
    operation: impl FnOnce() -> Result<T, String> + Send,
) -> Result<T, String> {
    // Browser callers already run in a Web Worker. wasm32-unknown-unknown
    // cannot spawn OS threads; its linker reserves the equivalent stack.
    #[cfg(target_arch = "wasm32")]
    {
        let _ = name;
        operation()
    }
    #[cfg(not(target_arch = "wasm32"))]
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name(name.into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, operation)
            .map_err(|error| format!("cannot start {name}: {error}"))?
            .join()
            .map_err(|_| format!("{name} panicked"))?
    })
}
