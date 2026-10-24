//! Give recursive bootstrap passes a fixed stack independently of their caller.
//! Semantic depth and work limits remain mandatory; this is not a resource proof.
pub(crate) fn run<T: Send>(
    name: &str,
    operation: impl FnOnce() -> Result<T, String> + Send,
) -> Result<T, String> {
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
