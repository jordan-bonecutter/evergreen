//! Static type layout observations shared by verification and execution.
//! Layout numbers confer no reference or allocation authority.

use super::*;

pub(crate) fn value(
    name: &str,
    arguments: &[Expr],
    structs: &BTreeMap<String, Struct>,
) -> Result<usize> {
    value_for(TargetKind::X86_64, name, arguments, structs)
}

pub(crate) fn value_for(
    target: TargetKind,
    name: &str,
    arguments: &[Expr],
    structs: &BTreeMap<String, Struct>,
) -> Result<usize> {
    let [argument] = arguments else {
        return Err(format!("{name} requires one type argument"));
    };
    let ty = argument
        .literal_type_for(target.word_bits())
        .ok_or("layout queries require a type")?;
    let layout = storage_for(target, &ty, structs)?;
    match name {
        "size_of" => Ok(layout.size),
        "align_of" => Ok(layout.align),
        _ => Err("unknown layout query".into()),
    }
}

#[cfg(test)]
mod tests {
    use crate::compiler::verify::{prove, verify, verify_with_certificate};

    #[test]
    fn layout_queries_measure_targets_and_large_types_without_expansion() {
        for source in [
            "fn main() -> usize {proof _: size_of(u8) == 1 && size_of(usize) == 8 && size_of([u16; 3]) == 6 && size_of(unique([u8; 1000000000])) == 8; 42}",
            "type Pair struct {byte: u8, word: u16} fn main() -> usize {proof _: size_of(Pair) == 4 && align_of(Pair) == 2 && size_of(shape(Pair)) == 4; 42}",
            "type Huge struct {data: [u8; 1000000000], tag: usize} fn main() -> usize {proof _: size_of(Huge) == 1000000008 && align_of(Huge) == 8; 42}",
            "fn bytes<T>(count: usize) -> usize where integer(count) * integer(size_of(T)) <= integer(isize::MAX) ensures result == count * size_of(T) {count * size_of(T)} fn main() -> usize {proof _: size_of([u8; 1000000000]) == 1000000000; bytes::<u16>(21)}",
            "fn main() -> usize {proof _: old(size_of(u8)) == size_of(u8); 42}",
            include_str!("../../../examples/layout_queries.evg"),
        ] {
            let (checked, certificate) = prove(source).unwrap_or_else(|error| panic!("{error}: {source}"));
            assert_eq!(checked.run().unwrap().to_string(), "42", "{source}");
            assert!(checked.trusted_assumptions().is_empty());
            assert_eq!(verify_with_certificate(source, &certificate).unwrap().proof_search_count(), 0);
        }
    }

    #[test]
    fn layout_bounds_preserve_quantified_contract_dependencies() {
        let source = r#"fn observe<T>(N: usize, data: &[T | shape(T); N], length: usize)
where length <= N && integer(N) * integer(size_of(T)) <= integer(isize::MAX) &&
(forall(i: integer) where (0 <= i && i < integer(length) && i < integer(N)) {typeof((*data)[i]) == T})
{
proof initialized: forall(i: integer) where (0 <= i && i < integer(length) && i < integer(N)) {typeof((*data)[i]) == T} by {assumption};
if length > 0 { let first: &T = &(*data)[0]; }
}
fn main() -> usize {
let data: unique(unique(usize) | shape(unique(usize)), 1) = alloc(1, shape(unique(usize)));
(*data)[0] = alloc(42);
observe::<unique(usize)>(1, &*data, 1);
let value: unique(usize) = move((*data)[0]);
arrays::release_empty::<unique(usize)>(data);
*value
}
"#;
        for query in ["size_of", "align_of"] {
            let source = source.replace("size_of", query);
            let (program, certificate) = prove(&source).unwrap();
            assert!(program.trusted_assumptions().is_empty());
            assert_eq!(program.run().unwrap().to_string(), "42");
            assert_eq!(
                verify_with_certificate(&source, &certificate)
                    .unwrap()
                    .proof_search_count(),
                0
            );
            // Layout facts do not establish any element's active member.
            let vacant = source.replace("(*data)[0] = alloc(42);", "");
            assert!(verify(&vacant).is_err());
        }
    }

    #[test]
    fn invalid_layout_types_bounds_and_effects_are_rejected() {
        let tick =
            "fn tick(n: &usize) -> usize where *n < usize::MAX modifies(n) { *n = *n + 1; *n }";
        let runtime = format!("{tick} fn main() -> usize {{let n: usize = 0; tick(&n)}}");
        assert_eq!(verify(&runtime).unwrap().run().unwrap().to_string(), "1");
        let erased = format!(
            "{tick} fn main() -> usize {{let n: usize = 0; size_of(unique(u8, tick(&n)))}}"
        );
        assert!(verify(&erased)
            .unwrap_err()
            .contains("modifying calls are forbidden in proof expressions"));
        for source in [
            "fn main() -> usize {size_of(integer)}",
            "fn main() -> usize {align_of(Unknown)}",
            "fn main() -> usize {size_of([u64; usize::MAX])}",
            "fn main() -> usize {size_of([u8; -1])}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
    }
}
