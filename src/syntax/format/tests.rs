use super::*;

#[test]
fn owner_start_blocks_indent_the_write_and_preserve_following_proofs() {
    let input = "fn clone() { starts_owner(self.data) { self.data.count=self.data.count+1; } proof accurate: nat(self.data.count)==owner_count(self.data); Self { data:self.data } }";
    let formatted = source(input).unwrap();
    assert!(formatted.contains("    starts_owner(self.data) {\n        self.data.count = self.data.count + 1;\n    }\n    proof accurate:"), "{formatted}");
    assert_eq!(source(&formatted).unwrap(), formatted);
    assert!(super::super::parse(&formatted).is_ok());
}

#[test]
fn contracts_have_indented_keywords_and_trailing_conjunctions() {
    let input = "fn reserve(x: &usize) -> usize where *x < usize::MAX && *x > 0 modifies(x) ensures result == old(*x) { *x }";
    let expected = "fn reserve(x: &usize) -> usize\n    where\n        *x < usize::MAX &&\n        *x > 0\n    modifies(x)\n    ensures\n        result == old(*x)\n{\n    *x\n}\n";
    assert_eq!(source(input).unwrap(), expected);
    assert_eq!(source(expected).unwrap(), expected);
}

#[test]
fn concrete_literals_comments_and_distinct_operators_survive() {
    let input = "// leading λ\nfn main(){let text=\"// 🦀 \\\" \\n\"; // trailing\nlet p=& &text;\n// final\n0}";
    let formatted = source(input).unwrap();
    assert!(formatted.contains("\"// 🦀 \\\" \\n\""));
    assert!(formatted.contains("// trailing\n"));
    assert!(formatted.contains("& &text"));
    assert_eq!(source(&formatted).unwrap(), formatted);
}

#[test]
fn conditional_contracts_and_generic_receiver_patterns_are_stable() {
    for input in [
        "type R struct {v: usize} impl Drop for R {fn drop({v}) ensures if old(self.v)>0 {true} else {true} {}}",
        "type Pair<T> struct {a:T,b:T} impl<T> Drop for Pair<T> {fn drop({a,b}) {}}",
        "fn max(a: &usize,b: &usize)->&usize borrows(a) when *a>=*b else borrows(b) ensures *result>=*a && *result>=*b {if *a>=*b {a} else {b}}",
        "type A struct {v:[usize;10]} where (fact ok = true; ok); fn main(){0}",
        "fn test(x:usize) ensures forall(i: integer) where(i>=0) {i>=0} {0}",
    ] {
        let formatted = source(input).unwrap();
        assert_eq!(source(&formatted).unwrap(), formatted, "{input}");
        assert!(super::super::parse(&formatted).is_ok(), "{formatted}");
    }
}

#[test]
fn bundled_sources_format_idempotently() {
    fn visit(path: &std::path::Path) {
        for entry in std::fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(&path);
            } else if path.extension().is_some_and(|ext| ext == "evg") {
                let original = std::fs::read_to_string(&path).unwrap();
                let formatted =
                    source(&original).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
                assert_eq!(source(&formatted).unwrap(), formatted, "{}", path.display());
                if super::super::parse(&original).is_ok() {
                    assert!(
                        super::super::parse(&formatted).is_ok(),
                        "{}",
                        path.display()
                    );
                }
            }
        }
    }
    for dir in ["stdlib", "targets", "examples", "proofs"] {
        visit(std::path::Path::new(dir));
    }
}

#[test]
fn loop_contracts_follow_the_same_layout_as_function_contracts() {
    let input = "fn main() {let n:usize=0; while n<10 invariant n<=10 modifies(&n) decreases 10-n {n=n+1;} n}";
    let formatted = source(input).unwrap();
    assert!(formatted.contains("while n < 10\n        invariant\n            n <= 10\n        modifies(&n)\n        decreases 10 - n\n    {"), "{formatted}");
    assert_eq!(source(&formatted).unwrap(), formatted);
    assert!(super::super::parse(&formatted).is_ok());
}

#[test]
fn generic_reference_type_observations_keep_angle_and_reference_spacing() {
    let source = "type Pair<T> struct {value:T} fn main(){let pair=Pair::<usize>{value:42};let view=&pair;proof _:typeof(view)==&Pair<usize>;}";
    let formatted = super::source(source).unwrap();
    assert!(
        formatted.contains("typeof(view) == &Pair<usize>"),
        "{formatted}"
    );
    assert_eq!(super::source(&formatted).unwrap(), formatted);
    let indirect =
        super::source("fn f(x: &&Pair<usize>) {proof _: typeof(x) == &&Pair<usize>;}").unwrap();
    assert!(indirect.contains("x: &&Pair<usize>"), "{indirect}");
    assert!(
        indirect.contains("typeof(x) == &&Pair<usize>"),
        "{indirect}"
    );
}

#[test]
fn long_proofs_indent_quantifiers_and_each_domain_clause() {
    let input = "fn check() {proof initialized: forall(i: integer) where (0 <= i && i < integer::from(length) && i < integer::from(capacity)) {typeof((*data)[i]) == T} by {assumption};}";
    let expected = "fn check() {\n    proof initialized:\n        forall(i: integer)\n        where (\n            0 <= i &&\n            i < integer::from(length) &&\n            i < integer::from(capacity)\n        ) {typeof((*data)[i]) == T} by {assumption};\n}\n";
    assert_eq!(source(input).unwrap(), expected);
    assert_eq!(source(expected).unwrap(), expected);
}

#[test]
fn proof_continuations_keep_comments_nested_groups_and_following_statements() {
    for input in [
        "fn check() {proof frame: (forall(i: integer) where(0 <= i && i < integer::from(length)) {typeof(old(*data)[i]) == T}) => (forall(i: integer) where(0 <= i && i < integer::from(length) - 1) {typeof((*data)[i]) == T}) by {intro prior; intro i; omega}; let after: usize = 42;}",
        "fn check() {proof initialized: forall(i: integer) where(0 <= i && // lower bound\ni < integer::from(length) && i < integer::from(capacity)) {typeof((*data)[i]) == T} by {assumption}; // named witness\nlet after: usize = 42;}",
        "fn check() {proof forall(i: integer) where(0 <= i && i < integer::from(length) && i < integer::from(capacity)) {i == i} by {intro i; omega}; let after: usize = 42;}",
    ] {
        let formatted = source(input).unwrap();
        assert!(formatted.contains("\n    let after: usize = 42;\n}"), "{formatted}");
        assert_eq!(source(&formatted).unwrap(), formatted);
        assert!(super::super::parse(&formatted).is_ok(), "{formatted}");
    }
    let short = source("fn check(x: usize) {proof _: x == x;}").unwrap();
    assert!(short.contains("    proof _: x == x;"), "{short}");
}
