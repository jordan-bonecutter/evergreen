# Concrete generic specialization

Records and free functions accept type and const parameters using angle brackets.
Each used instance becomes ordinary concrete syntax and goes through the existing
type, ownership, effect, arithmetic, and proof checks. Unused templates are not
certified universal theorems. A bad instance fails even if another instance passed.

```evg
type Buffer<T, const N: usize> struct {data: array(T, N)}

fn get<T, const N: usize>(buffer: &Buffer<T, N>, index: usize) -> T
where index < N {
    buffer.data[index]
}

fn main() -> usize {
    let buffer = Buffer::<usize, 3> {data: [7, 42, 9]};
    get::<usize, 3>(&buffer, 1)
}
```

Use `Buffer<usize, 3>` in types and `Buffer::<usize, 3>` or `get::<usize, 3>`
in expressions. Explicit arguments are required unless the declaration supplies
trailing defaults, such as `fn identity<T = usize>(value: T) -> T {value}`.
Nested applications and module qualification work. Type parameters can appear in
refinements as ideal type values: `ensures (typeof(result) == T)`.

Const parameters currently use machine integers or `bool`. Arguments are closed
compile-time values; compound arithmetic uses braces, for example
`get::<usize, {1 + 2}>(...)`. Every arithmetic intermediate must fit the declared
machine type. Runtime values cannot become const arguments. Runtime-dependent
borrowed extents still use `linear_plane(T, n)`.

Specialization keys use resolved scalar identities, closed array extents, and
canonical const values. Repeated instances reuse one declaration. Template body
copies, substituted type trees, and expansion depth have checked work limits.
Declaring a billion-element array does not create a billion specialization nodes.
Certificates bind the original source and loaded library sources; replay checks
the same concrete obligations without repeating proof search.

Generic impl blocks provide associated functions, methods, Drop, and Copy.
An implementation uses a complete parameter pattern:

```evg
impl<T, const N: usize> Buffer<T, N> {
    fn new(data: array(T, N)) -> Self {Self {data: data}}

    method& get(index: usize) -> &T
    where index < N
    borrows(&self.data[index]) {&self.data[index]}
}
```

`Self` names the concrete instance. Call an associated function with
`Buffer::<usize, 3>::new(...)`. A consuming method can use a complete `Self`
pattern. A free generic function can use `let Buffer::<T, N> {data} = value;`.
An impl must be in the type's defining module and bind each record parameter
exactly once; parameter renaming and reordering are allowed.

Method bodies instantiate only when called. An unused method with a growing
generic return type does not recursively expand more instances. Frontend
signature prototypes help resolve calls, then are discarded; they never provide
proof assumptions. Drop is instantiated with the record and checked normally.
An explicit generic Copy implementation still needs Copy fields and must
preserve refinements under shared-pointer census changes.

Method-level generic parameters, trait bounds, specialized impl patterns, and
argument inference remain unfinished. [Rc](rc.md) now uses generic payloads;
[Vec](vec.md) specializes initialized backing storage and scalar copy operations.
Move-only vector elements still need initialization and consumption proofs. Arrays still
use their existing layout rule; replacing it with a source const-generic
definition using `make_type` remains future work.

`size_of(T)` and `align_of(T)` return target-derived `usize` values in runtime
expressions and specifications. Their operand uses type syntax, including generic
instances, arrays, and pointer types. Ideal mathematical types have no storage
layout. Inspecting a type neither allocates storage nor grants ownership.

A generic allocation bound can use
`integer(count) * integer(size_of(T)) <= integer(isize::MAX)` rather than assuming
an element width. Array layout uses checked multiplication, so measuring a
billion-element array does not visit its elements. A layout must fit the target's
addressable object range. This observation does not increase the backend's
separate budget for inline values. Dependent type bounds are checked as
specifications and cannot execute runtime effects.

See [layout_queries.evg](../examples/layout_queries.evg) for generic byte counts,
record padding, and large-array layout observations.

The example runs with:

```sh
cargo run --locked --offline -- run examples/generics.evg
cargo run --locked --offline -- build examples/generics.evg
```

Reference type observations use the same angle syntax as annotations:
`proof _: typeof(view) == &Pair<usize>;`. Nested and qualified forms such as
`&&pairs::Pair<[usize; 2]>` work too. Expression calls and constructors still use
`Pair::<usize>::new(...)` and `Pair::<usize> {...}`. A type proof does not change
an expression's static type or restore access to a dropped plane. See
[`examples/rc_generic_view.evg`](../examples/rc_generic_view.evg).
