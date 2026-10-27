# Evergreen

## Bootstrap implementation

The bootstrap compiler is written in Rust, with an internal verifier. See
[the bootstrap guide](docs/bootstrap.md) for commands, supported syntax, and
the current trust boundary. The remainder of this README is the original
language design sketch; not all of it is implemented yet.

`cargo run -- --deny-trust build examples/native.evg -o /tmp/answer` builds a
standalone Linux x86-64 executable for the supported verified subset. Without
`-o`, the output uses the last source file's path without `.evg`, so
`cargo run -- build examples/native.evg` produces `examples/native`.

Bundled stdlib dependencies load automatically. For byte output, try
`cargo run -- build examples/hello.evg -o /tmp/hello` and run `/tmp/hello`.
String literals are fixed byte arrays; see [literal semantics](docs/string-literals.md)
and `examples/string_bytes.evg` for Unicode, empty literals, and extent inference.

`cargo run -- run examples/raw_union.evg` exercises a source-defined optional
payload. `examples/raw_union_owner.evg` adds conditional owning pointers, and
`examples/raw_union_borrow.evg` demonstrates borrowed access and an exchange
contract using `old()`. [Raw-union notes](docs/raw-unions.md) describe active-type
proofs and the remaining limitations.

### Neovim support

Run `./scripts/install-nvim.sh` to install `.evg` highlighting, indentation, and
comment settings. See [the Neovim runtime documentation](editors/nvim/README.md)
for custom install locations and removal.

### Reading the compiler

| Responsibility | Code |
| --- | --- |
| Entry point and command handlers | [main.rs](src/main.rs), [cli](src/cli/mod.rs) |
| Shared syntax, parsing, and name resolution | [syntax.rs](src/syntax.rs), [syntax modules](src/syntax) |
| Symbolic verification and language rules | [compiler/verify.rs](src/compiler/verify.rs), [verification modules](src/compiler/verify) |
| Declaration and body verification passes | [verification orchestration](src/compiler/verify/program.rs) |
| State while checking a body | [verification context](src/compiler/verify/context.rs) |
| Small proof kernel and certificate replay | [compiler/kernel.rs](src/compiler/kernel.rs), [compiler/certificate.rs](src/compiler/certificate.rs) |
| Target scalar layout data | [targets/x86_64.evg](targets/x86_64.evg), [target decoder](src/shared/target.rs), [aggregate layout](src/compiler/layout.rs) |
| Native expression and statement emission | [compiler/native.rs](src/compiler/native.rs) |
| Function compilation and executable packaging | [program.rs](src/compiler/native/program.rs), [elf.rs](src/compiler/native/elf.rs) |
| Native call and cleanup dependencies | [order.rs](src/compiler/native/order.rs) |
| Executing a verified program | [interpreter](src/interpreter/mod.rs) |
| Shared plane model and ownership rules | [shared](src/shared/mod.rs) |

The interpreter accepts a `VerifiedProgram` produced by the compiler. The
compiler does not execute the interpreter. Shared code contains the generic
plane store, type ownership classification, and host worker utility; each side
keeps its own values and execution/checking logic.

Verifier and native regression tests live in their subsystem directories.
[tests/verification.rs](tests/verification.rs) exercises the CLI and optional
independent mathematical specifications.

Evergreen is a systems programming language, aimed to finally be a successor to
C and C++. Why have we failed so many times? Let's look at Rust for an example:

## Why Rust Will Never Take Over

Rust is an incredible language, don't get me wrong. But it will never replace
C/++. It is too inflexible. It makes too many assumptions about what good looks
like.

For example, consider references and mutable references. Mutable references are
*always* unique references. This allows the compiler to perform certain 
optimizations, sure. But it prevents the programmer from doing certain things
that should be totally allowed, a la:

```rs
fn vec_stuff(v: &mut Vec<Thing>) {
    let v1 = &mut v[1];
    let v2 = &mut v[2];
    v1.do_thing_with(v2);
}
```

This code is not allowed! There are a couple reasons for it:
- v1 and v2 are of the lifetime of their parent vec. Only 1 mutable reference
  is allowed per lifetime in Rust.
- The real reason is that we want to protect against:

```rs
fn vec_stuff2(v: &mut Vec<Thing>) {
    let v1 = &mut v[1];
    let v2 = &mut v[2];
    v.push(Thing::new());
    v1.do_thing_with(v2);
}
```

This, of course, shouldn't be allowed (at least under some circumstances)
because the push may invalidate v1 and v2. So how do we fix this?

## Evergreen

At a certain level evergreen is an incredibly simple language because it has 1
rule:

1. You may never misinterpret the type of a variable.

That's it. If your types check then your code is guaranteed to be safe. So how
do we get good behavior with only one rule? Let's take a look at how vec might
be implemented in Evergreen:

```evg
type Vec<T> struct {
    cap: isize,
    len: isize,
    data: linear_plane(T, len) | null where len == 0 <=> typeof(data) == null // compiler checks this is true at all times or code doesn't compile. if it can't easily check this it must be proven by the programmer
} where (pub fact len_at_most_cap = len <= cap; len_at_most_cap);

impl<T> Vec<T> {
    fn new() -> Self {
        Self{cap: 0, len: 0, data: null}
    }

    // code won't compile unless this is true.
    pub fact length_returns_len = self.length() == self.len;
    
    fn length() -> isize {
        // if we returned anything other than self.len here the above fact
        // would not be true and the code wouldn't compile.
        // probably need to think of some way to be able to prove these lean
        // style but that's up 2 u mr ai.
        self.len
    } where length_returns_len;
}

impl<T> Index<isize> for Vec<T> {
    fact index_in_range = index < self.length();

    fn index(&self, index: isize) -> T {
        fact index_less_than_len = 
            // lean style proof to combine Vec::length_returns_len and index_in_range. idk how to do that but you'll figure it out!!
        ; // we need to prove this because the built in linear plane type (which describes an array layout in memory) requires it to be true to call get
        // the footprint of linear_plane.get is:
        //
        // type linear_plane<T, Len: depends(const isize)> builtin; // depends == dependent types! types can depend on values! here we've said the value is const. which doesn't mean the value must be a constant it just means that if it changes then the linear plane is dropped/invalidated
        // impl<Len, T> linear_plane<Len, T> {
        //   fn get(&self, idx: isize) -> &T where idx < Len {...}
        //}
        self.data.get(index)
    } where index_in_range;

    // we could also provide a method that takes in a non-proven index but it'd
    // have to return an option.
}
```

I think you get it now. Some other thoughts:

- Memory model is in a tree of "planes". The stack is a tree. Each function is
  a node. Each variable is another node. If it's a struct then it's also a node.
  Down to the most atomic types, which are just the integers.
- `array(T, N)` is inline homogeneous storage with compile-time extent `N`.
  `linear_plane(T, n)` is a pointer to contiguous storage bounded by the runtime
  value `n`; the dependent type ties that pointer view to its length delineator.
- When a plane is dropped then anything in that plane is now not referencable 
  which fixes the vec problem from above, the type of anything in a dropped
  plane is never. So the variable's type changes.
- When a variable is moved out (i reassign a vec or smth) the old variable is
  of type shape(T) where T is the type that was moved out. You can upgrade it
  back to a T by assinging a T. Moving a shape(T) out of a plane drops it, but
  the drop method does nothing. There is no shape(shape(T)).
- I also wanted to bring up `patterns` which are like Rust enums but better.

```evg
type Option<T> pattern {
    None,
    Some(T)
}

// if we don't implement drop, we don't compile. raw union types (| syntax gives a raw union) cannot be dropped.
type MaybeNullPtr<T> = &T | null whre self == null <=> typeof(self) == null;

impl<T> Drop for MaybeNullPtr<T> {
    fn drop(self) {
        // looks a little silly. maybe we find way to make better
        if self != null {
            self.drop();
        } else {
            self.drop();
        }
    }
}

impl<T> Option<Self> with &T | null where self == null <=> typeof(self) == null { // type unions don't represent tagged unions, they're untagged. types must be non-overlapping. But by the rule of evg we must have some way to distinguish between them by looking at the value. They can also not be dropped, user must implement drop for raw unions.
    fn make_None() -> &T | null {
        null
    }

    fn make_Some(t: &T) -> &T | null {
        t
    }

    // i think u get the pt
}

// by default we use a Rust-enum implementation. But in evg that looks like:

type OptionImpl<T> struct {
    payload: never | T,
    is_some: bool where is_some <=> typeof(payload) == T
}
```

Some things I haven't figured out are doing updates. Like to the above OptionImpl
there will be some loc where you set payload and another where is_some is set.
In that brief moment the invariant is technically not held. We must figure this out.
I think we could do this by allowing assingment for the whole struct at once.
Similar problem for RC type:


```evg
type RCPayload<T> struct {
    data: T,
    count: isize
}

type RC<T> struct {
    data: lone_plane(RCPayload<T>) 
} where pointees(data) == data.count
```

But you can figure that out perhaps.
