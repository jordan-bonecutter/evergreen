# Source-defined Option

`option::Option<T>` stores `T | shape(T)` and a Boolean `ok` field. Its invariant
is exactly `self.ok <=> typeof(self.data) == T`. Neither the type nor its tag
handling is built into the compiler.

```evg
fn main() -> usize {
    let value = option::Option::<usize>::some(42);
    value.unwrap()
}
```

- `some(value)` moves the payload into the option and proves `result.ok`.
- `none()` constructs vacant storage and proves `!result.ok`.
- `is_some()` returns the tag with a checked equality guarantee.
- `get()` borrows the payload; its precondition requires presence.
- `take()` moves the current option out through a reference and leaves it empty.
  Its contract proves the returned tag equals the old tag. Taking an empty option
  returns another empty option.
- `unwrap()` consumes a known-present option and returns its payload.
- `unwrap_or(fallback)` consumes the option and returns its payload or fallback.
  The unused fallback is dropped normally, including when it owns an allocation.

Drop destructures the option immediately. A populated option consumes and drops
its payload; an empty option consumes only its vacant shape. The type is not
Copy. Its fields are visible, as in the original sketch; ordinary invariant
checks still reject inconsistent updates.

See [the owning example](../examples/option.evg). This initial API does not yet
provide replacement, map, or pattern-specific conveniences.

Consuming methods destructure their receiver explicitly in the body:

```evg
method or_else(fallback: T) -> T {
    let Self {data, ok} = self;
    if ok {
        let value: T = data;
        value
    } else {
        let vacant: shape(T) = data;
        fallback
    }
}
```

Destructuring consumes the container, so its destructor does not run again.
Each extracted field remains subject to normal ownership and cleanup checks.
Receiver patterns in parameter lists remain available for `fn drop({data, ok})`;
ordinary methods use the explicit statement above.
