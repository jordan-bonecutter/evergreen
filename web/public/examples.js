export const examples = {
  hello: `fn main() {
    console::println(&"Hello, Evergreen!");
}
`,
  nonzero: `type NonZero struct {data: usize} where data != 0;

impl NonZero {
    fn new(x: usize) -> Self
        where x != 0
    {
        return NonZero {data: x};
    }
}

fn main() -> usize {
    let my_nonzero = NonZero::new(10);
    0
}
`,
  error: `// Try a smaller input to satisfy the precondition.
fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result == n + 1
{
    n + 1
}

fn main() -> usize {
    increment(usize::MAX)
}
`,
};
