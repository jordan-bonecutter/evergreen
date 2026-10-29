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
  options: `type Option<T> struct {
	data: T | shape(T),
	ok: bool
} where (
	fact ok_iff_presence = self.ok <=> typeof(self.data) == T;
	ok_iff_presence
);

fn consume<T>(t: T) {}

impl<T> Option<T> {
	fn some(t: T) -> Self {
		Self {data: t, ok: true}
	}

	fn none(t: T) -> Self {
		Self {ok: false}
	}

	method or_else(t: T) -> T {
        let Self{data, ok} = self;
		if ok {
            data
		} else {
            consume::<shape(T)>(data);
            t
        }
	}
}

impl<T> Drop for Option<T> {
	fn drop({data, ok}) {
		if ok {
			consume::<T>(data);
		} else {
			consume::<shape(T)>(data);
		}
	}
}

fn main() -> usize {
	let x = Option::<usize>::some(10);
	x.or_else(0)
}

`,
};
