// Each solution is checked by the real browser compiler in the test suite.
export const lessons = [
  {
    id: "hello",
    title: "Hello, Evergreen",
    topic: "The basics",
    minutes: "1 min",
    introduction: "Every program starts at `main`. `console::println` writes a line of text. The `&` borrows the string for the call, and a semicolon finishes the statement.",
    goal: "Make the program print Hello, Evergreen! on its own line.",
    expected: {
  "output": "Hello, Evergreen!\n",
  "result": "()"
},
    hints: [
  "Put text inside double quotes.",
  "Replace the empty string with \"Hello, Evergreen!\". Keep the & and the semicolon."
],
    takeaway: "You just compiled Evergreen to WebAssembly and ran it in your browser. main returns unit, written (), when it has no return value.",
    starter: `fn main() {
    console::println(&"");
}
`,
    solution: `fn main() {
    console::println(&"Hello, Evergreen!");
}
`
  },
  {
    id: "values",
    title: "Values & expressions",
    topic: "The basics",
    minutes: "2 min",
    introduction: "`let` binds a value, and `: usize` gives it an unsigned machine integer type. The last expression in a function is its return value when it has no semicolon.",
    goal: "Use the two bindings to return 42 from main. Replace the final 0 with an addition.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "Add base and extra with +.",
  "The final line should be base + extra, without a semicolon. A semicolon would discard the value."
],
    takeaway: "Functions declare their return type with ->. On this browser target, usize is a 32-bit unsigned integer.",
    starter: `fn main() -> usize {
    let base: usize = 40;
    let extra: usize = 2;
    // Return the sum.
    0
}
`,
    solution: `fn main() -> usize {
    let base: usize = 40;
    let extra: usize = 2;
    base + extra
}
`
  },
  {
    id: "contracts",
    title: "Promises at the boundary",
    topic: "Contracts",
    minutes: "2 min",
    introduction: "`where` is a precondition: the caller must establish it. `ensures` is a postcondition: the function must establish it. Here, the input bound makes adding one exact instead of potentially overflowing.",
    goal: "Run the starter to see the failed precondition. Then change only the call in main so increment returns 42.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "usize::MAX is the largest usize, so it cannot satisfy n < usize::MAX.",
  "Call increment(41). Its precondition holds, and its result is 42."
],
    takeaway: "The caller proves where; the implementation proves ensures. A precondition failure stops compilation before any program runs.",
    starter: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result == n + 1
{
    n + 1
}

fn main() -> usize {
    increment(usize::MAX)
}
`,
    solution: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result == n + 1
{
    n + 1
}

fn main() -> usize {
    increment(41)
}
`
  },
  {
    id: "invariants",
    title: "A type with a rule",
    topic: "Invariants",
    minutes: "2 min",
    introduction: "`type NonZero usize where self != 0;` gives a name and an invariant to a `usize`. Here, `self` is the integer itself. Constructing `NonZero(value)` requires the compiler to prove that the value is nonzero. There is no wrapper field to read.",
    goal: "Construct a valid `NonZero` with the value 42, then return it. Keep the invariant intact.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "The starter constructs `NonZero(0)`, but zero violates `self != 0`.",
  "Change the construction to `NonZero(42)`. You can use the result directly as an integer."
],
    takeaway: "`NonZero` has the representation and arithmetic of `usize`, with the extra rule that its value cannot be zero. Every explicit construction must establish that rule.",
    starter: `type NonZero usize where self != 0;

fn main() -> usize {
    let answer = NonZero(0);
    answer
}
`,
    solution: `type NonZero usize where self != 0;

fn main() -> usize {
    let answer = NonZero(42);
    answer
}
`,
    revision: 2
  },
  {
    id: "overflow",
    title: "Machine numbers & ideal integers",
    introduction: "A `u8` holds values from 0 to 255. Adding 250 and 10 has the mathematical answer 260, which does not fit. Evergreen allows the machine addition, but its overflow result is unspecified: you cannot rely on it wrapping to 4. The ideal type `integer` represents mathematical integers without machine overflow. `integer::from(value)` gives the mathematical view of a value; convert each operand before adding. An `ideal let` binding exists only for checking, is erased from the executable, and cannot supply a runtime result.",
    goal: "Run the starter: the supplied `proof fits` check fails because the mathematical sum exceeds 255. Change only `right` so the sum is exactly 255 and both supplied checks pass. You do not need to write any proof steps yet.",
    expected: { output: "", result: "255" },
    hints: [
      "The code computes the sum twice: `machine_sum` uses `u8` arithmetic, while `exact_sum` uses ideal `integer` arithmetic. The supplied checks connect them when the sum fits.",
      "There is room for 5 above 250 before reaching `u8::MAX`.",
      "Change `let right: u8 = 10;` to `let right: u8 = 5;`. Keep the ideal binding and both supplied checks."
    ],
    takeaway: "`proof fits` is a compile-time check, not a runtime assertion. `integer::from(left) + integer::from(right)` describes the exact mathematical sum. Converting `machine_sum` afterward cannot recover an already overflowing result. Next, see how a runtime check lets you safely use an observed result even when the addition overflows.",
    starter: `fn main() -> u8 {
    let left: u8 = 250;
    let right: u8 = 10;
    let machine_sum: u8 = left + right;

    // A mathematical sum, erased after checking.
    ideal let exact_sum: integer =
        integer::from(left) + integer::from(right);

    // These compile-time checks are supplied for you.
    proof fits: exact_sum <= integer::from(u8::MAX);
    proof agrees: integer::from(machine_sum) == exact_sum;

    machine_sum
}
`,
    solution: `fn main() -> u8 {
    let left: u8 = 250;
    let right: u8 = 5;
    let machine_sum: u8 = left + right;

    // A mathematical sum, erased after checking.
    ideal let exact_sum: integer =
        integer::from(left) + integer::from(right);

    // These compile-time checks are supplied for you.
    proof fits: exact_sum <= integer::from(u8::MAX);
    proof agrees: integer::from(machine_sum) == exact_sum;

    machine_sum
}
`
  },
  {
    id: "observed-overflow",
    title: "Overflow, then inspect",
    revision: 2,
    introduction: "Overflow itself is allowed. Here, `250 + 10` cannot fit in a `u8`, but the result is still a valid `u8`. Store it once in `candidate`. The runtime condition `if candidate < 10` inspects that actual value. Inside its true branch, the compiler can use the condition to establish `accept_small`’s precondition. The other branch handles values that do not qualify. No particular overflow result or wrapping behavior is assumed.",
    goal: "Check at runtime whether `candidate` is safe to pass into `accept_small`. Add an `if` that calls it only when `candidate < 10`; otherwise print the skip message and return 42. Keep the overflowing addition and `accept_small`’s precondition. The starter fails verification until the call is guarded.",
    expected: {
      outputs: ["Accepted: the observed value is below 10.\n", "Skipped: the observed value is 10 or greater.\n"],
      result: "42"
    },
    hints: [
      "`accept_small` requires its argument to be below 10. Test that condition on the stored `candidate` before making the call.",
      "Use `if candidate < 10 { accept_small(candidate) } else { ... }`. Only the true branch gets to rely on `candidate < 10`.",
      "In the `else` branch, call `console::println(&\"Skipped: the observed value is 10 or greater.\");` and finish with `42` without a semicolon."
    ],
    takeaway: "An unspecified value can be inspected and used once its actual value satisfies the requirements. This is defined, typed behavior, rather than C-style undefined behavior. You cannot infer `candidate == 4` just because an implementation currently wraps that way. The branch proves a property of this stored result; it does not prove that the original mathematical sum fit or that another overflowing evaluation would give the same value.",
    starter: `fn accept_small(value: u8) -> usize
    where value < 10
{
    console::println(&"Accepted: the observed value is below 10.");
    42
}

fn main() -> usize {
    // This overflows u8. Its value is unspecified, but is still a u8.
    let candidate: u8 = 250 + 10;

    // TODO: check the observed value at runtime before this call.
    accept_small(candidate)
}
`,
    solution: `fn accept_small(value: u8) -> usize
    where value < 10
{
    console::println(&"Accepted: the observed value is below 10.");
    42
}

fn main() -> usize {
    // This overflows u8. Its value is unspecified, but is still a u8.
    let candidate: u8 = 250 + 10;

    // Check the stored result, not the mathematical sum.
    if candidate < 10 {
        // The true branch establishes accept_small's precondition.
        accept_small(candidate)
    } else {
        console::println(&"Skipped: the observed value is 10 or greater.");
        42
    }
}
`
  },
  {
    id: "nonzero-add",
    revision: 2,
    title: "Keep the sum nonzero",
    introduction: "An `impl NonZero` block defines operations on the type. `method add(other: Self) -> Self` receives the value you call it on as `self`; `Self` means `NonZero` here. The body is already written, but it cannot compile: even two positive machine integers can overflow. An unspecified overflow result cannot be proved nonzero. Use the exact `integer::from` sum from the earlier overflow example to describe when the machine sum fits.",
    goal: "Run the starter to see the failed invariant. Add a `where` clause to `.add` that bounds the mathematical sum by `usize::MAX`. Keep the body and the call in `main`.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "You already used `where` to restrict inputs. Both operands are nonzero; what is missing is a guarantee that their sum fits in `usize`.",
  "Convert each operand before adding: `integer::from(self) + integer::from(other)`. Compare that sum with `integer::from(usize::MAX)`.",
  "Add `where integer::from(self) + integer::from(other) <= integer::from(usize::MAX)` between the return type and the opening brace."
],
    takeaway: "The type invariant describes valid values. The method precondition describes when an operation can preserve that invariant. With no overflow and both operands positive, their sum is nonzero.",
    starter: `type NonZero usize where self != 0;
impl NonZero {
    method add(other: Self) -> Self
        // TODO: require that the sum fits in usize.
    {
        NonZero(self + other)
    }
}
fn main() -> usize {
    let first = NonZero(10);
    let second = NonZero(32);
    first.add(second)
}
`,
    solution: `type NonZero usize where self != 0;
impl NonZero {
    method add(other: Self) -> Self
        where integer::from(self) + integer::from(other) <= integer::from(usize::MAX)
    {
        NonZero(self + other)
    }
}
fn main() -> usize {
    let first = NonZero(10);
    let second = NonZero(32);
    first.add(second)
}
`
  },
  {
    id: "bounds",
    title: "Make indexing safe",
    topic: "Memory & bounds",
    minutes: "3 min",
    introduction: "An array type includes its length: `[usize; 3]` has three elements. Indexing starts at zero. A function is checked for every input its contract permits, even if `main` happens to pass a safe index.",
    goal: "Add a where clause to read_at that guarantees its index is in bounds. Keep the array access and the call in main.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "Valid indices for three elements are 0, 1, and 2. usize already excludes negative numbers.",
  "Replace the TODO comment with where index < 3, between the return type and the opening brace."
],
    takeaway: "A safe call in main cannot rescue an unconstrained function. The contract gives read_at a bound for all its callers, and each caller must prove that bound.",
    starter: `fn read_at(values: &[usize; 3], index: usize) -> usize
    // TODO: require an in-bounds index.
{
    (*values)[index]
}

fn main() -> usize {
    let values: [usize; 3] = [10, 20, 42];
    read_at(&values, 2)
}
`,
    solution: `fn read_at(values: &[usize; 3], index: usize) -> usize
    where index < 3
{
    (*values)[index]
}

fn main() -> usize {
    let values: [usize; 3] = [10, 20, 42];
    read_at(&values, 2)
}
`
  },
  {
    id: "proof-equality",
    title: "Your first proof",
    demonstration: true,
    introduction: "A proof is a sequence of commands for establishing a claim. The claim after `proof known:` becomes the current goal: something the compiler still needs evidence for. You are operating on that goal, not modifying a runtime value. This complete example proves a single equality.",
    goal: "Run the complete example. Read the goal before and after `rfl` below; no code changes are needed yet.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "The proof is already complete. Run it to see that the compiler accepts it."
],
    walkthrough: [
  {
    "title": "Before rfl",
    "text": "The pending goal is the claim written after `proof known:`. The context contains `let answer: usize = 42`.",
    "goals": "Current goal: answer == 42"
  },
  {
    "title": "After rfl",
    "text": "`rfl` is short for reflexivity: an expression equals itself. Substitute the definition of `answer`, and the equality is `42 == 42`. The equality is established, so there are no pending goals. `known` now names the checked evidence.",
    "goals": "42 == 42  ✓\nPending goals: none"
  }
],
    takeaway: "A proof command works on the current pending claim. Finishing the proof records evidence under its name. It does not assign a value to `answer` or add runtime work.",
    starter: `fn main() -> usize {
    let answer: usize = 42;
    proof known: answer == 42 by {
        rfl
    };
    answer
}
`,
    solution: `fn main() -> usize {
    let answer: usize = 42;
    proof known: answer == 42 by {
        rfl
    };
    answer
}
`
  },
  {
    id: "proof-arithmetic",
    title: "Prove an inequality",
    demonstration: true,
    introduction: "Now the goal is an inequality about an unknown input. `omega` asks the compiler’s integer arithmetic procedure to prove it from the context: the input bounds, the `where` clause, and definitions such as `next = n + 1`. Every allowed input must work.",
    goal: "Run the complete example. Compare this goal with the equality in the previous lesson. No code changes are required.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "This proof is already complete. Read the available facts and the goal below, then run it."
],
    walkthrough: [
  {
    "title": "Before omega",
    "text": "The goal is `next > n`. The definition says `next = n + 1`, and `where n < usize::MAX` guarantees the addition does not overflow.",
    "goals": "Context: n < usize::MAX\n         next = n + 1\nCurrent goal: next > n"
  },
  {
    "title": "After omega",
    "text": "One added to an integer is larger when the machine addition is exact. `omega` establishes that inequality. The name `grows` now refers to its evidence.",
    "goals": "next > n  ✓\nPending goals: none"
  },
  {
    "title": "At exact grows",
    "text": "After returning `next`, the function must establish `result > n`. `exact grows` supplies the evidence just proved, since `result` is the returned `next`.",
    "goals": "Postcondition: result > n\nEvidence: grows  ✓"
  }
],
    takeaway: "We use `rfl` to express equality by definition and `omega` for arithmetic bounds. In the current compiler both names use the same bounded arithmetic procedure, so these are readable proof conventions rather than two separate solvers.",
    starter: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result > n
{
    let next = n + 1;
    proof grows: next > n by {
        omega
    };
    next
} proof { exact grows }

fn main() -> usize {
    increment(41)
}
`,
    solution: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result > n
{
    let next = n + 1;
    proof grows: next > n by {
        omega
    };
    next
} proof { exact grows }

fn main() -> usize {
    increment(41)
}
`
  },
  {
    id: "proof-example",
    title: "Follow a proof",
    topic: "Proofs",
    minutes: "3 min",
    introduction: "This time the claim contains two parts joined by `&&`: `next == n + 1` and `next > n`. The proof must establish both. `constructor` constructs evidence for this “and” by replacing the single combined goal with two pending goals. The next command works on the first; once it is proved, the second becomes current. No code or data is being split.",
    goal: "The proof is already written for you. Run it with 10, then change only the call in main to increment(41) and run again. Read the comments beside each proof step; you’ll use the same pattern next.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "Leave the proof as it is. Only the input in main needs to change.",
  "Change increment(10) to increment(41)."
],
    takeaway: "The proof works for every n allowed by where, so changing the caller does not require a new proof. Next you’ll reuse these three steps to prove a decrease instead of an increase.",
    starter: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result == n + 1 && result > n
{
    let next = n + 1;
    proof correct: next == n + 1 && next > n by {
        constructor; // Split the two claims joined by &&.
        rfl;         // First: next equals n + 1 by its definition.
        omega        // Second: next > n, using the input bound.
    };
    next
} proof { exact correct } // Use the evidence for the postcondition.

fn main() -> usize {
    increment(10)
}
`,
    solution: `fn increment(n: usize) -> usize
    where n < usize::MAX
    ensures result == n + 1 && result > n
{
    let next = n + 1;
    proof correct: next == n + 1 && next > n by {
        constructor; // Split the two claims joined by &&.
        rfl;         // First: next equals n + 1 by its definition.
        omega        // Second: next > n, using the input bound.
    };
    next
} proof { exact correct } // Use the evidence for the postcondition.

fn main() -> usize {
    increment(41)
}
`,
    walkthrough: [
  {
    "title": "Before constructor",
    "text": "There is one pending goal: the whole conjunction written after `proof correct:`.",
    "goals": "Current goal: next == n + 1 && next > n"
  },
  {
    "title": "After constructor",
    "text": "The proof checker now has two goals, in their written order. The equality is current, and the inequality waits behind it.",
    "goals": "1. next == n + 1   ← current\n2. next > n        ← waiting"
  },
  {
    "title": "After rfl",
    "text": "The definition of `next` makes the first goal `(n + 1) == (n + 1)`. `rfl` establishes it. The checker advances to the remaining inequality.",
    "goals": "1. next == n + 1   ✓\n2. next > n        ← current"
  },
  {
    "title": "After omega",
    "text": "Using `n < usize::MAX`, `omega` establishes the remaining inequality. Both parts are proved, so `correct` is now checked evidence for their conjunction. The final `exact correct` reuses it for the return contract.",
    "goals": "1. next == n + 1   ✓\n2. next > n        ✓\nPending goals: none"
  }
]
  },
  {
    id: "proof-challenge",
    title: "Now prove it yourself",
    topic: "Proofs",
    minutes: "3 min",
    introduction: "Use the same proof structure for subtraction. The precondition `n > 0` prevents underflow. The promise is `result == n - 1 && result < n`. `constructor` gives you the equality as your current goal and the inequality as the next goal. Prove them in that order.",
    goal: "Fill in correct with the three proof steps you just saw: split the two claims, prove the equality, then prove the inequality. Keep the contract and final exact correct block.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "In the previous example, constructor split a claim joined by && into two goals. Start with that.",
  "The first goal is next == n - 1. Use rfl, just as you did for addition.",
  "Finish with omega. The precondition n > 0 supplies the bound needed to prove next < n. The steps are constructor; rfl; omega."
],
    why: "The function promises a smaller result for every allowed input, not just 43. At zero, unsigned subtraction can underflow, so strict decrease would not follow. The precondition excludes zero; the proof uses that bound to justify the promise. The final exact correct block requires the named evidence, so an unfinished script stops compilation. Evergreen can infer this small arithmetic result automatically too; writing the steps makes the reasoning explicit. Proofs are checked during compilation and erased from the executable.",
    takeaway: "You transferred the proof structure from addition to subtraction: constructor splits the promise, rfl establishes the equality, and omega establishes the inequality using the input bound. Try allowing n == 0 or deleting the final omega step and see why the proof fails.",
    starter: `fn decrement(n: usize) -> usize
    where n > 0
    ensures result == n - 1 && result < n
{
    let next = n - 1;
    proof correct: next == n - 1 && next < n by {
        // TODO: use the three steps from the previous example.
    };
    next
} proof { exact correct }

fn main() -> usize {
    decrement(43)
}
`,
    solution: `fn decrement(n: usize) -> usize
    where n > 0
    ensures result == n - 1 && result < n
{
    let next = n - 1;
    proof correct: next == n - 1 && next < n by {
        constructor;
        rfl;
        omega
    };
    next
} proof { exact correct }

fn main() -> usize {
    decrement(43)
}
`
  },
  {
    id: "loop-invariant",
    title: "What stays true in a loop",
    demonstration: true,
    introduction: "`where` describes what must be true when a function starts. A loop’s `invariant` must hold before its first iteration and after every iteration. The compiler checks one arbitrary iteration, rather than assuming it has watched the loop run. `modifies(&count)` declares which value can change. `decreases(42 - count)` proves termination: this nonnegative quantity gets smaller each time.",
    goal: "Run this complete loop and follow why it must finish at 42. The invariant and proof are supplied here; you’ll use this pattern in the final example.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "No changes needed. The loop and its invariant are complete."
],
    walkthrough: [
  {
    "title": "Before the loop",
    "text": "`count` is zero, so `count <= 42` holds. This establishes the invariant at entry.",
    "goals": "count = 0\nInvariant: count <= 42  ✓"
  },
  {
    "title": "One arbitrary iteration",
    "text": "Assume the invariant and the guard `count < 42`. Adding one preserves `count <= 42` and reduces `42 - count`. This argument applies to every iteration.",
    "goals": "Before: count < 42\nAfter increment: count <= 42  ✓"
  },
  {
    "title": "At loop exit",
    "text": "The guard is false, so `count >= 42`. The invariant still says `count <= 42`. Together they force `count == 42`, which the final `omega` proves.",
    "goals": "count >= 42 && count <= 42\nGoal: count == 42  ✓"
  }
],
    takeaway: "An invariant carries a useful fact across an unknown number of iterations. At exit, combine it with the false loop guard to establish the result.",
    starter: `fn main() -> usize {
    let count: usize = 0;
    while count < 42
        invariant(count <= 42)
        modifies(&count)
        decreases(42 - count)
    {
        count = count + 1;
    }
    proof finished: count == 42 by { omega };
    count
}
`,
    solution: `fn main() -> usize {
    let count: usize = 0;
    while count < 42
        invariant(count <= 42)
        modifies(&count)
        decreases(42 - count)
    {
        count = count + 1;
    }
    proof finished: count == 42 by { omega };
    count
}
`
  },
  {
    id: "forall",
    title: "Prove it for every index",
    demonstration: true,
    introduction: "`forall(i: integer)` means “for every mathematical integer i.” Its `where` clause restricts which integers are included. The claim below says that every index from 0 through 41 can advance once without passing 42. `intro i` picks an arbitrary index and makes its domain bounds available to the rest of the proof. Because the proof uses only those bounds, it covers every index in the domain.",
    goal: "Run the complete proof. Follow how `intro i` changes a “for every index” claim into one arithmetic goal. This proof does not execute a loop or test all 42 cases.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "The proof is supplied. `intro i` introduces an arbitrary index; `omega` proves the arithmetic claim about it."
],
    walkthrough: [
  {
    "title": "Before intro i",
    "text": "The current goal is a universally quantified claim. There is not yet an individual index to reason about.",
    "goals": "For every integer i with 0 <= i < 42:\n    prove i + 1 <= 42"
  },
  {
    "title": "After intro i",
    "text": "`i` is now an arbitrary mathematical integer. Its domain supplies `0 <= i` and `i < 42`. The current goal is just the body of the claim.",
    "goals": "Context: 0 <= i && i < 42\nCurrent goal: i + 1 <= 42"
  },
  {
    "title": "After omega",
    "text": "The arithmetic procedure proves this goal from the domain bounds. No special value for `i` was chosen, so the result establishes the entire `forall` claim.",
    "goals": "i + 1 <= 42  ✓\nPending goals: none"
  }
],
    takeaway: "A runtime loop performs work repeatedly. A `forall` proof establishes one argument for an arbitrary member of a domain. The proof is erased; the program does not enumerate the domain.",
    starter: `fn main() -> usize {
    proof bounded:
        forall(i: integer)
        where (0 <= i && i < 42)
        {i + 1 <= 42} by {
            intro i;
            omega
        };
    42
}
`,
    solution: `fn main() -> usize {
    proof bounded:
        forall(i: integer)
        where (0 <= i && i < 42)
        {i + 1 <= 42} by {
            intro i;
            omega
        };
    42
}
`
  },
  {
    id: "loop-forall",
    title: "Bring the loop and proof together",
    introduction: "This loop counts to 42. Now prove that every visited index is below 42. `integer::from(count)` views the machine integer as a mathematical integer for the proof. The supplied `using finished; intro at_end` brings the checked exit fact `count == 42` into the universal proof’s context. Then use the `intro i; omega` pattern you just saw.",
    goal: "Restore the loop invariant `count <= 42`. Then finish the `forall` proof: introduce an arbitrary index and prove it is below 42. Keep the loop, its exit proof, and the universal claim.",
    expected: {
  "output": "",
  "result": "42"
},
    hints: [
  "Replace `invariant(true)` with `invariant(count <= 42)`. Without an upper bound, the exit condition alone cannot establish equality to 42.",
  "After `intro at_end`, use `intro i` to introduce the arbitrary index. Its domain gives `0 <= i` and `i < integer::from(count)`.",
  "Finish with `omega`. Since `count == 42`, an index smaller than count is smaller than 42."
],
    why: "The loop guard is only known while the body runs. The invariant preserves the upper bound across iterations, so the false guard at exit establishes count == 42. The universal proof then uses that exit fact to cover every index in the visited range. Without the invariant, the exit equality is unproved; without the universal proof steps, the forall goal remains open. These are compile-time obligations, not runtime tests.",
    takeaway: "You combined a loop invariant, an exit proof, and a universal claim. The loop does the work; the invariant connects its iterations; the forall proof reasons about every visited index in one argument.",
    starter: `fn main() -> usize {
    let count: usize = 0;
    while count < 42
        invariant(true)
        modifies(&count)
        decreases(42 - count)
    {
        count = count + 1;
    }
    proof finished: count == 42 by { omega };
    proof visited_in_bounds:
        forall(i: integer)
        where (0 <= i && i < integer::from(count))
        {i < 42} by {
            using finished;
            intro at_end;
            // TODO: introduce the index, then prove its bound.
        };
    count
}
`,
    solution: `fn main() -> usize {
    let count: usize = 0;
    while count < 42
        invariant(count <= 42)
        modifies(&count)
        decreases(42 - count)
    {
        count = count + 1;
    }
    proof finished: count == 42 by { omega };
    proof visited_in_bounds:
        forall(i: integer)
        where (0 <= i && i < integer::from(count))
        {i < 42} by {
            using finished;
            intro at_end;
            intro i;
            omega
        };
    count
}
`
  },
];

// Progress requires a successful real run. Source spelling is deliberately unrestricted.
export function meetsGoal(lesson, execution) {
  return execution.ok === true && !execution.runtimeError
    && (lesson.expected.outputs?.includes(execution.output) ?? execution.output === lesson.expected.output)
    && execution.result === lesson.expected.result
    && (execution.assumptions ?? []).every(a => a.goal === 'external contract for console::print');
}
