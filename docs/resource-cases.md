# Resource case proofs

The verifier first tries its ordinary branch join. Compatible plane generations,
token sets, and symbolic owner totals stay in one joined state. Projection fact
revisions retain their branch histories, queried lazily by later obligations.

Some correct programs leave different resource states. The source Rc destructor
either deallocates its unique allocation or releases one of several claims.
Joining those outcomes as an unconditional live allocation would be wrong.
The checker instead verifies each branch's entire remaining continuation in its
own storage world. This is a generic frontend case proof; it has no Rc rule.

When a runtime resource join cannot be represented, the declaration is retried
with separate runtime cases. Each undecided guard forks two continuations.
Already decided guards can select a branch only with admission-free checked
evidence. A saved case decision is checked against its function, source line,
and frozen mathematical guard when replayed. A checked contradiction can close
an unreachable case. No unchecked trace or unfinished fork publishes a summary.

Each complete case checks normal statements, actual helper calls, scope cleanup,
return provenance, and the declared postcondition. The allocation store itself
still checks generations and token membership. A reference into a freed plane
cannot be read merely because another case kept its plane alive. Mutating the
variable used in a guard does not change the frozen mathematical decision.
Conditional specifications may select an already checked case; this lets a
destructor describe surviving storage without observing freed storage on the
final-release path.

Conditional expression types must agree across cases, including a later
conditional whose guard became known differently in earlier cases. The checker
records both decision-prefix results and source conditional results. Source keys
include complete syntax and expected type context; hash collisions still require
exact key equality. Cross-case refinement facts may differ, but the source
expression cannot silently acquire another representation.

Safety and contract admission dependencies are combined over all completed
cases. Recursive summary dependencies reach their fixed point after that
combination. An actual heap-call recheck follows its own checked case; it does
not inherit admissions used only in an unreachable alternative. A `trustme`
claim cannot close a resource case or authorize reading dead storage.

The bootstrap currently replays the function prefix for each needed case.
Evaluation and value-work budgets accumulate across the entire case tree,
including aborted joins, saved decisions, syntax keys, and replayed prefixes.
Large case trees can therefore reach the work limit. Sharing persistent worlds
and continuations would reduce repeated prefix work; this optimization is not
implemented. Normal compatible branches keep the ordinary joined pass.

The interpreter executes the original source branches. Native Rc drop works
because both arms consume the same local handle even though allocation lifetime
differs. Native generation still rejects other programs with different live
local bindings across arms: it needs runtime drop flags for their later cleanup.
The rejection happens before an executable is emitted.

Case coverage, source typing, and frontend resource transitions remain trusted
compiler boundaries. Arithmetic leaves replay through the internal certificate
checker; this is not an independently checked theorem of the whole compiler.
