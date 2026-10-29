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

The interpreter executes the original source branches. Native generation keeps
a private drop flag for each local requiring cleanup. Moving the binding clears
its flag; initialization and replacement set it. Conditional branches join the
set of possibly live bindings, while their runtime flags retain which path
actually consumed each one. Scope cleanup checks the flags before invoking
destructors. This supports both different allocation lifetimes and different
live local bindings across arms without changing type layouts or the call ABI.
[`conditional_rc_drop.evg`](../examples/conditional_rc_drop.evg) exercises an early
drop followed by a borrow read only on the path that retained its owner.

Case coverage, source typing, and frontend resource transitions remain trusted
compiler boundaries. Arithmetic leaves replay through the internal certificate
checker; this is not an independently checked theorem of the whole compiler.

## Snapshot cost and owning-buffer composition

[`buffer_growth.evg`](../examples/buffer_growth.evg) verifies the combined
push/grow/pop sequence within the unchanged 262144-unit work budget. Native
x86-64 execution returns 42. This does not establish a bound for arbitrary
compositions or complete the public Vec migration.

Before payload sharing, a temporary caller-location trace identified about
39,000 charged units in `snapshot_memory` and `clone_store` together for this
probe. This measured symbolic work, not elapsed time. The tracing was removed.

Plane payloads now use immutable shared storage. A snapshot copies plane metadata
and owner-token sets but shares payloads; writes install new payloads, and taking
a value clones its payload only if another snapshot retains it. The verifier
charges snapshot metadata and conservatively charges payload work at `take`.
Arena identities, generations, ownership census revisions, and branch isolation
remain intact. This is payload sharing, not yet a persistent map for the plane
metadata itself.

Actual-body calls also re-prove and export logical invariants of unconditionally
available modified record inputs before restoring caller proof scope. This
preserves the checked initialized-prefix and vacant-suffix guarantees after
`pop`. Conditional input views still need a corresponding guarded export path.

Input-cell observation and quantified selector specialization now reject
candidate proofs that do not mention the requested predicate before cloning
their formulas. This uses the existing interned predicate index and leaves
specialization, revision checks, and admission checks intact. It reduces work
from unrelated array versions without changing the work limit. A combined
positive/zero-capacity buffer reallocation body still exceeds that limit;
zero-capacity release remains a separate checked operation.
