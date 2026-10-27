# Proof evidence and scoped admissions

This records the requested proof model. It is not a description of completed
implementation. The current global treatment of `trustme` does not yet satisfy
these requirements.

## Claims and evidence

A named fact stores a proposition expression. It does not establish truth.
Using it instantiates that expression in the current state. Checking a declaration
must not publish proof assumptions as a side effect of unused facts.

A proof node records its instantiated claim, state dependencies, and the evidence
actually used. Named proofs refer to nodes; anonymous proofs need no user-visible
name. Arithmetic certificate weights identify the exact constraint rows used by
a checked derivation. Logical steps must likewise identify their premise nodes.
An admitted claim is a distinct node, not a proved constraint in the execution
path context. Row provenance is positional: equal arithmetic rows can have
different origins. Negated-goal rows must not become premise edges back to the
goal being proved.

The graph must distinguish these sources:

- Checked runtime/type facts and branch hypotheses.
- Checked arithmetic and logical derivations.
- Explicit admissions and checked derivations that use them.

Proof dependency bookkeeping does not establish validity. Arithmetic certificates
and logical rules still require checking. Artifact replay must reconstruct and
check dependencies rather than trusting cached graph annotations.

## State dependencies

Reads identify value/plane versions and projections, rather than only textual
variable names. Two reference fields have independent provenance even when they
happen to alias. Writes invalidate affected current-state evidence, including
aliased writes. A move of an owner slot does not change the owned payload plane;
a drop invalidates its liveness, and restoring storage must not revive old loans.

Calls must retain the origin of argument values through parameter renaming.
Entry snapshots, conditional scopes, invariant lifting, and returned owned planes
must preserve the same rules. Literal constant folding must not erase the subject
identity needed to distinguish unrelated admitted claims.

## Admission isolation

Unused admissions must not affect other obligations. Admission nodes do not
participate in execution-path feasibility pruning. Otherwise an admitted false
claim eliminates all paths and silently makes every later obligation vacuous.

Obligations first use ordinary checked evidence. Relevant, live admissions may
then support a dependent proof. That use is recorded transitively in the graph.
Derived claims and operations inherit the admissions actually needed for their
proofs; they must not acquire every admission merely available in scope.

Required regressions include:

- An unused false admission does not justify an unrelated failed precondition.
- A call using an admitted precondition records that dependency.
- Mutation prevents reuse of the old claim as a claim about the new value.
- Writes through aliases and modifications in helpers invalidate affected claims.
- One field's admission does not establish a different field's validity.
- Derived evidence retains its actual admission dependencies.
- A later admission cannot justify an earlier operation.
- Cache replay reconstructs and checks graph/state dependencies without proof search.

`--deny-trust` can remain stricter and reject any explicit admission, including an
unused one. Reporting unused admissions separately from runtime proof dependencies
is a reporting decision; it must not change which obligations they can justify.

## Implementation status

The arithmetic session exposes `prove_with_support`: original row indices with
nonzero weights in a kernel-checked certificate. This support is reconstructed
from the checked certificate during both search and replay. Tests check that an
unrelated constraint is excluded and an unsuccessful probe supplies no evidence.

Named witnesses now refer to nodes in an append-only evidence DAG. Explicit
logical rules (`exact`, `assumption`, `constructor`, introduction, cases, and
application) record their premise edges. Admissions are distinct nodes. Traversal
collects only reachable admissions, visits shared premises once, and preserves
historical dependencies after lexical hypotheses leave scope. Node, edge, and
aggregate claim-storage limits bound graph growth. Tests cover transitive and
unused admissions, local hypotheses, deep chains, and reconstruction on replay.

Arithmetic path rows now carry positional origins. Rows introduced by explicit
proofs and local proof hypotheses point to their evidence nodes; negated-goal
rows have a distinct origin and never become premise edges. Arithmetic proof
steps reconstruct edges from kernel-checked certificate support during search
and replay. Path deduplication retains distinct proof origins even for equal
arithmetic constraints.

Path sets retain checked support for removed alternatives. Successful optional
arithmetic queries reconstruct the contradiction's row support during both
search and replay; failed probes contribute no evidence. Direct constant-false
closures also retain their origin, including when no live alternatives remain.
An independently true goal does not inherit a contradiction merely because the
surrounding context is inconsistent. Explicitly supplied empty path sets without
an explanation remain unresolved.

Arithmetic leaves inherit unresolved provenance only when the checked support
actually uses unresolved origins. Runtime/type facts and call summaries still
lack complete origins, so an empty set of known admissions does **not** alone
imply admission-free evidence. Scoped hypotheses additionally need explicit
discharge metadata before the DAG can serve as independently checkable proof
evidence.

Explicit proof declarations now store state-subject snapshots separately from
arithmetic formulas. Canonical claim keys retain operator structure and replace
storage reads with projection/epoch stamps. Different subjects or different
statements cannot become the same key merely because arithmetic simplifies to
the same constant expression. Named facts are expanded when the proof is checked.

The epoch tracker is connected to direct and indirect assignments, declared call
writes, allocation, and ownership takes. Alias writes share the referent's epoch;
sibling fields and distinct constant indices stay independent. Unknown indices
conservatively overlap. Same-value writes advance the epoch. Liveness generations
and allocation notifications prevent a dropped or reused slot from reviving old
snapshots. Moving an owner slot preserves subjects on its separate payload plane.

Subject capture currently resolves existing places and literal/name indices
without evaluating user code again. Call results, conditional subjects, named
type facts, and more complex index expressions remain incomplete. Argument-value
origins across parameter renaming are pending. Epochs conservatively include
writes from either symbolic branch; precise availability within branches and
joined claims still needs integration.

Admission isolation and dependency-aware call summaries remain to be integrated.
The stored subjects are not yet used to authorize admission reuse or retract
assumptions. Existing acceptance of contradictions through global `trustme`
assumptions is a known gap, not the intended semantics.
