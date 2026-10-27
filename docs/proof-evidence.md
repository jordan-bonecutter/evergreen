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

Arithmetic leaves are explicitly marked as having unresolved context provenance.
An empty set of known admissions therefore does **not** imply admission-free
evidence. Checked arithmetic row support still needs to be connected to path-row
origins; scoped hypotheses also need explicit discharge metadata before the DAG
can serve as independently checkable proof evidence.

State-version tracking, admission isolation, and dependency-aware call summaries
remain to be integrated. Existing acceptance of contradictions through global
`trustme` assumptions is a known gap, not the intended semantics. The new graph
records explicit logical dependencies; it does not yet change that behavior.
