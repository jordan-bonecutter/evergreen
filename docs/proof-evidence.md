# Proof evidence and scoped admissions

This records the requested proof model and the partial implementation below.
It is not a completed trust boundary: declaration summaries and complete value
provenance still need integration.

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

## Immutable plane states

The verification state has a logical snapshot at each successful statement.
Snapshots share unchanged nodes rather than cloning every plane and fact set.
The current implementation uses a persistent compressed binary trie with exact
integer keys: plane identities index immutable plane states, and proof identities
index their evidence. It introduces no new package dependency.

Each plane state records a content version, projection versions, and an evidence
index. Projection versions provide the structural frame rule for unchanged
fields and distinct constant array indices. Every alias consults the same plane
entry in the current snapshot. A pointer copy does not freeze the pointee.

Evidence entries are candidates, not unchecked assumptions. A fact involving
several planes is indexed under each one, while its proof remains one DAG node.
Using it checks every recorded dependency against the selected snapshot. This
keeps invalidation lazy: a write does not scan and delete all dependent facts.
Old snapshots retain their evidence without making it available in the new state.

Branches fork the root. Their merge preserves unchanged regions and gives changed
regions fresh versions; branch-local facts require a join proof before they can
become generally available. Version identities are never reused. Subject identity
registration is append-only and separate from these immutable version maps.

An explicit proof can establish a property of a saved scalar before the source
changes. The saved scalar's independent plane then retains that evidence. A proof
about a copied pointer's pointee still depends on the shared target, so an alias
write invalidates it. Tests cover both cases, multi-plane facts, independent
branch snapshots, newly observed branch regions, and historical statement roots.
The persistent map is checked against `BTreeMap` across updates and old snapshots,
including boundary keys and independent forks. Structural diffs skip shared
subtrees, so a join does not scan every unchanged plane. Branch and `old()`
restoration pair the fact root with the corresponding memory view.

`examples/carry_proofs.evg` is a runnable example with no admissions: it explicitly
establishes a fact about a saved scalar, changes the source, and reuses the saved
proof. The pointer and multi-plane rejection cases are regression tests.

This is the first immutable state layer. Fact declarations and the proof DAG still
use the bootstrap's existing representations; memory, path constraints, and lexical
scopes have not all migrated to a unified persistent state. Explicit inference-rule
records, complete statement footprints, and function-summary transport remain work
in progress. The target model keeps propositions distinct from their evidence:
raw fact references require a witness or a scoped hypothesis to serve as premises.

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
type facts, and more complex index expressions remain incomplete. Scalar argument
keys now transfer through parameter renaming for call preconditions and dependent
postconditions. Aggregate/call-result value origins are not complete. Epochs
conservatively include writes from either symbolic branch; precise availability
within branches and joined claims still needs integration.

Explicit source proof declarations with admissions no longer constrain execution
paths. They enter a scoped candidate set. A proof obligation first tries ordinary
checked evidence; only a failed check tries relevant live candidates in a temporary
context. Checked certificate support records the dependencies actually used.
Relevance uses current projection stamps and immutable arithmetic variables;
constant-folded claims cannot match unrelated subjects through equal arithmetic
alone. Optional failures and successful support are reconstructed during replay.
Relevance scanning and dependency traversal charge the verifier's work budget.

Writes prevent reuse of a mutable source claim. Checked operations can retain
exact properties of already-evaluated SSA values for subsequent revalidation.
Those properties do not form a general contradiction context for new values
that share SSA variables. A call's precondition proof does not become a permanent
fact about its input. These value facts stay scoped to branches and helper bodies. Explicit `exact`/`apply` uses of
admitted claims check subject identity and state; explicit false elimination
remains possible and records the admission edge.

A call accepted under an admitted precondition retains that dependency. Its
postconditions and newly assumed refinements remain conditional evidence instead
of entering execution paths; fundamental fresh scalar representation bounds stay
ordinary type facts. Tests cover unrelated checks after false dependent posts and
impossible result invariants, as well as mutation, aliases, helper writes, anonymous
proofs, compound proofs, independently provable calls, and replay.

This is partial admission isolation, not the completed trust boundary. Declaration
summaries still need the admissions used in their own verification, including
external contracts and explicit postcondition proof scripts. Complete value-flow
provenance, branch guards, aggregate/constant value evidence, and independent
logical discharge checking remain pending. Fact well-formedness evaluation also
needs isolation from assumptions created by helper summaries. The public trust
manifest still lists every admission, including unused ones; operation-level DAG
reporting is not yet exposed. `--deny-trust` remains strict.

`examples/scoped_admissions.evg` demonstrates an admitted call followed by an
independent proof about the changed value. `examples/reject_stale_admission.evg`
rejects a second call that tries to reuse the old admission after mutation.
