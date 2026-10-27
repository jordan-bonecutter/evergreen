# Proof evidence and scoped admissions

This records the requested proof model and the partial implementation below.
It is not a completed trust boundary: complete value provenance and independent
checking of frontend state/contract imports remain work in progress.

Runtime loops use a finite initialization/preservation/exit rule in the frontend.
Their invariant imports have the same explicit unresolved context as checked
function-contract imports. The proof graph remains acyclic: an arbitrary head
is checked once, and exit evidence points back to entry and preservation
obligations. This is not yet an independently kernel-checked state-transition or
loop-induction certificate. Known admission sources used in the loop propagate
through its exit invariant and function summaries.

## Claims and evidence

A named fact stores a proposition expression. It does not establish truth.
Using it instantiates that expression in the current state. Checking a declaration
must not publish proof assumptions as a side effect of unused facts.

A proof node records its instantiated claim, state dependencies, and the evidence
actually used. Named proofs refer to nodes; anonymous proofs need no user-visible
name. Arithmetic certificate weights identify the exact constraint rows used by
a checked derivation. Logical steps identify their premise nodes and retain an
explicit inference rule.
The rule checker validates connective shape and premise/conclusion agreement
before inserting a derived node. Tactics cannot insert arbitrary logical edges.
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

Each plane state records a revision ID and an evidence index. An append-only
arena records writes and joins by predecessor IDs. A write does not scan every
observed field or update their facts. A read computes that projection's revision
only when requested, preserving unchanged fields and distinct constant indices.
The result is memoized by revision and immutable subject identity. Snapshots keep
sharing their roots; memoization does not change their meaning. Long histories
are queried and destroyed iteratively, without recursively linked allocations.

Mutable read dependencies identify a plane, revision, and projection. Aliases
consult the same plane entry. A saved proof-state ID selects historical revisions:
`old(*p)` observes the function/call entry value, while `*old(p)` reads the current
pointee through the saved pointer identity. Historical lookup does not authorize
a live memory read; generation checks still protect runtime references.

Branches record the condition alongside their revision join. Looking through an
unchanged branch produces a guarded historical premise. An overwritten branch
cannot inherit that premise. Same-guard facts are applied together; the checker
first resolves the condition from checked execution paths and otherwise checks
both cases. This avoids repeating an exponential case split for every premise.
The old fact is never renamed into a fact about new contents.

Evidence entries are candidates, not unchecked assumptions. A fact involving
several planes is indexed under each one, while its proof remains one DAG node.
Using it checks every recorded dependency against the selected snapshot. This
keeps invalidation lazy: a write does not scan and delete all dependent facts.
Old snapshots retain their evidence without making it available in the new state.

Branches fork the root. Their merge records fresh join revisions; projection
queries later determine which regions stayed unchanged. Branch-local facts still
require a join proof before becoming generally available. Revision identities are
never reused. Subject identities are append-only, with an exact ordered index of
reference generations and shared projection paths.

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

Instantiated propositions entering the evidence graph are interned in an
append-only arena. Proof nodes hold a distinct `FactId` for their conclusion;
several proofs can share that proposition without sharing their admission or
hypothesis dependencies. Formula storage is counted once, while graph edges,
state dependencies, and open hypotheses keep their own bounds. Interning preserves
connectives needed by inference rules rather than identifying every logically
equivalent formula. The formula index and arena share the same immutable allocation.

A raw fact ID establishes nothing and cannot occupy a proof-premise slot. Named
source facts remain lazy expression templates until instantiated; an unused fact
is not eagerly copied into the evidence graph. Tests cover false propositions
without evidence, separately admitted proofs of the same conclusion, sharing
through deep derivations, and storage limits for both fresh formulas and scoped
hypotheses.

This implements the first lazy state layer described in `README2.md`: writes
record transitions and projection/fact lookup is demanded by a proof. Formula
elaboration, contract decomposition, and path collection still perform eager
work. Memory, path constraints, and lexical scopes have not all migrated to a
unified persistent state. Complete statement
footprints, aggregate value origins, and guarded transport of branch-local facts
remain work in progress. Raw fact
references require a witness or a scoped hypothesis to serve as premises.

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
actually uses unresolved origins. Runtime/type facts and frontend contract instantiations still
lack completely checked origins, so an empty set of known admissions does **not** alone
imply admission-free evidence. Scoped hypotheses now have distinct identities
and are propagated through arithmetic imports and logical rules. Implication introduction discharges only
its declared binder. Disjunction elimination checks both branches, prevents
cross-branch assumptions, and forbids either case hypothesis from justifying the
source disjunction. Proof-script results and published state evidence must have
no remaining open hypotheses.

The propositional rule checker is separate from tactic selection. It checks
reuse, conjunction introduction/elimination, disjunction introduction/elimination,
implication introduction/elimination (including negation), and false elimination.
Implication application produces one checked elimination per argument rather than
an opaque group of premise edges. Unused conjunction destructuring does not add
an admission dependency to an independently proved result. Tests reject wrong
premises, forged binders, wrong conclusions, open-hypothesis publication, and
cross-branch leaks; a finite truth-table sweep checks accepted introduction and
elimination candidates for counterexamples. Nested case scopes are reconstructed
on replay.

These checks establish the local propositional rules, not the complete source-to-
proof pipeline. Arithmetic leaves still rely on the certificate session and its
row-origin translation; declaration imports remain explicitly unresolved. Graph
node/edge/storage limits also bound formula depth, open hypotheses, and aggregate
logical checking work.

Explicit proof declarations now store state-subject snapshots separately from
arithmetic formulas. Canonical claim keys retain operator structure and replace
storage reads with projection/revision stamps. Different subjects or different
statements cannot become the same key merely because arithmetic simplifies to
the same constant expression. Named facts are expanded when the proof is checked.

The revision tracker is connected to direct and indirect assignments, declared call
writes, allocation, and ownership takes. Alias writes share the referent's revision;
sibling fields and distinct constant indices stay independent. Unknown indices
conservatively overlap. Same-value writes advance the revision. Liveness generations
and allocation notifications prevent a dropped or reused slot from reviving old
snapshots. Moving an owner slot preserves subjects on its separate payload plane.

Subject capture currently resolves existing places and literal/name indices
without evaluating user code again. Call results, conditional subjects, named
type facts, and more complex index expressions remain incomplete. Scalar argument
keys now transfer through parameter renaming and retain the argument-evaluation
proof-state. Scalar call results can transfer advertised facts into their binding,
where direct and aliased writes invalidate them. Explicitly saved return values
and scalar entry parameters retain their value evidence through scope cleanup.
Aggregate value origins remain incomplete. Guarded historical queries handle
common branch predecessors; arbitrary branch-local fact transport remains pending.

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
fact about its input. These value facts stay scoped to branches and helper bodies. Explicit
`exact`/`apply` uses of admitted claims check subject identity and state; explicit false elimination
remains possible and records the admission edge.

A call accepted under an admitted precondition retains that dependency. Its
postconditions and newly assumed refinements remain conditional evidence instead
of entering execution paths; fundamental fresh scalar representation bounds stay
ordinary type facts. Tests cover unrelated checks after false dependent posts and
impossible result invariants, as well as mutation, aliases, helper writes, anonymous
proofs, compound proofs, independently provable calls, and replay.

This is partial admission isolation, not the completed trust boundary.
Declaration summaries now retain the admissions actually reached from their
runtime obligations and postcondition proofs. These are separate aspects: an
unused admitted postcondition of an ordinary function does not taint a caller
that ignores it. Safety
requirements propagate through calls, including external operation boundaries.
Explicit function proof scripts contribute their proof roots. Recursive summary
references retain their aspect until the enclosing declaration closes the two
finite dependency sets; only checked callees and the permitted self hypothesis
are available.

Imported trust sources have typed manifest IDs and no proposition. Propositional
rules reject them as mathematical premises. Contract conjuncts are indexed as
separate candidates using checked conjunction elimination, so an exchange's new
contents need not use its old-result clause. Named multi-plane source proofs keep
their declared dependencies; explicit projection can establish an independent
fact before a write. Projection of a constructed conjunction reuses only the
selected component proof.

Recursive hypotheses retain the call's saved state and branch condition. When
checked path relations connect a goal to a recursive contract, lookup can request
those historical facts under that condition. This supports the library CAS loops
without restoring globally assumed external postconditions.

`VerifiedProgram::function_safety_assumptions` and
`function_contract_assumptions` expose these known dependencies. Complete value-
flow provenance, aggregate origins, branch-local fact transport, and independent
checking of all state/contract imports remain pending. Fact well-formedness
evaluation also needs isolation from assumptions created by helper summaries.
The public trust manifest still lists every admission, including unused ones; operation-level DAG
reporting is not yet exposed. `--deny-trust` remains strict.

`examples/scoped_admissions.evg` demonstrates an admitted call followed by an
independent proof about the changed value. `examples/reject_stale_admission.evg`
rejects a second call that tries to reuse the old admission after mutation.
