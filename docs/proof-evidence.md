# Proof evidence and scoped admissions

This records the requested proof model and the partial implementation below.
It is not a completed trust boundary: complete value provenance and independent
checking of frontend state/contract imports remain work in progress.

Raw unions use ideal active-type selectors in the frontend. A selected member's
refinements hold under its selector case; layout equality alone establishes no
type equality or read permission. `typeof` claims carry plane/revision subjects,
including when an explicit admission authorizes an interpretation. The native
backend erases selectors and copies the proved member at offset zero. This
extends the frontend and backend trust boundary; it is not an independent kernel
proof of type elaboration or machine-code preservation. Owning pointer members
now use guarded footprints and allocation-presence checks. Borrowed-reference
members still need conditional provenance contracts.

Borrowing an active member through union storage retains a zero-offset
interpretation in the original reference path. The interpretation records both
the member index and its exact type. Operational reads, projected addresses,
and stores prove the current selector before using that path; a store checks
again after right-hand-side effects. Such stores invalidate the whole union
slot's proof region. These are frontend memory rules, not additional kernel
axioms or independent certificates of machine-code preservation.

Read-only ideal definitions can reduce concrete scalar results using bounded,
explicit evaluation stacks. Argument references are imported as immutable value
snapshots with their existing identities; the evaluator cannot write caller
storage or invoke external operations. Function safety imports and scoped
admissions still use the ordinary call checker. Definition interpretation is a
frontend trust boundary, rather than an independent kernel reduction certificate.
Symbolic inputs and unsupported computations continue through verified contracts.

Repeated read-only ideal Boolean applications use the same symbolic proposition
for identical scalar values, immutable array versions, and reference projection
revisions. Changing a referenced region creates a different application;
changing an independent sibling projection preserves the original one. These
application identities express congruence, not evidence of truth. Preconditions,
postconditions, explicit proofs, and admissions still pass through ordinary
checking. Nested references and resource-bearing inputs need transitive
observation footprints and are excluded from this identification for now.

Concrete Boolean reductions use the same revision-aware application keys to
reuse bounded computation. The cache stores values, not proofs or admissions;
every call still checks its precondition and imports its checked safety summary.
No result obtained before a pointee write authorizes the new revision.

Record refinements and functions are checked in one dependency graph. A record
can call an already checked source predicate, and a predicate can use already
checked record definitions. A cycle through a refinement and its own type is
rejected rather than treating an unverified declaration as an axiom. Implicit
destructor calls participate in that dependency order too.

Implicit cleanup imports a destructor's safety dependencies even when the body
has no visible writes. Reference-bearing destructors are elaborated against the
actual receiver, since independent declaration ports can describe an impossible
entry when the record invariant requires aliases. Their declaration summary
alone cannot authorize operations on an actual aliased receiver. Opaque arrays
with reference-dependent destructors still require element summaries and are
rejected when those summaries cannot be established. Known empty arrays run no
element cleanup and import no element safety dependencies.

Runtime loops use a finite initialization/preservation/exit rule in the frontend.
Their invariant imports have the same explicit unresolved context as checked
function-contract imports. The proof graph remains acyclic: an arbitrary head
is checked once, and exit evidence points back to entry and preservation
obligations. This is not yet an independently kernel-checked state-transition or
loop-induction certificate. Known admission sources used in the loop propagate
through its exit invariant and function summaries.

An optional loop `decreases(...)` expression supplies a ranking function. Its
integer value must be nonnegative at an arbitrary invariant-bearing active head,
and strictly decrease after the body and iteration-local cleanup. Calls in a
measure use specification permissions and must be total and non-modifying. These
obligations and their actual trust dependencies join the loop's finite evidence
graph. A measure does not make a divergent body total. Ranking expressions are
erased by both execution backends; this adds a frontend well-foundedness rule,
not an independently kernel-checked loop-induction certificate.

## Claims and evidence

A named fact stores a proposition expression. It does not establish truth.
Using it instantiates that expression in the current state. Checking a declaration
must not publish proof assumptions as a side effect of unused facts.

Proven facts should appear to users as refinements of the value's type at its
current plane revision, as though those properties were additional `where`
clauses. Their representation should remain a shared proof-state view queried
on demand, rather than eagerly copying a conjunction of all known facts into
every type. Mutation expires dependent inferred refinements. Declared nominal
invariants remain obligations, and nominal construction and ownership transfers
retain their own checks. A named proposition without evidence adds no guarantee.

A proof node records its instantiated claim, state dependencies, and the evidence
actually used. Named proofs refer to nodes; anonymous proofs need no user-visible
name. Arithmetic certificate weights identify the exact constraint rows used by
a checked derivation. Logical steps identify their premise nodes and retain an
explicit inference rule.

Logical hypotheses can themselves be universal propositions or contain
predicate atoms. They remain scoped witnesses: `intro all` introduces such a
premise, `specialize all(index)` exposes a checked instance, and `cases` exposes
the parts of conjunctions and disjunctions. Only arithmetic hypotheses become
solver rows. Leaving the proof scope removes its local witnesses and restores
the arithmetic context. This supports reusable range-restriction theorems.
Functions and loops also retain universal contract clauses as logical evidence,
with the import boundary and remaining storage limitations described below.
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

Conditional return provenance uses `borrows(a) when condition else borrows(b)`.
Each reference-bearing return field can independently use a conditional
reference expression in its `borrows(field: reference)` entry. These
guards use saved function/call-entry observations, as existing borrow origins do.
The returned pointer retains the selected plane and generation even when later
writes change the values used by the guard. Its proof representation stores
guarded real-plane alternatives, with every reachable case justified independently.
Scalar reads are memoized by those alternatives and their projection revisions;
each read replays its guarded value definition, without assuming a nominal
invariant about changed contents. A stale candidate stays stale, and only a
checked, admission-free guard can exclude it from an operational read.

Proof subjects retain the guards on their data dependencies. A candidate fact
about a selected value is available only in cases whose relevant regions remain
unchanged, and only for data flows which actually select the related region.
The same conditions propagate through historical searches. An admitted false
fact about one selection cannot automatically establish a property of the
opposite selection. These are frontend state/provenance rules, not independently
kernel-checked memory theorems.

Guarded stores and projected addresses use these same alternatives. Address
components and the assigned value are evaluated once; branch-state joins describe
the single runtime write. Modifying helpers and destructors carry guarded write
grants, checked against the caller's authority without admitted premises.
Actual-body rechecking preserves conditional ports through nested calls.

A stored array read resolves its base place before evaluating its index, then
reads the element from the current state after index effects. It never uses an
earlier array snapshot to justify that read's type or arithmetic safety. Explicit
copies and array rvalues retain their value semantics. The interpreter and native
backend use this same distinction, including through pointers and nested fields.

Observing reference-array cells in only one branch adds sparse metadata to that
array's unchanged contents identity. Joins merge only observed cells, recursively
through nested arrays and records; they reject differences in actual stored
values under one immutable identity. Bounds of immutable input observations
are replayed after installing the joined paths, never as assumptions about live
contents that may have changed. The declared extent is not enumerated.

Symbolic reference-array selection, guarded external effects, guarded loop
frames, and conditional storage-generation transitions remain incomplete.
Fresh unrelated pointees cannot stand in for such a selection.

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

The evidence kernel also checks guarded universal introduction and specialization
over mathematical integers. A universal claim stores its bound variable, domain,
and conclusion once; it does not enumerate the domain. Introduction discharges
the domain hypothesis and checks that its arbitrary index occurs in no remaining
open hypothesis or used external assumption. Arithmetic imports retain the free
variables of the unresolved rows actually used by their certificates for this
check. Specialization substitutes a checked integer term and requires evidence
of the corresponding domain. Substitution respects nested binders, rejects
variable capture, checks arithmetic overflow, and bounds expansion work.

Source proofs can now use these rules explicitly:

```evg
fact bounded = forall(i: integer) where (0 <= i && i < 10) { i <= 9 };
proof range: bounded by { intro i; omega };
let index: usize = 7;
proof selected: integer(index) <= 9 by { specialize range(index); omega };
```

`intro i` checks the conclusion at a fresh arbitrary integer under its domain.
`specialize range(index)` applies that theorem to the goal and opens a proof
obligation for its instantiated domain. The following `omega` proves that domain.
The argument currently accepts an integer literal or a local numeric name;
compute more involved arguments in an ideal local first. Omitting `where`
uses a true domain. Nested universals and renamed bound variables are supported.
A billion-element integer range uses the same number of proof obligations as a
ten-element one. These propositions have no executable Boolean representation.
See [universal.evg](../examples/universal.evg) for a runnable example.

Bound indices use lexical scope and mathematical integer arithmetic. Machine and
natural values need `integer::from(value)` (or the bootstrap `integer(value)`)
before arithmetic inside a quantifier.
Free scalar fields retain their ordinary plane/revision dependencies. Proof keys
store bound indices by their lexical distance, so renaming a binder does not
change its identity or confuse it with a plane read. Specialization preserves
these subjects; admitted theorems cannot be applied after their dependent plane
changes, or transferred to another plane merely because its value is equal.

Universal proofs, including anonymous ones, are indexed by their state subjects.
They are excluded from arithmetic paths and historical arithmetic searches.
Functions can require and advertise universal propositions; loops can combine
them with scalar invariant clauses. A matching live guarantee can discharge the
whole proposition. Otherwise implicit contract checking uses the same universal
introduction and conjunction rules as source proofs. It never samples a range.

Inside a body, `proof bounds: forall(...) {...} by {assumption};` names an
imported guarantee for explicit `specialize bounds(index)` use. Arithmetic
consequences require that specialization and a proof of its domain. Mixed
contracts publish their scalar and logical clauses separately. Unchanged
logical guarantees can be retained through a loop's ordinary storage frame.
See [universal_contracts.evg](../examples/universal_contracts.evg).

Logical imports retain their original plane and revision subjects. Scalar
return guarantees transfer into the receiving binding; same-value overwrites
still expire an admission. Discarded results and argument-result receipts do not
transfer to a surrounding call's result. Actual body checking exports that
function's own advertised guarantee. A branch receipt can transfer only when
its execution condition is established without admissions; merging conditional
result guarantees remains conservative. These rules prevent equal scalar values
from giving an unrelated result another call's guarantee.

Nominal declarations can now retain universal invariant clauses as logical
imports, rather than forcing them into arithmetic rows. Constructors still
prove the declared proposition, and retained-value checks recheck it after
writes. [range_type.evg](../examples/range_type.evg) uses an initialized-range
fact inside `Slot<T>` to authorize a typed element loan. Consuming the complete
record removes the parent before extraction changes that fact. Its generic
owning payload is moved once, and the empty backing buffer is freed. An empty
range wrapper over a billion-slot buffer uses the same obligation and certificate
count as its eight-slot version.

[range_drop.evg](../examples/range_drop.evg) implements cleanup of that owned
slot directly in Evergreen. A complete pattern consumes the destructor receiver;
only then may `move` extract a projected union member into its matching shape.
Ordinary member, liveness, and write-footprint checks remain in force. The empty
backing buffer is freed, and the moved payload receives normal local cleanup.
A borrowed payload slot requires its own declared write footprint even inside Drop.

This does not finish general invariant transport: scalar-only quantified facts
captured under an initial `self` root cannot yet be named through a different
borrowed parameter root. Referenced array ranges retain their actual backing
plane and work in the example above. Capacity-conditional pointer observations,
resource range loop frames, and general destructor prefix cleanup remain pending.
Type-invariant imports retain the same unresolved frontend substitution boundary
as other contract imports.

Destructor bodies can now use ordinary `while` statements with the same entry,
preservation, exit, frame, and optional ranking checks as runtime functions.
[drop_loop.evg](../examples/drop_loop.evg) proves a finite counter update during
cleanup. An unmeasured loop marks Drop as potentially divergent, and both actual
cleanup and cached cleanup summaries propagate that classification to callers,
including aggregate cleanup. Such callers cannot be used as total proof
computations. Empty arrays and borrowed references do not run element Drop and
do not inherit its divergence. Consuming surrounding owners in a loop still
requires a resource frame; enabling destructor syntax does not provide one.

Function and loop contract instantiation remains an explicitly unresolved
frontend import, just as scalar contract instantiation does. Logical clauses
retain their actual admission parents and do not become arithmetic assumptions.
Complete independent certification of these state substitutions remains pending.
General nominal-invariant subject transport, quantified domains, conditional
input-cell aliases, and resource range loop frames remain unfinished.
Generalization through declaration summaries or imported trust with untraced
context dependencies is rejected. Indexed payload reads inside quantifiers
remain rejected: opaque frontend identities must not hide a bound argument.
Indexed type observations have the implementation described below.

Pure ideal scalar calls can reduce inside a quantifier to exact arithmetic or
Boolean expressions containing the bound variable. Their preconditions are
separate universal obligations over the enclosing domains, discharged before the
formula is usable. A call in a domain must be valid without assuming that domain;
only outer domains and existing caller facts may justify it. This prevents a
partial predicate from supplying its own prerequisite. These checks apply even
to unproved named facts and admitted theorems. They use the same kernel rules as
indexed type bounds and do not enumerate a finite domain.

This path requires verified definitions with no trusted safety dependency. It
does not import postconditions or fall back to opaque results, and it rejects a
precondition that does not reduce to an arithmetic formula. Nested source calls
retain the defining function's checked safety requirements. Subject keys retain
the function identity and actual argument revisions; bound substitution traverses
all arguments. The source evaluator and its interpretation remain part of the
trusted frontend, rather than a newly independently certified reduction rule.

The kernel now has structured predicate atoms as groundwork for those memory
claims. An atom retains an uninterpreted symbol and its integer arguments.
Universal substitution, free-variable checks, and bound-variable renaming visit
every argument. Predicate congruence requires the same symbol and a checked
equality for each corresponding argument; it preserves all premise hypotheses
and admissions. Changing a symbol cannot be justified by equal indices.

The arithmetic kernel also supports immutable scalar application terms in
`src/compiler/kernel/terms.rs`. Terms are interned DAG nodes, with explicit
function symbols and argument IDs. Variables and applications have distinct
representations; applications from different contents versions or with different
indices cannot alias merely because of a printed spelling. Affine operations
normalize sums using checked arithmetic, and the existing arithmetic certificate
checker works over these atom IDs as well as the frontend's current named rows.

Free-variable collection and simultaneous substitution follow application
arguments iteratively and visit shared nodes once. Rewriting preserves existing
nodes. IDs carry an arena identity and cannot be used in another arena; they are
local references, not portable proof-artifact identities. Operations accept an
explicit work budget. Regression tests exercise a 4,000-level shared DAG without
expanding it into a tree, and reject arithmetic certificates after changing a
contents version or index.

This scalar term layer is kernel groundwork, not yet source-level indexed
payload support. The frontend still uses named affine rows. Connecting structured
terms to propositions, portable artifacts, typed array-read interpretations,
congruence evidence, and quantified source elaboration remains required. A bare
application supplies no truth, bounds, memory access, or ownership authority.

Atoms establish no truth by their construction and have no built-in memory or
ownership meaning. They cannot enter arithmetic paths as fresh Boolean variables.
The kernel also checks closed predicate definitions. Every free integer is an
explicit parameter, including captured array extents, stored indices, and type
selectors. Definitions can only refer to earlier declared predicates, cannot be
redefined, and unfold by a checked implication in either direction. Arguments
substitute simultaneously; a replacement containing another parameter's name is
not rewritten again. Capture, arithmetic overflow, and work limits are checked
before expanded rows are retained. Defining a predicate provides no proof that
the predicate is true. An opaque predicate declaration registers a fresh symbol
and its arity with no body and no evidence node. It cannot be unfolded or later
redefined. Closed definitions can refer to such earlier opaque predicates while
retaining their integer arguments; unfolding the wrapper does not prove its
opaque dependency.

Inside source universals, `typeof(array[i]) == T` and `!= T` retain the bound
index and the immutable array contents identity. The frontend builds a balanced
selector definition from the known default and sparse exceptions, without
observing a resource-bearing element at an arbitrary index. Definitions retain
integer selectors rather than payloads or owning handles. They include the
array extent. A separate universal obligation checks index bounds under the
quantifier's domain, including for negative type tests and nested quantifiers.
`omega` proves the unfolded arithmetic conditions; the kernel checks each
definition step and universal introduction. Array writes and alias writes use
fresh contents identities, preventing reuse of an earlier range theorem.

The mapping from verified storage to a selector definition remains a frontend
trust boundary, like the existing scalar and union observation model. These
definitions do not independently certify memory transitions or native execution.
Unknown input-union arrays now use an opaque selector for each immutable array
identity and target member type. Their ranges require checked premises; neither
the declaration nor existing sparse observations invent an empty default. The
checker can forward these range contracts and apply a separately proved
restriction theorem. This creates no element views or payload owners. See
[input_ranges.evg](../examples/input_ranges.evg); its billion-slot variant retains
the same obligation and certificate count as the eight-slot variant.
Empty domains use a checked arithmetic contradiction followed by the kernel's
false-elimination rule. The domain hypothesis is discharged by universal
introduction; it cannot establish a slot type outside that domain or escape
into the surrounding state.

At a demanded input index, the frontend can now link a selector
instance to the observed cell's active-member condition. It specializes a live,
closed range proof with no admissions or pending summaries, proves the domain
at the point of use, then applies an explicit frontend interpretation implication
using kernel `ForallElim` and `ImpElim`. Affine indices such as `2 * i` require
an exact integral specialization. Negative selectors retain their precise
meaning: excluding one member does not select another in a three-member union.
This link remains a frontend memory import, not an independent kernel memory
certificate. No owner is created by proving a selector.

[range_slots.evg](../examples/range_slots.evg) borrows an initialized owning
slot, extracts its real owner, and frees the now-empty backing buffer. A
reference into the extracted payload survives; a typed slot view cannot read
a cleared slot. Mutating a condition used by a range invalidates that
guarantee's subjects; an explicit proof may derive a guarantee independent of
that condition before it changes. Deferred payload planes retain their active-member presence guard,
independently of the branch that first observes them.

Runtime indices now select deferred input cells as well; see
[range_index.evg](../examples/range_index.evg). Before every demand, equality
reuses one existing cell recipe and separation permits another. Each relation
must follow from current admission-free facts. An ambiguous relation, or
previously separate recipes overlapping in a different branch, is rejected
until a conditional plane model can represent it. These checks visit observed
recipes, never the allocation extent. A symbolic nested port remains visible
to alias and liveness checks even when it has no named source footprint; it
grants no nested write authority. Actual calls still recheck borrowed payload
aliases: different array slots can contain references to the same pointee.

Input stores now define a fresh selector whose body distinguishes the changed
index from the earlier contents version. Stored member tests use the actual
replacement tag; other indices refer to the earlier selector. These closed,
acyclic definitions retain all captured indices and extents. Operational resource
reads follow the same store chain, resolving equality or separation against the
original input cell recipes rather than inventing new owners. When a branch
first observes an input cell through a stored version, the join replays primitive
bounds and scalar invariants of its immutable input recipe. It does not assume
nominal invariants about replacement values or changed live pointees.

[range_store.evg](../examples/range_store.evg) implements generic push and pop
on an initialized prefix followed by empty storage. Each operation names its
entry guarantee, changes one slot, proves a general frame implication from a
local range hypothesis, then applies that implication to the saved guarantee.
`typeof(old(*data)[i])` observes the entry selector; it does not copy or materialize
an owning array. A missing application does not automatically carry an input
range across the write. A later write creates another selector and expires the
new guarantee in turn.

Selector reduction builds kernel-checked conjunctions, disjunctions, negations,
universal specialization, and predicate unfolding. An undecided arithmetic
index guard can split into two local hypotheses; the guard-or-negation
disjunction has its own arithmetic certificate, and `OrElim` discharges both
branches. Local arithmetic hypotheses are preferred over unrelated ambient
storage imports. No predicate becomes an arithmetic Boolean or an assumed truth.
The negative type-test variants erase to identical native code. The billion-slot
variant retains the same obligation and certificate counts.

General joins, conditional input-cell identities, and resource loop frames
remain unfinished. Explicit specialization into a nested or restricted universal
works. Operational reads, empty-buffer narrowing, and destruction still
perform their own ownership and current-state checks; a false admitted range
does not erase an initialized owner. See [sparse_ranges.evg](../examples/sparse_ranges.evg).
Its generic allocator now advertises the initial empty range as a checked
postcondition. The caller reuses that guarantee, and its later writes still
expire the old range. No allocation-capacity enumeration is involved.

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
