# DeepSeek Harness ADR-04: Incarnation Identity, Freshness, and Alpha-Equivariance Architecture

| Field | Value |
|---|---|
| Decision ID | `ADR-04` |
| Status | **Architecture accepted — spike compiled** |
| Artifact version | `1.1.1-accepted-compiler-validated` |
| Semantic closure status | **Architecture resolved; downstream equivariance proofs pending** |
| Date | 2026-08-26 |
| Resolves | `BD-NAMES` (identity, freshness, and name-renaming architecture) |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Depends on | ADR-01 (equivalence), ADR-02 (coeffect store/partiality), ADR-03 (unified state), ADR-03-CLOSURE (BD-STATE) |
| Companion artifacts | `DeepSeek-Harness-08-ADR-04-Incarnation-Identity-and-Alpha-Equivariance-Architecture.json`; `DeepSeek-Harness-08-ADR-04-Incarnation-Identity-and-Alpha-Equivariance-Architecture-Spike.lean` |
| Frozen baselines | Harness-03 `1.0-frozen`; Harness-04 `1.0-baseline` |

## 1. Decision

The theorem-facing model uses an opaque `IncarnationId` for one allocation lifetime.
An ID is never reused inside one modeled run/trace identity domain. An epoch reset is
permitted only with a fresh identity namespace and no cross-boundary references. The
ADR-03 registry remains keyed by that ID, while the no-reuse ledger is carried at the
orchestration/trace boundary rather than inserted into ADR-03's `RawState` or its default
coeffect observation.

The paper's local insertion condition is retained as a compatibility predicate:

```text
CurrentFresh registry n  := n ∉ dom(registry)
```

The theorem profile adds the stronger lifetime condition:

```text
EverFresh ledger n := n ∉ everIssued
```

Every allocation carries an explicit freshness witness and monotonically adds its ID to
`everIssued`; retirement/removal deletes only the current registry entry and never erases
the ledger. Nested registrations (including the name returned by a D47 inverse handle)
must appear in the allocation labels/history, so they cannot evade the no-reuse check.
Consequently, an allocation-aware transition is evaluated over the product boundary
`(RawState, NameLedger/TraceMeta)` (or an equivalent orchestration state); `RawState` alone
is not a Markov carrier for the lifetime-freshness claim.
The default ADR-01 `CoreStateObs` remains allowed to project away this ledger, but it must
not then be used to state freshness-sensitive rule applicability or L55-style
same-rule-preservation for allocation steps. Such steps use a name-aware observation over
the product, or are treated as externally labelled orchestration inputs; lifecycle-only
suffixes may continue to use the default observation when the ledger is irrelevant.
The intended split is therefore: a lifecycle relation `→ₗ` on `RawState` for steps whose
applicability does not inspect freshness, and an orchestration relation `→ₒ` on
`(RawState, TraceMeta)` for allocation/retirement steps. If one unified labelled `Step`
relation is used instead, its state and observation must include the ledger component.

`ParentRef` is `Option IncarnationId`: `none` is a synthetic root marker, not a provider
entry, and multiple top-level fibers are allowed. Parent closure and acyclicity remain
explicit predicates; this ADR does not silently require a parent to be active, nor does it
choose the later control/staging proof of rootedness.

Alpha-renaming is an explicit action by `χ : Equiv.Perm IncarnationId`. It maps registry
keys, parent references, provider/committed/target-view references, allocation history,
ever-issued ledgers, actor labels, and trace labels. `none` is fixed. This action is
separate from ADR-01's observational relations (`CoreStateObs`, `LifecycleObs`, and
`EraseControl`); alpha equivalence is a reindexing witness, not a default observation.

`ComponentId`/loader `EntryId`, runtime object atoms, and theorem-level incarnation IDs are
different identities. If a runtime atom is recycled, the refinement boundary uses
`(atom, generation)` (or an allocation-event token) and maps it injectively to a fresh
`IncarnationId` on the admissible allocation domain. The standalone spike uses the
stronger globally-injective interface as a smoke-test boundary; a concrete integration may
carry an explicit admissible-domain subtype. A globally fresh runtime UID is merely a
special case. No theorem may
index an episode by a bare reusable atom.

## 2. Why this decision is necessary

The paper's D44--D47 rules describe an atom set and a finite partial registry. `O-Insert`
requires only that the chosen atom is absent from the *current* registry; D45's `O-Remove`
can therefore free it. Section 4.4.1 explicitly allows reissuing a freed name.

Later material uses the same name as if it denoted one stable actor: D53 indexes traces,
fields, episodes, and `e_n`; L56 renames all such references by one bijection; D60/T66
quantify over the names held by a trace; D67/L68 use registration order to reason about
parent/support well-foundedness; and T73 matches registration trees modulo a bijection.
With raw atom reuse, two different lifetimes have the same index and these statements are
ambiguous (a stale inverse or parent reference can be applied to the wrong incarnation).

The decision is therefore a deliberate refinement/profile, not a claim that the literal
current-domain rule already has lifetime semantics. A reusable-atom implementation must be
freshened to allocation-event/generation IDs before the lifetime-indexed theorems are
applied.

The paper also describes a runtime `fiber.uid` as fresh and never reused, while its loader
`entry.id` is a separate reconciliation/configuration key. That description motivates the
refinement but is not, by itself, a proof about an arbitrary implementation.

## 3. Normative architecture

### 3.1 Identity layers

| Identity | Role | Can be reused? | Appears in theorem registry? |
|---|---|---:|---:|
| `ComponentId` | code/catalog identity; many instances may share it | yes | no |
| `EntryId` | loader/configuration reconciliation key | implementation policy | no |
| runtime atom/UID | host object or runtime handle | possibly | no |
| `IncarnationId` | one allocation lifetime | no within a modeled run/trace identity domain | **yes** |

`IncarnationId` is abstract and requires equality for finite-map operations, but the generic
theorem layer does not assume a global `Fintype`. A fresh allocator is not a deterministic
`min`/`max` function in the core: arbitrary permutation renaming would not preserve such a
choice. Allocation is relational/witnessed; an executable allocator is a later
specialization with an explicit supply or exhaustion result. That optional `FreshSupply`
must either be excluded from L56/T73 or be equipped with its own permutation action and
equivariance law; the core theorem does not assume a canonical choice.

### 3.2 Current versus lifetime freshness

The boundary keeps both predicates:

```lean
CurrentFresh r n := n ∉ r.keys
EverFresh ledger n := n ∉ ledger.everIssued
AllocationAllowed r ledger parent n :=
  CurrentFresh r n ∧ EverFresh ledger n ∧ ParentAllowed r parent
```

When `registry.keys ⊆ ledger.everIssued`, `EverFresh` implies `CurrentFresh`. Thus the
strong theorem profile subsumes the paper's insertion premise without deleting it from the
surface API.

The successful allocation transition is conceptually:

```text
everIssued' = insert n everIssued
registry'   = insert n registry
```

under explicit freshness and parent witnesses. The checked interface may return `Option`
or `Except`; failure is not an identity/no-op transition. `O-Remove` changes only the
current domain. A retirement handle captures the allocated incarnation, and a later handle
cannot target a reissued runtime atom because the abstract ID is globally fresh.

### 3.3 Parent/root boundary

```text
ParentRef N       = Option N
ParentAllowed r none     = True
ParentAllowed r (some p) = p ∈ dom(r)
```

`ParentClosed`, `ParentAcyclic`, and (where needed) `ParentForest`/`ParentRooted` are
separate predicates. The virtual root is fixed under every alpha permutation. Registration
order/birth index is separate from the ID and remains available for D67/L68; ordering by
the arbitrary representation of an ID is forbidden.

### 3.4 Alpha action and opacity

For `χ : Equiv.Perm N`, the action maps:

- registry domain keys;
- `Option N` parent pointers;
- provider IDs in committed/target views;
- the ever-issued/allocation ledger;
- allocation/actor/registration labels and trace references;
- future episode, `S(n)`, `V(n)`, precedence, and support indices by reindexing.

Dependency keys and name-neutral payloads are unchanged. The spike's generic `payload : P`
therefore carries an explicit identity-opacity assumption. If behavior, accumulators,
ambient data, values, target hashes, or interpreter closures can capture an ID, the later
control/refinement layer must provide a `RenamePayload`/`RenameAmbient` action and prove
interpreter equivariance. It is not sound to rename only the registry and claim L56/T73.

The minimum labelled-rule contract is:

```text
step before label after  →
step (χ·before) (χ·label) (χ·after)
```

This is stronger than a unary predicate on registries and is intentionally left as a
contract for BD-CONTROL. Registry lookup/domain and identity laws are compiled in the
spike; full parent/WF, target/provider, episode, and trace laws remain proof obligations.
`TraceEquivariant` in the spike is an existential contract for renamed copies, not yet a
canonical trace action with identity/composition laws.
The spike's `StepLabel` is likewise only a name-footprint shell. The authoritative rule
tag and per-allocation owner/parent records (for steps that allocate multiple children)
belong to the BD-CONTROL constructors; until then, no NAMES gate claims a completed
operational trace encoding.

### 3.5 Trace support and episodes

`NameTrace.names` is a declared finite-support envelope: it is not automatically the exact
minimal set of names occurring in the trace. `TraceHasFiniteNames` says that this envelope
fits inside a finite `Finset`, while `TraceFieldsSupported` and `BoundaryNamesSupported`
make the listed allocation, label, parent/view, registry, and ledger fields lie in it.
The control/trace layer must define the exact occurrence union (including the initial
issued set, every boundary snapshot, and nested allocation) and either prove equality with
`names` or use the envelope explicitly in the theorem statement before interpreting it as
T66's set of names. Under
`NoReuse`, `EpisodeKey = IncarnationId` is well-defined. If a selected runtime profile
permits atom reuse without freshening, the episode key must instead be an
allocation-event/generation ID. T66 must separately state finite name support and any
finite per-ID work bound.

The spike's `NameWF` is deliberately only the name-boundary fragment
(`LedgerSound ∧ ParentForest`); it is not the full D58 `CoreWellFormed` predicate. A
parent-rooted/tree theorem requires the corresponding finite closed-forest/root witness at
the integration boundary. Likewise, the reusable-runtime-atom profile still needs a
separate trace-lifting/refinement theorem before it can be used as a literal-paper model.

## 4. Lean-facing spike

The standalone companion uses namespace `CordisADR04` and imports the ADR-02 `Finmap`
carrier API without importing production modules that would redeclare names. Its top-level
`IncarnationId` is an abstract type parameter (an integration may instantiate it with an
opaque nominal/token type), deliberately distinct from `RuntimeAtom` and `EntryId`. It
contains:

```text
ParentRef, NameCell, NameRegistry, NameLedger, FreshSupply
CurrentFresh, EverFresh, LedgerSound, ParentAllowed
AllocationAllowed, RegistrationWitness, allocateLedger, checkRegistration
registerFresh, tryRegisterFresh
renameFinset, mapValues, renameParent, renameCell, renameRegistry
renameLedger, NamedBoundary, renameBoundary, AlphaRenamed
RuntimeIdentity, ComponentId, EntryId, RealmId, RuntimeRefinement
StepLabel, BoundaryStepRelation, StepEquivariant
TraceHasFiniteNames, TraceFieldsSupported, NameTrace, TraceRenameSpec
TraceEquivariant, NoReuse, ParentClosed, ParentAcyclic, ParentForest
NameWF, WFEquivariant
```

The compiler-checked evidence includes (owner-run local check; the raw compiler log is not
retained as a separate artifact):

- successful/failed ledger allocation equations;
- current/ever freshness bridge;
- registry-domain and provider-view lookup transport under `χ`;
- root preservation, ledger-soundness preservation, and freshness invariance;
- allocation-step renaming;
- identity law for registry/ledger renaming;
- a labelled source→target equivariance contract;
- a declared finite support envelope for trace names, tied to the initial issued set and
  allocation/label/reference fields by `NameTrace`/`TraceFieldsSupported` (exact
  occurrence-set equality is a downstream obligation);
- no-reuse preservation under renaming;
- separation of runtime atom and generation, with an injective refinement map.

The spike deliberately does **not** pretend to prove the full lifecycle calculus. The
pending obligations are named below so that later ADRs cannot accidentally inherit a false
claim of readiness.

## 5. Alternatives considered

| Alternative | Decision | Reason |
|---|---|---|
| Current-registry freshness on bare atoms only | Rejected as theorem identity | Faithful to local O-Insert, but ambiguous for D53/L56/T66/T73 after reissue. |
| Globally fresh opaque `IncarnationId` with trace ledger | **Accepted** | Stable episode/parent/view identity and simple alpha action; matches the implementation's described never-reused UID profile. |
| `(RuntimeAtom, Generation)` as the authoritative registry key | Rejected for core; allowed as refinement | Models reuse directly but exposes runtime allocation policy and complicates nominal proofs. It can map injectively to the accepted ID layer. |
| Allocation-event tokens as the only core ID | Deferred alternative | Semantically sound, but event/order plumbing belongs with the later trace/control layer. |
| Deterministic counter or `min unused` allocator in core | Rejected | It is not equivariant under arbitrary alpha permutations and overcommits to a supply representation. |
| Per-cell generation field while retaining bare atom keys | Rejected | Parent/view/handle references can still become stale or ambiguous unless every reference is upgraded; this is an incomplete repair. |
| Quotient registry by alpha from the start | Rejected for executable core | Loses representatives needed by operational rules and still requires explicit congruence/action proofs. |

## 6. Acceptance and remaining obligations

| Gate | Result |
|---|---|
| `NAMES-01` Separate component, entry, runtime, and incarnation identities | represented and compiled |
| `NAMES-02` Current freshness plus monotone ever-issued ledger | represented; bridge and checked allocation equations compiled |
| `NAMES-03` Root-safe `Option` parent and explicit closure/acyclic predicates | represented; full preservation/rootedness proof deferred |
| `NAMES-04` Alpha action on registry, views, parents, ledger, and labels | registry/view/ledger action and identity law compiled; composition/inverse and full WF preservation deferred |
| `NAMES-05` Allocation events visible, including nested registration | boundary label/trace fields represented; concrete constructors deferred to BD-CONTROL |
| `NAMES-06` Lifetime-indexed episodes and stale-handle safety | architecture fixed; theorem proof deferred to control/trace layer |
| `NAMES-07` Finite support for actual traces | explicit `TraceHasFiniteNames`/`NameTrace` support-envelope interface compiled; exact occurrence-set equality deferred |
| `NAMES-08` Runtime atom reuse refinement | `(atom,generation)` and injective map compiled; implementation correspondence pending |
| `NAMES-09` Payload/ambient/target-hash opacity or rename action | explicit contract; no silent capture assumption |
| `NAMES-10` Preserve ADR-03 carrier and ADR-01/02 observation boundaries | no change to frozen carrier/baselines |
| `NAMES-11` Pinned Lean compile/no placeholders | passed locally; exit code 0 (warnings only) |
| `NAMES-12` Full alpha/rule/trace/episode/provider/target equivariance | deferred to BD-CONTROL, BD-ITER, BD-SUPPORT, and implementation refinement |

The spike is evidence for the architecture, not a completed proof of L56 or T73. Those
theorems still require the selected control/trace semantics to instantiate
`StepEquivariant`, prove ledger/label coverage for every nested allocation, establish the
exact trace occurrence set when needed, reindex episodes/support/precedence, and handle
payload actions.

Accordingly, “accepted” here means that the global representation decision is fixed and
the boundary shell compiles. It does not mark every `NAMES-*` proof gate as discharged;
the deferred rows are deliberate inputs to the next control/trace ADRs.

## 7. Readiness effect

Harness-03 and Harness-04 are immutable; this ADR changes neither dependency edges nor the
disposition file. It removes only `BD-NAMES` from the derived blocker sets.

The direct rows that become blocker-free after already accepted ADR-02/03 decisions are:

```text
D45, D58, D65
```

Other affected rows remain blocked by their independent decisions:

```text
D44      BD-ITER, BD-STAGING
D47      BD-CONTROL
D53      BD-EQUIV, BD-CONTROL
L56      BD-CONTROL
T59      BD-CONTROL
D60      BD-ITER, BD-EQUIV, BD-CONTROL
T66      BD-ITER, BD-CONTROL
D67      BD-SUPPORT
L68      BD-SUPPORT, BD-CONTROL
L71      BD-EQUIV, BD-CONTROL
L72      BD-SUPPORT, BD-EQUIV, BD-CONTROL
T73      BD-SUPPORT, BD-EQUIV, BD-ITER, BD-CONTROL
D74      BD-SCOPED
R.full   BD-ITER, BD-STAGING, BD-CONTROL
```

In particular, this ADR does not resolve `BD-CONTROL`, `BD-ITER`, `BD-SUPPORT`, or
`BD-SCOPED`, and it does not silently turn the paper's reissuable-atom paragraph into a
literal no-reuse theorem. A later change to the identity carrier, no-reuse policy, or
observation/ledger boundary requires a superseding ADR.

## 8. Revision policy

- Editorial clarification: patch version only.
- Repair of the spike/proof while retaining the decision: revised ADR-04 companion.
- Changing lifetime identity, allowing bare-atom theorem indexing, or moving the ledger
  into the core observation: superseding ADR required.
- Frozen Harness-03/04 and accepted ADR-01/02/03 artifacts remain unchanged.
