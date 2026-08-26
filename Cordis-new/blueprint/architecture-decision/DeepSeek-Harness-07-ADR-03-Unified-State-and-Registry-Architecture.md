# DeepSeek Harness ADR-03: Unified State and Registry Architecture

| Field | Value |
|---|---|
| Decision ID | `ADR-03` |
| Status | **Accepted — compiler validated (user-reported)** |
| Architecture validation | Accepted after paper audit, type/variance audit, and alternative comparison |
| Implementation validation | **Passed (user-reported)** — the repaired Lean spike supplied on 2026-08-26 compiles; the project build also completed successfully |
| Date | 2026-08-26 |
| Resolves | `BD-STATE` from Harness 04 |
| Depends on | `ADR-01: Equivalence Architecture` (accepted; user-reported one-shot compilation); `ADR-02: Coeffect Store, Specification, and Partiality Architecture` (accepted; user-reported revised-spike compilation) |
| Supersedes | Nothing |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Frozen dependency baseline | Harness 03 `1.0-frozen`, JSON SHA-256 `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| Disposition baseline | Harness 04 `1.0-baseline`, JSON SHA-256 `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |
| Companion artifacts | `DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture.json`; `DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike.lean` (compiler-validated repaired revision); historical pre-repair spike retained as `DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-v1.0-compiler-pending.lean`; repair report `DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fix-Notes.md` |

## 1. Decision

The formalization SHALL represent a concrete runtime state as a **positive, finite registry shell** with explicit well-formedness predicates:

```text
RawState = Ambient × Finmap IncarnationId FiberCell
ValidState = { s : RawState // WellFormed s }
```

The registry is the authoritative finite collection of currently known fiber incarnations. A fiber cell contains only data and **reified codes/tokens**; it SHALL NOT contain a function whose domain or codomain is `RawState` (in particular, no stored `RawState → RawState` action or inverse closure). Behavior, lifecycle transitions, iterators, failure choices, and recovery are supplied by an external relation/interpreter parameterized by the acting incarnation.

The coeffect context is a **derived view**:

```text
coe(s) = disjoint union of the local stores of fibers that currently provide
         bindings (active/providesNow), subject to WellFormed invariants.
```

There is no implicit mutable `rootStore` in the Section 4 core. A nonempty immutable seed is allowed only through a separately named boundary extension; the core calculus is its empty-seed specialization. Parent links, lifecycle payloads, freshness policy, iterator representation, failure/control labels, and scoped realms remain explicit parameters or later ADRs rather than being smuggled into this state decision.

This decision resolves `BD-STATE`. It makes `D32`, `D33`, and `D50` free of their state blocker, but it does not resolve any other blocker that remains on an affected node.

## 2. Why a decision is necessary

The paper uses two descriptions of state that cannot be copied literally into Lean.

### 2.1 The `Γ∞` equation is a design equation, not an inductive declaration

Definition 32 writes, schematically,

\[
\Gamma_\infty \;\triangleq\; \mu\Gamma.\,\Gamma\times(\Gamma\to\Gamma)\times\Sigma.
\]

The occurrence of `Γ` to the left of an arrow is negative. Ordinary Lean inductive declarations require strict positivity, and an ordinary set-theoretic fixed point with an unrestricted `Γ → Γ` component is also subject to a cardinality obstruction. The displayed equation is therefore read as an architectural layering metaphor: a context carries an accumulator, an action capability, and a coeffect view. It is not a type declaration to reproduce with `inductive` or a literal recursive `structure`.

### 2.2 The later `State / Registry / Fiber` prose forms another negative cycle

Definitions 43–50 put fibers in a finite registry, while a fiber carries an effect `e` and accumulator `g` that are presented as state-transforming functions. If those functions are stored directly, the cycle is:

```text
State → Registry → Fiber → (State → State)
```

This is the same variance problem in a more operational spelling. It also makes it impossible to state the intended frame property without deciding the entire iterator, failure, and control language at once.

### 2.3 The paper's global coeffect is derived, not a second mutable cache

Definition 45 describes the state coeffect as the union of local tables of exactly the active fibers. If a state record additionally stores an independently mutable global table, every transition would need a coherence invariant and two update paths. The core paper never needs that duplicate cache. A projection computed from the finite registry is both closer to the text and easier to reason about with ADR-02's `Finmap` laws.

### 2.4 Runtime nesting is finite per state but not globally depth-bounded

A finite registry with parent pointers represents any concrete finite runtime hierarchy. It does not impose one fixed maximum nesting depth. A finite-depth tower of context types would impose a compile-time bound and would still need a sum/limit construction for dynamic depth. The registry is therefore the authoritative representation; a finite tree is a property of each state, not a global type index.

Without this decision, contributors could independently choose a recursive fixed point, a nested product, a mutable global table, or a state-indexed closure field. Those choices are not definitionally compatible and would make D33, D43–D50, D53, and the Section 4 rules impossible to integrate.

## 3. Decision drivers

| Driver | Required consequence |
|---|---|
| Lean positivity and universe safety | No negative recursive occurrence and no unrestricted state-indexed function in a recursive carrier. |
| Fidelity to D45 | A finite registry and active-table union are explicit; no hidden root store is added to the core. |
| Arbitrary finite runtime hierarchy | Parent pointers permit unbounded (but finite-per-state) nesting. |
| ADR-02 compatibility | Local tables are `Store V = Finmap V`; missingness remains `Option`, not a default value. |
| Provider uniqueness | Static provision disjointness and table-confinement are explicit `WellFormed` obligations. |
| Lifecycle staging | `installed`, `providesNow`, and `committed` visibility are separate predicates; Reloading/Unloading can be installed without contributing to the global store. |
| D48 confinement | State updates are exposed through actor-indexed relations and frame lemmas, not arbitrary state functions hidden in cells. |
| D53 factorization | Data/state projection, control edits, traces, and observations can be named separately. |
| ADR-01 observations | `CoreStateObs` uses the derived coeffect store; lifecycle/control observations remain separate relations. |
| Later iterator/control work | Action and lifecycle codes are opaque parameters so `BD-ITER`, `BD-STAGING`, and `BD-CONTROL` can be resolved later without changing the state shell. |
| Runtime refinement | Mutable objects, disposer closures, and proxy behavior can be related to the shell by a refinement relation rather than made part of its mathematical carrier. |
| Team stability | All contributors use one state carrier and one projection API before module-level work begins. |

## 4. Alternatives considered

| Candidate | Decision | Reason |
|---|---|---|
| Literal `μΓ. Γ × (Γ → Γ) × Σ` | **Rejected** | Negative recursive occurrence; no ordinary Lean inductive declaration; ordinary Set fixed-point reading is not available for unrestricted functions. |
| Recursive `State`/`Registry`/`Fiber` carrying closures | **Rejected** | Reintroduces the same negative cycle and hides the actor/frame footprint needed by D48. |
| Domain-theoretic or quotient fixed point as execution state | **Rejected for the core** | Overkill for finite runtime registries, loses concrete representatives needed by operational rules, and would require a separate executable refinement. |
| Finite-depth tower `Ctx n` | **Rejected as authoritative** | Bounded by a type index and awkward for dynamic registration; may be used later as a lemma for a bounded fragment. |
| Abstract state interface only, with no concrete shell | **Rejected** | Cannot prove finite-registry, parent, support, provider, and frame facts needed by Section 4. |
| One state record with a duplicated cached global coeffect store | **Rejected** | Creates a second mutation path and a coherence burden not present in D45. |
| Implicit mutable `rootStore` in the core | **Rejected** | Changes the empty-state and provider-uniqueness assumptions of D45, T63, and T66. A named immutable seed extension is allowed below. |
| Put the complete iterator/failure/control DSL in `FiberCell` now | **Rejected** | Prematurely resolves `BD-ITER`/`BD-CONTROL` and recreates recursive references through the code semantics. |
| **Positive finite registry plus external code semantics** | **Accepted** | Satisfies positivity, preserves finite dynamic hierarchy, matches D45, and leaves later semantic choices explicit. |

## 5. Normative type architecture

The names below are architectural names. Final module paths and namespace spelling may change in the executable blueprint; the carrier boundaries and obligations are normative.

### 5.1 Parameters and reified codes

The state shell is parameterized by:

```lean
Ambient          : Type
IncarnationId    : Type
Key              : Type
Value            : Key → Type
ComponentCode    : Type
BehaviorCode     : Type
AccumulatorCode  : Type
Life             : Type
```

`BehaviorCode` is an instantiated/configured behavior for one incarnation, not necessarily a bare component identifier. None of these code/token types may contain a `RawState`-indexed function. If an implementation uses closures, it reifies their captures into data and interprets them outside the shell.

This is a lexical/module stratification rule: the code/token types are declared in a layer that does not import `RawState`. Merely writing them as unconstrained `Type` parameters would not enforce that rule, so a production module must keep the dependency direction auditable.

The Section 4 core is single-realm. A later scoped-context ADR may replace `IncarnationId` provider locations by a realm-qualified location, but it must provide a flat embedding and re-prove the affected provider/frame lemmas.

### 5.2 Lifecycle policy is a parameter, not a hidden phase choice

```lean
structure LifecyclePolicy (Life : Type) where
  installed         : Life → Bool
  providesNow       : Life → Bool
  committedVisible  : Life → Bool
```

The three predicates are intentionally distinct.

- `installed` says that the lifecycle phase is still installed (a retired vestigial registry entry may be present but not installed).
- `providesNow` says that its local table contributes to the derived global coeffect.
- `committedVisible` says that a previously committed consumer view may still be used during guarded teardown.

The spike's coherence predicate additionally requires an accumulator and committed view whenever a lifecycle policy says that a fiber is installed, requires either payload to imply installation, and requires an accumulator whenever the fiber contributes. The core does not require inactive local tables to be empty; that stronger reachable-state fact belongs to the lifecycle transition ADR.

For the base `Inactive | Active` lifecycle these may coincide. For the extended lifecycle, a Reloading or Unloading fiber can remain installed while `providesNow = false`; an existing committed view can remain valid until the guarded unload step. The concrete constructors and failure payloads belong to `BD-ITER`, `BD-STAGING`, and `BD-CONTROL`.

### 5.3 Provider views

A target/committed view is a finite dependent map, not a total function with an implicit default:

```lean
structure ProviderView (IncarnationId Key : Type) [DecidableEq Key] where
  domain    : Finset Key
  providers : Finmap (fun _ : Key => IncarnationId)
  keys_eq_domain : providers.keys = domain
```

`TargetView` has type `Option (ProviderView ...)`: `none` means retired or currently unsatisfied. `some view` carries a proof that the finite provider domain is exactly the requirement set. `globalLookup` searches the current active projection. `committedLookup` consults a fiber's stored committed view and the provider's local table; it is the API used for guarded teardown and is not identified with current global lookup.

### 5.4 Fiber cell

```lean
structure FiberCell where
  component    : ComponentCode
  behavior     : BehaviorCode
  requirements : Finset Key
  provisions   : Finset Key
  parent       : Option IncarnationId
  localStore   : Store Value
  retired      : Bool
  lifecycle    : Life
  accumulator  : Option AccumulatorCode
  committed    : Option (ProviderView IncarnationId Key)
```

The cell contains no `State → State`, `State → Option State`, iterator closure, inverse closure, or proof field quantifying over the state carrier. Proofs about a cell's fields live in `WellFormed` or in transition premises.

`component`, `behavior`, and `accumulator` are codes/tokens. The optional accumulator and committed-view fields are normalized lifecycle payload slots; `LifecycleCoherent` is the required invariant linking them to the abstract `Life` value. A later lifecycle ADR may instead make those payloads indexed constructors of `Life`, but it must preserve this shell-level API. The `requirements` and `provisions` fields are authoritative for this shell; if `component` is a catalog identifier with its own specification, `WellFormed` must include the equality/compatibility proof rather than allow two silently different declarations. Per-incarnation behavior is required: two fibers running one component may have different configuration and different accumulator histories. The external interpreter receives the acting incarnation explicitly.

### 5.5 Registry and raw/valid state

```lean
abbrev Registry := Finmap (fun _ : IncarnationId => FiberCell)

structure RawState where
  ambient  : Ambient
  registry : Registry

def ValidState := { s : RawState // WellFormed s }
```

`RawState` is intentionally permissive so that intermediate operational results, counterexample states, and failed checked operations can be represented. Trusted constructors and the production transition relation require a `WellFormed` proof or return an explicit partial/error result. The subtype `ValidState` is a convenience boundary, not a replacement for the raw carrier.

`Ambient` means only state inside the chosen formal observation boundary. External I/O, untracked emissions, and host resources are events or a separate refinement; they are not silently claimed to be recoverable by `CoreStateObs`.

### 5.6 Tracked context and external action semantics

The D32 “accumulator plus context” view is represented without a recursive fixed point:

```lean
structure TrackedContext where
  state       : RawState
  accumulator : AccumulatorCode
```

For a lifecycle policy, define `coe(s) := activeUnion(policy, s)`. Its coeffect projection is explicit: `trackedCoeffect ctx = coe(ctx.state)` (the spike names this `TrackedCoeffect`).

The finite registry supplies the hierarchy and parent relation. The accumulator token supplies the local undo/compensation history; its denotation is external.

The core semantics is relation-valued so later control decisions may be nondeterministic:

```lean
structure ActionSemantics where
  forward : IncarnationId → BehaviorCode → RawState → RawState → AccumulatorCode → Prop
  inverse : IncarnationId → AccumulatorCode → RawState → RawState → Prop
```

An implementation may add an executable evaluator (`Option`, `Except`, or a finite result list), but that evaluator is related to these relations and is not stored in `FiberCell`. Required obligations include actor-indexed confinement, selected-inverse/recovery laws from ADR-01, and preservation of `WellFormed`; they are predicates on the semantics, not fields that create a recursive carrier.

The code-denotation bridge is explicit: if two behavior/accumulator codes are claimed equivalent, a later law must show that their interpreted state transitions and selected inverses respect the ADR-01 relation. Token identity is not semantic equivalence by default.

### 5.7 State maps and control edits

D53/Table 1 is factored at the API boundary:

```text
StateMap    : RawState → RawState          -- data/action interpretation
ControlEdit : RawState → RawState          -- registry/lifecycle edit
step         = ControlEdit ∘ StateMap      -- when a rule is deterministic
```

For nondeterministic rules, a labelled relation carries the chosen `StateMap`/`ControlEdit` witness. No such function is a stored field of the state. Registration, retirement, and removal are explicit control edits; actor-local table modification is a lens-like update with frame lemmas.

## 6. Coeffect projection and state invariants

### 6.1 Active-table projection

Let `contributesNow(policy, cell)` abbreviate `policy.providesNow cell.lifecycle = true`. The canonical core projection is:

\[
\operatorname{coe}(s)
  = \biguplus_{n\in\operatorname{dom}(s.registry),\;\operatorname{contributesNow}(n)}
       \operatorname{localStore}(n).
\]

The spike contains a noncomputable semantic representative that traverses a finite key list. The production theorem package must additionally prove that the result is independent of key traversal order. The recommended executable implementation is an absorbing `Option Store` fold: a disjoint merge returns `some (σ ∪ τ)`, while any overlap returns `none`; conflict is absorbing, so the merge operation is commutative under the explicit disjointness hypothesis. On a `WellFormed` state the result is never `none`, and its unwrapped store is the displayed union.

Raw `Finmap.union` is left-biased. Under pairwise disjoint support the bias is unobservable and the union is commutative; this fact must be proved, not assumed from notation.

### 6.2 Three provider notions

The API keeps these notions separate:

1. **Declared possible provision**: `k ∈ cell.provisions`.
2. **Actual local support**: `k ∈ cell.localStore` (which may be a strict subset during a transition).
3. **Current active provider**: `k` is present in `coe(s)` and the contributing cell is active.

The retirement bit is intentionally not part of `contributesNow`: `O-Retire` may mark a fiber retired while it remains Active, and `L-Leave`/Unloading removes its contribution only after dependents have drained. Retirement affects target-view eligibility immediately, but not the active-table union until the lifecycle transition says `providesNow = false`.

`providerOf s k` returns `Option IncarnationId`; it is not a total function with a default. A provider-uniqueness theorem follows from well-formed provision disjointness and table confinement. The theorem is over incarnation identities, not component names, and permits multiple zero-provision fibers.

### 6.3 Well-formedness predicate

`WellFormed s` is a conjunction of named predicates, at minimum:

| Predicate | Required content |
|---|---|
| `ParentClosed` | Every non-root parent pointer names an entry in the registry. |
| `ParentAcyclic` | The transitive parent-edge relation has no cycle. |
| `ParentRooted` (boundary obligation) | The selected names/registration policy supplies the distinguished `root` convention and makes the acyclic parent forest a rooted tree; the spike represents the closed/acyclic part and leaves the root/freshness witness to `BD-NAMES`. |
| `TableConfined` | Every local-store key is declared in that cell's provisions. |
| `ProvisionDisjoint` | Distinct current incarnations have disjoint declared provision sets; retired entries remain in this check until `O-Remove`. |
| `LifecycleCoherent` | The lifecycle policy's installed/providesNow/committed predicates agree with the optional accumulator/committed payload slots; a retired-but-still-Active cell may continue to provide. |
| `CommittedViewClosed` | A stored committed view has exactly the requirement domain. |
| `CommittedProvidersClosed` | Every provider ID named by a stored view is an installed registry entry; the spike separates this check from the domain check. |

Registry keys are the incarnation identities by construction. Freshness, generation, alpha-renaming, and identity reuse are deliberately not specified here; a future names ADR may strengthen the registry transition API without changing this raw carrier.

### 6.4 No implicit root store and the explicit seed extension

The Section 4 core starts with an empty registry and derives `coe(s)` from active local tables. Root-parent fibers can provide root services through ordinary registration. For a runtime host environment that has immutable baseline bindings, define a separately named extension:

```text
RootEnvState = (seed : Store Value, state : RawState)
seededCoeffect(seed, state) = seed ⊎ coe(state)
```

The seed must be unchanged by lifecycle actions and disjoint from every declared provision. This value-only extension is for coeffect observation only; a target/provider calculus using it must introduce an extension-only provider identity such as `root | fiber n` and re-prove uniqueness and guard lemmas. The core is `seed = ∅`. A mutable or overlapping root store would require a new provider-identity and guard proof and is outside ADR-03.

## 7. Update and observation API

### 7.1 Pure persistent registry updates

The primitive operations are pure:

```text
insertFiber  : IncarnationId → FiberCell → RawState → RawState
modifyFiber  : IncarnationId → (FiberCell → FiberCell) → RawState → RawState
removeFiber  : IncarnationId → RawState → RawState
```

They expose frame laws:

- pure registry/control updates preserve `ambient`; an action may change only an explicitly permitted ambient/read slice, as stated by its actor-indexed frame premise;
- a `modifyFiber n` changes only the cell at `n`;
- lookup at every `m ≠ n` is unchanged;
- `removeFiber n` leaves every other registry entry unchanged;
- changing only a local table changes `coe` only through that incarnation's active contribution;
- lifecycle edits have the four explicit projection cases: Active→Unloading removes a contribution, Inactive→Reloading adds none, Reloading→Active adds the table, and guarded unload acts after the provider is already excluded.

These laws are the concrete frame counterpart of D48 and the transition-factorization part of D53. Production proofs should use the `Finmap` façade from ADR-02 rather than unfold the map implementation. The first ambient clause applies to registry/control updates; an actor action that changes ambient data must satisfy its explicit read/write-slice frame premise.

### 7.2 Observation boundaries

The following relations remain separately named and parameterized by ADR-01 relation values:

```text
CoreStateObs R s t
  := StoreObs R (coe(s)) (coe(t))

LifecycleObs R s t
  := CoreStateObs R s t ∧ lifecycle/control observations agree

EraseControl R s t
  := the Section 4 recovery relation that intentionally forgets control fields
```

`CoreStateObs` intentionally forgets `Ambient` and registry control unless a stronger relation is supplied. It must not be used to claim equality of untracked host effects. `LifecycleObs` and `EraseControl` are not interchangeable merely because both may be written with a paper `≈`/`≃` symbol.

### 7.3 Target and committed lookup

`targetView` is specified from current active provider presence and returns `none` when the fiber is retired or unsatisfied. The spike supplies a classical-choice semantic representative; the executable finite provider-map construction is deferred to the later names/control blueprint. A committed view is retained as a cell field and is used by dependents during guarded Unloading. The invariant required for T63 is:

```text
provider Unloading ⇒ its local table is frozen until guarded L-Unload,
                  and dependent committedLookup remains valid meanwhile.
```

This guard is a transition theorem, not a reason to keep an Unloading provider in the active coeffect union.

## 8. Repair manifest for the paper's definitions

| Paper item | ADR-03 repair |
|---|---|
| D32 | Replace the negative `μΓ` equation by `TrackedContext` plus a finite parent-pointer registry and externally interpreted accumulator/action codes. State that this is a representation/refinement target, not definitional equality to `Γ∞`. |
| D33 | Define the coeffect observation through `coe : RawState → Store V`; lift ADR-01/02 `StoreObs` explicitly. |
| D43 | Component declarations use finite requirements/provisions and behavior codes; frame obligations are predicates. |
| D44 | Use the lifecycle-parameterized `FiberCell`; per-incarnation behavior and accumulator tokens are data. |
| D45 | Use finite registry, parent-tree predicates, active local-table union, `Option` provider lookup, and uniqueness lemmas. |
| D46 | Use `Option ProviderView` and an explicit lifecycle policy. |
| D47 | Registration/retirement are external control edits returning explicit identity witnesses; freshness remains `BD-NAMES`. |
| D48 | Actor-indexed external action relation plus local update/frame predicates. |
| D49 | Keep installed/providesNow/committed visibility separate; phase constructors await staging/iterator/control ADRs. |
| D50 | Define relied-upon relation from the finite installed registry and committed provider views. |
| D53 | Split traces, reached states, episodes, state-map/control-edit witnesses, and observation relations; the raw carrier is now available. |
| L55 | State shell is ready; same-label applicability and successor invariance still await `BD-CONTROL` and ADR-01 relation-respect premises. |
| D58 | State the parent-tree and support/uniqueness clauses as `WellFormed`; the fresh-name policy remains `BD-NAMES`. |
| `R.full` | Use one state carrier and labelled external relations; the ten-rule split remains deferred to the iterator/staging/control/names decisions. |

## 9. Effect on dependency readiness

ADR-03 changes only the effective blocker set derived from the frozen disposition baseline. It does not edit Harness 03 or Harness 04.

### 9.1 Affected direct set (integrity check)

```text
D32, D33, D43, D44, D45, D46, D47, D48, D49, D50,
D53, L55, D58, R.full
```

This is exactly the set of direct nodes whose baseline blocker set contains `BD-STATE`.

### 9.2 Effective status after removing only `BD-STATE`

| Node | Remaining blockers | Effective status |
|---|---|---|
| `D32` | none | ready for next-stage specification |
| `D33` | none | ready for next-stage specification |
| `D43` | `BD-ITER` | decision-blocked |
| `D44` | `BD-ITER`, `BD-STAGING`, `BD-NAMES` | decision-blocked |
| `D45` | `BD-NAMES` | decision-blocked |
| `D46` | `BD-STAGING` | decision-blocked |
| `D47` | `BD-CONTROL`, `BD-NAMES` | decision-blocked |
| `D48` | `BD-ITER` | decision-blocked |
| `D49` | `BD-ITER`, `BD-STAGING`, `BD-CONTROL` | decision-blocked |
| `D50` | none | ready for next-stage specification |
| `D53` | `BD-CONTROL`, `BD-NAMES` | decision-blocked |
| `L55` | `BD-CONTROL` | decision-blocked |
| `D58` | `BD-NAMES` | decision-blocked |
| `R.full` | `BD-ITER`, `BD-STAGING`, `BD-CONTROL`, `BD-NAMES` | decision-blocked |

The next architecture packet should therefore target the next blocker in dependency order rather than start full lifecycle proofs immediately.

## 10. Coding and proof rules

1. Import and use ADR-02's `Store`/`Finmap` façade; do not introduce a second store representation in downstream modules.
2. Keep `RawState` positive and data-only. A code/token type that mentions `RawState` is a design violation and requires an ADR revision.
3. Pass the acting `IncarnationId` to external action/undo semantics; do not assume one behavior function is shared by every instance of a component.
4. Keep `RawState` and `ValidState` distinct. Never repair a failed operation by silently manufacturing a proof of `WellFormed`.
5. Derive the global coeffect from active local tables. Do not add a cached global table to `RawState` without a superseding ADR and coherence proof.
6. Use `Option` for absent provider/target views. Defaults are not providers.
7. Prove active-union order independence under explicit disjointness; never infer it from left-biased union notation.
8. Keep declared provisions, local support, active presence, and committed visibility as separate predicates.
9. Keep `CoreStateObs`, `LifecycleObs`, and `EraseControl` distinct. Use ADR-01's explicit relation parameters rather than a global relation instance.
10. State-map/control-edit factorization is an external semantic witness, not a recursive field in a state record.
11. Treat `BD-NAMES`, `BD-ITER`, `BD-STAGING`, `BD-CONTROL`, and `BD-SCOPED` as unresolved. A spike may abstract over them, but may not choose their final representation by accident.
12. Any runtime closure, proxy, asynchronous task, or disposer is introduced only in a later concrete-refinement layer.

## 11. Acceptance criteria

| ID | Criterion | Architecture status | Spike status |
|---|---|---|---|
| `STATE-AC-01` | No literal negative `μΓ`/recursive closure field; positive raw carrier | passed by variance audit | represented; user-reported compiler pass |
| `STATE-AC-02` | Finite registry and lifecycle-parameterized fiber shell | passed | represented; user-reported compiler pass |
| `STATE-AC-03` | Explicit parent, support, provision-disjointness, and lifecycle-coherence predicates | passed | core predicates represented; user-reported compiler pass; rooted/catalog obligations remain deferred |
| `STATE-AC-04` | Active-only coeffect projection with order-independence contract and provider uniqueness boundary | passed by design audit | noncomputable ordered representative plus contract compiled; executable `Finmap.foldl` proof pending production work |
| `STATE-AC-05` | `Option` target/committed provider views with finite-domain proof | passed | represented; user-reported compiler pass |
| `STATE-AC-06` | Pure registry update/frame API | passed | representative lookup/frame lemmas; user-reported compiler pass |
| `STATE-AC-07` | `CoreStateObs` lift through ADR-01/02 observation API | passed | represented as explicit relation shell; user-reported compiler pass |
| `STATE-AC-08` | External actor-indexed action semantics and WF-preservation premise | passed | represented; user-reported compiler pass |
| `STATE-AC-09` | Code-token denotation/equivalence bridge remains an explicit ADR-01 obligation | passed | relation hook compiled; semantic law remains pending |
| `STATE-AC-10` | No hidden decisions for names, iterators, staging, control, or scoped realms | passed | no concrete choices in spike |
| `STATE-AC-11` | Frozen affected-node set and readiness subtraction match Harness 04 | passed; machine-checked in JSON | represented in JSON |
| `STATE-AC-12` | Pinned Lean compilation of the companion spike | passed (user-reported) | repaired spike and project build passed; exact raw log/lock revision remains to be recorded |

## 12. Validation record

The paper audit covered Definition 32, Definitions 43–50, Definition 53, Lemma 55, Definition 58, and the Section 4 state/transition prose. The variance audit rejects the literal recursive equation and closure-bearing cell. The API audit aligns the store and observation boundaries with ADR-01 and ADR-02.

The original creation environment did not contain `lean` or `lake`, so the initial spike was deliberately marked compiler-pending. The user subsequently supplied a repaired spike and reported the following validation in the project's pinned environment (Lean 4.33.0, current locked Mathlib/Lake environment):

```text
lake env lean Scratch/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fixed.lean
  → passed, no errors, no warnings

rg -n '\\b(sorry|admit|axiom)\\b' \\
  Scratch/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike-Fixed.lean
  → no matches

lake build
  → Build completed successfully (8738 jobs)
```

The canonical companion source now contains the exact supplied repaired file. Its SHA-256 is recorded below; the pre-repair source is retained under its historical name. The repair report identifies the first failure as an elaboration problem caused by implicit generalization of the parameterized `Fiber` alias at the `Registry` definition, followed by type annotations and proof-script/API explicitness repairs. It reports no change to the carrier decision, `WellFormed` logic, acyclicity assumptions, committed-provider semantics, target eligibility/activity distinction, or the Core/full-Cordis boundary.

The required reproducibility gate remains:

```text
lake env lean artifacts/DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture-Spike.lean
```

This is a **user-reported compiler result**. The exact compiler log is not stored in the packet, so reproducibility metadata remains a follow-up even though the implementation-validation gate is accepted. The repaired source changes the surface API by making parameters explicit; callers must specialize `Fiber`, `Registry`, `RawState`, `TrackedContext`, and `ActionSemantics` rather than use the former bare aliases. This is an elaboration/API repair, not a semantic revision. A future compiler failure is a revision signal for the spike; it does not silently change the decision or the frozen baselines.

The compiler pass validates the carrier/API spike only. It does **not** by itself prove active-union traversal independence, `WellFormed` preservation, guarded committed lookup, actor frame laws, code-denotation respect, or the full lifecycle theorems.

### 12.1 Repair disposition and remaining technical debt

The repair was necessary because Lean implicitly generalized the parameters used by the
`Fiber` alias; at `Registry`, instance search therefore saw an unresolved
`DecidableEq ?m` rather than the intended key instance. The repaired source explicitly
specializes `Fiber`, `Registry`, `RawState`, `TrackedContext`, and `ActionSemantics`, and
uses local notation to keep those applications readable. It also makes several Bool/type
annotations and proof cases explicit. These changes are recorded as an implementation
revision, not a new architectural decision.

The compiler gate does not close the following known follow-ups:

- the current carrier declarations still carry a `DecidableEq Key` parameter; moving that
  requirement to operations/theorems may be a later API cleanup;
- `ParentRooted` and catalog `DeclarationConsistency` remain boundary obligations rather
  than conjuncts of the spike's `WellFormed` predicate;
- `providesNow` is policy-parameterized and still needs a later soundness law tying it to
  the selected Active phase;
- `providerOf` and `targetView` are noncomputable classical-choice representatives and
  still need WF-relative specification/adequacy lemmas;
- committed-provider table support/freeze, checked static-field-preserving updates, the
  actor frame law, and executable order-independent folding remain later proof/API work.

## 13. Non-decisions

ADR-03 intentionally does **not** decide:

- the fresh-name, generation, alpha-renaming, or identity-reuse policy (`BD-NAMES`);
- the iterator, continuation, failure-result, or stage carrier (`BD-ITER`);
- staging/commit protocol details (`BD-STAGING`);
- asynchronous scheduling, failure labels, or full control-step semantics (`BD-CONTROL`);
- isolation realms and interception metadata (`BD-SCOPED`);
- the final module/import graph or namespace names;
- whether the external action relation is implemented by an evaluator, finite transition list, or proof-relevant relation;
- application-specific component codes, error payloads, or ambient-state observations;
- mutable runtime object identity, proxies, host resources, and disposer closure representation;
- a mutable or overlapping root store in the Section 4 core.

## 14. Revision policy

Editorial changes (wording, examples, cross-reference formatting) require a recorded patch version. A semantic change requires a superseding ADR and must not rewrite this decision in place.

Reopen or supersede ADR-03 if any of the following occurs:

1. the pinned compiler rejects the positive shell in a way that requires a negative recursive field or unsafe cast;
2. the finite registry cannot state the parent/frame/provider invariants needed by D45, D48, D53, or T63;
3. the active-table projection cannot be made traversal-order independent under the selected well-formedness invariant;
4. later proofs require an actually infinite reachable registry or coeffect support in one runtime state;
5. a faithful Section 4 core requires an implicit root store or a second mutable global cache;
6. action codes necessarily embed iterator/control choices that belong to another blocker;
7. committed lookup cannot preserve the guarded Unloading invariant;
8. a scoped-context extension cannot provide a lookup/update-faithful flat embedding;
9. runtime refinement establishes closure identity or untracked external effects as part of the chosen core observation.

## 15. Final adjudication

`BD-STATE` is accepted as resolved by the positive finite-registry architecture above, with compiler validation reported by the user for the repaired spike. The project now has one shared state shell on which D32, D33, D43–D50, D53, L55, D58, and `R.full` can be specified without a negative recursive type. The remaining blockers stay visible and independently actionable. The repaired compiler pass validates the selected carrier/API shape; it does not claim completion of the later iterator, staging, control, names, semantic-law, or full lifecycle proof work. The frozen dependency and disposition baselines remain unchanged.
