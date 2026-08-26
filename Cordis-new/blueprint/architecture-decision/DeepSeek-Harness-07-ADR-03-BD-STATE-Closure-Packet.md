# DeepSeek Harness ADR-03-CLOSURE: BD-STATE Contract Hardening

| Field | Value |
|---|---|
| Packet ID | `ADR-03-CLOSURE` |
| Parent decision | `ADR-03: Unified State and Registry Architecture` |
| Status | **Accepted — compiler validated** |
| Packet version | `1.1-accepted-compiler-validated` |
| Date | 2026-08-26 |
| Global blocker status | `BD-STATE` already resolved by ADR-03; this packet supplies closure evidence and downstream contracts |
| Semantic change | **None** |
| Supersedes | Nothing |
| Companion artifacts | `DeepSeek-Harness-07-ADR-03-BD-STATE-Closure-Packet.json`; `DeepSeek-Harness-07-ADR-03-BD-STATE-Closure-Spike.lean` |
| Parent ADR artifact | `DeepSeek-Harness-07-ADR-03-Unified-State-and-Registry-Architecture` (`1.1-accepted-compiler-validated-user-reported`) |

## 1. Purpose

ADR-03 made the architectural choice required by `BD-STATE`:

```text
RawState = Ambient × Finmap IncarnationId FiberCell
ValidState = { s : RawState // WellFormed s }
```

The compiler-validated spike established that this positive finite registry shell can be
elaborated. It deliberately left several state contracts as named obligations because
their final proofs or transition rules depend on other global decisions. This packet
hardens those contracts without reopening the carrier decision.

The distinction is important:

```text
global blocker BD-STATE       = resolved by ADR-03
state-contract evidence       = completed incrementally by this packet and later proofs
```

This is a companion/closure packet, not a new architectural ADR.

The Lean file is a standalone compile harness: it mirrors the accepted ADR-03 carrier so
that the packet can be checked independently. It is not intended to be imported together
with a production module that declares the same `CordisADR03` names; production code should
import the canonical module and retain only the `CordisADR03Closure` layer.

## 2. Scope and non-scope

The packet fixes the proof-facing interfaces for:

1. core well-formedness versus boundary obligations;
2. provider provenance and provider-choice specifications;
3. active-store aggregation and conflict-aware merge contracts;
4. static-field projection and checked raw updates;
5. lifecycle visibility and committed-table support contracts;
6. the `TrackedContext`/coeffect projection bridge;
7. registry and ambient frame contracts.

It does **not** choose:

- fresh names, generations, alpha-renaming, or identity reuse (`BD-NAMES`);
- iterator or failure carriers (`BD-ITER`);
- staging/commit phase constructors (`BD-STAGING`);
- asynchronous scheduler and lifecycle transition rules (`BD-CONTROL`);
- scoped realms/interception (`BD-SCOPED`);
- a mutable root store or a second global coeffect cache.

If completing a contract requires changing the state carrier, root policy, or observation
boundary, the work must stop and become a superseding ADR rather than silently expanding
this packet.

## 3. Normative closure decisions

### 3.1 Two levels of well-formedness

`CoreWellFormed` is the state-local conjunction already used by ADR-03:

```text
ParentClosed ∧ ParentAcyclic ∧ TableConfined ∧ ProvisionDisjoint
∧ LifecycleCoherent ∧ CommittedViewClosed ∧ CommittedProvidersClosed
```

Root conventions and catalog declaration agreement are represented as separately supplied
predicates:

```text
BoundaryWellFormed policy rootSpec declarationSpec s
  := CoreWellFormed policy s ∧ rootSpec s ∧ declarationSpec s
```

This keeps the core carrier independent of the eventual naming and component-catalog
decisions. The packet does not claim that `ParentRooted` or `DeclarationConsistency` is
already proved in the core spike.

### 3.2 Provider provenance

The coeffect union alone forgets which Fiber supplied a key. The closure API therefore
introduces a provenance-bearing relation/type:

```text
ActiveProviders policy s k
  := { n // ProvidesNow policy s.registry n k }

ActiveBinding policy s k
  := provider ID + value + provider witness + global-lookup witness
```

`ProviderChoiceSpec` records the intended specification of the classical `providerOf`
representative:

```text
CoreWellFormed policy s →
  (providerOf policy s k = some n
    ↔ ProvidesNow policy s.registry n k)
```

The choice definition remains noncomputable and is only a semantic representative. The
adequacy equivalence above and its WF-relative uniqueness corollary are proof obligations;
they are not silently inferred from `Classical.choose`.

`ProviderUniqueSpec` carries the same `CoreWellFormed policy s` premise. It is therefore a
state-validity contract, not an assertion that malformed/raw intermediate registries can
never contain duplicate active providers.

### 3.3 Active aggregation

The authoritative global view remains derived from contributing local stores. The packet
adds a key-level store-disjointness predicate and an absorbing checked merge:

```text
StoreDisjoint σ τ := ∀ k, k ∈ σ → k ∈ τ → False

checkedMerge σ τ : Option Store
  = some (σ ∪ τ)  when disjoint
  = none           on overlap
```

The semantic list representative in ADR-03 remains available. `ActiveFoldOrderIndependent`
is the explicit permutation-invariance contract needed before replacing that representative
with an executable `Finmap.foldl`. The packet does not claim that the fold theorem is
already proved.

### 3.4 Static fields and checked updates

The raw registry operations remain permissive for counterexamples and intermediate
semantics. To prevent lifecycle/control code from accidentally rewriting insertion-time
identity fields, the packet fixes:

```text
staticOf c
  = component, behavior, requirements, provisions, parent

SameStatic c d := staticOf c = staticOf d

checkedModify n f s : Option RawState
  = success only when SameStatic (oldCell) (f oldCell)
```

`checkedModify` is only a static-field gate. It does not claim to produce a `ValidState`;
full `CoreWellFormed` preservation remains a separate contract and depends on later
transition decisions.

### 3.5 Lifecycle visibility and committed support

`LifecyclePolicy` remains abstract. The packet exposes, but does not instantiate, the law

```text
providesNow life = true ↔ IsActive life
```

for a later selected lifecycle predicate. Concrete Active/Reloading/Unloading constructors,
retirement timing, and guarded-unload transitions remain `BD-STAGING`/`BD-CONTROL` work.

For committed views, the packet adds the state-level support contract:

```text
every key named by a committed view is present in the named provider's local store
```

The stronger transition law—provider table remains frozen while a dependent uses
`CommittedLookup` during guarded Unloading—is explicitly a later staging/control theorem.

### 3.6 Frame and observation boundaries

The packet names three independent facts:

- `RegistryFrameAt n s t`: entries at identities other than `n` are unchanged;
- `StaticFrameAt n s t`: the static projection at `n` is unchanged;
- `LocalStoreFrame n s t`: a provider's local table is unchanged across a guarded interval.

These are contracts for actor-indexed transitions, not claims that arbitrary raw
`modifyFiber` already satisfies them.

The existing `TrackedContext` remains the bridge for Definition 32:

```text
TrackedContext = state + accumulator
TrackedCoeffect(ctx) = activeUnion(ctx.state)
```

This is a representation/refinement interface, not a definitional identification with the
paper's negative fixed-point expression.

## 4. Lean-facing API

The companion spike reuses ADR-03's canonical positive carrier and adds the following
names in namespace `CordisADR03Closure`:

```lean
CoreWellFormed
BoundaryWellFormed
ActiveProviders
ActiveBinding
ProviderChoiceSpec
ProviderUniqueSpec
CommittedSupportClosed
StoreDisjoint
checkedMerge
ActiveStoreDisjointContract
ActiveFoldContract
ActiveFoldOrderIndependent
StaticFields
staticOf
SameStatic
checkedModify
RegistryFrameAt
StaticFrameAt
CheckedModifyPreservesWF
ProvidesNowPolicySound
LocalStoreFrame
CommittedLookupStable
TrackedContextProjectionSpec
```

The only executable lemmas claimed in this spike are the definitional bridge for
`TrackedContext`, the `checkedMerge` success/failure equations, the equivalence of
`CoreWellFormed` with ADR-03's `WellFormed`, and the static-gated update success equation.
The larger names ending in `Contract` or `Spec` are intentionally propositions awaiting
later proofs or transition instantiations.

## 5. Acceptance checks

| ID | Check | Status before packet | Closure target |
|---|---|---|---|
| `STATE-CLOSE-01` | Reuse the accepted positive finite carrier; no recursive closure field | passed by ADR-03 | compile-check companion reuse |
| `STATE-CLOSE-02` | Separate core WF from root/catalog boundary predicates | partially represented | API represented; root/catalog proofs deferred |
| `STATE-CLOSE-03` | Carry provider provenance and state the choice specification | choice representative only | API/contract represented; adequacy proof pending |
| `STATE-CLOSE-04` | Conflict-aware active merge and traversal-order contract | semantic representative only | checked merge compiles; fold/order theorem pending |
| `STATE-CLOSE-05` | Static-field projection and checked raw update | raw update only | checked gate and success lemma |
| `STATE-CLOSE-06` | Committed support and lifecycle visibility contracts | transition obligation documented | support predicate represented; freeze theorem deferred |
| `STATE-CLOSE-07` | Registry/ambient frame and Definition-32 projection contracts | partial frame API | named contracts and projection lemma |
| `STATE-CLOSE-08` | Companion spike compiles in pinned project | not yet run | required user gate |

## 6. Readiness effect

This packet changes no dependency edge and no blocker set. The effective readiness remains
the ADR-03 result:

```text
BD-STATE = resolved by ADR-03
D32, D33, D50 = free of their state blocker
all other remaining blockers = unchanged
```

The packet therefore upgrades the quality of the downstream API specification; it does not
make `D43`–`D49`, `D53`, `L55`, `D58`, or `R.full` proof-ready where their other blockers
remain.

## 7. Known limitations

The following are deliberately visible rather than hidden in the closure layer:

1. The current carrier declarations retain `[DecidableEq Key]`; moving this requirement to
   operations/theorems is a possible later API cleanup.
2. `ParentRooted` and catalog `DeclarationConsistency` are boundary obligations.
3. `providesNow` is policy-parameterized until the staging ADR selects lifecycle constructors.
4. `providerOf` and `targetView` are classical-choice semantic representatives and need
   WF-relative adequacy lemmas.
5. `CommittedSupportClosed` is state-level; table freeze and guarded lookup stability are
   transition-level obligations.
6. `checkedModify` does not prove `CoreWellFormed` preservation.
7. The action relation still needs its actor read/write frame law.
8. The theorem interface should continue to expose acyclicity as an explicit hypothesis
   where required, even though the accepted ADR-03 `WellFormed` conjunction retains the
   corresponding state predicate.

None of these limitations changes the accepted ADR-03 carrier. A limitation that would
require such a change is a reopen trigger for a superseding ADR.

## 8. Validation and promotion policy

The packet's required compiler gate is:

```text
lake env lean artifacts/DeepSeek-Harness-07-ADR-03-BD-STATE-Closure-Spike.lean
```

The command returned exit code `0` under Lean 4.33.0 / Lake 5.0.0 (`d8b1897`). The project
owner confirmed that this local compile is sufficient as the packet's validation gate, so
the closure is promoted to `closure-accepted-compiler-validated`.

All contract/proof gaps above remain explicit. A compiler failure that requires only elaboration
or proof-script repair produces a revised spike; a failure that requires changing the
carrier, root policy, or observation boundary requires a superseding ADR.

## 9. Final disposition

`BD-STATE` is already resolved at the global-decision level by ADR-03. This packet is the
next formalization step: it makes the accepted state architecture explicit enough for
downstream modules to consume, while preserving the separation between state contracts and
the unresolved iterator, staging, control, naming, and scoped-context decisions.
