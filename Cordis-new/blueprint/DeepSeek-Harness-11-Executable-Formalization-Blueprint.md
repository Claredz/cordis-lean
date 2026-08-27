# DeepSeek Harness: Executable Formalization Blueprint

| Field | Value |
|---|---|
| Blueprint ID | `DH-FORMAL-BP-01` |
| Version | `1.0.1` |
| Status | **proposed-executable / deliberately revisable** |
| Date | 2026-08-27 |
| Semantic change | **None** — this blueprint consumes accepted decisions; it does not supersede an ADR. |
| Supersedes | Nothing |
| Revision note | Formalization pipeline inputs narrowed: Project Guide and Research Ledger are excluded. |
| Primary target | Standalone Lean formalization of the paper's metatheory kernel |
| First executable slice | Two disjoint counters + failure + ranked iterator + alpha transport |
| Namespace | `DeepSeekHarness` (runtime connection reserved as `DeepSeekHarness.CordisAdapter`) |
| Bootstrap validation in this workspace | **Not run** — `lean`/`lake` are not installed here; the file is a compile-targeted skeleton, not a claimed compiler result. |

This blueprint turns the accepted formalization inputs into an executable, staged work plan.
It is intentionally not a promise that the whole paper or the Cordis implementation will
be verified in one pass.  The first target is a checked generic kernel plus a small finite
example; later feedback may revise module boundaries or individual contracts without
silently changing the accepted ADRs.

## 1. Fixed decision profile

The following choices are already accepted and are inputs to this blueprint.

| Choice | Decision |
|---|---|
| `G1` objective | Paper metatheory kernel first. Runtime verification is a separate future refinement track. |
| `G2` host | Start as a standalone package. Reserve a one-way Cordis adapter/refinement boundary. |
| `G3` first slice | Two counters, one failure path, a two-level ranked iterator, and a name-renaming test. |
| `G4` effect representation | Staged hybrid: shallow executable effects now; deep `EffectCode`/interpreter seam reserved. |
| `G5` registry | Abstract `RegistryLike`; Toy registry may use `List + Nodup`; formal ADR-03 registry later uses a `Finmap` adapter. This concerns the fiber registry and does not replace ADR-02's authoritative dependent coeffect `Finmap`. |
| `G6` failure | General failure retains error, boundary state, and successful-prefix undo. Atomic failure is only a Toy specialization. |
| State carrier | Begin with abstract `StateLike`; later instantiate/bridge to ADR-03 `RawState`, `ValidState`, and `WellFormed`. |
| Working validation profile | `A + I + K + E`; only an `R0` adapter seam is expected in this phase. |

The following architecture/contracts are not reopened: relation-parametric law architecture,
explicit observation
relations, no quotient execution carrier, positive finite ADR-03 state architecture,
incarnation-lifetime identity, ranked continuation architecture, and explicit failure
results.  `BD-CONTROL`, `BD-STAGING`, `BD-SUPPORT`, and `BD-SCOPED` remain independent.

## 2. What each evidence label means

The blueprint uses separate evidence dimensions rather than one linear notion of
"finished".

| Label | Meaning | Typical evidence |
|---|---|---|
| `A` | Semantic alignment/traceability | Paper/ADR reading, scope check, examples, counterexamples, repair rationale |
| `I` | Interface/elaboration | Changed Lean files and package build type-check; no claim that laws are true |
| `K` | Kernel semantic proof | A substantive theorem has a checked proof term with no placeholders |
| `E` | Executable validation | A concrete finite instance runs (`#eval`, `decide`, or property test) |
| `R0` | Adapter seam | Types for abstraction/simulation are present; no runtime correctness claim |
| `R1+` | Concrete refinement | A restricted or full runtime step is proved to simulate the abstract model |

`I` and `K` both use Lean compilation, but they answer different questions: `I` asks
whether the formal language is well formed; `K` asks whether a stated semantic proposition
has actually been proved. `A` is partly human/specification work and cannot be inferred
from a successful build.

## 3. Source and integrity contract

The blueprint consumes the following files as read-only inputs.  It never edits the frozen
dependency graph or disposition baseline; readiness reports are derived artifacts.

| Input | Role | Integrity |
|---|---|---|
| `a-programming-paradigm-for-spatitemporal-composability.pdf` | Primary source | SHA-256 `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| `DeepSeek-Harness-01-Formal-Reference.md` | Definitions, theorem anchors, notation | project source |
| Harness-03 dependency graph JSON | Immutable 74-item/8-auxiliary graph | SHA-256 `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| Harness-04 disposition JSON | Immutable treatment/readiness baseline | SHA-256 `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |
| ADR-01 … ADR-06 artifacts | Accepted architecture decisions and closure contracts | local hashes recorded in companion JSON |

The following project-context files are explicitly excluded from the formalization
pipeline and should not be assigned as Agent inputs:

| Excluded file | Reason |
|---|---|
| `DeepSeek-Harness-00-Project-Guide.md` | Project organization and study workflow, not a formalization dependency |
| `DeepSeek-Harness-02-Research-Ledger.md` | Research-history record, not a formalization dependency |

The ADR spike files are historical, standalone compiler mirrors.  Production modules are
ported declaration by declaration under the `DeepSeekHarness` namespace; they must not
import spikes that redeclare the same names.

## 4. Production module DAG

The initial package should use a single source of truth for each declaration.  The exact
file names may be adjusted after the first toolchain audit, but the dependency directions
must remain acyclic.

```text
Prelude.Finite
   ├── Foundation.Relation
   ├── Foundation.Result
   └── State.RegistryLike
Foundation.Relation + Foundation.Result ──> Core.Effect ──> Core.Partial ──> Core.Iterator
State.RegistryLike ──> State.Toy
State.Like + Foundation.Relation ──> State.Observation
Core.Iterator + State.Observation ──> Alpha.Transport
all core layers ──> Examples.TwoCounter ──> Conformance.Manifest
Core + State interfaces ──> Adapters.Cordis (R0 only)
```

Recommended initial tree:

```text
DeepSeekHarness/
  Foundation/Relation.lean
  Foundation/Result.lean
  Core/Effect.lean
  Core/Partial.lean
  Core/Iterator.lean
  State/Like.lean
  State/RegistryLike.lean
  State/Toy.lean
  State/Observation.lean
  Alpha/Core.lean
  Alpha/Transport.lean
  Examples/TwoCounter.lean
  Adapters/Cordis.lean
  Conformance/Manifest.lean
  Bootstrap.lean
```

The ADR-02 coeffect store remains a separate dependent-store interface.  The Toy
`RegistryLike` is the fiber-registry example, not a replacement for the authoritative
dependent coeffect `Finmap`.  The initial `Prelude.Finite` and `Foundation.Result` entries
are logical module layers to be created in P0/P1 if the host repository does not already
provide them.

## 5. Execution waves

The work is organized as waves.  A wave may be split into several commits and can be
replanned after its gate; no later wave should depend on an unrecorded semantic choice.

### Wave P0 — Baseline, toolchain, and traceability

| Task | Work | Depends on | Deliverable / gate |
|---|---|---|---|
| `P0-T01` | Locate the actual source-of-truth checkout (if any), read `lean-toolchain`, `lakefile`, and manifest; record Lean/Mathlib versions. If none exists, create the standalone Lake package and record the workspace snapshot. | none | `STATUS` entry; clean baseline command and result (`A,I`) |
| `P0-T02` | Create a branch/tag for formalization; record H03/H04 hashes and accepted ADR artifact hashes. | `P0-T01` | immutable-baseline check (`A,H`) |
| `P0-T03` | Build a Definition Ledger mapping each paper ID to target module, treatment, status, and deferred reason. | `P0-T01` | machine-readable ledger; no graph mutation (`A`) |
| `P0-T04` | Add strict scans and a minimal package `Bootstrap.lean`; distinguish comments/history from active declarations. | `P0-T01` | clean baseline/build protocol (`I`) |

### Wave P1 — Relation and result foundations

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P1-T01` | Define `RelSpec`, `RespectsOn`, `Respects`, same-input `PointwiseRel`, and cross-input `CrossRel`. | D36–D37, L38; ADR-01/06 | relation laws, Eq specialization, orientation tests (`A,I,K,E`) |
| `P1-T02` | Define `OptionRel`, result/failure relators, and observation pullback shells. | D33, D36–D39; ADR-02/06 | definedness/tag preservation is explicit (`I,K`) |
| `P1-T03` | Prove basic relation closure/congruence and keep raw computation on Lean equality. Effect-specific homomorphism proofs are scheduled in P2. | D36–D42, L38; ADR-01/06 | at least one nontrivial generic theorem (`K`) |

### Wave P2 — Shallow reversible Effect kernel

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P2-T01` | Define shallow `Effect`, success-only `EffectResult`, undo composition, identity, and sequential execution. | D1–D3, D8–D10 | executable raw algebra (`I,E`) |
| `P2-T02` | Define law records for selected-inverse stability, undo respects relation, and local recovery. | D8, T11, T15–T16; ADR-01/06 | explicit hypotheses, no hidden axioms (`A,I`) |
| `P2-T03` | Prove sequential composition and LIFO recovery for lawful effects; provide Eq specialization. | T10–T16 | generic proof + concrete counter instance (`K,E`) |
| `P2-T04` | Reserve `EffectCode`, interpreter, and refinement signatures without requiring a deep DSL theorem. | G4; ADR-03/05 | shallow/deep boundary compiles (`I,R0`) |

### Wave P3 — Partial operations and failure contracts

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P3-T01` | Define `OpResult`, `PartialOp`, outcome tags, definedness, and selected-inverse fields. | D23–D26, D34, D39; ADR-02/06 | undefined ≠ failure; tag is observable (`A,I`) |
| `P3-T02` | State weak/full operation-respect, common-definedness, outcome stability, foreign stability, and independence contracts. | D19, D36–D42; ADR-01/06 | positive law plus finite negative example (`K,E`) |
| `P3-T03` | Define the general failure result carrying error, boundary state, and successful-prefix undo, plus an explicit bridge from success-only `EffectResult` to `ExecResult`. | `R.fail`; ADR-05 | no `Option` erasure of iterator failure (`I,K`) |
| `P3-T04` | Instantiate `failIfZero` as an atomic Toy specialization, explicitly not as the general failure law. | ADR-05, G6 | executable failure example (`E`) |

### Wave P4 — Ranked iterator

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P4-T01` | Define `StageResult`, `RankedIterator`, external `Q`, rank and strict successor certificate. | D51–D52, D60, T66; ADR-05 | state-dependent continuation type-checks (`I`) |
| `P4-T02` | Define well-founded execution and `ExecResult`; fold successful inverses in LIFO order. | D52, `R.iter`, `R.fail`; ADR-05 | rank termination and prefix-undo theorem (`K`) |
| `P4-T03` | Add stage/iterator relation, witness, simulation and optional bisimulation interfaces. | D51–D52; ADR-06 | relation transport without quotient execution (`I,K`) |
| `P4-T04` | Add nested iterator and failure transport tests. | D51–D52, `R.fail` | finite `#eval` success/failure trace (`E`) |

### Wave P5 — Abstract state, registry, and observations

This wave may run partly in parallel with P2–P4, but its concrete ADR-03 adapter is not a
prerequisite for the first Effect proofs.

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P5-T01` | Define explicit `StateLike` and observation profiles; keep `CoreStateObs`, lifecycle observation, control erasure, and name-aware observation distinct. | D32–D33; ADR-01/03/06 | observer boundary and pullback laws (`A,I,K`) |
| `P5-T02` | Define `RegistryLike` with lookup/insert/erase/domain laws; instantiate Toy `List + Nodup`. | D44–D47; ADR-03, G5 | finite executable registry (`I,K,E`) |
| `P5-T03` | Define the one-way adapter seam to ADR-03 `RawState`, `ValidState`, `WellFormed`, provider provenance, and checked updates. | D32–D34; ADR-03 closure | interface only first; WF/provider proofs explicitly classified (`I,R0`) |
| `P5-T04` | Keep ADR-02 authoritative dependent coeffect `Finmap` and expose a compatible façade; do not duplicate mutable global stores. | D22–D31; ADR-02 | store/registry distinction recorded (`A,I`) |

### Wave P6 — Alpha transport

| Task | Work | Paper / ADR anchors | Deliverable / gate |
|---|---|---|---|
| `P6-T01` | Define `AlphaAction` and permutation action for name-neutral state, undo, stage, iterator, and execution. | D53, L56, T73; ADR-04/06 | identity/composition/inverse laws (`K`) |
| `P6-T02` | Add trace/reference transport and freshness-boundary interfaces; keep ledger outside default core observation. | D45, D53; ADR-04 | name-aware boundary is explicit (`A,I,R0`) |
| `P6-T03` | Defer name-bearing `Q`, `Xi`, ambient payload, and control-payload alpha proofs. | ADR-04/06 | explicit deferred rows, no false closure (`A`) |

### Wave P7 — Two-counter vertical slice

| Task | Work | Expected evidence |
|---|---|---|
| `P7-T01` | Define `CounterState` with two disjoint counters and shallow `inc₁`, `inc₂`, `dec₁`, `dec₂`. | concrete definitions (`I,E`) |
| `P7-T02` | Prove each increment lawful and prove exact/observational recovery. | `K` theorems |
| `P7-T03` | Prove disjoint commutation and the selected-inverse/independence contract. | `K` theorem + negative test |
| `P7-T04` | Define a two-level ranked iterator and a failing path using `failIfZero`. | rank proof (`K`) + `#eval` (`E`) |
| `P7-T05` | Apply a finite permutation to names/labels and prove name-neutral result transport. | alpha theorem/test (`K,E`) |
| `P7-T06` | Run the complete trace: success, failure boundary, prefix undo, and recovery. | vertical-slice report (`A,K,E`) |

### Wave P8 — Conformance and R0 adapter

| Task | Work | Deliverable |
|---|---|---|
| `P8-T01` | Generate a derived readiness manifest from H03/H04 plus current task evidence. | no baseline mutation; paper-ID traceability |
| `P8-T02` | Add `DeepSeekHarness.CordisAdapter` abstraction/simulation types only. | R0 seam; explicitly no runtime verification claim |
| `P8-T03` | Record feedback, failed proof attempts, counterexamples, and proposed superseding ADR triggers. | reproducible iteration log |

## 6. Initial API sketch

The following signatures are intentionally small and may be refined after the actual Lean
toolchain audit.  They are a contract sketch, not a claim that every theorem is already
proved.

```lean
namespace DeepSeekHarness

structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RespectsOn {α β : Type _} (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

def PointwiseRel {α β : Type _} (R : β → β → Prop)
    (f g : α → β) : Prop := ∀ x, R (f x) (g x)

def CrossRel {α β : Type _} (R : α → α → Prop) (S : β → β → Prop)
    (f g : α → β) : Prop := ∀ {x y}, R x y → S (f x) (g y)

inductive EffectResult (S : Type u) where
  | success (state : S) (undo : S → S)

abbrev Effect (S : Type u) := S → EffectResult S

structure StateLike (S : Type u) (O : Type v) where
  project : S → O

structure ObservationProfile (S : Type u) (O : Type v) where
  stateRel : RelSpec S
  obsRel : RelSpec O
  project : S → O
  project_respects : RespectsOn stateRel.rel obsRel.rel project

structure RegistryLike (K V R : Type u) [DecidableEq K] where
  empty : R
  lookup : R → K → Option V
  insert : R → K → V → R
  erase : R → K → R
  dom : R → List K
  dom_nodup : ∀ r, (dom r).Nodup
  lookup_empty : ∀ k, lookup empty k = none
  lookup_insert_eq : ∀ r k v, lookup (insert r k v) k = some v

inductive StageResult (S E Q : Type u) where
  | halt (state : S) (undo : S → S)
  | yield (state : S) (undo : S → S) (next : Q)
  | raise (error : E)

structure RankedIterator (S E Q : Type u) where
  root : Q
  rank : Q → Nat
  run : Q → S → StageResult S E Q
  next_lt : ∀ {q s s' u q'},
    run q s = .yield s' u q' → rank q' < rank q

structure ExecFailure (S E : Type u) where
  error : E
  boundary : S
  prefixUndo : S → S

structure AlphaAction (N X : Type u) where
  act : Equiv.Perm N → X → X
  act_id : ∀ x, act Equiv.refl x = x
  act_comp : ∀ (p q : Equiv.Perm N) x, act (p.trans q) x = act p (act q x)
  act_inv : ∀ (p : Equiv.Perm N) x, act p.symm (act p x) = x

end DeepSeekHarness
```

The exact `RegistryLike` laws will be expanded as the Toy and Finmap instances expose
their needed cases.  `EffectResult` is intentionally success-only in P2: partial-operation
and iterator failure information enters through `OpResult`/`ExecResult`, with an explicit
bridge.  This keeps the raw effect algebra small without losing the G6 boundary/prefix
contract.

## 7. Vertical-slice acceptance scenario

The first end-to-end example is deliberately small:

```text
initial state:       (counter₁ = 0, counter₂ = 0; named labels n₁, n₂)
success path:        inc₁ ; inc₂ ; halt
failure path:        inc₁ ; failIfZero(counter₂) ; ...
success undo:        undo₂ ; undo₁
failure evidence:    error + boundary state + undo for inc₁
iterator condition:   every yield strictly lowers rank
alpha test:           rename labels and transport the same result
```

The atomic behavior of `failIfZero` is a Toy-specific contract.  The general failure API
must still permit a boundary state that differs observably from the input.

The slice is successful only when all of the following are separately recorded:

1. a generic recovery theorem;
2. a generic or instance-level independence theorem;
3. a termination proof for the ranked iterator;
4. a concrete success execution;
5. a concrete failure execution retaining the prefix inverse;
6. an alpha-transport theorem or executable transport check;
7. an alignment note explaining which paper claims are instantiated and which remain assumptions.

## 8. Validation gates and commands

The exact commands depend on P0's toolchain audit.  The default protocol is:

```bash
lake env lean DeepSeekHarness/Foundation/Relation.lean
lake env lean DeepSeekHarness/Examples/TwoCounter.lean
lake build
```

At blueprint creation time the current scratch workspace has no `lean` or `lake` binary,
so no compilation result is claimed for the bootstrap file.  P0-T01 must run these
commands in the selected host environment and record the exact output before promoting
any `I` or `K` status.

The repository should also provide a `Bootstrap.lean` that imports all production modules,
checks the public signatures, and runs the finite examples.  A strict source scan should
cover active production code and exclude historical spike comments only by an explicit
path rule.

| Gate | Required check | Does not establish |
|---|---|---|
| `G-A` | Paper/ADR traceability, intended meaning, scope and strengthening review | Lean theorem truth |
| `G-I` | Per-file and milestone package compilation | Semantic lawfulness |
| `G-K` | Placeholder-free substantive theorem proofs and explicit hypotheses | Runtime correspondence |
| `G-E` | Concrete finite execution/property tests | Generic theorem validity by itself |
| `G-R0` | Abstraction/simulation interface compiles | Any Cordis implementation theorem |
| `G-H` | Frozen hashes and derived-manifest consistency | Correctness of the paper or code |

No item may be labelled `proved` merely because it compiles.  A contract field is an
assumption until a concrete instance or theorem discharges it.

## 9. Deferred scope and reopen rules

Deferred by design:

- full `BD-CONTROL` labelled lifecycle semantics, nondeterminism, and asynchronous landing;
- `BD-STAGING` base/extended calculus correspondence;
- `BD-SUPPORT` recursive support and late-registration cycle;
- `BD-SCOPED` realms/interception;
- concrete D34 typed operation-test AST;
- complete tracked-context/accumulator proof family;
- concrete `ValidState`/WF/provider/lifecycle preservation;
- reach-closed iterator monoids and the full Section 4 metatheory;
- name-bearing alpha actions for `Q`, `Xi`, ambient payloads, and control payloads;
- R1+ refinement to the TypeScript runtime.

Pending proof is different from deferred design.  For example, a recovery theorem may be
implemented as an interface (`I`) while its concrete proof is pending (`K`); that does not
make it a new blocker.  A change to the selected state carrier, failure meaning, relation
architecture, or iterator carrier requires a superseding ADR instead of an informal edit.

## 10. Feedback protocol

After each wave, record:

```text
wave / task:
toolchain and commit:
files changed:
commands and exact outcomes:
evidence state (A/I/K/E/R0/R1+):
new counterexamples or vacuity risks:
paper/ADR interpretation changes:
next action or rollback/defer decision:
```

The expected first implementation loop is therefore:

```text
P0 baseline
  → P1 thin relation core + one Toy check
  → P2 Effect/recovery
  → P3 partial/failure
  → P4 ranked iterator
  → P5 state/registry adapter
  → P6 alpha transport
  → P7 complete vertical slice
```

This ordering keeps the metatheory kernel executable and auditable while leaving a clean,
explicit route toward the later Cordis adapter and refinement work.
