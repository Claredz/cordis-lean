# DeepSeek Harness ADR-02: Coeffect Store, Specification, and Partiality Architecture

| Field | Value |
|---|---|
| Decision ID | `ADR-02` |
| Status | **Accepted** |
| Architecture validation | Accepted by paper audit, alternative comparison, and Mathlib API audit |
| Implementation validation | **Pending** - standalone Lean spike produced; compiler unavailable in creation environment |
| Date | 2026-08-25 |
| Resolves | `BD-COEFFECT` from Harness 04 |
| Depends on | `ADR-01: Equivalence Architecture` (accepted; user-reported one-shot compilation passed without modification) |
| Supersedes | Nothing |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Frozen dependency baseline | Harness 03 `1.0-frozen`, JSON SHA-256 `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| Disposition baseline | Harness 04 `1.0-baseline`, JSON SHA-256 `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |
| Companion artifacts | `DeepSeek-Harness-06-ADR-02-Coeffect-Store-and-Partiality-Architecture.json`; `DeepSeek-Harness-06-ADR-02-Coeffect-Store-and-Partiality-Architecture-Spike.lean` |

## 1. Decision

The formalization SHALL use a **finite dependent `Finmap` store, a dual semantic/executable specification layer, and an explicit `Option`-Kleisli partial-effect companion to ADR-01**.

Concretely:

1. The authoritative flat coeffect store is `Finmap V`, where `V : K → Type`. Its project-facing alias is `Store V`.
2. The store module exposes a stable proof API based on `lookup`, `keys`, `insert`, `erase`, `extract`, and disjoint `union`. Downstream proofs SHALL use that API rather than unfold `Finmap` internals. A carrier-polymorphic custom map typeclass is not introduced until a second implementation creates a demonstrated need.
3. Executable store and finite-specification operations require `[DecidableEq K]`. The core SHALL NOT assume `[Fintype K]` or `DecidableEq (V k)`.
4. A semantic dependency specification is `Set K`. An executable dependency specification and a provision declaration are `Finset K`. The coercion from `Finset K` to `Set K` is the authoritative bridge.
5. Semantic satisfaction is a `Prop`; executable satisfaction is finite subset checking against `σ.keys`; a Boolean checker is proved adequate. Finite store support alone is not used to claim that satisfaction of an arbitrary `Set K` is decidable.
6. Notification has a Prop-level classifier and a total executable function on `Finset K`, with an adequacy theorem. Classification is not identified with runtime delivery.
7. Raw storage operations remain total data-structure functions: lookup returns `Option`, insert overwrites, erase of an absent key is a no-op, and union is left-biased.
8. Legal binding transitions are a separate protocol: `get/require` needs presence; `provide` needs absence; `revoke` needs presence. Their returned inverses remain protocol-guarded partial maps: provide returns a presence-guarded revoke; revoke returns an absence-guarded provide of the captured value. An invalid protocol request has no successor state; it is never interpreted as the identity transition or an unchecked overwrite.
9. One operation has three related interfaces:
   - proof-indexed successful constructors for theorem statements;
   - `Option` for the mathematical partial semantics and Kleisli composition;
   - `Except StoreError` for executable diagnostics.
   The project proves erasure/refinement lemmas between them rather than maintaining three unrelated semantics.
10. ADR-01's total effect carrier remains intact. ADR-02 adds `PartialMap α β := α → Option β`, outcome-dependent `PartialEffect` return/bind, lifted result relations, partial law records, and an embedding of the total fragment. If either stage of partial-effect bind fails, its big-step mathematical denotation has no successor; if both succeed, their returned inverses compose in reverse order. A partial effect enters ADR-01's total fragment only after explicit forward-totality, invariant-closure, and inverse-totality-on-invariant proofs.
11. Definition 24 is represented by a typed operation-code family with per-key operation, argument, and outcome types. Local execution is partial, and its key-local store lift preserves all other lookups and, on successful value operations, preserves the store domain.
12. Domain-changing binding operations (`provide/revoke`) and domain-preserving D24 value operations are distinct protocols with distinct theorem families.
13. D33 store observation is the pointwise `Option` lifting of each key relation. This makes definedness part of observation and yields same-support, satisfaction-invariance, notification-invariance, and update/erase congruence lemmas.
14. Section 4 requirements and provisions are finite data. Active fiber tables are finite dependent stores; their global union is formed only under pairwise-disjoint provision/support invariants. Left bias is then observationally irrelevant.
15. The set of possible providers declared by provision sets and the currently active provider present in the global store are separate notions.

This decision resolves `BD-COEFFECT`. It does not resolve type-correct realms/interception (`BD-SCOPED`), the unified state (`BD-STATE`), iterators (`BD-ITER`), names/registries (`BD-NAMES`), or control/failure semantics (`BD-CONTROL`).

## 2. Why a decision is necessary

The paper's Section 3.2 combines four questions that Lean forces us to separate.

### 2.1 Finite partial storage

Definition 22 asks for a finite dependent partial map

\[
\sigma : (k : K) \rightharpoonup V_k.
\]

A plain function `(k : K) → Option (V k)` gives dependent lookup but does not carry an executable enumeration of its support. Adding a proof that its support is finite proves a proposition but still does not directly provide a `Finset K` for computation. Later definitions need both lookup laws and actual enumeration.

### 2.2 Semantic versus executable specifications

Definition 25 uses an arbitrary set of keys, while Definition 26 treats satisfaction as executable. The inference printed in the paper is invalid:

> finite `dom(σ)` does not make `d ⊆ dom(σ)` decidable when `d : Set K` is an arbitrary predicate.

Taking `σ` empty reduces the question to whether an arbitrary set `d` is empty. That is not constructively decidable. Execution therefore needs finite enumerable `d`, not merely finite support of `σ`.

### 2.3 Partial operations versus total effects

Definitions 23 and 24 describe lookup, set, local operations, and returned inverses as partial, but Definition 23 also classifies set as an instance of the earlier total witnessed-effect type. Those claims cannot all be copied literally. An absent lookup, duplicate provide, missing revoke, or undefined local operation must be represented in the type.

### 2.4 Local operations versus binding lifecycle

A D24 operation changes the value stored at one existing key and should preserve the store domain. `provide` and `revoke` change the domain and participate in component activation/deactivation. Treating them as one undifferentiated update operation obscures both recovery and the frame properties needed by T40 and Section 4.

Without one global decision, different team members could independently choose `Set`, `Finset`, proof preconditions, `Option`, `Except`, `Finsupp`, or totalized no-ops. Their definitions would look locally plausible but would not compose into one calculus.

## 3. Decision drivers

| Driver | Required consequence |
|---|---|
| Dependent type safety | A binding at key `k` has type `V k` without packaging/casting at every lookup. |
| Genuine finite support | The store carries an executable `Finset K` of keys. |
| Local proofs stay general | Lookup, update, frame, and independence results do not require global finiteness arguments or `Fintype K`. |
| Semantic fidelity | Arbitrary `Set K` specifications remain expressible as propositions. |
| Executability | Notification and lifecycle dependency checks iterate over `Finset K`. |
| Honest failure | Invalid operations yield no successor; no-op totalization is forbidden. |
| ADR-01 compatibility | Definedness, successor relation, selected inverse, inverse properness, recovery, and exact outcome are all visible in the partial result relator. |
| D24 heterogeneity | Operation, argument, and outcome types may depend on the key and operation code without an untyped existential registry. |
| T40 frame reasoning | A key-local lift exposes unchanged lookup at every distinct key and common-domain behavior. |
| Section 4 aggregation | Active tables can be combined under disjointness, and provider uniqueness is a theorem of explicit invariants. |
| Runtime refinement | Diagnostic errors can be implemented without making error payloads part of every mathematical theorem. |
| Team stability | One canonical representation and bridge theorem family prevents parallel modules from inventing incompatible partiality conventions. |

## 4. Alternatives considered

### 4.1 Store carrier

| Candidate | Description | Decision | Reason |
|---|---|---|---|
| A. Function plus finite-support proof | `(k : K) → Option (V k)` together with a proposition that the support is finite. | Rejected as the concrete store | Excellent extensional model, but it does not directly carry an executable support enumeration and recreates much of `Finmap`. It may be used as a semantic view. |
| B. `Finmap V` | Mathlib finite dependent map with dependent lookup, finite keys, insert, erase, extract, union, and extensionality. | **Accepted** | It exactly matches D22 and supplies the laws needed downstream under only `DecidableEq K`. |
| C. `DFinsupp` | Dependent finitely supported function. | Rejected | It requires a distinguished zero/default in each `V k` and conflates absence with that value. Coeffects need genuine missingness. |
| D. `Finsupp K (Sigma V)` | Ordinary finite map to an existentially packaged dependent value. | Rejected | It loses the invariant that a value packaged at key `k` really has type `V k`, forcing casts or validation. |
| E. Custom carrier-polymorphic store class now | Abstract over all possible finite dependent-map implementations. | Deferred | The proof-facing API is fixed now, but a higher-kinded custom class adds design and inference cost without a second implementation. Introduce it only through a later ADR if the need becomes concrete. |

Mathlib's current documentation confirms that `Finmap V` is a finite dependent map, `lookup k σ : Option (V k)`, `keys : Finset K`, and the library supplies lookup/insert/erase/extensionality/disjoint-union laws: [Mathlib `Finmap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finmap.html).

### 4.2 Specification carrier

| Candidate | Decision | Reason |
|---|---|---|
| `Set K` only | Rejected | Semantically general but cannot be enumerated or generally decided. |
| `Finset K` only | Rejected | Executable, but would silently strengthen every semantic statement to finite specifications and erase the paper's abstract distinction. |
| `Set.Finite d` proof | Rejected as executable carrier | It proves finiteness but is not the runtime data structure the notification algorithm consumes. |
| `Set K` plus `Finset K` and a bridge | **Accepted** | Keeps propositions general and programs finite; every executable theorem states its adequacy relation explicitly. |

Finite subset is decidable under `DecidableEq K`, independently of any equality on values: [Mathlib `Finset` decidability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html#Finset.instDecidableRelSubset).

### 4.3 Failure representation

| Candidate | Decision | Reason |
|---|---|---|
| Proof arguments only | Rejected as the sole interface | Best for success theorems, but it cannot execute on unchecked runtime input or express common-domain partiality. |
| `Option` only | Rejected as the sole interface | Correct mathematical partiality and composition, but insufficient diagnostics for the implementation boundary. |
| `Except Error` only | Rejected as the mathematical core | It makes error payload comparison infect D24/D39 and ADR-01 laws even where only definedness matters. |
| Totalize failure as identity/no-op | Rejected | It creates a false transition, breaks protocol meaning, and can make recovery claims vacuous. |
| Proof success view + `Option` semantics + `Except` checked view | **Accepted** | Each layer has one role; erasure/refinement theorems prevent semantic drift. |

### 4.4 Relation to ADR-01

| Candidate | Decision | Reason |
|---|---|---|
| Force partial operations into ADR-01's total `Effect` | Rejected | Preconditions and definedness disappear or must be hidden in an artificial state invariant. |
| Build a completely separate partial theory | Rejected | It duplicates ADR-01's result relations, inverse laws, and equality/observational specializations. |
| Add an `Option`-Kleisli companion with a total embedding | **Accepted** | Partiality is explicit, composition is standard, and the total lawful fragment remains a proved specialization. |

## 5. Normative type architecture

Names below are architectural names. Final module paths may change in the executable blueprint, but their distinctions and laws are normative.

### 5.1 Concrete store and proof-facing interface

```lean
abbrev Store {K : Type u} (V : K → Type v) := Finmap V

lookup : (k : K) → Store V → Option (V k)
keys   : Store V → Finset K
insert : (k : K) → V k → Store V → Store V
erase  : (k : K) → Store V → Store V
extract : (k : K) → Store V → Option (V k) × Store V
union  : Store V → Store V → Store V
```

The production store façade must export at least these laws:

| Law family | Required statement |
|---|---|
| Extensionality | Equal lookup at every key implies equal stores. |
| Presence | `k ∈ σ.keys ↔ k ∈ σ ↔ lookup k σ` is defined. |
| Same-key insert | `lookup k (insert k v σ) = some v`. |
| Other-key insert frame | If `j ≠ k`, lookup at `j` is unchanged. |
| Same-key erase | `lookup k (erase k σ) = none`. |
| Other-key erase frame | If `j ≠ k`, lookup at `j` is unchanged. |
| Insert support | Keys become `insert k σ.keys`; if `k` was present, support is unchanged. |
| Erase support | Keys become `σ.keys.erase k`. |
| Fresh provide recovery | If `k ∉ σ`, then `erase k (insert k v σ) = σ`. |
| Captured revoke recovery | If `lookup k σ = some v`, then `insert k v (erase k σ) = σ`. |
| Distinct-key algebra | Insert/erase operations at distinct keys commute with the necessary dependent typing. |
| Disjoint union | Union has the union of supports; under disjointness it is unbiased and commutative. |

Only `[DecidableEq K]` is required for these executable operations. The project must not introduce `DecidableEq (V k)` merely to compare stores; proofs use lookup extensionality instead.

### 5.2 Semantic and executable specifications

```lean
abbrev SemanticSpec (K) := Set K
abbrev ExecSpec     (K) := Finset K
abbrev Provision    (K) := Finset K

semanticize : ExecSpec K → SemanticSpec K
```

The satisfaction layer is:

```lean
SatisfiesSem  (σ : Store V) (d : Set K)    : Prop
SatisfiesExec (σ : Store V) (d : Finset K) : Prop := d ⊆ σ.keys
satisfiesB    (σ : Store V) (d : Finset K) : Bool
```

Required bridge theorems are:

\[
\operatorname{SatisfiesExec}(\sigma,d)
\iff
\operatorname{SatisfiesSem}(\sigma,\uparrow d),
\]

and

\[
\operatorname{satisfiesB}(\sigma,d)=\mathrm{true}
\iff
\operatorname{SatisfiesExec}(\sigma,d).
\]

`SemanticSpec` is used for general propositions and abstraction theorems. `ExecSpec` is used wherever an algorithm enumerates requirements: notification, target-view computation, lifecycle guards, finite provider search, and executable tests. Section 4 component requirements and provisions are `Finset K`; their semantic coercions appear in general statements.

### 5.3 Notification

```lean
inductive Notification
  | activating | deactivating | neutral

ClassifiesSem  : Store V → Store V → Set K    → Notification → Prop
ClassifiesExec : Store V → Store V → Finset K → Notification → Prop
notify         : Store V → Store V → Finset K → Notification
```

The truth table is fixed:

| Before satisfies | After satisfies | Result |
|---:|---:|---|
| false | true | `activating` |
| true | false | `deactivating` |
| false | false | `neutral` |
| true | true | `neutral` |

Two adequacy results are mandatory:

1. `notify` satisfies `ClassifiesExec`.
2. `ClassifiesExec` at `d` is equivalent to `ClassifiesSem` at `↑d`.

These results classify one observed before/after pair. They do not prove that every affected component is found, queued exactly once, or notified in an admissible order. Those are registry/control obligations for later ADRs.

### 5.4 Raw operations and protocol operations

The following separation is mandatory.

| Layer | Operation | Behavior |
|---|---|---|
| Raw store | `lookup` | Total function returning `Option (V k)`. |
| Raw store | `insert` | Total overwrite at `k`. |
| Raw store | `erase` | Total; absent key is unchanged. |
| Required access | `requireWith` | Returns `V k` from a proof that `k` is present. |
| Mathematical protocol | `provide?`, `revoke?`, `require?` | Returns `Option`; `none` means no legal transition/result. |
| Checked protocol | `provideE`, `revokeE`, `requireE` | Returns `Except StoreError`; errors distinguish missing and duplicate binding. |
| Success theorem view | `provideWith`, `revokeWith` | Accepts the precondition as proof data and exposes the successful state directly. |

For `provide(k,v)` the successful successor is `insert k v σ`; its returned inverse is a **presence-guarded revoke** at the captured physical key `k`. For `revoke(k)` the successful operation captures the old value `v` and erases `k`; its returned inverse is an **absence-guarded provide** of that captured `v`. The latter must not be implemented by raw overwriting `insert`, because a later binding at `k` makes the inverse undefined rather than authorizing it to destroy that binding. An inverse must capture the storage location and value chosen by the forward run; it must not recompute them from an arbitrary later resolution context.

The checked and mathematical views are related by error erasure:

```lean
provideE k v σ = .ok τ ↔ provide? k v σ = some τ
revokeE  k σ   = .ok r ↔ revoke?  k σ   = some r
```

Equivalent statements exist for errors and required lookup. Proof-indexed views are proved equal to the corresponding successful branch. No interface is permitted to turn an error into `some σ`.

### 5.5 Partial maps and effects

```lean
abbrev PartialMap (α) (β) := α → Option β

pid   : PartialMap α α
pcomp : PartialMap α β → PartialMap β γ → PartialMap α γ
```

`pcomp` is Option bind in execution order and satisfies exact associativity and unit laws. It is the authoritative composition for partial state functions and returned partial inverses.

ADR-01's relation lift is extended as follows:

```lean
OptionRel R none     none     := True
OptionRel R (some x) (some y) := R x y
OptionRel R _        _        := False

PRespects R S f := ∀ ⦃x y⦄, R x y → OptionRel S (f x) (f y)
PPointwiseRel S f g := ∀ x, OptionRel S (f x) (g x)

structure PartialResult (Γ) (B) where
  state   : Γ
  undo    : PartialMap Γ Γ
  outcome : B

abbrev PartialEffect (Γ) (B) := Γ → Option (PartialResult Γ B)

ppure       : B → PartialEffect Γ B
pbindEffect : PartialEffect Γ B → (B → PartialEffect Γ C) → PartialEffect Γ C
```

`pbindEffect first next` executes `first`; on success it selects `next` from the exact ordinary outcome and executes it at the first successor. If either stage is `none`, the whole big-step denotation is `none` and exposes no committed successor. This is an atomic mathematical denotation, not a claim that a mutable runtime can forget a partially executed first stage; staged execution, rollback-on-second-failure, and exceptions belong to the iterator/control refinement.

On two successes, if the returned inverses are `u₁` and `u₂`, the combined inverse is

\[
u_2 >=> u_1,
\]

so recovery remains LIFO. `ppure` and `pbindEffect` satisfy exact left unit, right unit, and associativity laws. Lawful partial effects are closed under bind when the first effect is lawful and each outcome-indexed continuation is lawful at the same explicit relation. Exact outcome equality in `run_respects` is what makes related runs choose the same continuation, as required by D41-T42.

For an explicit ADR-01 equivalence `S`, a lawful partial effect must provide:

| Field | Obligation |
|---|---|
| `run_respects` | Related inputs have identical definedness. Successful runs have `S`-related successors, pointwise `OptionRel S` selected inverses, and exactly equal outcomes. |
| `undo_respects` | Every inverse returned by a successful run is a partial map respecting `S`, including definedness. |
| `recovers` | The returned inverse is defined at the actual successor and restores the input modulo `S`. |

This is the partial counterpart of ADR-01, not a weakening of it. In particular, `OptionRel` makes success versus failure observable.

### 5.6 Boundary between partial and total effects

Every total ADR-01 effect embeds into the partial layer by wrapping its run, successor, and undo applications in `some`. The embedding preserves lawfulness.

The reverse direction is not automatic. Forward success alone is insufficient, because an ADR-01 effect also returns a total inverse. A partial effect `e` may be restricted to an invariant only under a package equivalent to:

```lean
structure TotalizableOn (I : Γ → Prop) (e : PartialEffect Γ B) : Prop where
  run_total   : ∀ x, I x → ∃ r, e x = some r
  state_closed : ∀ x (hx : I x) r, e x = some r → I r.state
  undo_total_closed :
    ∀ x (hx : I x) r, e x = some r → ∀ y, I y →
      ∃ z, r.undo y = some z ∧ I z
```

This evidence permits a total outcome-carrying effect on `{x // I x}`. To obtain ADR-01's plain state-only `Effect`, the ordinary outcome is then explicitly projected away; an operation theorem that observes the outcome keeps the outcome-carrying result layer instead. A call-site guard may also prove the same obligations for a narrower domain. If failure becomes an operational lifecycle outcome, it is routed through the future `R.fail`/iterator design. It is never erased to a total ADR-01 effect by choosing a default successor or inverse.

### 5.7 Typed D24 operation family

The heterogeneous operation universe is represented by codes, not by an untyped set of existential functions:

```lean
structure KeyOperation (K) (V : K → Type) where
  Op  : K → Type
  Arg : (k : K) → Op k → Type
  Out : (k : K) → Op k → Type
  run : (k : K) → (op : Op k) → Arg k op → V k →
    Option (PartialResult (V k) (Out k op))
```

`Op k` need not be finite or decidably enumerable. Enumeration is required only for an executable finite test language if and when D34 chooses one.

For each key relation `KeyObs k`, local operation admission uses the full lawful partial-effect contract above. The checked implementation may use an operation-specific `Except E`; erasing `E` must refine the `Option` run. If a later calculus observes `E`, its result relation is supplied explicitly; by default ADR-01 requires exact error tags.

The key-local lift performs this data flow:

\[
\sigma(k)
\xrightarrow{\text{local run}}
(v',u,b)
\quad\leadsto\quad
(\sigma[k\mapsto v'],\widehat u,b),
\]

where `û` looks up the current value at the same physical key, applies `u`, and writes the recovered value back at that key. The mandatory lift theorem family contains:

1. missing local binding implies an undefined lifted run;
2. local undefinedness implies lifted undefinedness;
3. successful lifting preserves the store support;
4. lookup at the operated key agrees with the local successor;
5. every distinct-key lookup is unchanged;
6. local recovery lifts to store recovery;
7. local `KeyObs` lawfulness lifts to `StoreObs` lawfulness;
8. operations at distinct physical keys preserve each other's definedness, outcomes, successors, and selected inverses, yielding T40;
9. all partial commutation equations are stated on their common successful domain or through `OptionRel`, never by applying a partial function as if it were total.
10. `ppure`/`pbindEffect` denotation and lawfulness are closed under the typed, outcome-dependent D41 constructors, yielding the exact compositional premise consumed by T42.

### 5.8 Binding protocol is not D24 value update

The project keeps two operation classes:

| Class | Domain behavior | Typical use | Independence theorem |
|---|---|---|---|
| `BindingTransition` | May add/remove one key | component provide/revoke | Distinct-key protocol transitions commute when both orders are legal; recovery uses fresh/present premises. |
| `KeyOperation` | Requires an existing key and preserves support | D24 service/value operations | T40 key-local independence under full partial lawfulness. |

This separation prevents a D24 support-preservation lemma from being falsely applied to activation/deactivation.

## 6. Store observational relation

Given a per-key equivalence `KeyObs k` from ADR-01, define:

\[
\operatorname{StoreObs}(\sigma,\tau)
\iff
\forall k,\;
\operatorname{OptionRel}(\operatorname{KeyObs}_k)
  (\operatorname{lookup}\,k\,\sigma)
  (\operatorname{lookup}\,k\,\tau).
\]

The paper writes D33 as same domain plus pointwise related values. The `OptionRel` formulation is equivalent and makes the definedness obligation reusable by D24 and D39.

Required theorems are:

- `StoreObs` is an equivalence when every `KeyObs k` is an equivalence;
- `StoreObs σ τ` implies `σ.keys = τ.keys`;
- semantic and executable satisfaction are invariant under `StoreObs`;
- notification classification and executable `notify` are invariant under `StoreObs` at both endpoints;
- related inserts at the same key preserve `StoreObs`;
- erasing the same key preserves `StoreObs`;
- disjoint union preserves `StoreObs` componentwise;
- D24 lifts respect `StoreObs` under the local operation law.

No equality of service values is required. Definedness and support equality follow from `OptionRel`, not from `DecidableEq (V k)`.

## 7. Section 4 finite declarations and active-store aggregation

The coeffect-facing portion of a component/fiber has finite data:

```lean
requirements : Finset K
provisions   : Finset K
table        : Store V
```

The following invariants are normative inputs to later state and registry ADRs:

1. **Write confinement:** every key written by a component action lies in its declared `provisions`.
2. **Table confinement:** `table.keys ⊆ provisions` in every reachable fiber state.
3. **Provision disjointness:** distinct registered fiber incarnations in `dom(Fγ)` have disjoint declared provision sets within the flat/single-realm calculus, including retired/vestigial entries not yet removed.
4. **Active table selection:** only fibers whose lifecycle constructor is exactly `Active` contribute their local tables to the global coeffect store. In the base calculus `installed` and `Active` coincide; in the extended calculus `installed` also includes `Reloading` and `Unloading`, whose tables are not globally visible.
5. **Global store:** fold finite active tables with `Finmap.union`.
6. **Bias elimination:** pairwise table disjointness proves the result independent of fold order despite raw union being left-biased.
7. **Active provider uniqueness:** at most one active table contains any physical key.
8. **Possible provider uniqueness:** at most one registered declaration in `dom(Fγ)` contains any physical key; this is stronger/different from current presence and continues to count retired entries until `O-Remove`.
9. **D69 total provision:** after every successful completed activation in scope, `table.keys = provisions`, not merely subset.

The finite registry that permits folding active tables belongs to `BD-STATE`/`BD-NAMES`. ADR-02 fixes the table, declaration, disjointness, and aggregation contracts consumed by that later decision.

Under isolation, all of these statements must be indexed by resolved physical realm/location. ADR-02 decides only the flat physical-key substrate; `BD-SCOPED` must provide the type-preserving resolver and embedding.

## 8. Paper repair manifest

| Paper node | Authoritative formal target after ADR-02 |
|---|---|
| `D22` | `Store V := Finmap V` plus the stable finite-dependent-map theorem surface. |
| `D23` | Raw lookup/insert/erase separated from checked `require/provide/revoke`; successful provide and revoke have captured inverses; partiality is explicit. |
| `D24` | Typed `KeyOperation` codes; partial result with outcome and partial inverse; full ADR-01-compatible relation law; key-local store lift and frame/recovery theorems. |
| `D25` | `SemanticSpec := Set K`, `ExecSpec := Finset K`, and `semanticize`. |
| `SAT` | Prop-level semantic satisfaction, finite executable satisfaction, Boolean checker, and adequacy. |
| `D26` | Prop classifier plus computable `notify` on `Finset K`, with adequacy; no false finite-support decidability inference. |
| `D28-D31` | Reuse this store/spec/partiality substrate, but remain blocked until `BD-SCOPED` supplies type-correct realms and metadata inheritance. |
| `D33` | Pointwise `OptionRel KeyObs` on store lookup; same support and congruence theorems; full-state lift awaits `BD-STATE`. |
| `D34-L35` | Tests use the typed operation-code family and partial evaluation; exact definedness/outcomes and ADR-01's selected-inverse repair are representable. Concrete test syntax remains the node-level implementation task. |
| `D39` | Partial independence includes common definedness, `StoreObs` successors, pointwise-related selected inverses, and exact outcomes. |
| `T40` | Distinct **physical** key theorem from key-local frame and full partial laws; does not claim distinct logical keys under isolation. |
| `D41-T42` | Typed mediated-program syntax denotes through `ppure`/outcome-dependent `pbindEffect`; exact outcomes select the same continuation, and bind lawfulness plus D39/T40 support the structural independence proof. |
| `D43` | Requirements/provisions are `Finset K`; no-write-outside-provision becomes an explicit support/frame obligation. State and iterator carriers remain undecided. |
| `D45` | Local/active tables and their disjoint union are fixed; registry and incarnation representation remain blocked. |
| `D69` | Totality means equality between the successful completed activation table's keys and declared provisions; quantification over activation awaits `BD-ITER`. |

## 9. Consequences for affected disposition nodes

Harness 04 has exactly 20 retained entries blocked by `BD-COEFFECT`: 19 numbered nodes plus auxiliary `SAT`.

| Group | Nodes | Consequence of ADR-02 |
|---|---|---|
| Flat store and reactivity | `D22`, `D23`, `D24`, `D25`, `D26`, `SAT` | Carrier, failure convention, specification split, checker, notification, and lift contracts are fixed. |
| Scoped extensions | `D28`, `D29`, `D30`, `D31` | Flat substrate and partiality convention are fixed; `BD-SCOPED` remains. |
| Observation and independence | `D33`, `D34`, `L35`, `D39`, `T40`, `D41`, `T42` | Store/result relators and typed operation family are fixed; D33's full-state projection still awaits `BD-STATE`. |
| Calculus shell | `D43`, `D45` | Finite declarations, local tables, confinement, disjoint union, and provider distinctions are fixed; state/iterator/name blockers remain. |
| Total provision | `D69` | The table/support predicate is fixed; successful activation semantics awaits `BD-ITER`. |

Effective readiness is derived, not written back into Harness 04. With both ADR-01 and ADR-02 accepted, these entries have no remaining global blocker from the baseline register:

```text
D22 D23 D24 D25 D26 D34 L35 D39 T40 D41 T42 SAT
```

The following affected entries retain at least one blocker:

| Nodes | Remaining blocker(s) |
|---|---|
| `D28`, `D29`, `D30`, `D31` | `BD-SCOPED` (and only already-resolved `BD-EQUIV` where listed) |
| `D33` | `BD-STATE` |
| `D43` | `BD-STATE`, `BD-ITER` |
| `D45` | `BD-STATE`, `BD-NAMES` |
| `D69` | `BD-ITER` |

Every frozen dependency edge and every non-`BD-COEFFECT` blocker is preserved.

## 10. Coding and proof rules imposed by this ADR

1. Use the project `Store` façade; do not unfold `Finmap.entries` or depend on its quotient implementation in downstream proofs.
2. Require `DecidableEq K` only at executable store/specification boundaries. Do not add `Fintype K` globally.
3. Do not require equality or decidable equality on service values for presence, support, satisfaction, notification, recovery, or observational proofs.
4. State semantic results over `Set K` when arbitrary specifications matter; state algorithms over `Finset K`; expose the coercion/adequacy theorem.
5. Never cite finite `σ.keys` as sufficient to decide an arbitrary `Set K` specification.
6. Keep raw overwrite/no-op operations out of protocol transition relations unless their preconditions have been proved.
7. Invalid `provide/revoke/require` operations produce no successor. No default state and no identity transition are allowed.
8. Use `Option` as the mathematical partiality erasure and `Except` as the checked diagnostic view. Every checked operation must have an erasure/refinement theorem.
9. Partial functions compose with Option bind. Do not simulate partial composition by supplying arbitrary defaults.
10. Partial effects compose with outcome-dependent bind; second-stage failure means no big-step successor, and two successful inverses compose in reverse order.
11. A partial operation can be used as an ADR-01 total effect only after proofs of forward totality, successor invariant closure, and returned-inverse totality/invariant closure—not merely forward success.
12. Compare partial results with equal definedness, related successors, pointwise-related selected inverses, inverse properness, recovery, and exact outcome tags.
13. Use typed operation codes for D24/D34/D41; do not form an untyped heterogeneous `Set` of functions.
14. Prove domain preservation for D24 value operations and keep it separate from domain-changing binding transitions.
15. Returned binding inverses must re-check protocol preconditions; raw erase/insert appears only inside the proved successful branch.
16. State T40 for distinct flat physical keys. Realm-sensitive independence must be restated in `BD-SCOPED` using resolved locations.
17. Form the Section 4 global store only from exactly `Active` fibers in a finite registry and under an explicit disjointness invariant; raw union's left bias is not a provider-selection policy.
18. Distinguish registered possible provider, currently active provider, and present binding in theorem names.
19. Express D69 as equality of finite supports after a successful completed activation, not as a global axiom that every intermediate table is total.

## 11. Acceptance record

| ID | Check | Architecture result | Implementation state |
|---|---|---|---|
| `COE-AC-01` | Dependent finite store supports lookup, update, erase, extract, finite keys, and extensionality. | Passed | `Finmap` API audited; representative signatures in spike. |
| `COE-AC-02` | Executable operations require only `DecidableEq K`, not `Fintype K` or value equality. | Passed | Spike has only `[DecidableEq K]`. |
| `COE-AC-03` | Semantic `Set K` and executable `Finset K` specifications are distinct and bridged. | Passed | Adequacy theorem represented in spike. |
| `COE-AC-04` | Satisfaction checker is genuinely decidable for executable specifications. | Passed | Boolean checker and correctness theorem represented. |
| `COE-AC-05` | Notification has Prop and executable layers with the four-case truth table. | Passed | Classifier, function, and adequacy represented. |
| `COE-AC-06` | Raw operations and legal protocol transitions are separated. | Passed | `provide?`/`provideE` and raw `Finmap` operations represented. |
| `COE-AC-07` | Invalid operations have no successor and are not identity. | Passed | `Option.none`/`Except.error` branches fixed. |
| `COE-AC-08` | Proof, `Option`, and `Except` views have one refinement contract. | Passed | Success erasure lemmas represented; full family is blueprint work. |
| `COE-AC-09` | Fresh provide and captured revoke have valid recovery laws. | Passed by theorem audit | Both recovery proofs represented; compiler validation pending. |
| `COE-AC-10` | Option-Kleisli partial maps and outcome-dependent partial effects have exact unit/associativity and reverse-order inverse composition. | Passed by theorem audit | Map and effect-bind laws plus failure behavior represented; compiler validation pending. |
| `COE-AC-11` | Partial ADR-01 law preserves definedness, successor relation, selected inverse, inverse properness, recovery, and outcome, and is closed under outcome-dependent bind. | Passed by law audit | Full law record and bind-closure proof represented; compiler validation pending. |
| `COE-AC-12` | Total ADR-01 effects embed lawfully into the partial layer. | Passed by theorem audit | Embedding proof represented; compiler validation pending. |
| `COE-AC-13` | D24 has typed heterogeneous operation/argument/outcome families and a key-local lift. | Passed | Codes and lift represented; full lift theorem family is blueprint work. |
| `COE-AC-14` | `StoreObs` includes definedness and preserves support/satisfaction. | Passed by theorem audit | Core definition and representative proofs represented; compiler validation pending. |
| `COE-AC-15` | Section 4 finite declarations, table confinement, disjoint union, provider distinctions, and D69 support equality are fixed. | Passed | Contracts fixed; concrete registry awaits other ADRs. |
| `COE-AC-16` | Affected node set exactly matches Harness 04. | Passed | 20 entries: 19 numbered plus `SAT`. |
| `COE-AC-17` | Partial-to-total restriction requires forward success, successor closure, and inverse totality/closure on the invariant. | Passed | `TotalizableOn` represented in spike; restriction construction is production work. |

## 12. Validation record

The companion Lean spike covers:

- `Store V := Finmap V`;
- semantic/executable specifications and satisfaction adequacy;
- Boolean satisfaction checking;
- Prop/executable notification and adequacy;
- checked `provide/revoke` views and successful-erasure lemmas;
- provide/revoke recovery and distinct-key frame laws;
- Option-Kleisli identity and associativity;
- outcome-dependent partial-effect bind, atomic failure behavior, and reverse-order inverse selection;
- partial result relators and lawful partial effects;
- lawfulness closure under outcome-dependent partial-effect bind;
- `TotalizableOn` evidence separating forward success from inverse totality on an invariant;
- lawful total-to-partial embedding;
- typed D24 operation codes and key-local lift;
- `StoreObs`, definedness agreement, support membership agreement, and semantic-satisfaction invariance.

The current creation environment does not contain `lean` or `lake`, so implementation validation remains pending. The required gate is:

```text
lake env lean DeepSeek-Harness-06-ADR-02-Coeffect-Store-and-Partiality-Architecture-Spike.lean
```

or its equivalent from the project root. The exact Lean and Mathlib versions must be recorded when that gate is run. A successful spike validates the selected API shape; it is not yet the production module decomposition or the full proof inventory.

## 13. Non-decisions

ADR-02 intentionally does not decide:

- the literal module names, namespaces, or import graph of the final Lean project;
- whether a later second store implementation justifies a carrier-polymorphic store typeclass;
- the type-preserving realm resolver, realm identity, interception metadata algebra, or derived-context inheritance (`BD-SCOPED`);
- the unified state/registry/action-code representation (`BD-STATE`);
- iterator finiteness, failure carrier, or asynchronous semantics (`BD-ITER`, `BD-CONTROL`);
- finite registry and fiber-incarnation representation (`BD-NAMES`);
- the concrete D34 test AST and whether it is finitely enumerable;
- concrete per-key equivalences for an application;
- error payloads for application-specific D24 operations;
- ownership, milestones, tactics, code style beyond the architectural rules above.

## 14. Revision policy and triggers

ADR-02 is accepted but may be superseded when later formalization reveals a genuine global blocker.

### 14.1 Change protocol

- Editorial clarification may update this artifact with a recorded patch version.
- A semantic change to the store carrier, semantic/executable split, failure layering, partial law, or D24 operation family requires a superseding ADR.
- The frozen graph and Harness 04 baseline are not silently edited. Effective readiness is recomputed from the immutable baseline plus accepted/superseding ADRs and newly recorded blockers.
- A new node-local proof difficulty becomes a work item. It becomes a global blocker only if it forces incompatible signatures across multiple downstream modules or invalidates an architectural acceptance condition.
- Any superseding decision must list affected merged modules and revalidation obligations.

### 14.2 Reopen triggers

Reopen or supersede ADR-02 if any of the following occurs:

1. the pinned Lean/Mathlib compilation shows that `Finmap` cannot realize one of the required dependent lookup/update/erase/frame laws without adding a materially stronger global assumption;
2. D24's typed operation family cannot express a required paper operation without unsafe casts or loss of outcome typing;
3. total-to-partial lawfulness requires a stronger ADR-01 result relation than ADR-01 fixed;
4. Section 4 active-table aggregation cannot be made fold-order independent under the specified disjointness invariants;
5. the selected unified-state architecture requires coeffect stores that are infinite or non-enumerable in ordinary reachable states rather than only as semantic views;
6. `BD-SCOPED` proves that the flat physical-key store cannot embed lookup/update faithfully into the realm-aware model;
7. executable notification requires information not representable as a finite requirement set plus finite registry/reverse index;
8. implementation repeatedly needs error-payload relations in mathematical independence proofs, showing that `Option` erasure is not an adequate common core;
9. a second concrete store implementation becomes necessary and the façade cannot support it without a carrier-polymorphic abstraction.

## 15. Final adjudication

`BD-COEFFECT` is **resolved** by this ADR.

The authoritative architecture is:

\[
\boxed{
\begin{aligned}
&\texttt{Finmap V} &&\text{finite dependent storage},\\
&\texttt{Set K} + \texttt{Finset K} &&\text{semantic and executable specifications},\\
&\texttt{Option} + \texttt{Except} + \text{proof views}
  &&\text{partial semantics, diagnostics, and success theorems},\\
&\text{Option-Kleisli partial effects} + \text{ADR-01 laws}
  &&\text{honest composition and observation}.
\end{aligned}}
\]

This is the fixed substrate for D22-D26, the flat portion of D28-D31, D33-D42, and the finite coeffect-facing portions of D43, D45, and D69.
