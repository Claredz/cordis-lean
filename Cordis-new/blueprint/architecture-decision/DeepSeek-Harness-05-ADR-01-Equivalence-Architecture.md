# DeepSeek Harness ADR-01: Equivalence Architecture

| Field | Value |
|---|---|
| Decision ID | `ADR-01` |
| Status | **Accepted** |
| Architecture validation | Accepted by paper audit and law-level feasibility proof |
| Implementation validation | **Pending** compilation in the project's pinned Lean toolchain |
| Date | 2026-08-25 |
| Resolves | `BD-EQUIV` from Harness 04 |
| Supersedes | Nothing |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Frozen dependency baseline | Harness 03 `1.0-frozen`, JSON SHA-256 `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| Disposition baseline | Harness 04 `1.0-baseline`, JSON SHA-256 `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |
| Companion artifacts | `DeepSeek-Harness-05-ADR-01-Equivalence-Architecture.json`; `DeepSeek-Harness-05-ADR-01-Equivalence-Architecture-Spike.lean` |

## 1. Decision

The formalization SHALL use an **explicit-equivalence, relation-parametric law layer over a raw exact algebra**.

Concretely:

1. Raw transformations, effect results, effect composition, tracking, lifting, projections, and control-state constructors remain ordinary Lean data and functions. Their computational and structural equations use Lean equality.
2. Recovery, observational commutation, inverse-selection stability, and other semantic correctness claims are parameterized by an explicitly supplied equivalence value.
3. The selected relation is passed explicitly. It SHALL NOT be installed as a unique global `[Setoid Γ]`, because the same state carrier may simultaneously support several incomparable relations.
4. The primary correctness API is a predicate or law record over a raw effect. A proof-carrying bundled subtype may be offered as a convenience, but it is not the raw computational carrier.
5. Quotients may be constructed later as derived semantic views after congruence proofs. They SHALL NOT be the state or effect representation on which the operational semantics executes.
6. Equality is one explicit specialization of the generic law layer. The repaired equality reading of Definition 8 is recovered by theorem, not maintained as a second copied theory.
7. A lawful effect must make the inverse selected at related inputs stable **pointwise modulo the selected relation**, must require every actually returned inverse to preserve that relation, and must satisfy local recovery modulo that relation.
8. Paper relations with different observation boundaries remain different named values: per-key/store `≃`, D33's projection-only state `≃`, D53's lifecycle-state `≃`, operation-test indistinguishability `≈_A`, the Section 4 control-erasing relation `≈`, and fresh-name renaming are not silently identified.
9. The fixed-generator test language of Definition 34 does not by itself prove selected-inverse coherence. Lemma 35 is split and repaired as specified in Section 8 below.
10. Lemma 38 is not implemented as one proposition that “replaces every equality.” It is realized by the exact/relational theorem manifest in Section 9, generic closure theorems, and equality/observational specializations.

This decision resolves the architecture question `BD-EQUIV`. It does not make every affected node implementation-ready: any other blocker listed for that node in Harness 04 remains in force.

## 2. Why a decision is necessary

The paper uses three different modes of comparison.

- Section 3.1 presents exact functions and exact equations. Definitions 1, 3, 9, and 12 are computations; Theorems 4, 5, 10, 13, and 14 are structural equalities.
- Section 3.3.2 says that physically exact recovery is generally the wrong observation boundary. Definition 36 distinguishes relation-preserving maps from pointwise-related maps, Definition 37 rereads witnessed effects modulo `≃`, and Lemma 38 claims that the earlier results transfer.
- Section 4.4 introduces another relation written `≈` that forgets control fields. The paper explicitly states that this relation and its full-state `≃` neither refine one another.

Three naive implementations are therefore unsafe.

1. Replacing every occurrence of `=` with one relation destroys computational equations and makes monoid laws needlessly weak.
2. Keeping a complete equality theory and copying it for `≃` duplicates the central effect metatheory and makes later extensions drift.
3. Quotienting the state at the start hides representatives needed by operational rules and first requires precisely the congruence obligations that the formalization is meant to prove.

There is also a separate defect around returned inverses. For an effect

\[
e : \Gamma \to \Gamma \times (\Gamma \to \Gamma),
\]

related inputs can select different inverse functions. It is not enough that each inverse individually preserves `≃`; the two selected functions must also be pointwise related. The proof of Lemma 35 does not establish that property from its fixed-generator tests.

## 3. Decision drivers

The chosen architecture must satisfy all of the following.

| Driver | Required consequence |
|---|---|
| One raw executable semantics | Effect execution and composition do not depend on quotient representatives or proof fields. |
| No duplicated Section 3.1 theory | Equality and observational readings share the same law proofs. |
| Exact computations remain exact | Definitions and structural homomorphism laws remain rewrite-friendly Lean equalities. |
| Multiple relations on one carrier | `≃`, control erasure, test indistinguishability, and conjunctions can coexist without instance conflicts. |
| State-dependent inverses | The law talks about the inverse returned by this run and compares inverses selected by related runs. |
| Compositionality | Lawful effects are closed under sequential composition; relation-level commutation extends through generated transformations under properness. |
| Operational observability | Definedness, outcome tags, and control constructors are not accidentally quotiented away. |
| Later iterator support | The design has an output-relator/bisimulation extension point rather than assuming function equality of continuations. |
| Auditable repairs | L35 and L38 receive named, reviewable replacements rather than an informal “read modulo equivalence” convention. |

## 4. Alternatives considered

| Candidate | Description | Decision | Reason |
|---|---|---|---|
| A. Equality-first, transport later | Formalize all of Section 3.1 at equality, then build a separate observational copy or transport layer. | Rejected | L38 is not automatic transport. D19, T20, C21, iterator laws, and returned-inverse stability would require a parallel theorem family or repeated conversion proofs. |
| B. Explicit relation-parametric laws over raw functions | Keep computations exact; parameterize only semantic laws and observational conclusions by an explicit equivalence. | **Accepted** | It preserves rewrite-friendly algebra, proves closure once, supports several relations on one carrier, and yields equality as an instance. |
| C. Quotient-first execution | Replace `Γ` by `Quotient S` and treat observational equality as Lean equality. | Rejected as the core | Descent to the quotient already requires Definition 36/37 congruence. Operational rules need concrete fields and representatives, and Section 4 uses incomparable relations. |
| D. One implicit `[Setoid Γ]` | Make the theory relation-parametric through a global typeclass instance. | Rejected | There is no unique intended relation on `Γ`. Instance inference would make theorem meaning depend on local instance state and would be fragile around `≃`, both uses of `≈`, and conjunctions. |
| E. Bundle every effect with proofs from the start | Use only `LawfulEffect S` as the effect carrier. | Rejected as the primary carrier | Proof-field equality obstructs raw algebra and extensional rewriting. A bundle is still useful at trusted boundaries, but the primary API is `Effect` plus `IsLawfulEffect S e`. |

## 5. Normative architecture

The identifiers in this section are illustrative. Their semantic signatures and separation of concerns are normative; final Lean names belong to the executable blueprint.

### 5.1 Raw exact layer

The computational carrier is independent of any observational relation.

```lean
structure EffectResult (Γ : Type u) where
  state : Γ
  undo  : Γ → Γ

abbrev Effect (Γ : Type u) := Γ → EffectResult Γ

def seqRun (first second : Effect Γ) : Effect Γ :=
  fun γ =>
    let r₁ := first γ
    let r₂ := second r₁.state
    { state := r₂.state
      undo  := r₁.undo ∘ r₂.undo }
```

This layer owns:

- function composition and extensional equality;
- the twisted pair multiplication of Definition 1;
- effect composition and unit of Definition 9;
- exact definitions of `track`, `recover`, and `effect`;
- exact projection and homomorphism equations;
- exact factorization of one operational step into its data transformation and control edit.

Raw data are allowed to be ill behaved. Correctness is expressed in the law layer rather than by changing the result type of every raw function.

### 5.2 Explicit equivalence values

```lean
structure RelSpec (α : Type u) where
  rel   : α → α → Prop
  refl  : Reflexive rel
  symm  : Symmetric rel
  trans : Transitive rel
```

Every declaration whose meaning depends on observation receives a particular `RelSpec` explicitly. A local adapter to Mathlib's `Setoid` is allowed, but the core theorem signature must reveal which relation is in use.

The architecture does not require all future logical relations to be equivalences. A later refinement proof may introduce a directed simulation relation. Such a proof must use a more general relation package rather than silently weakening `RelSpec`. The paper's recovery and observational claims in scope for ADR-01 do require equivalences.

### 5.3 Common relation liftings

The common API contains three distinct notions.

```lean
def RespectsOn (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

def Respects (S : RelSpec α) (f : α → α) : Prop :=
  RespectsOn S.rel S.rel f

def PointwiseRel (S : RelSpec α) (f g : α → α) : Prop :=
  ∀ x, S.rel (f x) (g x)

def CrossRel (S : RelSpec α) (f g : α → α) : Prop :=
  ∀ {x y}, S.rel x y → S.rel (f x) (g y)
```

Their roles must not be conflated.

- `Respects` is Definition 36's congruence/properness condition for one map.
- `PointwiseRel` is Definition 36's relation between two maps at the same input.
- `CrossRel` is a derived proof device useful when a composition contains a map from each of two related runs.

For an equivalence `S`:

\[
\operatorname{Respects}_S(f) \land f \mathrel{\dot S} g
\quad\Longrightarrow\quad
\operatorname{CrossRel}_S(f,g),
\]

where \(f \mathrel{\dot S} g\) denotes `PointwiseRel S f g`. Conversely, `CrossRel S f g` implies `PointwiseRel S f g` by reflexivity. `CrossRel S f g` alone does not establish that both maps individually preserve `S`, so the full law record keeps the relevant properness fields explicit.

### 5.4 Relation on returned effect results

Definition 36's product lifting is authoritative:

```lean
def EffectResult.Rel (S : RelSpec Γ)
    (x y : EffectResult Γ) : Prop :=
  S.rel x.state y.state ∧ PointwiseRel S x.undo y.undo
```

Thus a run from related inputs must produce:

1. related successor states; and
2. inverses that are pointwise related on every argument.

Function identity or closure identity is not required. Two different disposer closures may count as the same observable inverse when their applications are pointwise related.

### 5.5 Lawful witnessed effects

The central correctness predicate is:

```lean
structure IsLawfulEffect (S : RelSpec Γ) (e : Effect Γ) : Prop where
  run_respects  : RespectsOn S.rel (EffectResult.Rel S) e
  undo_respects : ∀ γ, Respects S (e γ).undo
  recovers      : ∀ γ, S.rel ((e γ).undo (e γ).state) γ
```

Each field has a separate purpose.

| Field | Obligation | Why it cannot be omitted |
|---|---|---|
| `run_respects` | Related inputs yield related successors and pointwise-related selected inverses. | Supplies D37's **related-input inverse coherence** and the relation vocabulary later reused by iterators. It does not discharge D19 clause (2): a foreign transformation need not carry an input to an `S`-related input. |
| `undo_respects` | Every inverse returned by an actual run preserves `S`. | Lets recovery relations pass through accumulated or composed inverses. Pointwise agreement between two selected inverses does not imply this property. |
| `recovers` | The inverse returned by `e γ` restores that run's successor to `γ` modulo `S`. | Repairs the vacuous dependent-pair encoding printed in Definition 8 and ties the witness to the actual result. |

The predicate is closed under the exact `seqRun` operation. The proof uses transitivity, the second effect's local recovery, and properness of the first returned inverse. The companion spike contains this proof.

An optional boundary bundle may be defined as:

```lean
structure LawfulEffect (S : RelSpec Γ) where
  run    : Effect Γ
  lawful : IsLawfulEffect S run
```

Use the bundle when a component or operation is admitted into a trusted registry. Use raw functions plus predicates for algebra, theorem statements, and refinement.

### 5.6 Equality specialization

Let `equality Γ` be `RelSpec` with relation `Eq`. Then:

\[
\operatorname{IsLawfulEffect}_{=}(e)
\quad\Longleftrightarrow\quad
\forall\gamma,\; (e\gamma).\mathrm{undo}((e\gamma).\mathrm{state})=\gamma.
\]

The `run_respects` and `undo_respects` fields are automatic for equality. The remaining field is precisely the repaired, non-vacuous reading of Definition 8. Therefore Section 3.1's equality version is a specialization, not a separately maintained theory.

### 5.7 Operation results, partiality, and outcomes

ADR-01 does not choose the `Option`, `Except`, or proof-precondition representation; that remains `BD-COEFFECT`. It does fix the relation contract that any choice must implement.

For related inputs, an operation must have:

- the same definedness status;
- equal success/failure constructor tags;
- related successor values or states;
- pointwise-related selected inverses;
- exact equal ordinary outcomes, as required by Definitions 24 and 39; and
- an individually relation-preserving inverse for every successful run.

If a later operation has an outcome whose representation should itself be observational, that operation must supply an explicit outcome `RelSpec`; this is not inferred from the state relation. Until such an extension is approved, paper outcomes and lifecycle/control tags use equality.

### 5.8 Generated transformation monoids and independence

The raw generated monoid of Definition 17 remains a submonoid of exact endomorphisms. There are two commutation predicates:

```lean
ExactCommute f g       := f ∘ g = g ∘ f
CommuteUpTo S f g     := PointwiseRel S (f ∘ g) (g ∘ f)
```

The exact generator-closure result in Lemma 18 remains available. Its relational companion requires that every generator involved preserve `S`. Pairwise generator commutation modulo `S` does not lift through arbitrary composites without this properness premise.

Definition 19's relational reading uses:

- `CommuteUpTo S` for transformations;
- `PointwiseRel S` for **foreign-transformation inverse stability**; and
- symmetric clauses, exactly as in the paper.

The second item is an additional independence/noninterference obligation:

\[
h\in\mathfrak M(e_2)
\quad\Longrightarrow\quad
\operatorname{PointwiseRel}_S
\bigl(\operatorname{undo}(e_1(h(\gamma))),
      \operatorname{undo}(e_1(\gamma))\bigr).
\]

It is not implied by `IsLawfulEffect.run_respects`, because lawfulness only compares runs whose inputs are already `S`-related, whereas D19 does not assume \(h(\gamma)\mathrel S\gamma\). The formal vocabulary is shared; the proof obligation is separate.

Theorems 20 and Corollary 21 then conclude relation of the reached states, not function or representative equality. Their equality statements are obtained by choosing `equality Γ`.

### 5.9 Iterator and failing-result extension point

ADR-01 does not select the iterator carrier; that remains `BD-ITER`. It does constrain that decision.

- Iterator output must have an explicit relator covering successor state, selected inverse, and continuation.
- Continuations are compared by an iterator relation or bisimulation, not by function equality.
- Each returned inverse must preserve the state relation.
- `Nothing` relates only to `Nothing`; `Just i` relates to `Just j` only through the chosen iterator relation.
- For failing iterators, success and error tags are exact unless a separate payload relation is supplied.

This is the iterator analogue of `EffectResult.Rel`; it prevents D51 from inventing a second equivalence architecture.

## 6. The paper's relations remain distinct

The reused glyphs in the paper are not one global relation.

| Project name | Paper notation/location | Carrier and observation boundary | Relationship |
|---|---|---|---|
| `KeyObs k` | `≃ₖ`, D24/D33 | Values at one key, chosen as part of the coeffect interface | Must be an explicit equivalence and operation congruence. |
| `StoreObs` | `≃`, D33 | Same domain and pointwise `KeyObs` bindings | Lifted from per-key relations. |
| `CoreStateObs` | `≃`, D33 | States whose coeffect projections are `StoreObs`-related; other state is outside this observation boundary | Constructed explicitly from the D32/D33 coeffect projection. |
| `LifecycleObs` | `≃`, D53 | `CoreStateObs` together with exact registry-domain/control observations and lifted relations on function/iterator fields | A separately named relation, constructed explicitly as the relevant conjunction; it does not silently replace `CoreStateObs`. |
| `OpTestEq A` | `≈_A`, D34-L35 | Indistinguishability by the declared operation tests | Candidate/coarsest relation for an operation interface; not automatically fully admissible because of selected-inverse coherence. |
| `EraseControl` | `≈`, D53/T61 | Exact data/effect state while designated registry control artifacts are ignored | Independent of `LifecycleObs`; neither refinement direction is assumed. |
| `NameRenaming` | L56 and later trace results | Equivariance under a finite permutation or fresh-name renaming | An action/refinement principle, not a replacement state equivalence and not a global `Setoid`. |

If a theorem needs both `LifecycleObs` and `EraseControl`, it must state both premises/conclusions or use an explicitly constructed conjunction relation. No coercion or instance priority may silently choose one. Likewise, a theorem cannot use the bare name “state observational equivalence”: it must choose `CoreStateObs` or `LifecycleObs` according to its observation boundary.

## 7. Exact equality versus observational relation

The controlling rule is:

> Equality describes computation and representation; an explicit relation describes the semantic observation claimed by a theorem.

| Kind of statement | Comparison |
|---|---|
| Definition unfolding, record projection, function composition, monoid unit/associativity, rule factorization | Lean equality |
| State recovered by an inverse, soundness invariant, arbitrary-order removal endpoint | Selected `RelSpec` |
| Equality of ordinary operation outcomes and lifecycle tags | Lean equality, unless a separate outcome relation is explicitly supplied |
| Equality of returned disposer closures | Avoided; use `PointwiseRel` at the selected state relation |
| One map's congruence | `Respects` |
| Two maps' same-input observable agreement | `PointwiseRel` |
| Fresh-name variance | Renaming/equivariance relation, not state observation by default |

This rule is normative for code review. A theorem that uses equality for a semantic endpoint or uses `≃` for a computational rewrite must justify the exception.

## 8. Adjudication of D34 and L35

### 8.1 The rejected inference

The fixed-generator tests of Definition 34 can establish that every fixed forward or inverse generator preserves test indistinguishability. They do **not** establish:

\[
v \approx_A v'
\land a(v)=(\delta,g,b)
\land a(v')=(\delta',g',b)
\quad\Longrightarrow\quad
\forall x,\; g(x)\approx_A g'(x).
\]

The premise compares two executions of the same test from related initial values. The conclusion compares two different, dynamically selected inverse functions at an arbitrary third value. Prefixing a test by one fixed generator proves preservation by that generator, not agreement between two different selected generators.

A finite countermodel pattern makes the gap concrete. Partition values into one nontrivial observable class `{a,b}` and a distinct value `{c}`. Let an operation behave identically at `a` and `b` except that it selects inverse `g` at `a` and `g'` at `b`. Let both maps preserve the partition, while `g(c)` lies in `{a,b}` and `g'(c)=c`. Fixed-generator tests cannot distinguish `a` from `b`, and each generator respects the partition, but the selected inverses are not pointwise related at `c`.

### 8.2 Accepted repair

The formalization SHALL distinguish:

```text
WeakOperationRespects
  = definedness stability
  + related successors
  + equal outcomes
  + every fixed/returned inverse individually preserves the relation

SelectedInverseCoherent
  = related inputs select pointwise-related inverses

OperationRespects
  = WeakOperationRespects + SelectedInverseCoherent
```

Lemma 35 becomes a theorem family:

1. `OpTestEq_is_equivalence` establishes the basic relation laws for the typed test semantics.
2. `OpTestEq_is_coarsest_weak` proves the universal property justified by the paper's fixed-generator proof.
3. `full_respect_of_testEq` requires an explicit `SelectedInverseCoherent` hypothesis.
4. A mechanized finite countermodel shows that `WeakOperationRespects` does not imply `SelectedInverseCoherent`.

The full `OperationRespects` law, not the weak theorem, is required when constructing `IsLawfulEffect`, a D24 operation interface, or a D37 observational effect.

A future D34 decision may strengthen the observer to a contextual test that captures and invokes the inverse selected by the current run. If that stronger observer proves selected-inverse coherence, it may discharge the explicit hypothesis. It may not weaken the core effect law, and ADR-01 does not depend on that future choice.

This is a deliberate logical repair of L35, not a stylistic decomposition.

## 9. Adjudication of L38

There will be no declaration with the literal meaning “every equality in Section 3.1 remains true after textual replacement.” Instead, L38 is a generated theorem manifest.

| Paper material | Formal treatment |
|---|---|
| D1, D2, D3, T4, T5, D6 | Raw definitions and exact algebra; no relational replacement. |
| T7 | Generic recovery/soundness theorem at `S`; the exact theorem is the `equality` specialization. The accumulator-respects invariant is explicit. |
| D8 | Raw `Effect` plus `IsLawfulEffect S`; equality specialization recovers repaired D8. |
| D9, T10 | Raw exact composition and monoid laws. |
| T11 | Closure of `IsLawfulEffect S` under raw composition; equality and observational corollaries. |
| D12, T13, T14 | Raw exact lift and projection/composition equations. |
| T15 | Exact computation equation for the lifted inverse, plus relation-level recovery/soundness consequences and a separately quantified global criterion. |
| T16 | Generic LIFO recovery modulo `S`; exact result at `equality`. |
| D17 | Raw generated transformation submonoid. |
| L18 | Exact closure theorem plus a relation-level properness-and-commutation closure theorem. |
| D19 | Relation-parametric independence using `CommuteUpTo` and pointwise inverse-selection stability. |
| T20, C21 | Relation-level selective removal and arbitrary-order recovery; equality corollaries. |

The L38 deliverable is therefore:

- a shared relation API;
- closure/properness lemmas;
- a theorem mapping each semantic equality claim to its generic relation theorem;
- an `Eq` specialization theorem family;
- a `CoreStateObs` specialization theorem family for D33-L38, together with a `LifecycleObs` specialization for the Section 4 state relation; and
- no duplicate implementation of raw composition, tracking, or lifting.

## 10. Consequences for affected disposition nodes

Harness 04 lists 36 retained items blocked by `BD-EQUIV` (35 numbered items and auxiliary block `R.fail`). ADR-01 removes only that blocker from the effective readiness calculation.

| Group | Nodes | Consequence of ADR-01 |
|---|---|---|
| Core effects | `D8`, `T11`, `T15`, `T16`, `D19`, `T20`, `C21` | Use raw effects plus explicit relation laws; exact statements are `Eq` specializations. |
| Coeffect operations and observation | `D23`, `D24`, `D29`, `D31`, `D33`, `D34`, `L35`, `D36`, `D37`, `L38`, `D39`, `T40`, `D41`, `T42` | Operation output relators include definedness/outcome rules and selected-inverse coherence; L35/L38 use the repairs above. |
| Unified state and confinement | `D32`, `D48` | Any state architecture must expose explicit observation projections and relation-preservation/frame proofs. |
| Iterators and calculus metatheory | `D51`, `D52`, `D53`, `L55`, `L57`, `D60`, `T61`, `C62`, `T64`, `L71`, `L72`, `T73`, `R.fail` | Iterator/control/result relators follow the same pattern; `LifecycleObs`, `EraseControl`, and name renaming remain separate, while `LifecycleObs` explicitly incorporates `CoreStateObs`. |

For example, `D24` remains blocked by `BD-COEFFECT`; `D32` remains blocked by `BD-STATE`; `D51` remains blocked by `BD-ITER`. An ADR resolver must subtract only its own blocker and must not rewrite the frozen graph or the baseline disposition rows.

## 11. Coding and proof rules imposed by this ADR

1. Every semantic theorem must expose the selected relation in its signature or through an explicitly named local value.
2. Core files must not depend on a globally inferred `[Setoid Γ]` to decide theorem meaning.
3. Raw definitions and their computation lemmas must not be stated on quotients.
4. Function-valued fields are compared with `PointwiseRel` or a specialized relator; closure identity is not a semantic observation.
5. Every transformation used in a relation-level composite or generated monoid must have an available `Respects` proof.
6. A returned inverse law must be indexed by the run that returned it; existential packaging that can avoid the actual result is forbidden.
7. Partial operations must preserve definedness. Ordinary outcomes and sum/control tags remain exact unless their own relation is explicitly supplied.
8. A theorem involving both `LifecycleObs` and `EraseControl` must name both; no refinement between them is presumed. D33-level theorems must instead name `CoreStateObs`.
9. Equality and observational theorem variants must be generated by specialization/corollary, not copied proof scripts.
10. Any future observer theorem that claims full operation admissibility must explicitly prove selected-inverse coherence.

## 12. Acceptance record

| ID | Check | Architecture result | Implementation state |
|---|---|---|---|
| `EQ-AC-01` | Exact raw algebra is separated from semantic relation laws. | Passed | Signatures represented in spike. |
| `EQ-AC-02` | Multiple relations can coexist on one carrier without global instance choice. | Passed | Explicit `RelSpec`; conjunction constructor represented in spike. |
| `EQ-AC-03` | `Respects`, `PointwiseRel`, and cross-input lifting are distinguished and connected. | Passed | Bridge lemmas represented in spike. |
| `EQ-AC-04` | Lawful effects include successor relation, selected-inverse coherence, inverse properness, and local recovery. | Passed | `IsLawfulEffect` represented in spike. |
| `EQ-AC-05` | Lawfulness is closed under exact sequential composition. | Passed by manual proof audit | **Pending Lean compilation.** |
| `EQ-AC-06` | Equality specialization recovers repaired Definition 8. | Passed by manual proof audit | **Pending Lean compilation.** |
| `EQ-AC-07` | L35's unsupported inference is not admitted. | Passed | Split theorem family specified; countermodel mechanization is a D34/L35 work item. |
| `EQ-AC-08` | L38 does not duplicate the effect theory or weaken structural equations. | Passed | Theorem manifest fixed; declarations remain blueprint work. |
| `EQ-AC-09` | D33 `CoreStateObs`, D53 `LifecycleObs`, both paper uses of `≈`, and renaming have distinct names and roles. | Passed | Concrete relation definitions await the relevant state/coeffect ADRs. |
| `EQ-AC-10` | Iterator and failure extensions have an explicit relator contract. | Passed | Carrier/bisimulation proof awaits `BD-ITER`. |
| `EQ-AC-11` | Quotients are optional derived views, not execution states. | Passed | No quotient appears in the spike. |

The companion Lean spike is a feasibility artifact, not production code. Lean and Lake were unavailable in the creation environment, so claiming compiler validation would be false. Before the executable blueprint imports this API, the team must run:

```text
lake env lean DeepSeek-Harness-05-ADR-01-Equivalence-Architecture-Spike.lean
```

or the equivalent command in the pinned project environment.

A merely syntactic correction does not reopen the decision. Failure of composition closure, equality specialization, or the stated result relation with exactly these law obligations does reopen ADR-01.

## 13. Non-decisions

ADR-01 intentionally does not decide:

- the concrete unified state replacing `Γ∞` (`BD-STATE`);
- the dependent finite-map implementation or partial-operation error carrier (`BD-COEFFECT`);
- the type-correct realm/interception representation (`BD-SCOPED`);
- the finite, coinductive, or other iterator carrier (`BD-ITER`);
- the concrete D34 typed test AST;
- the concrete per-key observational relations for a Cordis application;
- the action-code representation used to break the State/Registry/Fiber negative cycle;
- Lean module names, namespaces, tactic policy, work ownership, or milestones.

Those decisions must conform to the contracts fixed here.

## 14. Revision policy and triggers

This ADR is accepted, not immutable. Later formalization may reveal a genuine global decision blocker. The workflow must handle that discovery without silently rewriting history.

### 14.1 Change protocol

- Editorial clarification and typo fixes may update this artifact with a recorded patch version.
- A semantic change to the chosen relation laws, equality boundary, L35 repair, or role of quotients requires a superseding ADR that cites `ADR-01`.
- The frozen dependency graph remains unchanged. A newly discovered theorem dependency goes into a reviewed graph revision; a newly discovered architecture blocker goes into the decision register and effective readiness calculation.
- The executable blueprint consumes the **effective decision set**: the baseline disposition minus blockers resolved by accepted ADRs, plus any subsequently recorded blockers. It never treats the baseline file as if it had been retrospectively edited.
- Work already merged under this ADR is revalidated by an explicit impact list when a superseding decision is accepted.

### 14.2 Reopen triggers

Reopen or supersede ADR-01 if any of the following occurs:

1. the pinned Lean toolchain shows that sequential-law closure needs a materially stronger field than those specified here;
2. the selected iterator representation cannot express continuation congruence through an output relator or bisimulation compatible with this API;
3. a mechanized L35 countermodel falsifies the stated weak universal property, rather than only the selected-inverse inference rejected here;
4. the concrete state architecture requires a theorem to use a directed simulation where ADR-01 currently mandates an equivalence, and the theorem cannot be factored into refinement plus equivalence layers;
5. implementation experience demonstrates unavoidable duplicated equality/observational proofs across more than isolated adapter lemmas;
6. a runtime-refinement proof establishes that disposer identity itself is an observable required by the intended system boundary.

## 15. Final adjudication

`BD-EQUIV` is **resolved** by this ADR.

The project's equivalence architecture is not “use `Setoid` everywhere” and not “quotient the state.” It is:

\[
\boxed{
\text{one exact computational algebra}
\; + \;
\text{explicit relation-indexed correctness laws}
\; + \;
\text{specializations for each observation boundary}
}
\]

This is the authoritative basis for the signatures of D8, D24, D33-D39, the relational reading of D19-T21, and the equivalence-facing portions of the Section 4 calculus.
