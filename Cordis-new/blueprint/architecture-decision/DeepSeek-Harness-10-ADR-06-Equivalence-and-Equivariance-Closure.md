# DeepSeek Harness ADR-06-CLOSURE: Equivalence and Equivariance Contract Hardening

| Field | Value |
|---|---|
| Packet ID | `ADR-06-CLOSURE` |
| Parent decision | `ADR-01: Equivalence Architecture` |
| Status | **Accepted — compiler validated** |
| Packet version | `1.0-accepted-compiler-validated` |
| Date | `2026-08-27` |
| Global blocker status | `BD-EQUIV` was resolved architecturally by ADR-01; this packet closes the residual cross-module contracts and evidence |
| Semantic change | **None** |
| Supersedes | Nothing |
| Source | Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability* |
| Source SHA-256 | `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f` |
| Frozen dependency graph SHA-256 | `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8` |
| Frozen disposition SHA-256 | `63d1fb68bcebb63e5282c7314d03038a93db0a836a6c8b1a08a41c2cd70a43db` |
| Companion artifacts | `DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure.json`; `DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure-Spike.lean` |

## 1. Adjudication

`BD-EQUIV` is closed at the architecture and integration-contract level. ADR-01 remains
the authoritative semantic decision: computations stay on a raw exact carrier, while
recovery and observational claims are parameterized by an explicitly supplied relation.
ADR-06 does not introduce a second equivalence theory and does not replace ADR-01.

The packet closes the work that was still ambiguous at the boundaries between ADR-01 and
ADR-02--ADR-05:

- one canonical vocabulary for congruence, same-input map agreement, and cross-input map
  transport;
- relation relators for effects, partial outcomes, failures, stores, and iterators;
- explicit inverse-selection, operation-outcome, and continuation-stability contracts;
- a non-vacuous split of the L35 operation law, including a compiled finite countermodel;
- a ranked execution bridge for D51/D52 and a failure-preserving recovery witness;
- name-neutral alpha transport for state, inverse, stage, iterator, execution, and trace;
- a theorem-manifest boundary for L38 rather than textual substitution of `=` by a glyph.

This is a companion/closure packet. It changes no edge, row, or blocker in the frozen
Harness-03 dependency graph or Harness-04 disposition baseline. “Closed” below means that
the shared interfaces and their admissibility conditions are fixed; it does not mean that
the concrete D34 test syntax, lifecycle traces, support theorem, or runtime refinement has
already been proved.

## 2. Why a closure packet was needed

ADR-01 fixed the high-level choice, but later artifacts exposed three integration hazards:

1. ADR-05 used the name `PointwiseRel` for a related-input lifting. ADR-01 had already
   reserved that name for same-input agreement. The collision could silently change the
   type of iterator and inverse proofs.
2. D19, D39, and D60 quantify over generated transformation monoids and require more than
   ordinary congruence: foreign maps must preserve selected inverses, outcomes, and (for
   iterators) continuations.
3. L35 and L38 are not obtained by an informal “read modulo equivalence” sentence. The
   selected inverse is part of a returned result, and the equality theory must be reused by
   specialization rather than copied.

ADR-06 fixes these as named, reviewable contracts. It deliberately leaves the concrete
   monoid construction, typed coeffect test AST, reachable lifecycle traces, and external
   name-bearing payload refinement to the blockers that own those semantics.

## 3. Normative relation vocabulary

The core uses an explicit `RelSpec` value. A theorem that depends on observation must
receive its relation (or a named profile containing it); no global inferred `Setoid` chooses
the meaning of a state theorem.

```lean
RespectsOn R S f := ∀ {x y}, R x y → S (f x) (f y)
Respects   S f   := RespectsOn S.rel S.rel f
PointwiseRel S f g := ∀ z, S.rel (f z) (g z)
CrossRel     S f g := ∀ {x y}, S.rel x y → S.rel (f x) (g y)
```

`PointwiseRel` is the canonical same-input relation. `CrossRel` is a separate, derived
cross-input transport. The spike proves the following bridges:

- `Respects f` plus `PointwiseRel f g` implies `CrossRel f g`;
- `CrossRel f g` implies same-input `PointwiseRel f g` by reflexivity;
- for an actual equivalence (`RelSpec`), `CrossRel f g` also implies `Respects f` and
  `Respects g` by symmetry and transitivity.

The last fact is specific to equivalence relations. A future directed simulation relation
must use a different relation package and may not import that endpoint-properness shortcut.
The old ADR-05 name is therefore an editorial/API correction, not a semantic change to its
accepted iterator carrier. ADR-05 remains an immutable historical artifact; new code uses
the ADR-06 canonical names and migrates its old cross-input `PointwiseRel` occurrences to
`CrossRel`.

## 4. Relator and observation contracts

### 4.1 Tagged and dependent relators

`OptionRel` relates `none` only to `none`, and relates `some x` to `some y` through the
supplied relation. `optionRelSpec` proves that this is an equivalence when the payload
relation is an equivalence. `EffectResultRel` and `ExecRel` lift a state relation to the
returned state, selected inverse, and (on failure) error tag; `effectResultRelSpec` and
`execRelSpec` prove the corresponding equivalence shells.

The spike also contains `DepStore`, `DepStoreObs`, and `depStoreObsSpec`. These are a
readable pointwise dependent-store adapter. The authoritative finite dependent map,
lookup/update protocols, and executable specification remain ADR-02's `Finmap` layer;
the adapter must not be mistaken for a replacement implementation.

### 4.2 Named observation boundaries

`PullbackRel` and `CoreStateObs` make a D33-style observation an explicit pullback along a
coeffect projection. `ObservationFamily` gives distinct slots for core, lifecycle,
control-erased, and operation-test observations. The names have different obligations:

| Profile | Meaning | ADR-06 status |
|---|---|---|
| `CoreStateObs` | coeffect/state projection observation | generic pullback and dependent-store shell compiled; concrete ADR-03 state instance remains downstream |
| `LifecycleObs` | Section-4 state observation including lifecycle/control fields | named boundary only; CONTROL/STAGING instantiate it |
| `EraseControl` | exact data/effect state with selected control artifacts erased | separate named relation; no refinement to `LifecycleObs` assumed |
| `OpTestEq` | indistinguishability generated by declared operation tests | typed D34 test AST and coarsestness proof remain BD-COEFFECT work |
| `NameRenaming` | permutation action/refinement | not a state observation and not a global `Setoid` |

No theorem may silently use one of these profiles in place of another.

## 5. Effects, independence, and operations

### 5.1 Lawful effects and equality specialization

`IsLawfulEffect R e` has three independent fields:

1. `run_respects`: related inputs produce related successor states and same-input-related
   selected inverses;
2. `undo_respects`: every inverse returned by an actual run preserves `R`;
3. `recovers`: that very returned inverse recovers the state at which it was returned,
   modulo `R`.

`seqRun_lawful` proves closure under the exact sequential composition, including the LIFO
   inverse orientation. `equality Γ` and `lawful_equality_iff` recover the repaired exact
   witness condition as a specialization. This is a generic effect result; the tracked
   context/accumulator lift and its full T15/T16 theorem family remain the implementation
   bridge owned by the effect/state modules.

### 5.2 D19 and generated monoids

`CommuteUpTo` and `SelectedInverseStable` encode the relational reading of D19. To prevent
the independence premise from becoming vacuous, the spike adds:

- `TransformationMonoidProfile`, with identity and composition closure;
- `GeneratedEffectProfile`, which additionally records membership of the forward map and
  every actually returned inverse;
- `GeneratedIndependenceContract`, which carries commutation, properness, and symmetric
  inverse-selection stability for those profiles.

The older predicate-level `IndependenceContract` remains as a local adapter. A trusted
instance must use the generated-profile form (or provide equivalent inclusion/closure
proofs). The profile is a conservative submonoid interface; leastness/equality with the
paper's generated monoid is a D17/L18 implementation theorem, not an axiom hidden here.

### 5.3 Partial operations, L35, and D39

`OpResult` and `PartialOp` preserve the ADR-02 partiality boundary. `WeakOperationRespects`
requires common definedness/tag shape, related successor states, exact ordinary outcomes,
and individual inverse properness. `SelectedInverseCoherent` separately requires that
the inverses selected at related inputs are pointwise related. `OperationRecovers` states
the local recovery law, and `OperationRespects` is their conjunction.

The packet makes the D39 noninterference clauses explicit rather than hiding them inside
state congruence:

```lean
DefinednessStable op h
OutcomeStable op h
SelectedInverseStableOp R op h
OperationForeignStability R op M
OperationIndependenceContract R op₁ op₂ M₁ M₂
```

`OutcomeStable` is equality-specialized, matching the paper's exact outcome clause. An
operation with observational outcomes must supply an explicit outcome relation. The
operation-independence contract also carries commutation and properness of the two supplied
transformation profiles; it is paired with the separately typed lift law for successor
states.

The finite `Toy` countermodel has an observation partition `{a,b}`/`{c}`. Both selected
inverse maps preserve the partition and recover locally, but the maps selected at related
inputs are not pointwise related. It compiles and proves the exact logical point needed by
the L35 repair. It is a schematic countermodel, not the final typed D34 operation-test AST.

## 6. Iterator and failure bridge

The iterator core is the ranked continuation machine accepted by ADR-05:

- `StageResult` has `halt`, `yield`, and `raise` constructors;
- a `yield` carries a strictly lower `Nat` rank;
- `execFrom` is well-founded and composes inverses as `outer ∘ inner`;
- `ExecResult.failure` retains the error, the final prefix state, and the accumulated
  prefix inverse rather than erasing failure to `none` or identity.

`StageRelC` relates state, selected inverse, continuation, and error tags. The packet keeps
the distinction between:

- `IteratorSimulation`, a directional one-step relation sufficient for `execFrom_rel`;
- `IteratorBisim`, two simulations, with the second using the converse continuation
  relation `fun q q' => C q' q`.

The spike compiles `StageInverseProper`, `IteratorInverseProper`, `StageWitness`,
`IteratorWitness`, `StepLawful`, and `IteratorLawful`. It proves `execFrom_witness`, so a
successful or failing complete run recovers its boundary modulo `R` while a `raise` stage
itself carries no invented effect witness. `execFrom_rel` uses the sum of the two ranks;
it does not impose an unjustified equality-of-ranks premise.

For the D60 continuation clause, `ContinuationStable` and
`IteratorIndependenceContract` package commutation, properness, inverse properness, and
full state/inverse/continuation stability. The contract is intentionally conservative:
it is all-node `StageRelC` stability. The exact reach-closed generated monoid and the
reachable-yield-only specialization remain D60/CONTROL integration work. A supplied
continuation relation must be given its own laws before it is treated as an equivalence.

## 7. Alpha-equivariance

`AlphaAction` carries identity, composition, and inverse/cancellation laws. The spike
proves transport for:

- inverse conjugation (`renameUndo`) and its properness;
- stage relations, iterator simulations/bisimulations, inverse properness, witnesses, and
  the `IteratorLawful` bundle;
- recursive `execFrom` and root-level `exec` in a name-neutral continuation/error profile;
- event and trace identity/composition.

The execution theorem is now an actual compiled theorem (`execFrom_rename_transport`,
`exec_rename_transport`, and `execTransportContract_proof`), not only a proposition shell.
The proof leaves `Q` and `Ξ` unchanged. If continuation codes, errors, ambient values,
accumulators, or control labels carry names, their actions and interpreter equivariance
must be supplied explicitly. Full L56/T73 trace/rule equivariance, runtime atom reuse, and
the ADR-04 ledger refinement remain BD-NAMES/CONTROL/SUPPORT work.

## 8. L38 and paper correspondence

L38 is represented as a generated theorem manifest. The relation-parametric core supplies
the generic theorem; the paper's exact Section-3.1 claims are obtained with `equality Γ`.
There is no textual global rewrite from `=` to an observational glyph.

| Paper area | ADR-06 contract/result | Closure classification |
|---|---|---|
| D8, T11, T15, T16 | lawful effect, exact specialization, sequential/LIFO interface | relation architecture closed; tracked accumulator proofs remain implementation work |
| D19, T20, C21 | commute-up-to, generated profiles, selected-inverse stability | contract closed; concrete generated-submonoid theorem remains |
| D23, D24, D41, T42 | tagged/partial relators and operation foreign-stability boundary | adapter closed; finite dependent/key-lift proofs remain ADR-02 work |
| D32, D33, D36, D37 | explicit pullback/observation and result relators | boundary closed; concrete `ValidState`/WF/provider instance remains ADR-03 work |
| D34, L35 | weak/full split and finite countermodel | logical repair closed; typed test AST/coarsest universal property remains |
| L38 | manifest and specialization rule | architecture closed; full generated theorem inventory remains |
| D48, D51, D52 | state relation hook, ranked iterator, witness and execution transport | interface closed; confinement/lifecycle integration remains |
| D39, T40 | operation commutation plus exact outcome/definedness stability | contract closed; distinct-key theorem remains ADR-02/coeffect work |
| D60 and later Section 4 rows | continuation-stability contract and result relator | interface closed; reach/control/support theorems remain separately blocked |

## 9. Readiness effect

The readiness calculation is subtract-only. For every Harness-04 row, the effective blocker
set is its frozen set minus the already accepted decisions (`BD-STATE`, `BD-COEFFECT`,
`BD-NAMES`, `BD-ITER`) and minus `BD-EQUIV` closed here. No H03 edge is added, removed, or
redirected.

Harness-04 contains 36 rows mentioning `BD-EQUIV` (35 numbered rows plus `R.fail`). The
ten rows whose original baseline-local blocker was only `BD-EQUIV` are:

`D8`, `T11`, `T15`, `T16`, `D19`, `T20`, `C21`, `D36`, `D37`, `L38`.

After accounting for the already accepted ADR-02/03/04/05 decisions, 23 EQUIV-affected
rows are free of their remaining local blocker:

`D8`, `T11`, `T15`, `T16`, `D19`, `T20`, `C21`, `D23`, `D24`, `D32`, `D33`, `D34`, `L35`,
`D36`, `D37`, `L38`, `D39`, `T40`, `D41`, `T42`, `D48`, `D51`, `D52`.

The remaining 13 EQUIV-tagged rows retain independent blockers:

| Remaining blocker | Rows |
|---|---|
| `BD-SCOPED` | `D29`, `D31` |
| `BD-CONTROL` | `D53`, `L55`, `L57`, `D60`, `T61`, `C62`, `T64`, `L71`, `R.fail` |
| `BD-CONTROL` + `BD-SUPPORT` | `L72`, `T73` |

Under the project’s local (non-transitive) readiness rule, the global ready count moves
from 24 to 47. A strict transitive dependency traversal gives a smaller diagnostic number
(41 in the current audit); that number is not written back to the frozen baseline because
it includes unresolved ancestor SCCs and staging/control edges.

## 10. Acceptance checks

| ID | Check | Status |
|---|---|---|
| `EQ-CLOSE-01` | Same-input `PointwiseRel` and distinct `CrossRel`, with equivalence bridges | passed in spike |
| `EQ-CLOSE-02` | Option/effect/execution relators and dependent-store equivalence shell | passed in spike |
| `EQ-CLOSE-03` | Lawful effect, sequential closure, and equality specialization | passed in spike |
| `EQ-CLOSE-04` | Non-vacuous generated-monoid profile and D19 contract | API represented; least-generated proof pending |
| `EQ-CLOSE-05` | Partial operation definedness/tags/outcomes and L35 split | API plus finite countermodel compiled; typed D34 AST pending |
| `EQ-CLOSE-06` | D39 outcome/definedness/selected-inverse foreign stability | contract represented; concrete key-lift theorem pending |
| `EQ-CLOSE-07` | Ranked iterator, failure prefix, witness, simulation, and bisimulation bridge | passed for the standalone carrier; lifecycle integration pending |
| `EQ-CLOSE-08` | D60 continuation stability and symmetric converse relation | conservative contract represented; reach specialization pending |
| `EQ-CLOSE-09` | Core-state pullback and named observation profiles | generic/dependent shells passed; concrete state instances pending |
| `EQ-CLOSE-10` | Alpha state/undo/stage/iterator/witness/trace transport | passed for name-neutral `Q`/`Ξ`; named payload actions pending |
| `EQ-CLOSE-11` | L38 manifest boundary and equality specialization rule | recorded; full theorem inventory pending |
| `EQ-CLOSE-12` | Standalone spike hygiene | exit 0, warnings only; no `sorry`, `admit`, custom `axiom`, or `unsafe` |

## 11. Validation record

The companion Lean file is a standalone compiler mirror in namespace `CordisADR06`; it is
not production code and must not be imported beside another module that redeclares the
same names.

```text
lake env lean artifacts/DeepSeek-Harness-10-ADR-06-Equivalence-and-Equivariance-Closure-Spike.lean
```

Validation was run with the pinned Lean 4.33.0 / Lake 5.0.0 environment. The exit code was
`0`; the output contained only linter warnings (unused variables/simp arguments and
constructor-name style). A placeholder scan found no `sorry`, `admit`, custom `axiom`, or
`unsafe`. This is a standalone spike validation, not a claim that the whole downstream
project build or all paper theorems are complete.

## 12. Remaining obligations and ownership

The closure leaves the following work intentionally visible:

- `BD-COEFFECT`: concrete finite dependent maps, typed D34 tests, key-local lifts, and the
  proofs of D24/T40/D41/T42;
- `BD-STATE`: concrete `ValidState` pullbacks, provider adequacy, WF preservation, and
  transition-level frame proofs;
- `BD-ITER`: integration of the accepted ranked carrier with the lifecycle rules and
  reachable iterator monoids;
- `BD-CONTROL`: labelled traces, orchestration/lifecycle separation, failure landing,
  D53/L55/L57/D60/T61/C62/T64/L71, and name-bearing rule equivariance;
- `BD-STAGING`: base/full staging, commit timing, and guarded unloading;
- `BD-SUPPORT`: support well-foundedness and L72/T73 confluence envelope;
- `BD-SCOPED`: realm/interception embedding (`D29`, `D31`).

In particular, the packet does not assert that `OperationIndependenceContract` or
`IteratorIndependenceContract` is automatically inhabited. Their purpose is to make the
missing hypotheses impossible to hide in prose.

## 13. Revision policy

- Editorial wording or additional cross-reference: patch version.
- A repair to the standalone spike that preserves these carriers and contracts: revised
  closure packet and spike, with new hashes.
- A change to the raw carrier, observation boundary, iterator failure model, or name
  identity policy: superseding ADR, not an in-place ADR-06 edit.
- Harness-03 and Harness-04 remain immutable; readiness is always recomputed by blocker
  subtraction and never by rewriting their rows.
