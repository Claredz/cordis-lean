# DeepSeek Harness: Formalization Disposition Specification

Version: **1.0-baseline**  
Created: 2026-08-25  
Source: Shi, Zhang, and Cui, *A Programming Paradigm for Spatiotemporal Composability*  
Source SHA-256: `4d48478dc0b6222d9f74d7db10ee776449b1209eb112632336544d32a49db97f`  
Dependency baseline: **DeepSeek Harness 03, version 1.0-frozen**  
Dependency-graph JSON SHA-256: `8f99db87d7aa4d856657abdaf469d9941d3af7fea88ababd2e58cba49041ded8`

This specification assigns a formalization disposition to every one of the paper's 74 numbered formal items and the 8 auxiliary formal blocks retained by the frozen dependency graph. It answers five questions only:

1. In which formal layer does the item belong?
2. Is it formalized directly, repaired, subsumed, kept as exposition, or deferred?
3. How does the proposed artifact relate to the paper's formulation?
4. What kind of formal artifact should eventually exist?
5. Which global architecture decisions block implementation of that artifact?

It deliberately does **not** choose Lean declaration names, concrete modules, tactics, file ownership, work allocation, or a schedule. Those belong to later architecture and executable-blueprint specifications.

## Normative boundary

- The dependency graph in Harness 03 remains immutable: this document adds no dependency edge, removes none, and redirects none.
- A blocker is not a newly asserted theorem dependency. It is a project-level design decision that several items share.
- A repair must preserve the item's stated design intent while making its type, logic, computability assumptions, scope, or hypotheses explicit.
- “Subsumed” never means “ignored”: the paper claim must be recoverable by an instance, corollary, derived view, or simulation theorem.
- The formalization must not claim that the Section 4 metatheory already covers arbitrary isolation/interception or that it verifies the TypeScript runtime.

## Disposition vocabulary

### Target layers

| Code | Meaning |
|---|---|
| `EFFECT-CORE` | Revertible-effect algebra and local recovery (Section 3.1). |
| `COEFFECT-FLAT` | Typed flat coeffect store, specifications, and reactivity (Sections 3.2.1-3.2.2). |
| `COEFFECT-SCOPED` | Isolation, interception, and derived-context extensions (Section 3.2.3). |
| `OBSERVATIONAL` | Observational relations, tests, and independence (Section 3.3.2). |
| `CALCULUS-SHELL` | Components, fibers, registries, targets, and shared calculus infrastructure (Sections 4.1-4.2). |
| `CALCULUS-BASE` | The atomic base lifecycle, retained only as a view or simulated fragment (Section 4.2). |
| `CALCULUS-EXTENDED` | Guarded, iterative, asynchronous, and failure-aware lifecycle semantics (Section 4.3). |
| `METATHEORY` | Trace infrastructure and the global results of Section 4.4. |
| `IMPLEMENTATION-REFINEMENT` | Configuration and implementation correspondence beyond the core calculus (Section 5). |

### Treatments

| Code | Meaning |
|---|---|
| `DIRECT` | Give the item its own formal declaration or proof, preserving its intended mathematical content. |
| `REPAIR` | Give the item its own formal artifact after a type, logic, computability, scope, or hypothesis repair. |
| `SUBSUMED` | Do not duplicate the paper item as a primary artifact; recover it as an instance, corollary, derived view, or simulation theorem. |
| `EXPOSITORY` | Keep the item as a design/refinement note; it is not a proposition or datatype needed by the core metatheory. |
| `DEFER` | The item is a legitimate later formal target, but belongs to an implementation-refinement phase rather than the paper-metatheory core. |

Treatment and readiness are intentionally separate. For example, D32 has treatment `REPAIR` and paper relation `replacement`, while its readiness is `decision-blocked` by `BD-STATE`.

### Relations to the paper

| Code | Meaning |
|---|---|
| `faithful` | The formal artifact states the same mathematical content, modulo ordinary proof-assistant encoding. |
| `faithful-explicit` | The content is preserved while an implicit domain, scope, finiteness, reachability, or inherited hypothesis is made explicit. |
| `type-repair` | The intended construction is retained but an ill-scoped, partial, dependent, or recursive type formulation is replaced. |
| `logical-repair` | The intended claim is retained but a vacuous, ambiguous, overstrong, or under-specified logical formulation is corrected. |
| `computability-repair` | The semantic proposition is separated from the extra data/instances needed for executable decision procedures. |
| `decomposition` | One compound paper item becomes several declarations and linking lemmas without changing its intended content. |
| `derived` | The paper item is generated as a proved view or report from the authoritative formal object rather than maintained independently. |
| `generalization` | A relation-parametric or otherwise more general artifact yields the paper item by instantiation. |
| `specialization` | The paper item is recovered as a restricted fragment or specialization of a more general model. |
| `replacement` | The literal paper object cannot serve as the formal object; a different construction must realize its required interface and be related back to the intent. |
| `refinement-only` | The item concerns runtime realization or implementation correspondence rather than the abstract calculus itself. |

## Global decision register

These are the only cross-cutting blockers admitted by this version. Resolving one later must produce a small architecture decision record; it must not silently alter the frozen dependency graph or the disposition of unrelated nodes.

| ID | Decision | Question | Acceptance condition |
|---|---|---|---|
| `BD-STATE` | Unified state and context architecture | What Lean-compatible object replaces the literal recursive equation for Gamma-infinity and the later State/Registry/Fiber cycle while exposing the coeffect projection, effect action, local tables, and frame structure? | Choose a construction or abstract interface, state its invariants, and prove that every later operation is well typed. Do not assume a literal fixed point or store unrestricted State → State functions inside the State datatype. |
| `BD-EQUIV` | Equality and observational-relation architecture | Will the effect theory be relation-parametric from the start, or will an equality theory be transported to a separate observational layer, and what can a test observe about yielded inverses? | Fix the equivalence(s), map-respect and pointwise-map relations, congruence laws, yielded-inverse observation/stability, and the distinct roles of the paper relations ≃ and ≈. |
| `BD-COEFFECT` | Finite dependent stores, specifications, and partiality | How are finite dependent maps, semantic specifications, executable specifications, and failing/preconditioned operations represented? | Support dependent lookup/update/erase and finite key enumeration; distinguish Prop-level satisfaction from executable notification; state whether invalid operations use proof arguments, Option, or Except. |
| `BD-SCOPED` | Type-correct scoped coeffects | How are realm resolution and interception metadata typed, composed, inherited, and embedded over the flat store? | Give a total resolver with type-preservation, a precise metadata merge order, derived-context semantics, and a flat-model embedding with lookup/update preservation. |
| `BD-ITER` | Iterator and failing-iterator representation | Are iterators finite inductive trees, coalgebraic objects with a productivity/boundedness predicate, or another executable representation? | Define one-step execution, continuation reach, length/boundedness, observational relation or bisimulation, folding/tracking, and failure without assuming an unjustified recursive fixed point. |
| `BD-STAGING` | Base versus extended calculus staging | Is the base calculus a separate transition system with a simulation into the full calculus, or a derived fragment/view of one final system? | Avoid duplicated metatheory while retaining a precise correspondence for the atomic base rules and lifecycle states. |
| `BD-CONTROL` | Control, nondeterminism, asynchrony, and failure | How are orchestration choices, lifecycle nondeterminism, asynchronous landing restrictions, exceptions, and rule-labelled traces represented? | Separate external inputs from internal lifecycle steps; define admissible traces and maximal runs; make every rule premise and failure/landing outcome explicit. |
| `BD-NAMES` | Fresh fiber names and equivariance | How are fresh allocation, name supply, possible runtime atom reuse, fiber incarnations, and alpha-renaming modeled? | Use globally fresh trace identities or allocation-event/generation IDs for theorem-level fibers; relate any runtime atom reuse by refinement. Prove a well-defined renaming action sufficient for Lemma 56 and Theorem 73. |
| `BD-SUPPORT` | Support recursion and well-foundedness | Is support defined by well-founded recursion, an inductive least fixed point, or another construction that avoids the D67/L68 forward cycle? | Define support before using it, prove existence/uniqueness under explicit reachability and acyclicity hypotheses, and expose the exact assumptions inherited by Lemmas 70/72 and Theorem 73. |

## Summary

### Numbered items by treatment

| Treatment | Meaning | Count |
|---|---|---:|
| `DEFER` | The item is a legitimate later formal target, but belongs to an implementation-refinement phase rather than the paper-metatheory core. | 1 |
| `DIRECT` | Give the item its own formal declaration or proof, preserving its intended mathematical content. | 34 |
| `EXPOSITORY` | Keep the item as a design/refinement note; it is not a proposition or datatype needed by the core metatheory. | 1 |
| `REPAIR` | Give the item its own formal artifact after a type, logic, computability, scope, or hypothesis repair. | 37 |
| `SUBSUMED` | Do not duplicate the paper item as a primary artifact; recover it as an instance, corollary, derived view, or simulation theorem. | 1 |

### All 82 retained items by readiness

| Readiness | Meaning | Count |
|---|---|---:|
| `decision-blocked` | Disposition is fixed, but a listed architecture choice must be resolved before implementation. | 66 |
| `later-phase` | Scheduled for implementation refinement after the core calculus. | 1 |
| `non-core` | Retained as a design/refinement note rather than a core formal declaration. | 1 |
| `ready` | Can be stated without first resolving a listed global decision. | 14 |

The relatively high repair count is intentional. It does not mean that the paper's design is discarded. Most repairs fall into five recurring classes: non-vacuous witness packaging (D8), semantic versus executable specifications (D25-D26/SAT), observer and returned-inverse semantics (D34-L35), Lean-compatible recursive/state representations (D32/D44/D51/D67), and lifecycle theorem scope or invariant defects (T64/T66/L68/L70/L72/T73).

## High-impact audit findings

These findings explain the most consequential dispositions. They are formalization targets, not changes to the frozen dependency graph. A “counterexample outline” must be mechanized before it is treated as a final disproof.

| ID | Nodes | Status | Finding |
|---|---|---|---|
| `F-D8-WITNESS` | `D8` | formula defect | The displayed nested dependent-pair witness can be discharged vacuously by choosing an output pair different from e(gamma). The prose-intended let-bound witness is the formal target. |
| `F-D26-DECIDE` | `D25`, `SAT`, `D26` | invalid computability inference | Finite support of the current store does not decide satisfaction for an arbitrary d : Set K. Executable notification requires enumerable finite dependency data and decidable presence. |
| `F-L35-INVERSE` | `D24`, `D34`, `L35`, `D37` | logical design gap | Tests over fixed generators show that each yielded inverse preserves indistinguishability, but not that different inverses selected at indistinguishable inputs are pointwise related. The observer or respect condition must change. |
| `F-STATE-RECURSION` | `D32`, `D44`, `D49`, `D51` | representation blocker | There are two distinct recursive issues: the literal Gamma-infinity equation, and a concrete State containing fibers that contain State → State behavior. D51 is different: its iterator variable occurs positively, but finite versus coinductive semantics still must be chosen. |
| `F-NAME-REUSE` | `D47`, `D53`, `L54`, `L56`, `D60`, `T66`, `D65`, `L68`, `T73` | identity ambiguity | The rules permit reissuing an atom after O-Remove, while later trace quantities treat one name as one immutable fiber. The theorem model needs allocation/generation identities or a trace-global no-reuse premise. |
| `F-L68-CYCLE` | `D67`, `L68`, `L70`, `L72`, `T73` | counterexample outline to mechanize | The full rules appear to reach a state with acyclic precedence but cyclic combined support: a retired Reloading child can land a late registration after the former provider is removed, yielding r ≺ n, parent(n,c), and parent(c,r). Literal L68 is not accepted as a proof target. |
| `F-T66-ORIGIN` | `D53`, `T66` | scope defect | D53 starts traces from an empty registry. Requiring every step of that same trace to be a lifecycle step makes T66 vacuous; the intended theorem is about lifecycle-only suffixes from reachable states. |

## Numbered disposition registry

Each row is normative for the *kind* of artifact and its relationship to the paper. The prose in “Rationale” explains the judgment but does not add graph edges.

### Section 3.1 — Revertible effects

| Node | Paper item | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `D1` | Twisted composition of transformation pairs | `EFFECT-CORE` | `DIRECT` | `faithful` | Definition of forward/inverse transformation pairs with twisted multiplication. | — | The construction is total, well typed, and is the algebraic base used by tracking. |
| `D2` | Effect context | `EFFECT-CORE` | `DIRECT` | `faithful` | Effect-context type together with state and accumulator projections. | — | The product Gamma × End(Gamma) is directly representable. |
| `D3` | Tracking transformation | `EFFECT-CORE` | `DIRECT` | `faithful` | Tracking endomorphism and its basic simplification equations. | — | The definition is total and fixes the composition order needed by later recovery proofs. |
| `T4` | Projection of tracking | `EFFECT-CORE` | `DIRECT` | `faithful` | Projection theorem for tracking. | — | A direct extensional calculation; it is useful as a named rewrite lemma. |
| `T5` | Tracking is a monoid homomorphism | `EFFECT-CORE` | `DIRECT` | `faithful` | Monoid-homomorphism theorem for tracking. | — | The statement is precise once D1-D3 are in place. |
| `D6` | Recovery transformation | `EFFECT-CORE` | `DIRECT` | `faithful` | Recovery endomorphism and reset law. | — | The definition is total and requires no extra system structure. |
| `T7` | One-step recovery invariance | `EFFECT-CORE` | `DIRECT` | `faithful` | One-step recovery-invariance theorem. | — | This is the local soundness invariant later reused under observational equivalence. |
| `D8` | Effect functions and witnessed effect functions | `EFFECT-CORE` | `REPAIR` | `logical-repair` | Structures Effect and WitnessedEffect, with the witness stated as: for each input, the inverse returned by that very run restores the input. | `BD-EQUIV` | The displayed dependent-pair encoding can satisfy its implication vacuously by choosing a pair unequal to e(gamma). The let-bound/output-indexed predicate captures the prose intent. The equality/relational parameterization is architectural. |
| `D9` | Effect composition | `EFFECT-CORE` | `DIRECT` | `faithful` | Effect composition and unit. | — | The Writer/Kleisli-style composition is total and directly executable. |
| `T10` | Monoid of effects and embedding of uniform pairs | `EFFECT-CORE` | `DIRECT` | `faithful` | Monoid laws for effects and homomorphic embedding of uniform transformation pairs. | — | The theorem is sound for the unrefined effect carrier. |
| `T11` | Witnessing survives composition | `EFFECT-CORE` | `DIRECT` | `faithful` | Closure of repaired witnessed effects under composition, plus the uniform-left-inverse embedding theorem. | `BD-EQUIV` | The theorem preserves the paper intent once D8 is read non-vacuously; its proof should not preserve the faulty packaging. |
| `D12` | Lift of an effect to the effect context | `EFFECT-CORE` | `DIRECT` | `faithful` | Lift from an effect on Gamma to an effect on the tracked context. | — | The formula is well typed and its returned higher-level inverse is explicit. |
| `T13` | The effect lift preserves composition | `EFFECT-CORE` | `DIRECT` | `faithful` | Composition-preservation theorem for the effect lift. | — | The proof is a direct use of T5 and effect extensionality. |
| `T14` | Projection compatibility across effect levels | `EFFECT-CORE` | `DIRECT` | `faithful` | Forward- and inverse-projection compatibility lemmas. | — | The two claims are exact and useful separately as rewrite lemmas. |
| `T15` | Exact behavior of the lifted inverse | `EFFECT-CORE` | `REPAIR` | `logical-repair` | A theorem family separating (a) the exact lifted-inverse equation, (b) the pointwise recovery invariant, and (c) the global iff criterion for lifted witnessing. | `BD-EQUIV` | The printed paragraph moves between one fixed returned inverse and global membership in the witnessed-effect class. The formal version must quantify the global criterion over every input. |
| `T16` | LIFO recovery for witnessed effects | `EFFECT-CORE` | `DIRECT` | `faithful` | Inductive finite-sequence LIFO recovery theorem, including the intermediate soundness invariant. | `BD-EQUIV` | The result follows from the repaired witness and T15 without requiring independence. |
| `D17` | Transformation monoid of an effect | `EFFECT-CORE` | `DIRECT` | `faithful` | Generated transformation submonoid of an effect. | — | The forward map and all possible returned inverses form a standard generated submonoid. |
| `L18` | Generator commutation and composition closure | `EFFECT-CORE` | `DIRECT` | `decomposition` | Two lemmas: generator-wise commutation extends to generated monoids; composition introduces no generators outside the generated union. | — | The paper packages two reusable algebraic facts under one number; separate declarations improve reuse without changing content. |
| `D19` | Independence of effect functions | `EFFECT-CORE` | `DIRECT` | `faithful` | Symmetric effect-independence predicate with commutation and inverse-selection stability clauses. | `BD-EQUIV` | The definition is mathematically meaningful; only the later equality-versus-observation reading must be fixed globally. |
| `T20` | Selective removal across later independent effects | `EFFECT-CORE` | `DIRECT` | `faithful` | Selective-removal theorem for a finite interleaving of pairwise-independent effects. | `BD-EQUIV` | The statement is a core theorem and should be proved at the same relation level chosen for D19. |
| `C21` | Arbitrary-order recovery | `EFFECT-CORE` | `DIRECT` | `faithful` | Arbitrary-permutation recovery corollary. | `BD-EQUIV` | It is a genuine consequence of T20 and pairwise independence, not a separate model. |

### Sections 3.2–3.3 — Coeffects and observational structure

| Node | Paper item | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `D22` | Finite dependent partial-map coeffect context | `COEFFECT-FLAT` | `DIRECT` | `faithful-explicit` | Abstract finite dependent partial-map interface, followed by one concrete finite implementation. | `BD-COEFFECT` | Finite support is part of the paper object, but later local proofs should use only lookup/update laws unless enumeration is genuinely needed. |
| `D23` | Basic get and revertible set | `COEFFECT-FLAT` | `REPAIR` | `type-repair` | Separate raw lookup/insert/erase operations from legal get/provide/revoke transitions and prove the successful provide transition witnessed. | `BD-COEFFECT`, `BD-EQUIV` | The paper types get and set as partial while calling set an element of a total witnessed-effect class. Preconditions or failure must be represented rather than erased. |
| `D24` | Coeffect interface at a key and its context lift | `COEFFECT-FLAT` | `REPAIR` | `type-repair` | Typed coeffect-operation record with argument/outcome types, partial-domain behavior, relation-respect obligations, and a key-local lift theorem. | `BD-COEFFECT`, `BD-EQUIV` | The prose contains the needed obligations, but dependent partiality, yielded inverses, outcomes, and respect must be packaged so the lift is actually typed. |
| `D25` | Coeffect specifications | `COEFFECT-FLAT` | `REPAIR` | `computability-repair` | Semantic specifications plus an explicitly finite/enumerable executable specification type and a relation between them. | `BD-COEFFECT` | Set(K) is a valid semantic specification, but it does not by itself provide an executable enumeration or decidable emptiness/inclusion. |
| `D26` | Reactive transition classifier notify | `COEFFECT-FLAT` | `REPAIR` | `computability-repair` | Prop-level transition classification and a computable notify function for executable specifications, with an adequacy theorem between them. | `BD-COEFFECT` | Finite dom(sigma) alone does not decide satisfaction of an arbitrary predicate d. Executability requires finite/enumerable d and decidable presence. |
| `D27` | In-place and derived realizations | `COEFFECT-SCOPED` | `EXPOSITORY` | `refinement-only` | Design note and later refinement obligations distinguishing in-place mutation from persistent derived contexts; no core theorem declaration. | `BD-SCOPED` | Object identity, aliasing, and discarding a child context are realization concerns not captured by the abstract state-function type used in the paper. |
| `D28` | Isolation context | `COEFFECT-SCOPED` | `REPAIR` | `type-repair` | Type-preserving isolation context with a finite override table, total resolver, and realm-indexed provider store. | `BD-COEFFECT`, `BD-SCOPED` | The paper declares rho partial but applies it totally using a default, and V_r is not related to the V_k expected by a logical key. Both facts must be represented. |
| `D29` | Isolation-aware get, set, and isolate | `COEFFECT-SCOPED` | `REPAIR` | `type-repair` | Isolation-aware lookup/provide/revoke/isolate operations, captured-realm inverse law, and flat-store compatibility lemmas. | `BD-COEFFECT`, `BD-SCOPED`, `BD-EQUIV` | Return types cannot depend on an unresolved realm without a type-preservation witness; an inverse should delete the realm selected at application time rather than recompute an arbitrary later resolver. |
| `D30` | Interception context and specification | `COEFFECT-SCOPED` | `REPAIR` | `type-repair` | Interception context/specification with per-key metadata monoids, provider functions, and presence separated from metadata. | `BD-COEFFECT`, `BD-SCOPED` | The construction is viable, but the inheritance/default behavior and the relation between a metadata-bearing specification and its dependency domain must be explicit. |
| `D31` | Interception-aware get, set, and intercept | `COEFFECT-SCOPED` | `REPAIR` | `faithful-explicit` | Interception-aware lookup/provide/revoke/intercept operations and nested-merge laws. | `BD-COEFFECT`, `BD-SCOPED`, `BD-EQUIV` | Associativity and identity come from a monoid, but right bias does not. Merge order and any override law must be assumptions of the chosen metadata algebra. |
| `D32` | Recursive unified context | `CALCULUS-SHELL` | `REPAIR` | `replacement` | A Lean-compatible unified-state interface plus a concrete realization or representation theorem sufficient for all later projections and updates. | `BD-STATE`, `BD-EQUIV` | The literal equation mu Gamma. Gamma × (Gamma → Gamma) × Sigma is mixed-variance, violates the intended ordinary fixed-point reading, and faces a cardinality obstruction. It cannot be copied as an inductive type. |
| `D33` | Observational relation on coeffect contexts and states | `OBSERVATIONAL` | `REPAIR` | `faithful-explicit` | Equivalence on coeffect stores and a lifted full-state relation defined through an explicit coeffect projection. | `BD-STATE`, `BD-EQUIV`, `BD-COEFFECT` | The pointwise store relation is sound, but calling the lifted relation observational depends on the chosen system boundary and on proving it is an equivalence/congruence. |
| `D34` | Tests and operation-induced indistinguishability | `OBSERVATIONAL` | `REPAIR` | `decomposition` | Typed test syntax, partial evaluation semantics, outcome trace, yielded-inverse observations, and induced indistinguishability relation. | `BD-EQUIV`, `BD-COEFFECT` | The prose definition quantifies over heterogeneous operations, arguments, inverses, and outcomes. The test language must also say whether it follows the inverse returned by this run or merely ranges over fixed inverse generators. |
| `L35` | Indistinguishability is the coarsest operation-respecting relation | `OBSERVATIONAL` | `REPAIR` | `logical-repair` | A corrected universal-property theorem after either strengthening tests to observe run-selected inverses or weakening the operation-respect relation; include a countermodel lemma for the rejected combination. | `BD-EQUIV`, `BD-COEFFECT` | Prefixing by one fixed generator proves that each inverse preserves indistinguishability, but does not by itself prove that two different inverses selected at indistinguishable inputs are pointwise related. The paper proof conflates these obligations. |
| `D36` | Equivalence-respecting and pointwise-related maps | `OBSERVATIONAL` | `DIRECT` | `faithful` | Definitions of relation-respecting maps, pointwise-related maps, and the induced product relation. | `BD-EQUIV` | These are standard relation-lifting constructions and should form the common congruence API. |
| `D37` | Witnessed effects modulo observational equivalence | `OBSERVATIONAL` | `REPAIR` | `logical-repair` | Relation-parametric witnessed-effect record requiring effect respect, local recovery, and respect of every yielded inverse. | `BD-EQUIV` | This is the intended non-vacuous relational replacement for D8 and must identify the inverse actually returned by the run. |
| `L38` | Transport of Section 3.1 equalities to observational equivalence | `OBSERVATIONAL` | `SUBSUMED` | `generalization` | Instantiate a relation-parametric effect theory at observational equivalence and expose only a small transport/compatibility theorem family. | `BD-EQUIV` | A single lemma claiming that every Section 3.1 equality transports is not a useful Lean proposition. Building the core algebra over a relation makes the paper claim an instance rather than duplicated metatheory. |
| `D39` | Operation independence and commutative keys | `OBSERVATIONAL` | `REPAIR` | `type-repair` | Operation-independence predicate including common-domain/definedness stability, relation-level lifted-effect independence, outcome stability, and key commutativity. | `BD-EQUIV`, `BD-COEFFECT` | The extra outcome clause is essential, and partial operations require explicit common-domain premises rather than equations at undefined applications. |
| `T40` | Operations at distinct keys are independent | `OBSERVATIONAL` | `DIRECT` | `faithful-explicit` | Distinct-key independence theorem for the flat key-local store. | `BD-COEFFECT`, `BD-EQUIV` | The theorem is correct for flat storage locations. It must be scoped as such: under isolation, distinct logical keys may share a realm and equal keys may resolve to different realms. |
| `D41` | Coeffect-mediated effect functions | `OBSERVATIONAL` | `REPAIR` | `type-repair` | Inductively generated predicate or typed syntax for outcome-dependent coeffect-mediated computations, with denotation into effects. | `BD-COEFFECT`, `BD-EQUIV` | The least semantic set can be represented, but a typed constructor/denotation boundary avoids function-equality and heterogeneous-outcome problems. |
| `T42` | Independence of coeffect-mediated effect functions | `OBSERVATIONAL` | `DIRECT` | `faithful` | Structural induction proving independence of two mediated computations under shared-key commutativity. | `BD-COEFFECT`, `BD-EQUIV` | This is the main payoff of D39-D41 and should remain a standalone theorem. |

### Sections 4.1–4.3 — Calculus objects and extensions

| Node | Paper item | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `D43` | Components | `CALCULUS-SHELL` | `REPAIR` | `faithful-explicit` | Component record containing requirements, declared provisions, effect/iterator, and an explicit no-write-outside-provision obligation. | `BD-STATE`, `BD-COEFFECT`, `BD-ITER` | The triple is straightforward, but the crucial provision-frame condition is prose in the paper and must become data or a predicate. The effect carrier later changes to iterators. |
| `D44` | Fibers and the base lifecycle state | `CALCULUS-SHELL` | `REPAIR` | `type-repair` | Lifecycle-parameterized fiber shell whose behavior and accumulator are action codes/semantics rather than unrestricted functions stored recursively in State; base and extended payloads are instances. | `BD-STATE`, `BD-ITER`, `BD-STAGING`, `BD-NAMES` | Besides the lifecycle type changing later, a concrete State contains a registry of fibers that contain e and g : State → State. This negative State/Registry/Fiber cycle needs an action representation or abstract semantic interface. |
| `D45` | Registry, derived coeffect context, and providers | `CALCULUS-SHELL` | `REPAIR` | `decomposition` | Finite registry, parent-tree invariant, global state projections, active-table union, provider function, and uniqueness lemmas. | `BD-STATE`, `BD-COEFFECT`, `BD-NAMES` | The paper combines data, invariants, derived views, and uniqueness reasoning in one definition; Lean needs these separated and the ambient “whatever else” state made explicit. |
| `D46` | Target view and base quiescence | `CALCULUS-SHELL` | `DIRECT` | `faithful` | Target-view function and quiescence predicate, parameterized over the chosen lifecycle view. | `BD-STATE`, `BD-STAGING` | The definitions are precise once providers, retirement, and lifecycle observations are available. |
| `D47` | Nested registration primitive | `CALCULUS-SHELL` | `REPAIR` | `type-repair` | Fresh-incarnation registration transition/action returning the allocated identity and a retirement inverse, plus its frame and witness laws. | `BD-STATE`, `BD-CONTROL`, `BD-NAMES` | A rule that draws a name is nondeterministic or name-supply-parametric; theorem-level identity must also distinguish later reuse of the same runtime atom. |
| `D48` | Confinement | `CALCULUS-SHELL` | `REPAIR` | `logical-repair` | Confinement predicate factored into explicit write-frame and read-noninterference relations, extended to iterator stages and registration. | `BD-STATE`, `BD-EQUIV`, `BD-ITER` | The write clause is concrete, but “the part no table names” and agreement on provider restrictions need explicit projections/equivalences to be mechanically meaningful. |
| `D49` | Extended lifecycle, installed/failed predicates, and quiescence | `CALCULUS-EXTENDED` | `REPAIR` | `decomposition` | Final lifecycle datatype over the chosen action/iterator codes, installed/failed predicates, and extended quiescence, defined after iterator and failure outcomes. | `BD-STATE`, `BD-ITER`, `BD-STAGING`, `BD-CONTROL` | The printed definition forward-refers to iterator/failure machinery, overloads the base Theta, and would store State-indexed behavior back inside State. Reordering plus the D44 action boundary removes these cycles. |
| `D50` | Relied-upon relation | `CALCULUS-EXTENDED` | `DIRECT` | `faithful` | Relied-upon relation over installed fibers and committed provider views. | `BD-STATE` | The relation is finite and directly definable from the registry view. |
| `D51` | Witnessed effect iterators | `CALCULUS-EXTENDED` | `REPAIR` | `type-repair` | Chosen iterator carrier, one-step runner, witnessed/respectful iterator predicate, and iterator observational relation or bisimulation. | `BD-ITER`, `BD-EQUIV` | The paper mixes a least recursive type with a greatest observational relation and leaves finite versus potentially infinite behavior open. The formal carrier must match the termination hypotheses used later. |
| `D52` | Effect-iterator transformation | `CALCULUS-EXTENDED` | `REPAIR` | `type-repair` | Fold/tracking transformation for the chosen finite or well-founded iterator representation, with compatibility laws. | `BD-ITER`, `BD-EQUIV` | The printed recursive invocation is justified only after the iterator representation supplies structural or well-founded recursion. |

### Section 4.4 — Global metatheory

| Node | Paper item | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `D53` | Indexed traces, episodes, step factorization, and state relations | `METATHEORY` | `REPAIR` | `decomposition` | Separate definitions for incarnation-indexed labelled traces, reached states, fiber episodes, per-step state transformation, control edit, and the relations ≃ and ≈. | `BD-STATE`, `BD-EQUIV`, `BD-CONTROL`, `BD-NAMES` | This single paper number introduces several objects with different invariants. Splitting them supplies induction principles, separates ≃ from ≈, and prevents two lifetimes that reuse one atom from becoming one episode. |
| `L54` | Structural write facts | `METATHEORY` | `DIRECT` | `decomposition` | A named family of per-rule structural write/read/monotonicity lemmas derived from the transition constructors. | `BD-CONTROL` | The claims should be proved by cases on rules rather than imported from a prose table. |
| `L55` | Observational-equivalence invariance | `METATHEORY` | `REPAIR` | `faithful-explicit` | Same-label rule applicability and successor invariance/bisimulation under observational equivalence, with nondeterministic choices and relation-respect premises explicit. | `BD-STATE`, `BD-EQUIV`, `BD-CONTROL` | “The same rule applies” is ambiguous for registration, divert, iterator, and failure choices unless the step label carries the relevant witnesses. The intended congruence result remains central. |
| `L56` | Equivariance under fiber-name renaming | `METATHEORY` | `REPAIR` | `faithful-explicit` | Equivariance theorem for state, targets, rules, and traces under bijective renaming of allocation identities, with a refinement lemma for runtime atom names. | `BD-NAMES`, `BD-CONTROL` | The paper permits an atom to be reissued after removal, while later trace proofs treat a name as one stable fiber. Equivariance must act on incarnations or assume trace-global freshness. |
| `L57` | Vestigial entries | `METATHEORY` | `DIRECT` | `decomposition` | Vestigial-entry equivalence plus rule-preservation and deletion lemmas. | `BD-EQUIV`, `BD-CONTROL` | The paper contains several operational consequences under one lemma; named sublemmas will be reused in recovery and deletion proofs. |
| `D58` | Well-formed registry | `METATHEORY` | `REPAIR` | `faithful-explicit` | Well-formed-registry predicate with the parent-tree/acyclicity invariant either included or guaranteed by the registry type. | `BD-STATE`, `BD-NAMES` | The four displayed clauses do not themselves imply the parent pointers form the tree assumed in D45; the formal boundary must carry that invariant explicitly. |
| `T59` | Preservation of registry well-formedness | `METATHEORY` | `DIRECT` | `faithful-explicit` | Single-step preservation followed by trace preservation as a corollary. | `BD-CONTROL`, `BD-NAMES` | The printed theorem is one-step; the mechanization should immediately expose its induction over reachable traces. |
| `D60` | Iterator reach, length, transformation monoid, and independence | `METATHEORY` | `REPAIR` | `decomposition` | Iterator reachability, bounded length, generated transformation monoid, and incarnation-indexed iterator/component independence as separate definitions with closure lemmas. | `BD-ITER`, `BD-EQUIV`, `BD-CONTROL`, `BD-NAMES` | Reach and len depend on the iterator carrier, while independence stabilizes inverses and continuations. Indexing by incarnations also makes e_n unambiguous if a runtime atom is reused. |
| `T61` | Recovery exactness | `METATHEORY` | `DIRECT` | `faithful-explicit` | Episode-indexed recovery-exactness theorem modulo ≈, with an explicit optional strengthening for intervals whose nested registrations take no steps. | `BD-EQUIV`, `BD-CONTROL` | The displayed theorem is meaningful as stated. The common informal reading “as if n never began” needs the extra child-step condition recorded separately. |
| `C62` | Terminal recovery | `METATHEORY` | `DIRECT` | `faithful` | Terminal-recovery corollary for a closed/removed fiber. | `BD-EQUIV`, `BD-CONTROL` | This is a principal temporal-composability result and a genuine corollary of T61. |
| `T63` | Provider-consumer ordering | `METATHEORY` | `DIRECT` | `faithful-explicit` | Provider-before-consumer activation and consumer-before-provider-withdrawal ordering theorem in the single-realm calculus. | `BD-CONTROL` | The guarded calculus supplies the asserted temporal orderings; no realm-aware generalization is claimed at this layer. |
| `T64` | Resolution coherence | `METATHEORY` | `REPAIR` | `faithful-explicit` | Resolution-coherence theorem with the independence assumptions inherited from C62 stated explicitly. | `BD-EQUIV`, `BD-ITER`, `BD-CONTROL` | The rollback equation invokes C62, so pairwise independence is required even though the displayed theorem omits it. |
| `D65` | Precedence relation | `METATHEORY` | `DIRECT` | `faithful-explicit` | Static provider-before-consumer precedence relation over the current registry of fiber incarnations. | `BD-NAMES` | The relation depends only on declared provision and dependency sets and is finite on a finite registry; its operands must denote current incarnations, not an atom reused across lifetimes. |
| `T66` | Progress and lifecycle termination | `METATHEORY` | `REPAIR` | `logical-repair` | No-deadlock theorem, per-incarnation step bound, global lifecycle termination theorem, and maximal-run quiescence corollary for a lifecycle-only suffix from an arbitrary reachable state. | `BD-ITER`, `BD-CONTROL`, `BD-NAMES` | A D53 trace starts from an empty registry, so “every step is lifecycle” is vacuous unless the theorem ranges over a reachable suffix. Name reissue also makes fixed e_n, S(n), and V(n) ambiguous without generation identities or a no-reuse premise. |
| `D67` | Support relation and support set | `METATHEORY` | `REPAIR` | `type-repair` | Combined support relation plus a support predicate/set defined without a forward reference, according to the chosen well-founded or least-fixed-point construction. | `BD-SUPPORT`, `BD-NAMES` | Lean cannot define A by recursion whose well-foundedness is supplied only by the following lemma unless the proof is reordered or support is defined inductively. |
| `L68` | Support is well founded | `METATHEORY` | `REPAIR` | `logical-repair` | First mechanize the reached-state counterexample to the literal lemma; then prove a corrected well-foundedness/uniqueness theorem under a strengthened invariant or for a restricted support-relevant relation. | `BD-SUPPORT`, `BD-CONTROL`, `BD-NAMES` | The full rules appear to permit an in-flight retired child to land a late registration after the former provider is removed, producing r ≺ n, parent(n,c), parent(c,r): a cycle in ⊲ while ≺ remains acyclic. Reachability and D58 well-formedness alone do not exclude it. |
| `D69` | Totality on declared provision | `METATHEORY` | `DIRECT` | `faithful-explicit` | Component total-on-provision predicate quantified over successful completed activations. | `BD-ITER`, `BD-COEFFECT` | The semantic obligation is clear, but its quantification must range over the formal activation semantics rather than an informal phrase. |
| `L70` | Support at quiescence | `METATHEORY` | `REPAIR` | `faithful-explicit` | Support-equals-active theorem at reachable, well-formed, quiescent, nonfailed states under total provision and the corrected support existence/uniqueness premise. | `BD-SUPPORT`, `BD-CONTROL` | The literal L68 route is not available. The formal statement must import the repaired support theorem or assume the exact well-foundedness/uniqueness property it needs. |
| `L71` | Transposition of adjacent independent steps | `METATHEORY` | `DIRECT` | `faithful` | Adjacent-step transposition lemmas for independent activation steps and compatible orchestration steps. | `BD-EQUIV`, `BD-CONTROL`, `BD-NAMES` | These are the local diamond moves used to normalize schedules. |
| `L72` | Deletion of a closed episode | `METATHEORY` | `REPAIR` | `faithful-explicit` | Closed-episode deletion theorem with reachability/well-formedness and the repaired support/L70 envelope stated explicitly. | `BD-SUPPORT`, `BD-EQUIV`, `BD-CONTROL`, `BD-NAMES` | The printed proof calls L70 although the displayed premises do not state its support-existence and well-foundedness envelope. |
| `T73` | Canonical form and confluence | `METATHEORY` | `REPAIR` | `decomposition` | Canonical-form theorem and confluence for traces with the same ordered orchestration inputs under a corrected support-order hypothesis, plus a separate unique-normal-form corollary adding T66 termination hypotheses. | `BD-SUPPORT`, `BD-EQUIV`, `BD-ITER`, `BD-CONTROL`, `BD-NAMES` | The proof requires maximal/minimal elements and a linearization of ⊲, which literal L68 does not currently justify. Its formal input is the same ordered orchestration sequence, not merely an extensional final configuration. |

### Section 5 — Implementation-level item

| Node | Paper item | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `D74` | Declarative configuration entry | `IMPLEMENTATION-REFINEMENT` | `DEFER` | `refinement-only` | Later typed configuration-entry record, support interpretation, configuration-to-orchestration semantics, and loader refinement specification. | `BD-SCOPED`, `BD-NAMES` | The record is not used by Section 4. Its “final configuration” interpretation is stronger than T73’s same-ordered-input theorem and therefore needs a loader/refinement proof rather than prose correspondence. |

## Auxiliary disposition registry

| Node | Paper block | Target | Treatment | Paper relation | Intended artifact | Blocking decisions | Rationale |
|---|---|---|---|---|---|---|---|
| `SAT` | Satisfaction predicate (Equation 24) | `COEFFECT-FLAT` | `REPAIR` | `computability-repair` | Semantic satisfaction predicate plus a decidable executable checker and an adequacy theorem. | `BD-COEFFECT` | Satisfaction itself needs no finiteness. Its computation needs a finite/enumerable dependency specification and decidable key presence. |
| `R.base` | Base operational rules | `CALCULUS-BASE` | `SUBSUMED` | `specialization` | A derived base-system view and simulation/adequacy theorem against the extended calculus; no duplicate global metatheory. | `BD-STAGING`, `BD-CONTROL` | The atomic calculus is pedagogically useful, but maintaining two unrelated rule developments would duplicate the main proof burden. |
| `R.withdraw` | Withdrawal rules | `CALCULUS-EXTENDED` | `SUBSUMED` | `decomposition` | L-Leave/L-Unload constructors as a named rule subfamily of R.full, with guard and frame lemmas. | `BD-CONTROL` | These rules are central, but they should not form a second transition relation independent of the authoritative full calculus. |
| `R.iter` | Iteration lifecycle rules | `CALCULUS-EXTENDED` | `SUBSUMED` | `decomposition` | L-Begin/L-Iter/L-Finish and separate abort/landing L-Divert constructors as a named subfamily of R.full. | `BD-ITER`, `BD-CONTROL` | Splitting the disjunctive divert premise improves induction while a subfamily view avoids a duplicate calculus. |
| `A.async` | Asynchronous inertia restriction | `CALCULUS-EXTENDED` | `REPAIR` | `replacement` | Explicit in-flight state or an admissible-host-trace/inertia policy relating launch and landing, with compatibility theorems for progress. | `BD-ITER`, `BD-CONTROL` | Asynchrony is a restriction on executions/hosts, not another state transformer. The paper state does not record whether an iteration was launched, so the restriction needs a new semantic carrier. |
| `R.fail` | Failing iterator refinement and L-Raise | `CALCULUS-EXTENDED` | `REPAIR` | `decomposition` | Failure-aware iterator outcome, success-only witness clause, error/success stability relation, L-Raise constructor, and erasure into nonfailing semantics. | `BD-ITER`, `BD-EQUIV`, `BD-CONTROL` | The exception refinement changes iterator results, witnessing, independence, and lifecycle landing; projections valid only on success must not be treated as total. |
| `R.full` | Full ten-rule calculus | `CALCULUS-EXTENDED` | `REPAIR` | `decomposition` | Single authoritative labelled semantics with separate orchestration/lifecycle relations and rule constructors (possibly splitting one printed rule into several typed constructors). | `BD-STATE`, `BD-ITER`, `BD-STAGING`, `BD-CONTROL`, `BD-NAMES` | Section 4.4 reasons about this rule set, but a faithful proof-assistant encoding must expose nondeterministic witnesses, in-flight/failure outcomes, and the two step classes rather than preserve “ten” as a datatype constraint. |
| `Table1` | Rule decomposition into state maps and control edits | `METATHEORY` | `SUBSUMED` | `derived` | Machine-derived per-constructor state-map/control-edit decomposition and write-set lemmas; no axiomatized copy of the prose table. | `BD-CONTROL` | Treating the table as an independent truth risks drift from the actual transition relation. Its facts should be proved by rule cases and consumed through L54. |

## Consequences fixed by this specification

The following choices are now part of the blueprint baseline even before the architecture decisions are resolved:

1. **The formalization is layered, not a transcription.** Every numbered paper item remains traceable, but a paper number need not correspond one-to-one with a Lean declaration.
2. **The equality and observational versions must not become two copied theories.** L38 is recovered from a relation-parametric core or an equally explicit transport layer.
3. **Semantic and executable coeffect specifications are distinct.** Arbitrary `Set K` is acceptable for propositions; executable notification needs finite/enumerable dependency data.
4. **The literal Gamma-infinity equation is rejected as the formal state type.** D32 requires a replacement related to the interface actually used later.
5. **Scoped coeffects are an extension, not silently part of the Section 4 proof.** D28-D31 require their own typed model and a flat embedding before any realm-aware generalization of T40 or the lifecycle calculus is claimed.
6. **The full lifecycle relation is authoritative.** The base calculus is retained through a derived view/simulation rather than a second copy of all metatheory.
7. **Tables and prose invariants are not axioms.** Table 1 and similar facts are derived by cases from rule constructors.
8. **Theorem hypotheses are explicit at the declaration boundary.** In particular, the independence inherited by T64 and the reachability/validity assumptions used by support and deletion results may not remain hidden in prose.
9. **Literal L68 is not assumed.** The project first mechanizes the late-registration cycle outline, then either strengthens the calculus/invariant or proves the needed theorem for a restricted support construction.
10. **A fiber identity denotes one allocation lifetime.** Runtime atom reuse is modeled only through a later refinement; trace-level theorems use generation-safe identities or an explicit no-reuse assumption.
11. **Unique normal forms are not conflated with confluence-at-given-quiescent-endpoints.** The T73 artifact is split, and the final unique-normal-form corollary imports T66's repaired termination hypotheses.
12. **Implementation correspondence is a later refinement claim.** D27 and D74 do not strengthen Section 4's abstract theorems into unproved claims about Cordis code.

## Exit criteria for this specification layer

This layer is complete when:

- all 74 numbered IDs and all 8 auxiliary IDs have exactly one disposition;
- every treatment, target, paper relation, and blocker is drawn from the declared vocabularies;
- every `REPAIR` row says what is preserved and what must change;
- every `SUBSUMED` row names the instance/corollary/view/simulation that recovers it;
- no concrete Lean identifier, tactic plan, owner, or timetable is required to interpret a row;
- the companion JSON validates the inventory against Harness 03 without copying or changing its 540 dependency edges.

## What comes next (not part of this file)

The next specification should be an **architecture decision packet**, resolving the blockers in dependency order rather than beginning with module names. A sensible first packet is `BD-EQUIV` + `BD-STATE` + `BD-COEFFECT`, because those decisions determine the signatures of D8, D22-D24, D32-D37, and the shared state interface consumed by Section 4. Only after those signatures stabilize should the project generate Lean declarations, module dependencies, milestones, ownership, and executable work tickets.

## Machine-readable companion

The JSON companion contains the same 82 rows, the full controlled vocabularies, the global decision register, derived readiness values, summary counts, and integrity checks. It intentionally references the frozen graph by version and hash rather than duplicating its edge list.
