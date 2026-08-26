# CordisLean Repository Instructions

These instructions govern the repository after the 2026-08-26 transition to the paper-first formalization.

## Authority order

For new work, authority is:

```text
paper baseline / frozen dependency graph
→ Formalization Disposition Specification
→ accepted ADRs and closure packets
→ production Lean modules
```

`Cordis-new/` currently contains the formal-reference, blueprint and architecture-decision artifacts. Until production modules are extracted from the spikes, accepted ADR documents are semantic authority for the new formalization.

The old `Core → Effects → Integrated → Extended → Examples` model is legacy. Its files remain buildable reference material, but `PLAN.md`, `PAPER_MAP.md`, `LAYERS.md`, `ASSUMPTIONS.md`, `DESIGN_NOTES.md` and `CONFLUENCE_STATUS.md` describe that legacy model unless and until rewritten. They must not override the new paper-first architecture.

See `ARCHIVE.md` for the migration boundary.

## Mathematical integrity

- Never weaken a theorem merely to close a proof.
- Never silently repair a paper definition or theorem. Record the literal paper item and the repaired target separately.
- If a paper claim appears false, vacuous, ill-typed, non-computable or under-specified, mechanize the defect or counterexample where practical before replacing the claim.
- Do not hide missing hypotheses inside an oversized `WellFormed` predicate.
- Distinguish semantic propositions from executable data and algorithms.
- Distinguish paper assumptions from properties enforced by the Cordis TypeScript runtime.
- Do not claim that Section 4 metatheory covers arbitrary realms/interception or verifies the production runtime unless a separate refinement theorem establishes that fact.

## Proof integrity

Lean source delivered as production formalization must not contain `sorry`, `admit`, or project-defined unchecked `axiom` declarations.

Do not manufacture proofs using:

- impossible well-formedness assumptions;
- empty/degenerate transition relations;
- vacuous implications introduced only to avoid the actual theorem;
- quotienting or observational relations that erase exactly the behavior under audit;
- hidden classical choices where an executable claim is being asserted.

If a statement is not currently provable, preserve a precise blocked theorem statement, counterexample, or named proof obligation instead.

## New architecture discipline

The target production structure is conceptually:

```text
Cordis/Paper
Cordis/Audit
Cordis/Runtime
Cordis/Refinement
```

- `Paper` owns faithful or explicitly repaired formalizations of paper mathematics.
- `Audit` owns no-go results, counterexamples, computability/scope/type audits and correspondence records.
- `Runtime` owns an abstract operational model of official Cordis engineering; it must not be confused with the paper calculus.
- `Refinement` owns simulation/refinement theorems relating runtime behavior to paper-facing semantics.

Architecture spikes under `Cordis-new/blueprint/architecture-decision/` are prototypes, not final public APIs. Production modules should extract only accepted interfaces and laws.

## Accepted architectural commitments

Current accepted decisions include:

- ADR-01: raw exact algebra with explicit relation-parametric semantic law layers; no unique global `[Setoid Γ]` and no quotient-first execution model.
- ADR-02: `Finmap` dependent coeffect store, semantic `Set K` versus executable `Finset K`, explicit partial semantics and checked executable views.
- ADR-03: positive finite registry/state shell; no literal `μΓ. Γ × (Γ → Γ) × Σ` state datatype and no stored unrestricted `State → State` closures inside recursive state.
- ADR-04: theorem-level `IncarnationId` denotes one allocation lifetime; runtime atoms/entry IDs are separate and alpha-renaming is explicit.

Do not reopen these decisions implicitly in downstream code. A change that contradicts an accepted ADR requires a superseding ADR or explicit review.

## Legacy discipline

The existing modules

```text
Cordis.Core
Cordis.Effects
Cordis.Integrated
Cordis.Extended
Cordis.Examples
```

are a frozen simplified model. Preserve their proved semantics and buildability unless doing an explicit archive-maintenance change. Do not extend them as if they were the new paper formalization.

The immutable historical snapshot is available on branch `archive/legacy-formalization-2026-08-24` at commit `afa8a0e29513c8be34878e054fa18f36def5fa6f`.

## API-first proof engineering

Before implementing generic machinery, search project declarations and mathlib. Prefer existing APIs for finite dependent maps, finite sets, relation closures, well-founded recursion, permutations/equivalences, cardinal arguments and decidability.

For nontrivial proofs:

1. inspect the exact goal and hypotheses;
2. isolate the mathematical lemma from architecture plumbing;
3. test the smallest candidate proof;
4. build the current module immediately;
5. promote reusable facts into named lemmas;
6. run axiom and placeholder audits at milestones.

Do not guess theorem names or duplicate generic mathlib infrastructure without documenting an actual API gap.

## Build policy

The current Lake default target still builds the legacy `Cordis` library as a regression/reference corpus. New production modules must be added to explicit build/import targets as they are created. Do not remove the old build target merely to make the repository look cleaner before the new production tree exists.
