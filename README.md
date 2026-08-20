# Cordis Lean mechanization

This repository is a layered Lean 4/mathlib model of selected Cordis ideas. It
is intentionally described as a **simplified mechanization**, not as verified
Cordis, an implementation refinement, or a verification of DeepSeek Harness.

The local project uses Lean/mathlib `v4.33.0`, the already-installed version
selected for this workspace (see `TOOLING.md`).

## Layers

1. `Cordis.Core` — finite lifecycle/dependency calculus, provider resolution,
   safety, progress, a reverse-priority termination measure, quiet reachability,
   and checked counterexamples.
2. `Cordis.Effects` — independent witnessed reversible effects, LIFO inverse
   accumulation, finite programs, prefix rollback, and independence predicates.
3. `Cordis.Integrated` — lifecycle phases carrying finite effect programs,
   erasure to Core, exact rollback, interleaved selective erasure, and a
   Core/remaining-program lexicographic termination proof with integrated
   quiet-state reachability.
4. `Cordis.Extended` — mechanically constructed independent residual steps,
   the same-actor/independent-actor local-confluence fragment, a project-local
   Newman lemma, and explicit quiet-only finite provider-replacement epochs.
5. `Cordis.Examples` — concrete chain/diamond schedules, quiet-state proof,
   executable effect tests, and the checked five-stage replacement derivation.

## Build and audit

```text
lake build Cordis.Core
lake build Cordis.Effects
lake build Cordis.Integrated
lake build Cordis.Extended
lake build Cordis.Examples
lake build
```

`Cordis/Audit.lean` runs `#print axioms` on representative strongest theorems.
The source policy forbids `sorry`, `admit`, and custom `axiom` declarations.

## Central modeling choice

Committed and target provider validity are different. An unloading provider is
still installed and may remain in a committed view, while a newly selected
target provider must be active. Provider resolution returns a result only for a
unique active candidate. Single-source applies only to the current `registered`
set, so a later orchestration epoch may replace a provider with a fresh ID.

See `LAYERS.md`, `ASSUMPTIONS.md`, and `PAPER_MAP.md` before interpreting any
theorem as a claim about the Cordis paper or an implementation.
