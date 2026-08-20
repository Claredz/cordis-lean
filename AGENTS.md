# CordisLean Repository Instructions

These instructions govern every file below this project root. `PLAN.md` and
`DESIGN_NOTES.md`, when present, are the authority for Cordis-specific semantic
decisions. Development tools may improve the workflow but may not change those
decisions.

## Mathematical integrity

- Do not weaken a theorem statement merely to close its proof.
- Do not silently strengthen `WellFormed`. If a theorem genuinely lacks a
  hypothesis, first give or explain a counterexample, record it in
  `DESIGN_NOTES.md`, add only the weakest reasonable hypothesis, and explain the
  difference from the Cordis source model.
- A committed provider need only be `installed`; it must not be strengthened to
  `active`.
- A target provider must be `active`.
- An unloading provider may remain in an installed consumer's committed view.
- `registered` and `spec` remain fixed during Core lifecycle normalization.
- Acyclicity is an explicit theorem hypothesis; never hide it in `WellFormed`.
- Never present a Core result as a result about full Cordis.

## Proof integrity

Lean source must not contain `sorry`, `admit`, or project-defined `axiom`
declarations. Do not manufacture theorems with vacuous hypotheses, an
impossible `WellFormed`, a degenerate `Step`, a trivialized `quiet` predicate,
or empty-relation tricks. If a desired theorem is false, keep the mechanically
checked counterexample and document the failure.

## Layer discipline

Maintain this dependency direction:

```text
Core
  Effects
    Integrated
      Extended
        Examples
```

- Core does not import Effects, Integrated, or Extended.
- Effects is independent of lifecycle semantics.
- Integrated may import Core and Effects.
- Extended may import preceding layers.
- Examples may import every layer.
- Do not alter a frozen, passing lower-layer semantics merely to prove an
  upper-layer theorem.

## API-first proof engineering

Do not guess declaration names. Search in this order: project declarations,
`#check`, `#find`, `exact?`, `apply?`, `simp?`, Lean MCP local search, local
mathlib sources, LeanSearch/Loogle, then (only if needed) prove a reusable
generic lemma.

Prefer mathlib's existing relation closures, accessibility/well-foundedness,
finite collections, lexicographic orders, finite sums, and decidability APIs.
Do not reimplement generic graph or finite-set infrastructure without a
documented API gap.

For nontrivial proofs, inspect the exact goal and local context, test the
smallest candidate proof, check diagnostics immediately, split meaningful
lemmas when needed, build the current module, and run `lake build` at each
milestone. Termination, preservation, progress, confluence, and rollback
proofs should be decomposed into named mathematical lemmas rather than hidden
inside one large automation call.

Core is the permanent regression gate. Run an axiom audit for each layer's
strongest theorems and scan Lean sources for forbidden placeholders before
delivery.
