# Assumptions and scopes

- `FiberId` and keys used by termination are finite and have decidable equality.
- The static catalog is fixed during one lifecycle normalization epoch.
- `registered` is fixed by Core steps; single-source and priority edges are
  restricted to this set.
- `PriorityAcyclic` is explicit and is not hidden inside `WellFormed`.
- Committed bindings require a registered, installed declared provider.
- Target selection requires a registered, active declared provider and succeeds
  only for a unique candidate.
- Witness validity is pointwise: the returned undo restores the input from that
  invocation's output.
- Selective interleaved rollback requires `PairwiseIndependentPrograms`, which
  includes transformation commutation, state-dependent inverse stability, and
  inverse/foreign-forward commutation.
- Extended replacement requires a quiet sound source, a fresh universe
  identity, identical provision interface, satisfiable new dependencies, and
  checked post-removal/post-insertion well-formedness and acyclicity. These
  checks quantify over the actual first normalization endpoint; no confluence
  assumption chooses a canonical endpoint.
- The observed consumer-binding theorem additionally assumes that the fresh
  provider and observed consumer are ready at the actual final endpoint. This
  remains explicit because it is an orchestration readiness premise, not a Core
  confluence premise.
- `everRegistered` is monotone. Since the universe is finite, only finitely many
  fresh replacements can be represented in one trace.
- Classical choice, propositional extensionality, and quotient soundness may
  appear in `#print axioms`; these are Lean/mathlib foundations, not project
  axioms.
