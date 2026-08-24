# Mechanization plan and status

This file records the live implementation status. `AGENTS.md` remains the
semantic and proof-policy authority.

## Completed

- Core lifecycle semantics, preservation, withdrawal safety, progress,
  reverse-priority termination, quiet reachability, and checked counterexamples.
- Witnessed reversible effects, finite programs, exact/prefix rollback, and
  explicit interleaving independence.
- Integrated projection, rollback, selective erasure, finite-stuttering
  termination, progress lifting, and quiet reachability.
- Semantic provider/target/unload-guard stability and mechanically constructed
  independent Core residual steps.
- Same-actor determinism and the same-actor/independent-actor local-confluence
  fragment; all Priority-related peaks, full valid-state local confluence,
  project-local Newman, full valid-state Core confluence, and unique reachable
  quiet normal form.
- Quiet-only `retire → normalize → remove → insert → normalize`
  replacement derivations with monotone identity history, endpoint soundness,
  identity change, and observed consumer binding change.
- A fully concrete `Agent → Model → APIProvider` replacement with two
  explicit six-step normalization schedules and final `Model → API_new`
  committed observation.

## Open, without weakening proved semantics

1. Investigate Integrated confluence only under explicit shared-effect
   independence hypotheses.
2. Model omitted runtime features and an actual implementation refinement.

Full Core confluence is proved for well-formed priority-acyclic roots.
Integrated confluence remains outside the claim.
