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
  fragment; project-local Newman theorem and conditional Core confluence.
- Quiet-only `retire → normalize → remove → insert → normalize`
  replacement derivations with monotone identity history, endpoint soundness,
  identity change, and observed consumer binding change.

## Open, without weakening proved semantics

1. Enumerate and resolve or refute every priority-related Core critical pair.
2. Instantiate the observed replacement interface with an additional fully
   concrete provider/consumer example.
3. Model omitted runtime features and an actual implementation refinement.

Full Core or Integrated confluence is not claimed while item 1 is open.
