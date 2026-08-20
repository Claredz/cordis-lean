# Progress notes

## Frozen Core

- Implemented the four lifecycle phases and five rules.
- Proved all five rule-specific preservation lemmas and the aggregate theorem.
- Proved withdrawal safety, progress/deadlock freedom, termination, and quiet
  reachability.
- Added cyclic-dependency, ambiguous-provider, and unloading-provider witnesses.

## Effects

- Implemented witnessed pointwise inverses, LIFO tracking, composition, finite
  programs, exact full/prefix rollback, and explicit cross-program independence.
- Added checked invalid-inverse counterexamples.

## Integrated

- Added effect-carrying phases and a shared world.
- Proved Iter stuttering, lifecycle projection, Core invariant preservation,
  exact consecutive rollback, arbitrary interleaving selective erasure, and
  lexicographic termination.
- Proved that every enabled Core step has an enabled integrated refinement step,
  then combined progress and accessibility into integrated quiet reachability.

## Extended and examples

- Constructed residual steps for statically independent Core actors from
  provider/target/unload-guard stability, and proved the same-actor or
  independent-actor local-confluence fragment.
- Proved a generic Newman lemma and conditional Core confluence implication.
- Replaced the atomic epoch wrapper with quiet-only `retire`, `remove`, and
  `insert` actions, two explicit integrated normalization schedules, final ID
  change, soundness, quiet reachability, and observed consumer binding change.
- Added concrete chain and diamond `ReflTransGen` schedules with a shared quiet
  terminal state, plus native effect tests.

The remaining limitations are tracked in `ROADMAP.md` and are not presented as
verified Cordis claims.
