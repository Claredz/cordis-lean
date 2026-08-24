# Layer boundaries

## Core theorem

Imports only the lifecycle/dependency model. `WellFormed` contains registered
single-source, inactive unregistered fibers, exact dependency coverage, and
committed-provider validity. Acyclicity is a separate hypothesis. Core never
imports Effects, Integrated, Extended, or Examples.

## Effects theorem

Uses an abstract world `Γ` and no lifecycle state. A witnessed inverse is only a
left inverse at the actual result of `run`; no global bijection is assumed.

## Integrated theorem

Combines finite effect programs with lifecycle phases. `erase` maps every
integrated state to Core. Iter is a Core stutter; all other rules project to the
corresponding Core rule. Core well-formedness is preserved through this
projection. Finite-program accessibility plus a lifting progress lemma produces
an actual `Integrated.Step` schedule to a state with quiet Core projection.

## Extended theorem

Requires extra hypotheses about commuting peaks or a checked orchestration
epoch. Independent residual steps are conclusions of semantic stability lemmas,
not assumptions. Same-actor, independent-actor, and Priority-related peaks are
exhaustive and joinable at valid roots. Provider-first quiet endpoint uniqueness
and termination feed the generic Newman lemma, yielding `core_confluent_at` and
unique reachable Core normal forms. Registry mutation is confined to explicit
quiet-only `retire`, `remove`, and `insert` actions separated by integrated
normalization. Integrated shared-world confluence is not claimed.

## Paper-only claim

Anything involving the complete Cordis runtime, HMR transactions, dynamic child
registration, realms, async/failure behavior, effect iterators, or observational
equivalence remains outside this mechanization.
