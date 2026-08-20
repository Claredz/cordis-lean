# Design notes

## Provider identity and validity

The catalog covers the finite universe, but single-source only quantifies over
registered fibers. Core normalization never changes registration. Extended
epochs may remove an inactive retired provider and insert a different fresh ID.

Committed validity deliberately accepts unloading providers because they remain
installed. Target validity requires active providers. The unloading witness in
`Core.Counterexamples` checks that the reverse implication is false.

## Termination measure

`localFuel` is phase/target-sensitive. The proof first establishes actor
decrease, nonconsumer stability, and a uniform consumer growth bound. The
minimal bound used by the proof is `fuelGrowthBound = 3`; it is proved rather
than assumed. Reverse-priority recursive weights strictly dominate all direct
consumer growth. Integrated termination then lexicographically adds total
remaining program length, so Iter stutters cannot be infinite.

No counterexample to these fuel lemmas was found; the requested fallback to a
multiset or alternate phase potential was therefore unnecessary.

## Confluence boundary

The independent-peak proof derives target-view stability, provider stability,
`reliedUpon`/unload-guard stability, both residual steps, and their common state
from well-formedness plus absence of priority edges. Residual steps are not
hypotheses. Same-actor determinism and this commuting theorem give a checked
local-confluence fragment covering every same-actor or independent-actor peak.
The generic Newman lemma is complete, and Core confluence follows conditionally
from local confluence. Priority-related critical pairs have not all been
enumerated, so the project does not declare unconditional Core confluence.
Integrated confluence is not inferred from Core because a shared world requires
effect independence.

## Orchestration boundary

Replacement is an explicit `ReplacementDerivation` with `Action.retire`, an
actual integrated normalization schedule, `Action.remove`, `Action.insert`, and
a second integrated normalization schedule. Every registry/retirement mutation
requires a quiet source. `everRegistered` grows only at insertion. Compatibility
checks are quantified over the actual first normalization endpoint rather than
assuming confluence. The observed consumer theorem proves the committed key
changes from the old ID to the fresh ID under an explicit final-readiness check.
Only finite epochs are claimed.
