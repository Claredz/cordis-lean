# Core confluence status

## Result

Core is confluent from every well-formed, priority-acyclic root.  The strongest
checked statements are:

- `core_stepAt_peak_classification`: every labelled one-step peak is same actor,
  statically independent, or Priority-related, and carries a join witness;
- `core_local_confluent_at`: every one-step peak at a valid root is joinable;
- `core_confluent_at`: any two finite Core reductions from a valid root are
  joinable;
- `core_unique_normal_form` and `core_existsUnique_quiet_normal_form`: the
  reachable Core normal form exists, is quiet, and is unique.

The hypotheses are substantive: `FiberId` is finite, the root satisfies
`WellFormed`, and `PriorityAcyclic` is supplied separately.  No confluence claim
is made for malformed or cyclic states, or for Integrated shared-effect worlds.

## Exhaustive peak classification

`core_actor_pair_partition` is exhaustive for actor identities.  Same-actor
peaks use `stepAt_deterministic`; independent peaks use the constructed
one-step diamond `steps_on_independent_fibers_commute`; the complementary class
is exactly `CorePriorityRelated`.

For a Priority-related pair, each axis below is one of the five `StepAt`
constructors.  Every cell is covered without an extra rule assumption by
`priority_related_stepAt_joinable`:

| provider \ consumer | begin | finish | divert | leave | unload |
|---|---:|---:|---:|---:|---:|
| begin | join | join | join | join | join |
| finish | join | join | join | join | join |
| divert | join | join | join | join | join |
| leave | join | join | join | join | join |
| unload | join | join | join | join | join |

The table is intentionally universal rather than a list of syntactic tactic
cases: cells whose guards cannot coexist at a well-formed root are vacuous;
every reachable cell obtains an actual finite join.  Both orientations have
named lemmas, `provider_consumer_stepAt_joinable` and
`consumer_provider_stepAt_joinable`.

The join construction is factored into named semantic lemmas.  Core reduction
preserves well-formedness, registration, retirement, and acyclicity.  Every
branch reaches a quiet state.  `core_quiet_eq_of_same_frozen` proves those quiet
states equal by provider-first well-founded induction: equal phases of all
direct providers fix a consumer's provider resolution and target view, and
quietness then fixes its phase.  Thus Priority cascades of arbitrary depth join
at the unique quiet endpoint; no fixed two-step diamond is assumed.  The
invariant-restricted relation `ConfluentCoreStep` then combines full local
confluence with the existing termination theorem through the checked Newman
lemma.

## Adversarial audit

- **WellFormed.** Its four fields are single-source, inactive unregistered
  fibers, committed dependency coverage, and committed provider validity.  It
  contains neither acyclicity, progress, quietness, termination, nor confluence.
  `cyclic_dependency_deadlock` is a checked well-formed, non-quiet state with no
  step when the separate acyclicity hypothesis is removed.
- **`not_quiet_has_step`.** The cyclic witness above falsifies the theorem after
  dropping exactly `PriorityAcyclic`; the checked theorem keeps that hypothesis.
- **`committed_implies_priority`.** The edge is provider-to-consumer.
  `initial_committed_priority_orientation` checks concretely that Model's
  binding to API_old gives `API_old → Model` and not the reverse.
- **`fuelGrowthBound = 3`.** `fuelGrowthBound_minimal` derives the lower bound.
  `fuelGrowthBound_two_fails` rejects 2, while
  `fuelGrowthBound_three_suffices` exhausts all Boolean readiness pairs and
  accepts 3.  Both were exercised with `native_decide` during falsification;
  the committed proofs use kernel `decide` so the final axiom audit does not
  acquire a native-evaluator axiom.
- **`step_decreases_measure` and `lifecycle_terminates`.** These remain direct
  theorem dependencies of quiet reachability and the confluence construction;
  both are included in the axiom audit.  Their noncomputable provider choice and
  well-founded weight prevent a useful whole-theorem `native_decide` test.
- **Provider replacement compatibility.** The generic interface still requires
  fresh identity, equal provision interface, and actual post-removal/insertion
  well-formedness and acyclicity checks.  The concrete Agent→Model→API example
  constructs those checks directly rather than assuming the generic
  compatibility record, so replacement does not smuggle in confluence or final
  readiness.

As an additional non-kernel falsification attempt, a finite enumerator explored
all single-source three-fiber/three-key acyclic catalogs, retirement masks, and
well-formed phase states: 6,758 catalogs, 729,712 states, and 728,028 distinct
actor peaks.  It found zero nonjoinable peaks.  This exploration was used only
to attack the conjecture; the Lean theorem above is the proof.

## Concrete replacement

`Cordis.Examples.AgentModelApiReplacement` models
`Agent → Model → APIProvider`.  It checks the exact quiet-only sequence

```text
API_old → retire → six Core/effect normalization steps → remove
        → insert API_new → six normalization steps → quiet
```

Both normalization legs are explicit `Relation.ReflTransGen` derivations.
`checked_agent_model_api_replacement` packages the complete
`ReplacementDerivation`, final quiet proof, and the final committed
`Model.api = API_new` observation.

## Remaining boundary

Core confluence is closed under the stated invariants.  Integrated confluence
is still intentionally unclaimed: different actors share an effect world, so
Core independence alone does not establish effect commutation.  Async work,
failure, realms, dynamic registration, and implementation refinement remain
outside this run.
