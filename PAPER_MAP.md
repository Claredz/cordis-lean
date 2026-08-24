# Paper-to-model map

The reference named by the task is the active-revision preprint in the
[official Cordis paper repository](https://github.com/cordiverse/paper). This
file maps concepts, not implementation correctness.

| Concept | Mechanized result | Status |
|---|---|---|
| Installed vs active provider | `CommittedProviderValid`, `TargetProviderValid` | Core theorem |
| Unique active provider resolution | `provider_eq_some_iff` | Core theorem |
| Withdrawal safety | `unload_blocked_by_committed_consumer`, `unload_implies_no_committed_consumer` | Core theorem |
| Lifecycle progress | `no_lifecycle_deadlock` | Core theorem, assumes acyclicity |
| Lifecycle termination | `lifecycle_terminates` | Core theorem |
| Quiet reachability | `exists_quiet_reachable` | Core theorem |
| Witnessed rollback | `reverse_runProgram_exact`, `rollback_prefix_exact` | Effects theorem |
| Lifecycle/effect projection | `Integrated.StepAt.project`, `Integrated.Step.preserve_coreWellFormed` | Integrated theorem |
| Divert prefix rollback | `divert_then_unload_rolls_back_prefix` | Integrated theorem, no intervening world change |
| Selective interleaved rollback | `unload_erases_own_effects` | Integrated theorem, pairwise independence |
| Integrated termination | `Integrated.lifecycle_terminates` | Integrated theorem |
| Integrated quiet reachability | `Integrated.exists_coreQuiet_reachable` | Integrated theorem |
| Independent peaks | `independent_stepAt_commute`, `steps_on_independent_fibers_commute` | Extended theorem; residual steps constructed |
| Noninterfering local confluence | `core_noninterfering_local_confluent_at` | Extended same-actor/independent-actor fragment |
| Priority-dependent peaks | `priority_related_stepAt_joinable`, `core_stepAt_peak_classification` | Extended theorem; all five-by-five rule combinations covered |
| Full Core confluence | `core_local_confluent_at`, `core_confluent_at`, `core_unique_normal_form` | Extended theorem for well-formed priority-acyclic roots |
| Newman implication | `newman`, `confluentCoreStep_confluent` | Extended theorem applied to the invariant-restricted Core relation |
| Quiet-only provider replacement | `provider_replacement_derivation`, `provider_replacement_reaches_quiet`, `provider_identity_changes` | Extended explicit five-stage finite epoch |
| Observed binding replacement | `observed_consumer_binding_changes` | Extended theorem; explicit final-readiness assumption |
| Concrete Agent→Model→API replacement | `checked_agent_model_api_replacement` | Example; explicit schedules and final quiet binding |
| Full runtime/HMR semantics | none | Paper-only / future work |
