import Cordis.Integrated

/-!
# Cordis.Extended.Orchestration

Registry mutation is exposed only as three quiet-boundary actions.  Provider
replacement is an explicit five-stage derivation:

`retire → integrated normalize → remove → insert → integrated normalize`.

The monotone `everRegistered` set prevents identity reuse across finite epochs.
-/

namespace Cordis.Extended

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}
variable [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]

structure OrchState (FiberId Key : Type*) (Γ : Type u) [DecidableEq FiberId] where
  lifecycle : Integrated.State FiberId Key Γ
  everRegistered : Finset FiberId

def OrchState.Sound (spec : FiberId → Core.Spec Key)
    (state : OrchState FiberId Key Γ) : Prop :=
  Integrated.CoreWellFormed spec state.lifecycle ∧
    Core.PriorityAcyclic spec (Integrated.erase state.lifecycle) ∧
    state.lifecycle.registered ⊆ state.everRegistered

def retireLifecycle (state : Integrated.State FiberId Key Γ)
    (old : FiberId) : Integrated.State FiberId Key Γ :=
  { state with retired := insert old state.retired }

def removeLifecycle (state : Integrated.State FiberId Key Γ)
    (old : FiberId) : Integrated.State FiberId Key Γ :=
  { state with
    registered := state.registered.erase old
    retired := state.retired.erase old }

def insertLifecycle (state : Integrated.State FiberId Key Γ)
    (fresh : FiberId) : Integrated.State FiberId Key Γ :=
  { state with
    registered := insert fresh state.registered
    retired := state.retired.erase fresh }

def retireEpoch (state : OrchState FiberId Key Γ) (old : FiberId) :
    OrchState FiberId Key Γ where
  lifecycle := retireLifecycle state.lifecycle old
  everRegistered := state.everRegistered

def removeEpoch (state : OrchState FiberId Key Γ) (old : FiberId) :
    OrchState FiberId Key Γ where
  lifecycle := removeLifecycle state.lifecycle old
  everRegistered := state.everRegistered

def insertEpoch (state : OrchState FiberId Key Γ) (fresh : FiberId) :
    OrchState FiberId Key Γ where
  lifecycle := insertLifecycle state.lifecycle fresh
  everRegistered := insert fresh state.everRegistered

/-- A normalization segment changes neither registry nor retirement flags and
ends at a quiet Core projection with all soundness obligations preserved. -/
structure Normalization
    (spec : FiberId → Core.Spec Key)
    (program : FiberId → List (Effects.WitnessedEffect Γ))
    (source target : OrchState FiberId Key Γ) : Prop where
  schedule : Relation.ReflTransGen (Integrated.Step spec program)
    source.lifecycle target.lifecycle
  quiet : Core.quiet spec (Integrated.erase target.lifecycle)
  targetSound : target.Sound spec
  registered_eq : target.lifecycle.registered = source.lifecycle.registered
  retired_eq : target.lifecycle.retired = source.lifecycle.retired
  everRegistered_eq : target.everRegistered = source.everRegistered

private theorem retire_preserves_sound
    {spec : FiberId → Core.Spec Key} {state : OrchState FiberId Key Γ}
    {old : FiberId} (sound : state.Sound spec) :
    (retireEpoch state old).Sound spec := by
  rcases sound with ⟨wf, acyclic, registeredEver⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold Integrated.CoreWellFormed at wf ⊢
    refine {
      singleSource := ?_
      unregistered_inactive := ?_
      committed_covers := ?_
      committed_valid := ?_ }
    · simpa [retireEpoch, retireLifecycle, Integrated.erase,
        Core.SingleSource] using wf.singleSource
    · simpa [retireEpoch, retireLifecycle, Integrated.erase] using
        wf.unregistered_inactive
    · simpa [retireEpoch, retireLifecycle, Integrated.erase,
        Core.committedView] using wf.committed_covers
    · simpa [retireEpoch, retireLifecycle, Integrated.erase,
        Core.committedView, Core.CommittedProviderValid, Core.installed] using
        wf.committed_valid
  · simpa [retireEpoch, retireLifecycle, Core.PriorityAcyclic,
      Integrated.erase] using acyclic
  · simpa [retireEpoch, retireLifecycle] using registeredEver

/-- Integrated termination plus progress constructs the normalization segment
used between orchestration mutations. -/
theorem normalize_to_quiet
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {source : OrchState FiberId Key Γ} (sound : source.Sound spec) :
    ∃ target, Normalization spec program source target := by
  rcases sound with ⟨wf, acyclic, registeredEver⟩
  rcases Integrated.exists_coreQuiet_reachable_sound spec program wf acyclic with
    ⟨quietLifecycle, schedule, quiet, quietWf, quietAcyclic,
      registeredEq, retiredEq⟩
  let target : OrchState FiberId Key Γ :=
    ⟨quietLifecycle, source.everRegistered⟩
  have targetSound : target.Sound spec := by
    refine ⟨quietWf, quietAcyclic, ?_⟩
    intro p hp
    apply registeredEver
    rw [← registeredEq]
    exact hp
  exact ⟨target, schedule, quiet, targetSound, registeredEq, retiredEq, rfl⟩

/-- The only registry/retirement mutations admitted by the Extended model.
Every constructor is guarded by a quiet source.  Removal and insertion carry
the explicit post-mutation invariant/acyclicity checks. -/
inductive Action (spec : FiberId → Core.Spec Key) :
    OrchState FiberId Key Γ → OrchState FiberId Key Γ → Prop
  | retire {source : OrchState FiberId Key Γ} {old : FiberId}
      (sourceSound : source.Sound spec)
      (sourceQuiet : Core.quiet spec (Integrated.erase source.lifecycle))
      (oldRegistered : old ∈ source.lifecycle.registered)
      (oldNotRetired : old ∉ source.lifecycle.retired) :
      Action spec source (retireEpoch source old)
  | remove {source : OrchState FiberId Key Γ} {old : FiberId}
      (sourceSound : source.Sound spec)
      (sourceQuiet : Core.quiet spec (Integrated.erase source.lifecycle))
      (oldRegistered : old ∈ source.lifecycle.registered)
      (oldRetired : old ∈ source.lifecycle.retired)
      (oldInactive : source.lifecycle.phase old = .inactive)
      (oldUnrelied : Core.unloadable (Integrated.erase source.lifecycle) old)
      (postWellFormed : Integrated.CoreWellFormed spec
        (removeLifecycle source.lifecycle old))
      (postAcyclic : Core.PriorityAcyclic spec
        (Integrated.erase (removeLifecycle source.lifecycle old))) :
      Action spec source (removeEpoch source old)
  | insert {source : OrchState FiberId Key Γ} {fresh : FiberId}
      (sourceSound : source.Sound spec)
      (sourceQuiet : Core.quiet spec (Integrated.erase source.lifecycle))
      (freshUnused : fresh ∉ source.everRegistered)
      (freshInactive : source.lifecycle.phase fresh = .inactive)
      (postWellFormed : Integrated.CoreWellFormed spec
        (insertLifecycle source.lifecycle fresh))
      (postAcyclic : Core.PriorityAcyclic spec
        (Integrated.erase (insertLifecycle source.lifecycle fresh))) :
      Action spec source (insertEpoch source fresh)

/-- Each checked action produces a sound epoch state. -/
theorem Action.preserves_sound
    {spec : FiberId → Core.Spec Key} {source target : OrchState FiberId Key Γ}
    (action : Action spec source target) : target.Sound spec := by
  cases action with
  | retire sourceSound => exact retire_preserves_sound sourceSound
  | remove sourceSound _ _ _ _ _ postWellFormed postAcyclic =>
      refine ⟨postWellFormed, postAcyclic, ?_⟩
      intro p hp
      apply sourceSound.2.2
      exact Finset.mem_of_mem_erase (by simpa [removeEpoch, removeLifecycle] using hp)
  | insert sourceSound _ _ _ postWellFormed postAcyclic =>
      refine ⟨postWellFormed, postAcyclic, ?_⟩
      simpa [insertEpoch, insertLifecycle] using
        (Finset.insert_subset_insert _ sourceSound.2.2)

private theorem quiet_retired_inactive
    {spec : FiberId → Core.Spec Key} {state : OrchState FiberId Key Γ}
    {old : FiberId}
    (quiet : Core.quiet spec (Integrated.erase state.lifecycle))
    (retired : old ∈ state.lifecycle.retired) :
    state.lifecycle.phase old = .inactive := by
  have htarget : Core.targetView spec (Integrated.erase state.lifecycle) old = none :=
    Core.targetView_eq_none_iff_not_ready.mpr (fun ready => ready.2.1 retired)
  have hlocal := quiet old
  cases hp : state.lifecycle.phase old <;>
    simp [Core.LocallyQuiet, Integrated.erasePhase, hp, htarget] at hlocal ⊢

private theorem inactive_unloadable
    {spec : FiberId → Core.Spec Key} {state : OrchState FiberId Key Γ}
    {old : FiberId} (sound : state.Sound spec)
    (inactive : state.lifecycle.phase old = .inactive) :
    Core.unloadable (Integrated.erase state.lifecycle) old := by
  intro relied
  rcases relied with ⟨consumer, view, key, hview, hbinding⟩
  have valid := sound.1.committed_valid consumer view hview key old hbinding
  apply valid.2.1
  simp [Core.installed, Integrated.erase, Integrated.erasePhase, inactive]

/-- Compatibility data for a finite replacement epoch.  Post-removal and
post-insertion checks are quantified over the actual quiet normalization
endpoint, so the definition does not assume confluence. -/
structure ReplacementCompatible
    (spec : FiberId → Core.Spec Key)
    (program : FiberId → List (Effects.WitnessedEffect Γ))
    (state : OrchState FiberId Key Γ) (old fresh : FiberId) : Prop where
  differentId : old ≠ fresh
  sourceSound : state.Sound spec
  sourceQuiet : Core.quiet spec (Integrated.erase state.lifecycle)
  oldRegistered : old ∈ state.lifecycle.registered
  oldNotRetired : old ∉ state.lifecycle.retired
  freshUnused : fresh ∉ state.everRegistered
  sameInterface : (spec fresh).provs = (spec old).provs
  removalChecks : ∀ normalized,
    Normalization spec program (retireEpoch state old) normalized →
      Integrated.CoreWellFormed spec (removeLifecycle normalized.lifecycle old) ∧
      Core.PriorityAcyclic spec
        (Integrated.erase (removeLifecycle normalized.lifecycle old)) ∧
      Core.quiet spec
        (Integrated.erase (removeLifecycle normalized.lifecycle old))
  insertionChecks : ∀ normalized,
    Normalization spec program (retireEpoch state old) normalized →
      Integrated.CoreWellFormed spec
        (insertLifecycle (removeLifecycle normalized.lifecycle old) fresh) ∧
      Core.PriorityAcyclic spec (Integrated.erase
        (insertLifecycle (removeLifecycle normalized.lifecycle old) fresh))
  newDependenciesSatisfiedAfterRemoval : ∀ normalized,
    Normalization spec program (retireEpoch state old) normalized →
      Core.dependenciesSatisfied spec
        (Integrated.erase (removeLifecycle normalized.lifecycle old)) fresh

/-- The requested explicit action-by-action replacement witness. -/
structure ReplacementDerivation
    (spec : FiberId → Core.Spec Key)
    (program : FiberId → List (Effects.WitnessedEffect Γ))
    (initial : OrchState FiberId Key Γ) (old fresh : FiberId) where
  retired : OrchState FiberId Key Γ
  normalized : OrchState FiberId Key Γ
  removed : OrchState FiberId Key Γ
  inserted : OrchState FiberId Key Γ
  final : OrchState FiberId Key Γ
  retireAction : Action spec initial retired
  retired_eq : retired = retireEpoch initial old
  normalizeRetired : Normalization spec program retired normalized
  removeAction : Action spec normalized removed
  removed_eq : removed = removeEpoch normalized old
  insertAction : Action spec removed inserted
  inserted_eq : inserted = insertEpoch removed fresh
  normalizeInserted : Normalization spec program inserted final

/-- **Extended theorem.** Compatibility constructs the complete quiet-only
`retire → normalize → remove → insert → normalize` derivation. -/
theorem provider_replacement_derivation
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : OrchState FiberId Key Γ} {old fresh : FiberId}
    (compatible : ReplacementCompatible spec program state old fresh) :
    Nonempty (ReplacementDerivation spec program state old fresh) := by
  let retired := retireEpoch state old
  have retireAction : Action spec state retired :=
    .retire compatible.sourceSound compatible.sourceQuiet
      compatible.oldRegistered compatible.oldNotRetired
  have retiredSound := retireAction.preserves_sound
  rcases normalize_to_quiet (program := program) retiredSound with
    ⟨normalized, normalizeRetired⟩
  have oldRegisteredNormalized : old ∈ normalized.lifecycle.registered := by
    rw [normalizeRetired.registered_eq]
    simpa [retired, retireEpoch, retireLifecycle] using compatible.oldRegistered
  have oldRetiredNormalized : old ∈ normalized.lifecycle.retired := by
    rw [normalizeRetired.retired_eq]
    simp [retired, retireEpoch, retireLifecycle]
  have oldInactive := quiet_retired_inactive normalizeRetired.quiet
    oldRetiredNormalized
  have oldUnrelied := inactive_unloadable normalizeRetired.targetSound oldInactive
  rcases compatible.removalChecks normalized normalizeRetired with
    ⟨removeWf, removeAcyclic, removeQuiet⟩
  let removed := removeEpoch normalized old
  have removeAction : Action spec normalized removed :=
    .remove normalizeRetired.targetSound normalizeRetired.quiet
      oldRegisteredNormalized oldRetiredNormalized oldInactive oldUnrelied
      removeWf removeAcyclic
  have removedSound := removeAction.preserves_sound
  have freshInactive : removed.lifecycle.phase fresh = .inactive := by
    have freshNotRegistered : fresh ∉ normalized.lifecycle.registered := by
      intro hfresh
      have inEver := normalizeRetired.targetSound.2.2 hfresh
      rw [normalizeRetired.everRegistered_eq] at inEver
      exact compatible.freshUnused inEver
    have coreInactive := normalizeRetired.targetSound.1.unregistered_inactive
      fresh freshNotRegistered
    cases hp : normalized.lifecycle.phase fresh <;>
      simp [removed, removeEpoch, removeLifecycle, Integrated.erasePhase, hp]
        at coreInactive ⊢
  rcases compatible.insertionChecks normalized normalizeRetired with
    ⟨insertWf, insertAcyclic⟩
  let inserted := insertEpoch removed fresh
  have freshUnusedRemoved : fresh ∉ removed.everRegistered := by
    intro inRemoved
    apply compatible.freshUnused
    have everEq : normalized.everRegistered = state.everRegistered := by
      simpa [retired, retireEpoch] using normalizeRetired.everRegistered_eq
    rw [← everEq]
    simpa [removed, removeEpoch] using inRemoved
  have insertAction : Action spec removed inserted :=
    .insert removedSound (by simpa [removed, removeEpoch] using removeQuiet)
      freshUnusedRemoved
      freshInactive insertWf insertAcyclic
  have insertedSound := insertAction.preserves_sound
  rcases normalize_to_quiet (program := program) insertedSound with
    ⟨final, normalizeInserted⟩
  exact ⟨⟨retired, normalized, removed, inserted, final,
    retireAction, rfl, normalizeRetired, removeAction, rfl,
    insertAction, rfl, normalizeInserted⟩⟩

/-- Observation-specific assumptions for checking a consumer binding across a
replacement.  Final readiness is quantified over the actual derivation because
global Core confluence is deliberately not assumed. -/
structure ObservedReplacementCompatible
    (spec : FiberId → Core.Spec Key)
    (program : FiberId → List (Effects.WitnessedEffect Γ))
    (state : OrchState FiberId Key Γ) (old fresh consumer : FiberId)
    (key : Key) (initialView : Core.View Key FiberId) : Prop extends
      ReplacementCompatible spec program state old fresh where
  initialCommitted : Core.committedView (Integrated.erase state.lifecycle)
    consumer = some initialView
  initialBinding : initialView key = some old
  observedDependency : key ∈ (spec consumer).deps
  finalReady : ∀ derivation :
      ReplacementDerivation spec program state old fresh,
    Core.TargetReady spec (Integrated.erase derivation.final.lifecycle) fresh ∧
    Core.TargetReady spec (Integrated.erase derivation.final.lifecycle) consumer

private theorem active_of_quiet_ready
    {spec : FiberId → Core.Spec Key} {state : Core.State FiberId Key}
    {fiber : FiberId} (quiet : Core.quiet spec state)
    (ready : Core.TargetReady spec state fiber) : Core.active state fiber := by
  have hsome := Core.targetView_isSome_iff_ready.mpr ready
  cases htarget : Core.targetView spec state fiber with
  | none => simp [htarget] at hsome
  | some target =>
      have hlocal := quiet fiber
      cases hphase : state.phase fiber with
      | inactive => simp [Core.LocallyQuiet, hphase, htarget] at hlocal
      | reloading view => simp [Core.LocallyQuiet, hphase] at hlocal
      | active view => exact ⟨view, hphase⟩
      | unloading view => simp [Core.LocallyQuiet, hphase] at hlocal

/-- **Extended theorem (observed replacement).** A checked consumer binding
that initially names `old` names `fresh` at the final quiet endpoint. -/
theorem observed_consumer_binding_changes
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : OrchState FiberId Key Γ} {old fresh consumer : FiberId} {key : Key}
    {initialView : Core.View Key FiberId}
    (compatible : ObservedReplacementCompatible spec program state old fresh
      consumer key initialView) :
    ∃ derivation : ReplacementDerivation spec program state old fresh,
      Core.committedView (Integrated.erase state.lifecycle) consumer =
          some initialView ∧
      initialView key = some old ∧
      ∃ finalView,
        Core.committedView (Integrated.erase derivation.final.lifecycle) consumer =
          some finalView ∧
        finalView key = some fresh := by
  rcases provider_replacement_derivation compatible.toReplacementCompatible with
    ⟨derivation⟩
  let finalCore := Integrated.erase derivation.final.lifecycle
  have finalSound := derivation.normalizeInserted.targetSound
  have finalQuiet := derivation.normalizeInserted.quiet
  have readyFresh := (compatible.finalReady derivation).1
  have readyConsumer := (compatible.finalReady derivation).2
  have activeFresh : Core.active finalCore fresh :=
    active_of_quiet_ready finalQuiet readyFresh
  have freshProvides : key ∈ (spec fresh).provs := by
    have oldValid := compatible.sourceSound.1.committed_valid consumer
      initialView compatible.initialCommitted key old
      compatible.initialBinding
    rw [compatible.sameInterface]
    exact oldValid.2.2
  have providerFresh : Core.provider spec finalCore key = some fresh := by
    apply Core.provider_complete_of_candidate finalSound.1
    exact ⟨readyFresh.1, activeFresh, freshProvides⟩
  rcases active_of_quiet_ready finalQuiet readyConsumer with
    ⟨finalView, hactiveConsumer⟩
  have hactiveConsumer' : finalCore.phase consumer = .active finalView := by
    simpa [finalCore] using hactiveConsumer
  have htargetConsumer : Core.targetView spec finalCore consumer =
      some finalView := by
    have hlocal := finalQuiet consumer
    change Core.LocallyQuiet spec finalCore consumer at hlocal
    simp only [Core.LocallyQuiet, hactiveConsumer'] at hlocal
    exact hlocal
  have hcommittedConsumer : Core.committedView finalCore consumer =
      some finalView := by
    simp only [Core.committedView, hactiveConsumer']
  have hfinalBinding : finalView key = some fresh := by
    rcases Core.targetView_eq_some_iff.mp htargetConsumer with
      ⟨-, -, -, hview⟩
    rw [hview]
    simp [compatible.observedDependency, providerFresh]
  exact ⟨derivation, compatible.initialCommitted, compatible.initialBinding,
    finalView, hcommittedConsumer, hfinalBinding⟩

/-- **Extended theorem.** Every endpoint in the explicit derivation is sound;
in particular the final quiet endpoint preserves the Core invariant and
registered-priority acyclicity. -/
theorem replacement_preserves_wellFormed
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : OrchState FiberId Key Γ} {old fresh : FiberId}
    (compatible : ReplacementCompatible spec program state old fresh) :
    ∃ derivation : ReplacementDerivation spec program state old fresh,
      derivation.final.Sound spec := by
  rcases provider_replacement_derivation compatible with ⟨derivation⟩
  exact ⟨derivation, derivation.normalizeInserted.targetSound⟩

/-- **Extended theorem.** The old identity is absent and the fresh identity is
registered at the final quiet endpoint. -/
theorem provider_identity_changes
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : OrchState FiberId Key Γ} {old fresh : FiberId}
    (compatible : ReplacementCompatible spec program state old fresh) :
    ∃ derivation : ReplacementDerivation spec program state old fresh,
      old ∉ derivation.final.lifecycle.registered ∧
      fresh ∈ derivation.final.lifecycle.registered := by
  rcases provider_replacement_derivation compatible with ⟨derivation⟩
  have hfinal := derivation.normalizeInserted.registered_eq
  rw [derivation.inserted_eq] at hfinal
  simp only [insertEpoch, insertLifecycle] at hfinal
  rw [derivation.removed_eq] at hfinal
  simp only [removeEpoch, removeLifecycle] at hfinal
  have hnormalized := derivation.normalizeRetired.registered_eq
  rw [derivation.retired_eq] at hnormalized
  simp only [retireEpoch, retireLifecycle] at hnormalized
  have hregistered : derivation.final.lifecycle.registered =
      insert fresh (state.lifecycle.registered.erase old) := by
    rw [hfinal, hnormalized]
  refine ⟨derivation, ?_, ?_⟩
  · rw [hregistered]
    simp [compatible.differentId]
  · rw [hregistered]
    simp

/-- **Extended theorem.** A compatible finite replacement epoch reaches a
quiet state via the explicit five-stage derivation. -/
theorem provider_replacement_reaches_quiet
    {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : OrchState FiberId Key Γ} {old fresh : FiberId}
    (compatible : ReplacementCompatible spec program state old fresh) :
    ∃ derivation : ReplacementDerivation spec program state old fresh,
      Core.quiet spec (Integrated.erase derivation.final.lifecycle) := by
  rcases provider_replacement_derivation compatible with ⟨derivation⟩
  exact ⟨derivation, derivation.normalizeInserted.quiet⟩

end Cordis.Extended
