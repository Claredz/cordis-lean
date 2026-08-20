import Cordis.Core

/-!
# Cordis.Extended.CoreCommutation

Semantic stability lemmas used to derive residual Core steps from genuine
static independence.  Residual steps are conclusions, not hypotheses.
-/

namespace Cordis.Extended

open Cordis

variable {FiberId Key : Type*}
variable [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Core.Spec Key}

/-- Two Core actors are statically independent when neither is a direct
provider of the other. -/
def CoreIndependent (spec : FiberId → Core.Spec Key)
    (s : Core.State FiberId Key) (left right : FiberId) : Prop :=
  left ≠ right ∧ ¬ Core.Priority spec s left right ∧
    ¬ Core.Priority spec s right left

/-- The complementary distinct-actor class left for dependent critical-pair
analysis. -/
def CorePriorityRelated (spec : FiberId → Core.Spec Key)
    (s : Core.State FiberId Key) (left right : FiberId) : Prop :=
  left ≠ right ∧
    (Core.Priority spec s left right ∨ Core.Priority spec s right left)

/-- Every actor pair lies in exactly the broad case split used by the
local-confluence audit: same actor, independent, or priority-related. -/
theorem core_actor_pair_partition (s : Core.State FiberId Key)
    (left right : FiberId) :
    left = right ∨ CoreIndependent spec s left right ∨
      CorePriorityRelated spec s left right := by
  by_cases hsame : left = right
  · exact Or.inl hsame
  · by_cases hlr : Core.Priority spec s left right
    · exact Or.inr (Or.inr ⟨hsame, Or.inl hlr⟩)
    · by_cases hrl : Core.Priority spec s right left
      · exact Or.inr (Or.inr ⟨hsame, Or.inr hrl⟩)
      · exact Or.inr (Or.inl ⟨hsame, hlr, hrl⟩)

private theorem targetProviderValid_iff_of_other_phase
    {s t : Core.State FiberId Key} {actor candidate : FiberId} {key : Key}
    (hregistered : t.registered = s.registered)
    (hphase : ∀ r, r ≠ actor → t.phase r = s.phase r)
    (hnotProvided : key ∉ (spec actor).provs) :
    Core.TargetProviderValid spec t candidate key ↔
      Core.TargetProviderValid spec s candidate key := by
  by_cases hcandidate : candidate = actor
  · subst candidate
    simp [Core.TargetProviderValid, hnotProvided]
  · constructor
    · rintro ⟨hreg, hactive, hprovides⟩
      refine ⟨by simpa [hregistered] using hreg, ?_, hprovides⟩
      simpa [Core.active, hphase candidate hcandidate] using hactive
    · rintro ⟨hreg, hactive, hprovides⟩
      refine ⟨by simpa [hregistered] using hreg, ?_, hprovides⟩
      simpa [Core.active, hphase candidate hcandidate] using hactive

/-- Provider resolution is stable when one unrelated actor changes phase and
does not declare the queried key. -/
theorem provider_stable_of_not_provided
    {s t : Core.State FiberId Key} {actor : FiberId} {key : Key}
    (hregistered : t.registered = s.registered)
    (hphase : ∀ r, r ≠ actor → t.phase r = s.phase r)
    (hnotProvided : key ∉ (spec actor).provs) :
    Core.provider spec t key = Core.provider spec s key := by
  have hvalid := fun candidate =>
    targetProviderValid_iff_of_other_phase
      (spec := spec) hregistered hphase hnotProvided (candidate := candidate)
  cases ht : Core.provider spec t key with
  | none =>
      cases hs : Core.provider spec s key with
      | none => rfl
      | some candidate =>
          have hsData := Core.provider_eq_some_iff.mp hs
          have htSome : Core.provider spec t key = some candidate := by
            apply Core.provider_eq_some_iff.mpr
            refine ⟨(hvalid candidate).2 hsData.1, ?_⟩
            intro other hother
            exact hsData.2 other ((hvalid other).1 hother)
          rw [ht] at htSome
          contradiction
  | some candidateT =>
      cases hs : Core.provider spec s key with
      | none =>
          have htData := Core.provider_eq_some_iff.mp ht
          have hsSome : Core.provider spec s key = some candidateT := by
            apply Core.provider_eq_some_iff.mpr
            refine ⟨(hvalid candidateT).1 htData.1, ?_⟩
            intro other hother
            exact htData.2 other ((hvalid other).2 hother)
          rw [hs] at hsSome
          contradiction
      | some candidateS =>
          have htData := Core.provider_eq_some_iff.mp ht
          have hsData := Core.provider_eq_some_iff.mp hs
          have heq : candidateS = candidateT :=
            htData.2 candidateS ((hvalid candidateS).2 hsData.1)
          subst candidateS
          rfl

/-- A step by `actor` cannot change the target of a registered consumer when
`actor` is not a direct provider of that consumer. -/
theorem targetView_stable_of_no_priority
    {s t : Core.State FiberId Key} {actor consumer : FiberId}
    (wf : Core.WellFormed spec s)
    (hstep : Core.StepAt spec actor s t)
    (hconsumer : consumer ∈ s.registered)
    (hnoPriority : ¬ Core.Priority spec s actor consumer) :
    Core.targetView spec t consumer = Core.targetView spec s consumer := by
  classical
  have hactor := Core.StepAt.actor_registered spec wf hstep
  have hprovider : ∀ key, key ∈ (spec consumer).deps →
      Core.provider spec t key = Core.provider spec s key := by
    intro key hdependency
    have hnotProvided : key ∉ (spec actor).provs := by
      intro hprovided
      exact hnoPriority ⟨hactor, hconsumer, key, hprovided, hdependency⟩
    exact provider_stable_of_not_provided
      (spec := spec) hstep.registered_eq
      (fun r hne => Core.StepAt.other_fiber_eq spec hstep hne) hnotProvided
  have hdependencies :
      Core.dependenciesSatisfied spec t consumer ↔
        Core.dependenciesSatisfied spec s consumer := by
    constructor
    · intro hsatisfied key hkey
      rcases hsatisfied key hkey with ⟨providerId, hproviderId⟩
      exact ⟨providerId, by simpa [hprovider key hkey] using hproviderId⟩
    · intro hsatisfied key hkey
      rcases hsatisfied key hkey with ⟨providerId, hproviderId⟩
      exact ⟨providerId, by simpa [hprovider key hkey] using hproviderId⟩
  let readyS : Prop := consumer ∈ s.registered ∧ consumer ∉ s.retired ∧
    Core.dependenciesSatisfied spec s consumer
  let readyT : Prop := consumer ∈ t.registered ∧ consumer ∉ t.retired ∧
    Core.dependenciesSatisfied spec t consumer
  have hready : readyT ↔ readyS := by
    simp only [readyT, readyS, hstep.registered_eq, hstep.retired_eq,
      hdependencies]
  by_cases hs : readyS
  · have ht : readyT := hready.mpr hs
    have hs' : consumer ∈ s.registered ∧ consumer ∉ s.retired ∧
        Core.dependenciesSatisfied spec s consumer := by
      simpa [readyS] using hs
    have ht' : consumer ∈ t.registered ∧ consumer ∉ t.retired ∧
        Core.dependenciesSatisfied spec t consumer := by
      simpa [readyT] using ht
    simp only [Core.targetView, dif_pos ht', dif_pos hs']
    congr 1
    funext key
    by_cases hkey : key ∈ (spec consumer).deps
    · simp [hkey, hprovider key hkey]
    · simp [hkey]
  · have ht : ¬ readyT := fun h => hs (hready.mp h)
    have hs' : ¬(consumer ∈ s.registered ∧ consumer ∉ s.retired ∧
        Core.dependenciesSatisfied spec s consumer) := by
      simpa [readyS] using hs
    have ht' : ¬(consumer ∈ t.registered ∧ consumer ∉ t.retired ∧
        Core.dependenciesSatisfied spec t consumer) := by
      simpa [readyT] using ht
    simp only [Core.targetView, dif_neg ht', dif_neg hs']

private theorem committedView_eq_of_phase_eq
    {s t : Core.State FiberId Key} {consumer : FiberId}
    (hphase : t.phase consumer = s.phase consumer) :
    Core.committedView t consumer = Core.committedView s consumer := by
  simp only [Core.committedView]
  rw [hphase]

/-- A step by `actor` cannot change whether `providerId` is relied upon when
there is no provider-to-actor priority edge. -/
theorem reliedUpon_stable_of_no_priority
    {s t : Core.State FiberId Key} {actor providerId : FiberId}
    (wf : Core.WellFormed spec s)
    (hstep : Core.StepAt spec actor s t)
    (hnoPriority : ¬ Core.Priority spec s providerId actor) :
    Core.reliedUpon t providerId ↔ Core.reliedUpon s providerId := by
  have wfT : Core.WellFormed spec t :=
    Core.Step.preserve_wellFormed wf ⟨actor, hstep⟩
  have noActorBindingS :
      ∀ view key, Core.committedView s actor = some view →
        view key = some providerId → False := by
    intro view key hview hbinding
    exact hnoPriority (Core.committed_implies_priority wf hview hbinding)
  have noActorBindingT :
      ∀ view key, Core.committedView t actor = some view →
        view key = some providerId → False := by
    intro view key hview hbinding
    have hpriorityT := Core.committed_implies_priority wfT hview hbinding
    apply hnoPriority
    simpa [Core.Priority, hstep.registered_eq] using hpriorityT
  constructor
  · rintro ⟨consumer, view, key, hview, hbinding⟩
    by_cases hconsumer : consumer = actor
    · subst consumer
      exact (noActorBindingT view key hview hbinding).elim
    · refine ⟨consumer, view, key, ?_, hbinding⟩
      have hphase := Core.StepAt.other_fiber_eq spec hstep hconsumer
      rw [← committedView_eq_of_phase_eq hphase]
      exact hview
  · rintro ⟨consumer, view, key, hview, hbinding⟩
    by_cases hconsumer : consumer = actor
    · subst consumer
      exact (noActorBindingS view key hview hbinding).elim
    · refine ⟨consumer, view, key, ?_, hbinding⟩
      have hphase := Core.StepAt.other_fiber_eq spec hstep hconsumer
      rw [committedView_eq_of_phase_eq hphase]
      exact hview

theorem unloadable_stable_of_no_priority
    {s t : Core.State FiberId Key} {actor providerId : FiberId}
    (wf : Core.WellFormed spec s)
    (hstep : Core.StepAt spec actor s t)
    (hnoPriority : ¬ Core.Priority spec s providerId actor) :
    Core.unloadable t providerId ↔ Core.unloadable s providerId := by
  unfold Core.unloadable
  exact not_congr (reliedUpon_stable_of_no_priority wf hstep hnoPriority)

theorem setPhase_commute (s : Core.State FiberId Key) {left right : FiberId}
    (hne : left ≠ right) (leftPhase rightPhase : Core.Phase Key FiberId) :
    (s.setPhase right rightPhase).setPhase left leftPhase =
      (s.setPhase left leftPhase).setPhase right rightPhase := by
  unfold Core.State.setPhase
  congr 1
  funext current
  by_cases hleft : current = left
  · subst current
    simp [hne]
  · by_cases hright : current = right
    · subst current
      simp [hne, hleft]
    · simp [hleft, hright]

private theorem replay_stepAt
    {s changed result : Core.State FiberId Key} {actor : FiberId}
    (hstep : Core.StepAt spec actor s result)
    (hphase : changed.phase actor = s.phase actor)
    (htarget : Core.targetView spec changed actor =
      Core.targetView spec s actor)
    (hunloadable : Core.unloadable changed actor ↔ Core.unloadable s actor) :
    ∃ finalPhase, result = s.setPhase actor finalPhase ∧
      Core.StepAt spec actor changed (changed.setPhase actor finalPhase) := by
  cases hstep with
  | begin hp ht =>
      refine ⟨_, rfl, Core.StepAt.begin ?_ ?_⟩
      · rw [hphase]
        exact hp
      · rw [htarget]
        exact ht
  | finish hp ht =>
      refine ⟨_, rfl, Core.StepAt.finish ?_ ?_⟩
      · rw [hphase]
        exact hp
      · rw [htarget]
        exact ht
  | divert hp ht =>
      refine ⟨_, rfl, Core.StepAt.divert ?_ ?_⟩
      · rw [hphase]
        exact hp
      · rw [htarget]
        exact ht
  | leave hp ht =>
      refine ⟨_, rfl, Core.StepAt.leave ?_ ?_⟩
      · rw [hphase]
        exact hp
      · rw [htarget]
        exact ht
  | unload hp hu =>
      refine ⟨.inactive, rfl, ?_⟩
      apply Core.StepAt.unload
      · rw [hphase]
        exact hp
      · exact hunloadable.mpr hu

/-- Core rules are deterministic once the actor and source state are fixed. -/
theorem stepAt_deterministic
    {s leftState rightState : Core.State FiberId Key} {actor : FiberId}
    (leftStep : Core.StepAt spec actor s leftState)
    (rightStep : Core.StepAt spec actor s rightState) :
    leftState = rightState := by
  cases leftStep <;> cases rightStep <;> simp_all

/-- **Extended theorem.** Different Core actors with no priority interference
have mechanically constructed one-step residuals that meet at the same state. -/
theorem independent_stepAt_commute
    {s leftState rightState : Core.State FiberId Key}
    {left right : FiberId}
    (wf : Core.WellFormed spec s)
    (leftStep : Core.StepAt spec left s leftState)
    (rightStep : Core.StepAt spec right s rightState)
    (independent : CoreIndependent spec s left right) :
    ∃ join,
      Core.StepAt spec right leftState join ∧
      Core.StepAt spec left rightState join := by
  rcases independent with ⟨hne, hnoLeftRight, hnoRightLeft⟩
  have leftRegistered := Core.StepAt.actor_registered spec wf leftStep
  have rightRegistered := Core.StepAt.actor_registered spec wf rightStep
  have targetLeft := targetView_stable_of_no_priority wf rightStep
    leftRegistered hnoRightLeft
  have targetRight := targetView_stable_of_no_priority wf leftStep
    rightRegistered hnoLeftRight
  have unloadLeft := unloadable_stable_of_no_priority wf rightStep hnoLeftRight
  have unloadRight := unloadable_stable_of_no_priority wf leftStep hnoRightLeft
  rcases replay_stepAt leftStep
      (Core.StepAt.other_fiber_eq spec rightStep hne) targetLeft unloadLeft with
    ⟨leftPhase, hleftState, leftResidual⟩
  rcases replay_stepAt rightStep
      (Core.StepAt.other_fiber_eq spec leftStep hne.symm) targetRight unloadRight with
    ⟨rightPhase, hrightState, rightResidual⟩
  have hjoin :
      leftState.setPhase right rightPhase =
        rightState.setPhase left leftPhase := by
    rw [hleftState, hrightState]
    exact (setPhase_commute s hne leftPhase rightPhase).symm
  refine ⟨leftState.setPhase right rightPhase, rightResidual, ?_⟩
  rw [← hjoin] at leftResidual
  exact leftResidual

end Cordis.Extended
