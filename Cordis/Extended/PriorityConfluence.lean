import Cordis.Extended.Confluence

/-!
# Priority-dependent Core confluence

This file closes the remaining Core critical-pair boundary.  It proves quiet
endpoint uniqueness from the existing invariant and explicit acyclicity,
constructs arbitrary-depth joins for both Priority orientations, classifies
all actor-labelled peaks, and applies the project-local Newman theorem to the
invariant-restricted Core relation.
-/

namespace Cordis.Extended

open Cordis

variable {FiberId Key : Type*}
variable [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Core.Spec Key}


/-- On a finite type, reversing a well-founded relation is well-founded. -/
theorem wellFounded_swap_of_finite {α : Type*} [Finite α]
    {r : α → α → Prop} (wf : WellFounded r) :
    WellFounded (Function.swap r) := by
  have hirr : ∀ a, ¬ Relation.TransGen (Function.swap r) a a := by
    intro a h
    have hr : Relation.TransGen r a a := Relation.transGen_swap.mp h
    exact wf.transGen.irrefl.irrefl a hr
  let _ : Std.Irrefl (Relation.TransGen (Function.swap r)) := ⟨hirr⟩
  exact (Finite.wellFounded_of_trans_of_irrefl
    (Relation.TransGen (Function.swap r))).mono
      (fun _ _ h => Relation.TransGen.single h)

omit [Fintype FiberId] in
/-- Provider resolution for one consumer is fixed once all of that consumer's
direct providers have the same phases. -/
theorem provider_eq_of_priority_phases_eq
    {s t : Core.State FiberId Key} {consumer : FiberId} {key : Key}
    (hregistered : t.registered = s.registered)
    (hconsumer : consumer ∈ s.registered)
    (hdependency : key ∈ (spec consumer).deps)
    (hphase : ∀ providerId,
      Core.PriorityOn spec s.registered providerId consumer →
        t.phase providerId = s.phase providerId) :
    Core.provider spec t key = Core.provider spec s key := by
  have hvalid : ∀ candidate,
      Core.TargetProviderValid spec t candidate key ↔
        Core.TargetProviderValid spec s candidate key := by
    intro candidate
    constructor
    · rintro ⟨hcandidate, hactive, hprovides⟩
      have hcandidateS : candidate ∈ s.registered := by
        simpa [hregistered] using hcandidate
      have hedge : Core.PriorityOn spec s.registered candidate consumer :=
        ⟨hcandidateS, hconsumer, key, hprovides, hdependency⟩
      refine ⟨hcandidateS, ?_, hprovides⟩
      simpa [Core.active, hphase candidate hedge] using hactive
    · rintro ⟨hcandidate, hactive, hprovides⟩
      have hedge : Core.PriorityOn spec s.registered candidate consumer :=
        ⟨hcandidate, hconsumer, key, hprovides, hdependency⟩
      refine ⟨by simpa [hregistered] using hcandidate, ?_, hprovides⟩
      simpa [Core.active, hphase candidate hedge] using hactive
  apply Option.ext
  intro candidate
  simp only [Core.provider_eq_some_iff]
  constructor
  · rintro ⟨hcandidate, hunique⟩
    refine ⟨(hvalid candidate).mp hcandidate, ?_⟩
    intro other hother
    exact hunique other ((hvalid other).mpr hother)
  · rintro ⟨hcandidate, hunique⟩
    refine ⟨(hvalid candidate).mpr hcandidate, ?_⟩
    intro other hother
    exact hunique other ((hvalid other).mp hother)

omit [Fintype FiberId] in
/-- A consumer's target view is fixed once its direct providers' phases are
fixed and the registry and retirement set agree. -/
theorem targetView_eq_of_priority_phases_eq
    {s t : Core.State FiberId Key} {consumer : FiberId}
    (hregistered : t.registered = s.registered)
    (hretired : t.retired = s.retired)
    (hconsumer : consumer ∈ s.registered)
    (hphase : ∀ providerId,
      Core.PriorityOn spec s.registered providerId consumer →
        t.phase providerId = s.phase providerId) :
    Core.targetView spec t consumer = Core.targetView spec s consumer := by
  classical
  have hprovider : ∀ key, key ∈ (spec consumer).deps →
      Core.provider spec t key = Core.provider spec s key := by
    intro key hkey
    exact provider_eq_of_priority_phases_eq hregistered hconsumer hkey hphase
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
  have hready : Core.TargetReady spec t consumer ↔
      Core.TargetReady spec s consumer := by
    simp only [Core.TargetReady, hregistered, hretired, hdependencies]
  by_cases hs : Core.TargetReady spec s consumer
  · have ht : Core.TargetReady spec t consumer := hready.mpr hs
    have hs' : consumer ∈ s.registered ∧ consumer ∉ s.retired ∧
        Core.dependenciesSatisfied spec s consumer := by
      simpa [Core.TargetReady] using hs
    have ht' : consumer ∈ t.registered ∧ consumer ∉ t.retired ∧
        Core.dependenciesSatisfied spec t consumer := by
      simpa [Core.TargetReady] using ht
    simp only [Core.targetView, dif_pos ht', dif_pos hs']
    congr 1
    funext key
    by_cases hkey : key ∈ (spec consumer).deps
    · simp [hkey, hprovider key hkey]
    · simp [hkey]
  · have ht : ¬ Core.TargetReady spec t consumer := fun h => hs (hready.mp h)
    have hs' : ¬(consumer ∈ s.registered ∧ consumer ∉ s.retired ∧
        Core.dependenciesSatisfied spec s consumer) := by
      simpa [Core.TargetReady] using hs
    have ht' : ¬(consumer ∈ t.registered ∧ consumer ∉ t.retired ∧
        Core.dependenciesSatisfied spec t consumer) := by
      simpa [Core.TargetReady] using ht
    simp only [Core.targetView, dif_neg ht', dif_neg hs']

omit [Fintype FiberId] in
/-- At a quiet fiber, equality of target views determines equality of phases. -/
theorem quiet_phase_eq_of_targetView_eq
    {s t : Core.State FiberId Key} {fiber : FiberId}
    (quietS : Core.quiet spec s) (quietT : Core.quiet spec t)
    (htarget : Core.targetView spec t fiber = Core.targetView spec s fiber) :
    t.phase fiber = s.phase fiber := by
  have hs := quietS fiber
  have ht := quietT fiber
  cases hsp : s.phase fiber <;> cases htp : t.phase fiber <;>
    simp [Core.LocallyQuiet, hsp, htp] at hs ht <;> simp_all

/-- Quiet Core endpoints with the same frozen registry and retirement set are
identical.  The proof derives the provider-first induction order from the
explicit priority acyclicity hypothesis; no confluence property is assumed by
`WellFormed`. -/
theorem core_quiet_eq_of_same_frozen
    {s t : Core.State FiberId Key}
    (wfS : Core.WellFormed spec s) (wfT : Core.WellFormed spec t)
    (acyclicS : Core.PriorityAcyclic spec s)
    (quietS : Core.quiet spec s) (quietT : Core.quiet spec t)
    (hregistered : t.registered = s.registered)
    (hretired : t.retired = s.retired) : t = s := by
  have providerFirst : WellFounded (Core.PriorityOn spec s.registered) := by
    have reversed := wellFounded_swap_of_finite acyclicS
    have hrelation : Function.swap (Core.PrioritySuccOn spec s.registered) =
        Core.PriorityOn spec s.registered := by
      rfl
    rw [hrelation] at reversed
    exact reversed
  have hphase : ∀ fiber, t.phase fiber = s.phase fiber := fun root =>
    providerFirst.induction root (C := fun fiber => t.phase fiber = s.phase fiber)
      (fun fiber ih => by
        by_cases hfiber : fiber ∈ s.registered
        · have htarget := targetView_eq_of_priority_phases_eq
            hregistered hretired hfiber (fun providerId hedge => ih providerId hedge)
          exact quiet_phase_eq_of_targetView_eq quietS quietT htarget
        · have hfiberT : fiber ∉ t.registered := by
            simpa [hregistered] using hfiber
          rw [wfT.unregistered_inactive fiber hfiberT,
            wfS.unregistered_inactive fiber hfiber])
  cases s with
  | mk registeredS phaseS retiredS =>
      cases t with
      | mk registeredT phaseT retiredT =>
          dsimp at hregistered hretired hphase ⊢
          subst registeredT
          subst retiredT
          have : phaseT = phaseS := funext hphase
          subst phaseT
          rfl

omit [Fintype FiberId] in
/-- Well-formedness is invariant along every finite Core reduction. -/
theorem core_reflTransGen_preserves_wellFormed
    {s t : Core.State FiberId Key}
    (wf : Core.WellFormed spec s)
    (reach : Relation.ReflTransGen (Core.Step spec) s t) :
    Core.WellFormed spec t := by
  induction reach with
  | refl => exact wf
  | tail reach step ih => exact Core.Step.preserve_wellFormed ih step

omit [Fintype FiberId] in
/-- The registry is frozen along every finite Core reduction. -/
theorem core_reflTransGen_registered_eq
    {s t : Core.State FiberId Key}
    (reach : Relation.ReflTransGen (Core.Step spec) s t) :
    t.registered = s.registered := by
  induction reach with
  | refl => rfl
  | tail reach step ih => exact (Core.Step.registered_eq spec step).trans ih

omit [Fintype FiberId] in
/-- The retirement set is frozen along every finite Core reduction. -/
theorem core_reflTransGen_retired_eq
    {s t : Core.State FiberId Key}
    (reach : Relation.ReflTransGen (Core.Step spec) s t) :
    t.retired = s.retired := by
  induction reach with
  | refl => rfl
  | tail reach step ih => exact (Core.Step.retired_eq spec step).trans ih

omit [Fintype FiberId] in
/-- Priority acyclicity is invariant along every finite Core reduction. -/
theorem core_reflTransGen_preserves_acyclic
    {s t : Core.State FiberId Key}
    (acyclic : Core.PriorityAcyclic spec s)
    (reach : Relation.ReflTransGen (Core.Step spec) s t) :
    Core.PriorityAcyclic spec t := by
  have hregistered := core_reflTransGen_registered_eq reach
  simpa [Core.PriorityAcyclic, hregistered] using acyclic

/-- Any two Core reductions from a well-formed acyclic root can be extended to
the same quiet endpoint.  This is the arbitrary-depth join construction used
for the dependent `finish`/`leave` cascades. -/
theorem core_reductions_join_to_quiet
    {root left right : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (leftReach : Relation.ReflTransGen (Core.Step spec) root left)
    (rightReach : Relation.ReflTransGen (Core.Step spec) root right) :
    ∃ join,
      Relation.ReflTransGen (Core.Step spec) left join ∧
      Relation.ReflTransGen (Core.Step spec) right join ∧
      Core.quiet spec join := by
  have wfLeft := core_reflTransGen_preserves_wellFormed wf leftReach
  have wfRight := core_reflTransGen_preserves_wellFormed wf rightReach
  have acyclicLeft := core_reflTransGen_preserves_acyclic acyclic leftReach
  have acyclicRight := core_reflTransGen_preserves_acyclic acyclic rightReach
  rcases Core.exists_quiet_reachable wfLeft acyclicLeft with
    ⟨quietLeft, leftQuietReach, quietLeftProof⟩
  rcases Core.exists_quiet_reachable wfRight acyclicRight with
    ⟨quietRight, rightQuietReach, quietRightProof⟩
  have wfQuietLeft := core_reflTransGen_preserves_wellFormed wfLeft leftQuietReach
  have wfQuietRight := core_reflTransGen_preserves_wellFormed wfRight rightQuietReach
  have quietLeftRegistered : quietLeft.registered = root.registered :=
    (core_reflTransGen_registered_eq leftQuietReach).trans
      (core_reflTransGen_registered_eq leftReach)
  have quietRightRegistered : quietRight.registered = root.registered :=
    (core_reflTransGen_registered_eq rightQuietReach).trans
      (core_reflTransGen_registered_eq rightReach)
  have quietLeftRetired : quietLeft.retired = root.retired :=
    (core_reflTransGen_retired_eq leftQuietReach).trans
      (core_reflTransGen_retired_eq leftReach)
  have quietRightRetired : quietRight.retired = root.retired :=
    (core_reflTransGen_retired_eq rightQuietReach).trans
      (core_reflTransGen_retired_eq rightReach)
  have quietEq : quietRight = quietLeft := core_quiet_eq_of_same_frozen
    wfQuietLeft wfQuietRight
    (core_reflTransGen_preserves_acyclic acyclic
      (leftReach.trans leftQuietReach))
    quietLeftProof quietRightProof
    (quietRightRegistered.trans quietLeftRegistered.symm)
    (quietRightRetired.trans quietLeftRetired.symm)
  subst quietRight
  exact ⟨quietLeft, leftQuietReach, rightQuietReach, quietLeftProof⟩

/-- Every one-step Core peak at a well-formed acyclic root is joinable. -/
theorem core_step_peak_joinable
    {root leftState rightState : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (leftStep : Core.Step spec root leftState)
    (rightStep : Core.Step spec root rightState) :
    Joinable (Core.Step spec) leftState rightState := by
  rcases core_reductions_join_to_quiet wf acyclic
      (.single leftStep) (.single rightStep) with
    ⟨join, leftReach, rightReach, _⟩
  exact ⟨join, leftReach, rightReach⟩

/-- Named forward-priority dependent-peak join: the provider acts on the left
and its direct consumer acts on the right. -/
theorem provider_consumer_stepAt_joinable
    {root providerState consumerState : Core.State FiberId Key}
    {providerId consumerId : FiberId}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (_priority : Core.Priority spec root providerId consumerId)
    (providerStep : Core.StepAt spec providerId root providerState)
    (consumerStep : Core.StepAt spec consumerId root consumerState) :
    Joinable (Core.Step spec) providerState consumerState :=
  core_step_peak_joinable wf acyclic
    ⟨providerId, providerStep⟩ ⟨consumerId, consumerStep⟩

/-- Named reverse-priority dependent-peak join: the consumer acts on the left
and its direct provider acts on the right. -/
theorem consumer_provider_stepAt_joinable
    {root consumerState providerState : Core.State FiberId Key}
    {consumerId providerId : FiberId}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (priority : Core.Priority spec root providerId consumerId)
    (consumerStep : Core.StepAt spec consumerId root consumerState)
    (providerStep : Core.StepAt spec providerId root providerState) :
    Joinable (Core.Step spec) consumerState providerState := by
  rcases provider_consumer_stepAt_joinable wf acyclic priority
      providerStep consumerStep with ⟨join, providerReach, consumerReach⟩
  exact ⟨join, consumerReach, providerReach⟩

/-- Both orientations of every distinct Priority-related actor peak are
joinable.  Constructor cases of the two `StepAt` derivations are unrestricted,
so this single theorem covers the complete five-by-five rule matrix. -/
theorem priority_related_stepAt_joinable
    {root leftState rightState : Core.State FiberId Key}
    {left right : FiberId}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (leftStep : Core.StepAt spec left root leftState)
    (rightStep : Core.StepAt spec right root rightState)
    (related : CorePriorityRelated spec root left right) :
    Joinable (Core.Step spec) leftState rightState := by
  rcases related.2 with priority | priority
  · exact provider_consumer_stepAt_joinable wf acyclic priority leftStep rightStep
  · exact consumer_provider_stepAt_joinable wf acyclic priority leftStep rightStep

/-- Mechanical exhaustive classification of all actor-labelled one-step Core
peaks.  Each of the three disjoint broad classes carries its join witness. -/
theorem core_stepAt_peak_classification
    {root leftState rightState : Core.State FiberId Key}
    {left right : FiberId}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (leftStep : Core.StepAt spec left root leftState)
    (rightStep : Core.StepAt spec right root rightState) :
    (left = right ∧ Joinable (Core.Step spec) leftState rightState) ∨
      (CoreIndependent spec root left right ∧
        Joinable (Core.Step spec) leftState rightState) ∨
      (CorePriorityRelated spec root left right ∧
        Joinable (Core.Step spec) leftState rightState) := by
  rcases core_actor_pair_partition (spec := spec) root left right with
    hsame | hindependent | hrelated
  · subst right
    have hstates := stepAt_deterministic leftStep rightStep
    subst rightState
    exact Or.inl ⟨rfl, leftState, .refl, .refl⟩
  · exact Or.inr (Or.inl ⟨hindependent,
      steps_on_independent_fibers_commute wf leftStep rightStep hindependent⟩)
  · exact Or.inr (Or.inr ⟨hrelated,
      priority_related_stepAt_joinable wf acyclic leftStep rightStep hrelated⟩)

/-- Full Core local confluence at every well-formed acyclic state. -/
theorem core_local_confluent_at
    {root : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root) :
    ∀ ⦃left right⦄,
      Core.Step spec root left → Core.Step spec root right →
      Joinable (Core.Step spec) left right := by
  intro left right leftStep rightStep
  exact core_step_peak_joinable wf acyclic leftStep rightStep

/-- The invariant package used to apply global Newman without asserting facts
about malformed or cyclic Core states. -/
def CoreConfluentState (spec : FiberId → Core.Spec Key)
    (state : Core.State FiberId Key) : Prop :=
  Core.WellFormed spec state ∧ Core.PriorityAcyclic spec state

/-- Core reduction restricted only at its source to the proved invariant. -/
def ConfluentCoreStep (spec : FiberId → Core.Spec Key)
    (source target : Core.State FiberId Key) : Prop :=
  CoreConfluentState spec source ∧ Core.Step spec source target

omit [Fintype FiberId] in
/-- A restricted Core step preserves the invariant package. -/
theorem confluentCoreStep_preserves
    {source target : Core.State FiberId Key}
    (step : ConfluentCoreStep spec source target) :
    CoreConfluentState spec target := by
  refine ⟨Core.Step.preserve_wellFormed step.1.1 step.2, ?_⟩
  have hregistered := Core.Step.registered_eq spec step.2
  simpa [Core.PriorityAcyclic, hregistered] using step.1.2

omit [Fintype FiberId] in
/-- Lift a Core reduction from a valid root to the invariant-restricted
relation used by Newman. -/
theorem core_reflTransGen_lift_confluent
    {source target : Core.State FiberId Key}
    (valid : CoreConfluentState spec source)
    (reach : Relation.ReflTransGen (Core.Step spec) source target) :
    Relation.ReflTransGen (ConfluentCoreStep spec) source target := by
  induction reach with
  | refl => exact .refl
  | tail reach step ih =>
      have validMiddle : CoreConfluentState spec _ :=
        ⟨core_reflTransGen_preserves_wellFormed valid.1 reach,
          core_reflTransGen_preserves_acyclic valid.2 reach⟩
      exact ih.tail ⟨validMiddle, step⟩

omit [Fintype FiberId] in
/-- Forget the invariant evidence from a restricted Core reduction. -/
theorem confluent_reflTransGen_to_core
    {source target : Core.State FiberId Key}
    (reach : Relation.ReflTransGen (ConfluentCoreStep spec) source target) :
    Relation.ReflTransGen (Core.Step spec) source target := by
  apply Relation.ReflTransGen.mono
      (r := ConfluentCoreStep spec) (p := Core.Step spec)
  · intro _ _ step
    exact step.2
  · exact reach

/-- The invariant-restricted Core relation is globally well-founded. -/
theorem confluentCoreStep_terminates :
    WellFounded (fun child parent : Core.State FiberId Key =>
      ConfluentCoreStep spec parent child) := by
  apply WellFounded.intro
  intro root
  by_cases valid : CoreConfluentState spec root
  · have termination := Core.lifecycle_terminates valid.1 valid.2
    induction termination with
    | intro state descendants ih =>
        apply Acc.intro state
        intro child step
        exact ih child step.2 (confluentCoreStep_preserves step)
  · apply Acc.intro root
    intro child step
    exact (valid step.1).elim

/-- The invariant-restricted Core relation is locally confluent. -/
theorem confluentCoreStep_local :
    LocalConfluent (ConfluentCoreStep spec) := by
  intro root left right leftStep rightStep
  have validRoot := leftStep.1
  rcases core_step_peak_joinable validRoot.1 validRoot.2
      leftStep.2 rightStep.2 with ⟨join, leftReach, rightReach⟩
  have validLeft := confluentCoreStep_preserves leftStep
  have validRight := confluentCoreStep_preserves rightStep
  exact ⟨join,
    core_reflTransGen_lift_confluent validLeft leftReach,
    core_reflTransGen_lift_confluent validRight rightReach⟩

/-- Newman's lemma gives global confluence of the invariant-restricted Core
relation. -/
theorem confluentCoreStep_confluent :
    Confluent (ConfluentCoreStep spec) :=
  newman confluentCoreStep_terminates confluentCoreStep_local

/-- **Strongest Core confluence theorem.** Every pair of finite Core
reductions from a well-formed acyclic root is joinable.  The proof lifts the
reductions to the invariant-restricted relation and applies Newman. -/
theorem core_confluent_at
    {root : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root) :
    ∀ ⦃left right⦄,
      Relation.ReflTransGen (Core.Step spec) root left →
      Relation.ReflTransGen (Core.Step spec) root right →
      Joinable (Core.Step spec) left right := by
  intro left right leftReach rightReach
  have valid : CoreConfluentState spec root := ⟨wf, acyclic⟩
  rcases confluentCoreStep_confluent
      (core_reflTransGen_lift_confluent valid leftReach)
      (core_reflTransGen_lift_confluent valid rightReach) with
    ⟨join, leftJoin, rightJoin⟩
  exact ⟨join, confluent_reflTransGen_to_core leftJoin,
    confluent_reflTransGen_to_core rightJoin⟩

/-- A Core normal form has no outgoing lifecycle step. -/
def CoreNormalForm (spec : FiberId → Core.Spec Key)
    (state : Core.State FiberId Key) : Prop :=
  ∀ next, ¬ Core.Step spec state next

omit [Fintype FiberId] in
/-- Quiet Core states have no outgoing step, without any invariant
hypothesis. -/
theorem core_quiet_is_normal
    {state : Core.State FiberId Key}
    (quiet : Core.quiet spec state) : CoreNormalForm spec state := by
  intro next step
  rcases step with ⟨actor, actorStep⟩
  have localQuiet := quiet actor
  cases actorStep <;> simp_all [Core.LocallyQuiet]

omit [Fintype FiberId] in
/-- On well-formed acyclic states, quietness is exactly normality. -/
theorem core_quiet_iff_normal
    {state : Core.State FiberId Key}
    (wf : Core.WellFormed spec state)
    (acyclic : Core.PriorityAcyclic spec state) :
    Core.quiet spec state ↔ CoreNormalForm spec state := by
  constructor
  · exact core_quiet_is_normal
  · intro normal
    apply Core.no_lifecycle_deadlock wf acyclic
    rintro ⟨next, step⟩
    exact normal next step

/-- Reachable Core normal forms are unique. -/
theorem core_unique_normal_form
    {root left right : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root)
    (leftReach : Relation.ReflTransGen (Core.Step spec) root left)
    (rightReach : Relation.ReflTransGen (Core.Step spec) root right)
    (leftNormal : CoreNormalForm spec left)
    (rightNormal : CoreNormalForm spec right) : left = right := by
  rcases core_confluent_at wf acyclic leftReach rightReach with
    ⟨join, leftJoin, rightJoin⟩
  have joinEqLeft : join = left :=
    (Relation.reflTransGen_iff_eq leftNormal).mp leftJoin
  have joinEqRight : join = right :=
    (Relation.reflTransGen_iff_eq rightNormal).mp rightJoin
  exact joinEqLeft.symm.trans joinEqRight

/-- Every well-formed acyclic Core root has a unique reachable quiet normal
form. -/
theorem core_existsUnique_quiet_normal_form
    {root : Core.State FiberId Key}
    (wf : Core.WellFormed spec root)
    (acyclic : Core.PriorityAcyclic spec root) :
    ∃! quietState,
      Relation.ReflTransGen (Core.Step spec) root quietState ∧
      Core.quiet spec quietState := by
  rcases Core.exists_quiet_reachable wf acyclic with
    ⟨quietState, reach, quiet⟩
  refine ⟨quietState, ⟨reach, quiet⟩, ?_⟩
  intro other ⟨otherReach, otherQuiet⟩
  exact core_unique_normal_form wf acyclic otherReach reach
    (core_quiet_is_normal otherQuiet) (core_quiet_is_normal quiet)

end Cordis.Extended
