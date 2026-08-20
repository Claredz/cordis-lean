import Cordis.Core.Progress

/-! # Core theorem: termination by reverse-priority weights -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Spec Key} {s s' : State FiberId Key}

private theorem targetValid_setPhase_iff_of_not_provides
    (s : State FiberId Key) (actor q : FiberId) (ph : Phase Key FiberId) (k : Key)
    (hk : k ∉ (spec actor).provs) :
    TargetProviderValid spec (s.setPhase actor ph) q k ↔
      TargetProviderValid spec s q k := by
  by_cases hqa : q = actor
  · subst q
    simp [TargetProviderValid, hk]
  · simp [TargetProviderValid, active, State.setPhase_other s hqa ph]

private theorem provider_setPhase_of_not_provides
    (s : State FiberId Key) (actor : FiberId) (ph : Phase Key FiberId) (k : Key)
    (hk : k ∉ (spec actor).provs) :
    provider spec (s.setPhase actor ph) k = provider spec s k := by
  apply Option.ext
  intro q
  simp only [provider_eq_some_iff]
  constructor
  · rintro ⟨hq, hu⟩
    refine ⟨(targetValid_setPhase_iff_of_not_provides s actor q ph k hk).mp hq, ?_⟩
    intro r hr
    exact hu r ((targetValid_setPhase_iff_of_not_provides s actor r ph k hk).mpr hr)
  · rintro ⟨hq, hu⟩
    refine ⟨(targetValid_setPhase_iff_of_not_provides s actor q ph k hk).mpr hq, ?_⟩
    intro r hr
    exact hu r ((targetValid_setPhase_iff_of_not_provides s actor r ph k hk).mp hr)

private theorem targetReady_setPhase_iff_of_not_priority
    (s : State FiberId Key) (actor consumer : FiberId) (ph : Phase Key FiberId)
    (hactor : actor ∈ s.registered)
    (hnedge : ¬ Priority spec s actor consumer) :
    TargetReady spec (s.setPhase actor ph) consumer ↔ TargetReady spec s consumer := by
  by_cases hconsumer : consumer ∈ s.registered
  · constructor
    · rintro ⟨_, hnret, hs⟩
      refine ⟨hconsumer, by simpa using hnret, ?_⟩
      intro k hkdep
      rcases hs k hkdep with ⟨q, hq⟩
      have hkprov : k ∉ (spec actor).provs := by
        intro hk
        exact hnedge ⟨hactor, hconsumer, k, hk, hkdep⟩
      exact ⟨q, by simpa [provider_setPhase_of_not_provides s actor ph k hkprov] using hq⟩
    · rintro ⟨_, hnret, hs⟩
      refine ⟨by simpa using hconsumer, by simpa using hnret, ?_⟩
      intro k hkdep
      rcases hs k hkdep with ⟨q, hq⟩
      have hkprov : k ∉ (spec actor).provs := by
        intro hk
        exact hnedge ⟨hactor, hconsumer, k, hk, hkdep⟩
      exact ⟨q, by simpa [provider_setPhase_of_not_provides s actor ph k hkprov] using hq⟩
  · constructor <;> intro h
    · exact (hconsumer (by simpa [TargetReady] using h.1)).elim
    · exact (hconsumer h.1).elim

private theorem targetReady_actor_iff
    (acyclic : PriorityAcyclic spec s) {p : FiberId} (hpreg : p ∈ s.registered)
    {ph : Phase Key FiberId} :
    TargetReady spec (s.setPhase p ph) p ↔ TargetReady spec s p := by
  exact targetReady_setPhase_iff_of_not_priority s p p ph hpreg
    (acyclic.irrefl.irrefl p)

/-- Phase/target-sensitive local fuel. -/
noncomputable def localFuel (spec : FiberId → Spec Key)
    (s : State FiberId Key) (p : FiberId) : Nat :=
  by
    classical
    exact match s.phase p with
      | .inactive => if TargetReady spec s p then 3 else 0
      | .reloading _ => 2
      | .active _ => if TargetReady spec s p then 0 else 2
      | .unloading _ => if TargetReady spec s p then 4 else 1

/-- The uniform direct-consumer growth bound, derived from the local fuel
table.  It is three, rather than a preselected constant four. -/
def fuelGrowthBound : Nat := 3

private theorem localFuel_setPhase_nonconsumer
    (s : State FiberId Key) (actor q : FiberId) (ph : Phase Key FiberId)
    (hpq : q ≠ actor) (hactor : actor ∈ s.registered)
    (hnedge : ¬ Priority spec s actor q) :
    localFuel spec (s.setPhase actor ph) q = localFuel spec s q := by
  have hphase := State.setPhase_other s hpq ph
  have hready := targetReady_setPhase_iff_of_not_priority
    s actor q ph hactor hnedge
  simp only [localFuel, hphase]
  rw [propext hready]

private theorem localFuel_setPhase_growth
    (s : State FiberId Key) (actor q : FiberId) (ph : Phase Key FiberId)
    (hpq : q ≠ actor) :
    localFuel spec (s.setPhase actor ph) q ≤
      localFuel spec s q + fuelGrowthBound := by
  have hphase := State.setPhase_other s hpq ph
  by_cases hr : TargetReady spec s q <;>
    by_cases hr' : TargetReady spec (s.setPhase actor ph) q <;>
      cases hq : s.phase q <;>
        simp [localFuel, hq, hphase, hr, hr', fuelGrowthBound] <;> omega

/-- Three is minimal for the local fuel table: an inactive consumer becoming
target-ready changes from zero to three. -/
theorem fuelGrowthBound_minimal {b : Nat}
    (h : ∀ oldReady newReady : Bool,
      (if newReady then 3 else 0) ≤ (if oldReady then 3 else 0) + b) :
    fuelGrowthBound ≤ b := by
  simpa [fuelGrowthBound] using h false true

/-- Core termination lemma 1: the actor's local fuel strictly decreases. -/
theorem actor_fuel_decreases (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) {p : FiberId}
    (h : StepAt spec p s s') : localFuel spec s' p < localFuel spec s p := by
  have hpreg := StepAt.actor_registered spec wf h
  have readyEq : ∀ ph, TargetReady spec (s.setPhase p ph) p ↔ TargetReady spec s p :=
    fun ph => targetReady_actor_iff acyclic hpreg
  cases h with
  | begin hp ht =>
      have hr : TargetReady spec s p := targetView_isSome_iff_ready.mp (by simp [ht])
      simp only [localFuel, State.setPhase_self, hp, if_pos hr]
      try rw [if_pos ((readyEq _).mpr hr)]
      omega
  | finish hp ht =>
      have hr : TargetReady spec s p := targetView_isSome_iff_ready.mp (by simp [ht])
      simp only [localFuel, State.setPhase_self, hp, if_pos hr]
      rw [if_pos ((readyEq _).mpr hr)]
      omega
  | divert hp ht =>
      have hr : ¬ TargetReady spec s p := targetView_eq_none_iff_not_ready.mp ht
      simp only [localFuel, State.setPhase_self, hp, if_neg hr]
      rw [if_neg (fun hready => hr ((readyEq _).mp hready))]
      omega
  | leave hp ht =>
      have hr : ¬ TargetReady spec s p := targetView_eq_none_iff_not_ready.mp ht
      simp only [localFuel, State.setPhase_self, hp, if_neg hr]
      rw [if_neg (fun hready => hr ((readyEq _).mp hready))]
      omega
  | unload hp _ =>
      by_cases hr : TargetReady spec s p
      · simp only [localFuel, State.setPhase_self, hp, if_pos hr]
        rw [if_pos ((readyEq _).mpr hr)]
        omega
      ·
        simp only [localFuel, State.setPhase_self, hp, if_neg hr]
        rw [if_neg (fun hready => hr ((readyEq _).mp hready))]
        omega

/-- Core termination lemma 2: a non-consumer's local fuel is unchanged. -/
theorem nonconsumer_fuel_unchanged (wf : WellFormed spec s) {p q : FiberId}
    (h : StepAt spec p s s') (hpq : q ≠ p)
    (hnedge : ¬ Priority spec s p q) :
    localFuel spec s' q = localFuel spec s q := by
  have hpreg := StepAt.actor_registered spec wf h
  cases h <;> exact localFuel_setPhase_nonconsumer s p q _ hpq hpreg hnedge

/-- Core termination lemma 3: one consumer's local fuel can grow by at most
the derived uniform bound. -/
theorem consumer_fuel_growth_bounded {p q : FiberId}
    (h : StepAt spec p s s') (hpq : q ≠ p) :
    localFuel spec s' q ≤ localFuel spec s q + fuelGrowthBound := by
  cases h <;> exact localFuel_setPhase_growth s p q _ hpq

section Weights

variable [Fintype FiberId]

/-- Reverse-priority recursive weight.  The actor receives one more than the
maximum total growth budget of all direct consumers. -/
noncomputable def weight (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered)) (p : FiberId) : Nat := by
  classical
  exact acyclic.fix (fun p rec =>
    1 + ∑ q ∈ (Finset.univ.erase p),
      if hq : PrioritySuccOn spec registered q p then
        fuelGrowthBound * rec q hq else 0) p

noncomputable def consumerBudget (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered)) (p : FiberId) : Nat := by
  classical
  exact ∑ q ∈ (Finset.univ.erase p),
    if PriorityOn spec registered p q then
      fuelGrowthBound * weight registered acyclic q else 0

theorem weight_eq (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered)) (p : FiberId) :
    weight registered acyclic p = 1 + consumerBudget registered acyclic p := by
  classical
  rw [weight, WellFounded.fix_eq]
  rfl

theorem weight_positive (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered)) (p : FiberId) :
    0 < weight registered acyclic p := by
  rw [weight_eq]
  omega

theorem weight_dominates_consumers (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered)) (p : FiberId) :
    consumerBudget registered acyclic p < weight registered acyclic p := by
  rw [weight_eq]
  omega

/-- Global numeric termination measure. -/
noncomputable def lifecycleMeasure (registered : Finset FiberId)
    (acyclic : WellFounded (PrioritySuccOn spec registered))
    (t : State FiberId Key) : Nat :=
  ∑ p : FiberId, localFuel spec t p * weight registered acyclic p

/-- Core theorem: every step strictly decreases the reverse-priority measure. -/
theorem step_decreases_measure (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) (h : Step spec s s') :
    lifecycleMeasure s.registered acyclic s' < lifecycleMeasure s.registered acyclic s := by
  classical
  rcases h with ⟨p, hp⟩
  let w : FiberId → Nat := weight s.registered acyclic
  let oldTerm : FiberId → Nat := fun q => localFuel spec s q * w q
  let newTerm : FiberId → Nat := fun q => localFuel spec s' q * w q
  have hpreg := StepAt.actor_registered spec wf hp
  have hactor := actor_fuel_decreases wf acyclic hp
  have hactorMul : newTerm p + w p ≤ oldTerm p := by
    have hs : localFuel spec s' p + 1 ≤ localFuel spec s p := by omega
    have hm := Nat.mul_le_mul_right (w p) hs
    simpa [oldTerm, newTerm, Nat.add_mul] using hm
  have hrest :
      ∑ q ∈ (Finset.univ.erase p), newTerm q ≤
        (∑ q ∈ (Finset.univ.erase p), oldTerm q) +
          consumerBudget s.registered acyclic p := by
    calc
      _ ≤ ∑ q ∈ (Finset.univ.erase p),
          (oldTerm q + if Priority spec s p q then fuelGrowthBound * w q else 0) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
        by_cases hedge : Priority spec s p q
        · have hgrow := consumer_fuel_growth_bounded hp hqp
          have hm := Nat.mul_le_mul_right (w q) hgrow
          simpa [oldTerm, newTerm, hedge, Nat.add_mul, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm] using hm
        · have heq := nonconsumer_fuel_unchanged wf hp hqp hedge
          simp [oldTerm, newTerm, hedge, heq]
      _ = (∑ q ∈ (Finset.univ.erase p), oldTerm q) +
          consumerBudget s.registered acyclic p := by
        rw [Finset.sum_add_distrib]
        congr 1
  have hold : (∑ q ∈ Finset.univ.erase p, oldTerm q) + oldTerm p =
      ∑ q : FiberId, oldTerm q :=
    Finset.sum_erase_add Finset.univ oldTerm (Finset.mem_univ p)
  have hnew : (∑ q ∈ Finset.univ.erase p, newTerm q) + newTerm p =
      ∑ q : FiberId, newTerm q :=
    Finset.sum_erase_add Finset.univ newTerm (Finset.mem_univ p)
  have hdom : consumerBudget s.registered acyclic p < w p := by
    simpa [w] using weight_dominates_consumers s.registered acyclic p
  change (∑ q : FiberId, newTerm q) < ∑ q : FiberId, oldTerm q
  omega

/-- Core theorem: lifecycle normalization is accessible in the requested
orientation. -/
theorem lifecycle_terminates (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) :
    Acc (fun t' t => Step spec t t') s := by
  have hmeasure : ∀ ⦃t t'⦄,
      WellFormed spec t → t.registered = s.registered →
      Step spec t t' →
        lifecycleMeasure s.registered acyclic t' < lifecycleMeasure s.registered acyclic t := by
    intro t t' hwt hreg hstep
    have hac : PriorityAcyclic spec t := by
      simpa [PriorityAcyclic, hreg] using acyclic
    simpa [hreg] using step_decreases_measure hwt hac hstep
  let motive : State FiberId Key → Prop := fun t =>
    WellFormed spec t → t.registered = s.registered →
      Acc (fun t' t => Step spec t t') t
  have all : ∀ t, motive t := fun root =>
    (InvImage.wf (lifecycleMeasure s.registered acyclic) Nat.lt_wfRel.wf).induction
      (C := motive) root (fun t ih hwt hreg => by
        apply Acc.intro t
        intro t' hstep
        exact ih t' (hmeasure hwt hreg hstep)
          (Step.preserve_wellFormed hwt hstep) (hstep.registered_eq.trans hreg))
  exact all s wf rfl

end Weights

end Cordis.Core
