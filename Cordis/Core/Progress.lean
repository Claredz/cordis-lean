import Cordis.Core.Safety

/-! # Core theorems: progress and lifecycle deadlock freedom -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Spec Key} {s : State FiberId Key}

/-- A fiber is locally normalized exactly when it is inactive with no target,
or active at its current target. -/
def LocallyQuiet (spec : FiberId → Spec Key) (s : State FiberId Key)
    (p : FiberId) : Prop :=
  match s.phase p with
  | .inactive => targetView spec s p = none
  | .active v => targetView spec s p = some v
  | .reloading _ | .unloading _ => False

/-- A Core quiet state contains no enabled lifecycle normalization work. -/
def quiet (spec : FiberId → Spec Key) (s : State FiberId Key) : Prop :=
  ∀ p, LocallyQuiet spec s p

private theorem target_none_of_unloading_committed
    (wf : WellFormed spec s) {providerId consumerId : FiberId}
    {providerView consumerView : View Key FiberId} {k : Key}
    (hp : s.phase providerId = .unloading providerView)
    (hc : committedView s consumerId = some consumerView)
    (hb : consumerView k = some providerId) :
    targetView spec s consumerId = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro target htarget
  have hkdep : k ∈ (spec consumerId).deps :=
    (wf.committed_covers consumerId consumerView hc k).mp ⟨providerId, hb⟩
  rcases (targetView_covers htarget k).mpr hkdep with ⟨q, hq⟩
  have hqvalid := (targetView_binding htarget hq).2
  have hpvalid := wf.committed_valid consumerId consumerView hc k providerId hb
  have hqp : q = providerId := by
    by_contra hne
    exact Finset.disjoint_left.mp
      (wf.singleSource hqvalid.1 hpvalid.1 hne) hqvalid.2.2 hpvalid.2.2
  subst q
  rcases hqvalid.2.1 with ⟨w, hw⟩
  rw [hp] at hw
  cases hw

/-- An unloading fiber, or a committed consumer downstream of it, can move.
The recursion follows provider-to-consumer Priority edges. -/
theorem unloading_has_step (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) {p : FiberId} {v : View Key FiberId}
    (hp : s.phase p = .unloading v) : ∃ s', Step spec s s' := by
  let motive : FiberId → Prop := fun p =>
    ∀ v, s.phase p = .unloading v → ∃ s', Step spec s s'
  have all : ∀ p, motive p := fun root =>
    acyclic.induction (C := motive) root (fun p ih => by
      intro v hp
      by_cases hu : unloadable s p
      · exact ⟨s.setPhase p .inactive, p, StepAt.unload hp hu⟩
      · have hrel : reliedUpon s p := Classical.byContradiction fun hn => hu hn
        rcases hrel with ⟨c, cv, k, hc, hb⟩
        have hedge : PrioritySucc spec s c p := committed_implies_priority wf hc hb
        have ht : targetView spec s c = none :=
          target_none_of_unloading_committed wf hp hc hb
        cases hphase : s.phase c with
        | inactive =>
            simp [committedView, hphase] at hc
        | reloading w =>
            exact ⟨s.setPhase c (.unloading w), c,
              StepAt.divert hphase ht⟩
        | active w =>
            exact ⟨s.setPhase c (.unloading w), c,
              StepAt.leave hphase ht⟩
        | unloading w =>
            exact ih c hedge w hphase)
  exact all p v hp

/-- Core theorem: a well-formed, acyclic, non-quiet state has a step. -/
theorem not_quiet_has_step (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) (hnq : ¬ quiet spec s) :
    ∃ s', Step spec s s' := by
  classical
  simp only [quiet, not_forall] at hnq
  rcases hnq with ⟨p, hp⟩
  cases hphase : s.phase p with
  | inactive =>
      cases ht : targetView spec s p with
      | none => exact (hp (by simp [LocallyQuiet, hphase, ht])).elim
      | some v => exact ⟨s.setPhase p (.reloading v), p, StepAt.begin hphase ht⟩
  | reloading v =>
      cases ht : targetView spec s p with
      | none => exact ⟨s.setPhase p (.unloading v), p, StepAt.divert hphase ht⟩
      | some w =>
          have hc : committedView s p = some v := by simp [committedView, hphase]
          have hw : w = v := targetView_eq_committed wf hc ht
          subst w
          exact ⟨s.setPhase p (.active v), p, StepAt.finish hphase ht⟩
  | active v =>
      cases ht : targetView spec s p with
      | none => exact ⟨s.setPhase p (.unloading v), p, StepAt.leave hphase ht⟩
      | some w =>
          have hc : committedView s p = some v := by simp [committedView, hphase]
          have hw : w = v := targetView_eq_committed wf hc ht
          subst w
          exact (hp (by simp [LocallyQuiet, hphase, ht])).elim
  | unloading v =>
      exact unloading_has_step wf acyclic hphase

/-- Core theorem: lifecycle deadlock freedom is the progress theorem stated in
negated terminal-state form. -/
theorem no_lifecycle_deadlock (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) :
    (¬ ∃ s', Step spec s s') → quiet spec s := by
  intro hnostep
  by_contra hnq
  exact hnostep (not_quiet_has_step wf acyclic hnq)

end Cordis.Core
