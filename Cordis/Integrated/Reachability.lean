import Cordis.Integrated.Termination

/-!
# Cordis.Integrated.Reachability

Finite effect programs do not merely terminate: whenever the Core projection
is non-quiet, some integrated rule is enabled.  Accessibility therefore yields
a finite integrated schedule whose Core projection is quiet.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}
variable [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]
variable (spec : FiberId → Core.Spec Key)
variable (program : FiberId → List (Effects.WitnessedEffect Γ))

private theorem phase_inactive_of_erase
    {s : State FiberId Key Γ} {p : FiberId}
    (h : (erase s).phase p = .inactive) : s.phase p = .inactive := by
  cases hp : s.phase p <;> simp [erasePhase, hp] at h ⊢

private theorem phase_reloading_of_erase
    {s : State FiberId Key Γ} {p : FiberId} {view : Core.View Key FiberId}
    (h : (erase s).phase p = .reloading view) :
    ∃ remaining accumulator,
      s.phase p = .reloading view remaining accumulator := by
  cases hp : s.phase p with
  | inactive => simp [erasePhase, hp] at h
  | reloading actual remaining accumulator =>
      have hview : actual = view := by simpa [erasePhase, hp] using h
      subst actual
      exact ⟨remaining, accumulator, rfl⟩
  | active actual accumulator => simp [erasePhase, hp] at h
  | unloading actual accumulator => simp [erasePhase, hp] at h

private theorem phase_active_of_erase
    {s : State FiberId Key Γ} {p : FiberId} {view : Core.View Key FiberId}
    (h : (erase s).phase p = .active view) :
    ∃ accumulator, s.phase p = .active view accumulator := by
  cases hp : s.phase p with
  | inactive => simp [erasePhase, hp] at h
  | reloading actual remaining accumulator => simp [erasePhase, hp] at h
  | active actual accumulator =>
      have hview : actual = view := by simpa [erasePhase, hp] using h
      subst actual
      exact ⟨accumulator, rfl⟩
  | unloading actual accumulator => simp [erasePhase, hp] at h

private theorem phase_unloading_of_erase
    {s : State FiberId Key Γ} {p : FiberId} {view : Core.View Key FiberId}
    (h : (erase s).phase p = .unloading view) :
    ∃ accumulator, s.phase p = .unloading view accumulator := by
  cases hp : s.phase p with
  | inactive => simp [erasePhase, hp] at h
  | reloading actual remaining accumulator => simp [erasePhase, hp] at h
  | active actual accumulator => simp [erasePhase, hp] at h
  | unloading actual accumulator =>
      have hview : actual = view := by simpa [erasePhase, hp] using h
      subst actual
      exact ⟨accumulator, rfl⟩

/-- Every enabled Core step has an enabled integrated refinement step.  A Core
`finish` is refined by `iter` while the finite program is nonempty. -/
theorem core_step_enables_integrated_step
    {s : State FiberId Key Γ} {coreNext : Core.State FiberId Key}
    (hcore : Core.Step spec (erase s) coreNext) :
    ∃ next, Step spec program s next := by
  rcases hcore with ⟨p, hp⟩
  cases hp with
  | begin hphase htarget =>
      have hi := phase_inactive_of_erase hphase
      exact ⟨s.setPhase p (.reloading _ (program p) Effects.identityAccumulator),
        p, StepAt.begin hi htarget⟩
  | finish hphase htarget =>
      rcases phase_reloading_of_erase hphase with
        ⟨remaining, accumulator, hp⟩
      cases remaining with
      | nil =>
          exact ⟨s.setPhase p (.active _ accumulator), p,
            StepAt.finish hp htarget⟩
      | cons effect rest =>
          let tracked := Effects.track effect s.world accumulator
          exact ⟨(s.setPhase p (.reloading _ rest tracked.2)).setWorld tracked.1,
            p, StepAt.iter hp htarget rfl⟩
  | divert hphase htarget =>
      rcases phase_reloading_of_erase hphase with
        ⟨remaining, accumulator, hp⟩
      exact ⟨s.setPhase p (.unloading _ accumulator), p,
        StepAt.divert hp htarget⟩
  | leave hphase htarget =>
      rcases phase_active_of_erase hphase with ⟨accumulator, hp⟩
      exact ⟨s.setPhase p (.unloading _ accumulator), p,
        StepAt.leave hp htarget⟩
  | unload hphase hunloadable =>
      rcases phase_unloading_of_erase hphase with ⟨accumulator, hp⟩
      exact ⟨(s.setPhase p .inactive).setWorld
          (Effects.recover accumulator s.world),
        p, StepAt.unload hp hunloadable⟩

/-- A non-quiet Core projection enables an integrated step. -/
theorem not_coreQuiet_has_step
    {s : State FiberId Key Γ}
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s))
    (hnq : ¬ Core.quiet spec (erase s)) :
    ∃ next, Step spec program s next := by
  rcases Core.not_quiet_has_step wf acyclic hnq with ⟨coreNext, hcore⟩
  exact core_step_enables_integrated_step spec program hcore

private theorem acc_reaches_coreQuiet
    {s : State FiberId Key Γ}
    (acc : Acc (fun next current => Step spec program current next) s)
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s)) :
    ∃ quietState,
      Relation.ReflTransGen (Step spec program) s quietState ∧
      Core.quiet spec (erase quietState) ∧
      CoreWellFormed spec quietState ∧
      Core.PriorityAcyclic spec (erase quietState) ∧
      quietState.registered = s.registered ∧
      quietState.retired = s.retired := by
  induction acc with
  | intro current descendants ih =>
      by_cases hquiet : Core.quiet spec (erase current)
      · exact ⟨current, .refl, hquiet, wf, acyclic, rfl, rfl⟩
      · rcases not_coreQuiet_has_step spec program wf acyclic hquiet with
          ⟨next, hstep⟩
        have wfNext := Step.preserve_coreWellFormed spec program wf hstep
        have hregistered : (erase next).registered = (erase current).registered := by
          rcases hstep with ⟨p, hp⟩
          exact hp.registered_eq
        have acyclicNext : Core.PriorityAcyclic spec (erase next) := by
          unfold Core.PriorityAcyclic at acyclic ⊢
          rw [hregistered]
          exact acyclic
        rcases ih next hstep wfNext acyclicNext with
          ⟨quietState, hreach, hquietState, wfQuiet, acyclicQuiet,
            hregisteredQuiet, hretiredQuiet⟩
        rcases hstep with ⟨p, hp⟩
        exact ⟨quietState, hreach.head ⟨p, hp⟩, hquietState, wfQuiet,
          acyclicQuiet, hregisteredQuiet.trans hp.registered_eq,
          hretiredQuiet.trans hp.retired_eq⟩

/-- The quiet endpoint returned by integrated normalization retains the frozen
Core invariant and registered-priority acyclicity. -/
theorem exists_coreQuiet_reachable_sound
    {s : State FiberId Key Γ}
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s)) :
    ∃ quietState,
      Relation.ReflTransGen (Step spec program) s quietState ∧
      Core.quiet spec (erase quietState) ∧
      CoreWellFormed spec quietState ∧
      Core.PriorityAcyclic spec (erase quietState) ∧
      quietState.registered = s.registered ∧
      quietState.retired = s.retired :=
  acc_reaches_coreQuiet spec program (lifecycle_terminates spec program wf acyclic)
    wf acyclic

/-- **Integrated theorem.** Every well-formed acyclic integrated state reaches
a state with quiet Core projection by a finite integrated schedule. -/
theorem exists_coreQuiet_reachable
    {s : State FiberId Key Γ}
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s)) :
    ∃ quietState,
      Relation.ReflTransGen (Step spec program) s quietState ∧
      Core.quiet spec (erase quietState) := by
  rcases exists_coreQuiet_reachable_sound spec program wf acyclic with
    ⟨quietState, hreach, hquiet, -, -, -, -⟩
  exact ⟨quietState, hreach, hquiet⟩

end Cordis.Integrated
