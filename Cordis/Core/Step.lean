import Cordis.Core.Basic

/-! # Cordis Core lifecycle rules -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable (spec : FiberId → Spec Key)

/-- Some installed consumer still retains a committed binding to `p`. -/
def reliedUpon (s : State FiberId Key) (p : FiberId) : Prop :=
  ∃ c v k, committedView s c = some v ∧ v k = some p

/-- The unloading guard. -/
def unloadable (s : State FiberId Key) (p : FiberId) : Prop :=
  ¬ reliedUpon s p

/-- The five Core lifecycle rules, factored by actor. -/
inductive StepAt (p : FiberId) : State FiberId Key → State FiberId Key → Prop
  | begin {s v} :
      s.phase p = .inactive →
      targetView spec s p = some v →
      StepAt p s (s.setPhase p (.reloading v))
  | finish {s v} :
      s.phase p = .reloading v →
      targetView spec s p = some v →
      StepAt p s (s.setPhase p (.active v))
  | divert {s v} :
      s.phase p = .reloading v →
      targetView spec s p = none →
      StepAt p s (s.setPhase p (.unloading v))
  | leave {s v} :
      s.phase p = .active v →
      targetView spec s p = none →
      StepAt p s (s.setPhase p (.unloading v))
  | unload {s v} :
      s.phase p = .unloading v →
      unloadable s p →
      StepAt p s (s.setPhase p .inactive)

/-- Unlabelled Core step. -/
def Step (s s' : State FiberId Key) : Prop :=
  ∃ p, StepAt spec p s s'

namespace StepAt

theorem registered_eq {p : FiberId} {s s' : State FiberId Key}
    (h : StepAt spec p s s') : s'.registered = s.registered := by
  cases h <;> rfl

theorem retired_eq {p : FiberId} {s s' : State FiberId Key}
    (h : StepAt spec p s s') : s'.retired = s.retired := by
  cases h <;> rfl

/-- A Core rule changes only its actor's lifecycle phase. -/
theorem other_fiber_eq {p q : FiberId} {s s' : State FiberId Key}
    (h : StepAt spec p s s') (hne : q ≠ p) : s'.phase q = s.phase q := by
  cases h <;> simp [State.setPhase, hne]

theorem actor_registered {p : FiberId} {s s' : State FiberId Key}
    (wf : WellFormed spec s) (h : StepAt spec p s s') : p ∈ s.registered := by
  cases h with
  | begin _ ht => exact (targetView_eq_some_iff.mp ht).1
  | finish hp _ | divert hp _ | leave hp _ | unload hp _ =>
      by_contra hn
      have hi := wf.unregistered_inactive p hn
      simp [hi] at hp

end StepAt

namespace Step

theorem registered_eq {s s' : State FiberId Key} (h : Step spec s s') :
    s'.registered = s.registered := by
  rcases h with ⟨p, hp⟩
  exact hp.registered_eq

theorem retired_eq {s s' : State FiberId Key} (h : Step spec s s') :
    s'.retired = s.retired := by
  rcases h with ⟨p, hp⟩
  exact hp.retired_eq

end Step

end Cordis.Core
