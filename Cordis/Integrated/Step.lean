import Cordis.Integrated.Basic

/-!
# Cordis.Integrated.Step

`iter` is the sole world-changing forward rule and is a Core stutter.  `unload`
applies the accumulated inverse after the ordinary Core unload guard opens.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}
variable [DecidableEq FiberId] [DecidableEq Key]
variable (spec : FiberId → Core.Spec Key)
variable (program : FiberId → List (Effects.WitnessedEffect Γ))

inductive StepAt (p : FiberId) : State FiberId Key Γ → State FiberId Key Γ → Prop
  | begin {s v} :
      s.phase p = .inactive →
      Core.targetView spec (erase s) p = some v →
      StepAt p s (s.setPhase p (.reloading v (program p) Effects.identityAccumulator))
  | iter {s v effect rest acc next} :
      s.phase p = .reloading v (effect :: rest) acc →
      Core.targetView spec (erase s) p = some v →
      Effects.track effect s.world acc = next →
      StepAt p s ((s.setPhase p (.reloading v rest next.2)).setWorld next.1)
  | finish {s v acc} :
      s.phase p = .reloading v [] acc →
      Core.targetView spec (erase s) p = some v →
      StepAt p s (s.setPhase p (.active v acc))
  | divert {s v remaining acc} :
      s.phase p = .reloading v remaining acc →
      Core.targetView spec (erase s) p = none →
      StepAt p s (s.setPhase p (.unloading v acc))
  | leave {s v acc} :
      s.phase p = .active v acc →
      Core.targetView spec (erase s) p = none →
      StepAt p s (s.setPhase p (.unloading v acc))
  | unload {s v acc} :
      s.phase p = .unloading v acc →
      Core.unloadable (erase s) p →
      StepAt p s ((s.setPhase p .inactive).setWorld (Effects.recover acc s.world))

def Step (s t : State FiberId Key Γ) : Prop :=
  ∃ p, StepAt spec program p s t

namespace StepAt

theorem registered_eq {p : FiberId} {s t : State FiberId Key Γ}
    (h : StepAt spec program p s t) : t.registered = s.registered := by
  cases h <;> rfl

theorem retired_eq {p : FiberId} {s t : State FiberId Key Γ}
    (h : StepAt spec program p s t) : t.retired = s.retired := by
  cases h <;> rfl

/-- **Integrated theorem.** Iteration changes only effect data and therefore
stutters under Core erasure. -/
theorem iter_erases_to_stutter {p : FiberId} {s : State FiberId Key Γ}
    {v : Core.View Key FiberId} {effect : Effects.WitnessedEffect Γ}
    {rest : List (Effects.WitnessedEffect Γ)} {acc : Effects.Accumulator Γ}
    {next : Γ × Effects.Accumulator Γ}
    (hp : s.phase p = .reloading v (effect :: rest) acc) :
    erase ((s.setPhase p (.reloading v rest next.2)).setWorld next.1) = erase s := by
  rw [erase_setWorld, erase_setPhase]
  apply core_setPhase_eq_self
  change erasePhase (s.phase p) = .reloading v
  rw [hp]
  rfl

/-- Every integrated rule is either a Core stutter or exactly the corresponding
Core lifecycle step. -/
theorem project {p : FiberId} {s t : State FiberId Key Γ}
    (h : StepAt spec program p s t) :
    erase t = erase s ∨ Core.StepAt spec p (erase s) (erase t) := by
  cases h with
  | begin hp ht =>
      right
      have hpCore := congrArg erasePhase hp
      change (erase s).phase p = .inactive at hpCore
      simpa [erasePhase] using Core.StepAt.begin hpCore ht
  | iter hp ht htrack =>
      left
      exact iter_erases_to_stutter hp
  | finish hp ht =>
      right
      have hpCore := congrArg erasePhase hp
      change (erase s).phase p = _ at hpCore
      simpa [erasePhase] using Core.StepAt.finish hpCore ht
  | divert hp ht =>
      right
      have hpCore := congrArg erasePhase hp
      change (erase s).phase p = _ at hpCore
      simpa [erasePhase] using Core.StepAt.divert hpCore ht
  | leave hp ht =>
      right
      have hpCore := congrArg erasePhase hp
      change (erase s).phase p = _ at hpCore
      simpa [erasePhase] using Core.StepAt.leave hpCore ht
  | unload hp hu =>
      right
      have hpCore := congrArg erasePhase hp
      change (erase s).phase p = _ at hpCore
      simpa [erasePhase] using Core.StepAt.unload hpCore hu

end StepAt

namespace Step

/-- **Integrated theorem.** Core well-formedness is invariant under integrated
steps; the proof factors entirely through the frozen Core preservation theorem. -/
theorem preserve_coreWellFormed {s t : State FiberId Key Γ}
    (wf : CoreWellFormed spec s) (h : Step spec program s t) :
    CoreWellFormed spec t := by
  rcases h with ⟨p, hp⟩
  rcases hp.project with hstutter | hcore
  · simpa [CoreWellFormed, hstutter] using wf
  · exact Core.Step.preserve_wellFormed wf ⟨p, hcore⟩

end Step

end Cordis.Integrated
