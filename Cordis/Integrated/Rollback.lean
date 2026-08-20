import Cordis.Integrated.Step

/-!
# Cordis.Integrated.Rollback

The exact theorem below concerns consecutive divert/unload steps, hence no
intervening world-changing action.  Interleaved selective erasure is kept
separate and requires explicit independence hypotheses.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}
variable [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Core.Spec Key}
variable {program : FiberId → List (Effects.WitnessedEffect Γ)}

/-- **Integrated theorem.** If a reloading state has a sound prefix
accumulator, consecutive divert and unload rules restore its Begin-time world. -/
theorem divert_then_unload_rolls_back_prefix
    {p : FiberId} {before during unloading after : State FiberId Key Γ}
    {v : Core.View Key FiberId} {remaining : List (Effects.WitnessedEffect Γ)}
    {acc : Effects.Accumulator Γ}
    (hphase : during.phase p = .reloading v remaining acc)
    (hsound : Effects.recover acc during.world = before.world)
    (hdivert : StepAt spec program p during unloading)
    (hunload : StepAt spec program p unloading after)
    (hdivertShape : Core.targetView spec (erase during) p = none)
    (hguard : Core.unloadable (erase unloading) p) :
    after.world = before.world := by
  have hdEq : unloading = during.setPhase p (.unloading v acc) := by
    cases hdivert <;> simp_all
  subst unloading
  cases hunload with
  | begin hp _ => simp at hp
  | iter hp _ _ => simp at hp
  | finish hp _ => simp at hp
  | divert hp _ => simp at hp
  | leave hp _ => simp at hp
  | unload hp _ =>
      simp only [State.setPhase_self] at hp
      cases hp
      simpa using hsound

/-- A direct finite-prefix calculation used by the lifecycle theorem: the
accumulator stored after any prefix restores the Begin-time world. -/
theorem executed_prefix_accumulator_exact
    (executed : List (Effects.WitnessedEffect Γ)) (world : Γ) :
    let result := Effects.runProgram executed world Effects.identityAccumulator
    Effects.recover result.2 result.1 = world := by
  exact Effects.reverse_runProgram_exact executed world

end Cordis.Integrated
