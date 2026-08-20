import Cordis.Integrated.Rollback
import Cordis.Effects.Independence

/-!
# Cordis.Integrated.Interleaving

A tagged trace represents arbitrary interleaving between one fiber (`Sum.inl`)
and all other world-changing effect iterations (`Sum.inr`).  Selective execution
tracks only the first fiber's inverses.  Under the explicit paper-style
independence hypothesis, unloading deletes exactly those tagged iterations.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {Γ : Type u}

abbrev EffectInterleaving (Γ : Type u) :=
  List (Sum (Effects.WitnessedEffect Γ) (Effects.WitnessedEffect Γ))

def ownProgram : EffectInterleaving Γ → List (Effects.WitnessedEffect Γ)
  | [] => []
  | .inl effect :: rest => effect :: ownProgram rest
  | .inr _ :: rest => ownProgram rest

def otherProgram : EffectInterleaving Γ → List (Effects.WitnessedEffect Γ)
  | [] => []
  | .inl _ :: rest => otherProgram rest
  | .inr effect :: rest => effect :: otherProgram rest

def runForwards : List (Effects.WitnessedEffect Γ) → Γ → Γ
  | [], world => world
  | effect :: rest, world => runForwards rest (Effects.forward effect world)

def runSelective : EffectInterleaving Γ → Γ → Effects.Accumulator Γ →
    Γ × Effects.Accumulator Γ
  | [], world, acc => (world, acc)
  | .inl effect :: rest, world, acc =>
      let next := Effects.track effect world acc
      runSelective rest next.1 next.2
  | .inr effect :: rest, world, acc =>
      runSelective rest (Effects.forward effect world) acc

def AccumulatorCommutesWith (acc : Effects.Accumulator Γ)
    (effect : Effects.WitnessedEffect Γ) : Prop :=
  Function.Commute acc (Effects.forward effect)

theorem identityAccumulator_commutes (effect : Effects.WitnessedEffect Γ) :
    AccumulatorCommutesWith Effects.identityAccumulator effect := by
  intro world
  rfl

theorem track_accumulator_commutes
    (own other : Effects.WitnessedEffect Γ) (world : Γ)
    (acc : Effects.Accumulator Γ)
    (hacc : AccumulatorCommutesWith acc other)
    (hindependent : Effects.IndependentEffects own other) :
    AccumulatorCommutesWith (Effects.track own world acc).2 other := by
  intro final
  simp only [Effects.track, AccumulatorCommutesWith, Function.Commute,
    Effects.forward, Effects.inverseAt]
  change acc (Effects.inverseAt own world (Effects.forward other final)) =
    Effects.forward other (acc (Effects.inverseAt own world final))
  rw [hindependent.left_undo_commutes_with_right]
  exact hacc _

private theorem selective_recovery_general
    (trace : EffectInterleaving Γ) (world : Γ) (acc : Effects.Accumulator Γ)
    (hpair : Effects.PairwiseIndependentPrograms
      (ownProgram trace) (otherProgram trace))
    (hacc : ∀ effect ∈ otherProgram trace,
      AccumulatorCommutesWith acc effect) :
    Effects.recover (runSelective trace world acc).2
        (runSelective trace world acc).1 =
      runForwards (otherProgram trace) (Effects.recover acc world) := by
  induction trace generalizing world acc with
  | nil => rfl
  | cons tagged rest ih =>
      cases tagged with
      | inl own =>
          simp only [runSelective, ownProgram, otherProgram]
          have hpairRest : Effects.PairwiseIndependentPrograms
              (ownProgram rest) (otherProgram rest) := by
            intro left hleft right hright
            exact hpair left (List.mem_cons_of_mem own hleft) right hright
          have haccTracked : ∀ other ∈ otherProgram rest,
              AccumulatorCommutesWith (Effects.track own world acc).2 other := by
            intro other hother
            apply track_accumulator_commutes own other world acc
            · exact hacc other hother
            · exact hpair own List.mem_cons_self other hother
          calc
            Effects.recover
                (runSelective rest (Effects.track own world acc).1
                  (Effects.track own world acc).2).2
                (runSelective rest (Effects.track own world acc).1
                  (Effects.track own world acc).2).1 =
                runForwards (otherProgram rest)
                  (Effects.recover (Effects.track own world acc).2
                    (Effects.track own world acc).1) :=
              ih _ _ hpairRest haccTracked
            _ = runForwards (otherProgram rest) (Effects.recover acc world) := by
              rw [Effects.recover_track]
      | inr other =>
          simp only [runSelective, ownProgram, otherProgram, runForwards]
          have hpairRest : Effects.PairwiseIndependentPrograms
              (ownProgram rest) (otherProgram rest) := by
            intro left hleft right hright
            exact hpair left hleft right (List.mem_cons_of_mem other hright)
          have haccRest : ∀ effect ∈ otherProgram rest,
              AccumulatorCommutesWith acc effect := by
            intro effect heffect
            exact hacc effect (List.mem_cons_of_mem other heffect)
          calc
            Effects.recover
                (runSelective rest (Effects.forward other world) acc).2
                (runSelective rest (Effects.forward other world) acc).1 =
                runForwards (otherProgram rest)
                  (Effects.recover acc (Effects.forward other world)) :=
              ih _ _ hpairRest haccRest
            _ = runForwards (otherProgram rest)
                  (Effects.forward other (Effects.recover acc world)) := by
              change runForwards (otherProgram rest)
                (acc (Effects.forward other world)) =
                runForwards (otherProgram rest) (Effects.forward other (acc world))
              rw [hacc other List.mem_cons_self]

/-- **Integrated theorem.** For an arbitrary finite interleaving, applying the
first fiber's accumulated inverse produces exactly the execution obtained by
deleting that fiber's effect iterations from the trace. -/
theorem unload_erases_own_effects
    (trace : EffectInterleaving Γ) (world : Γ)
    (hpair : Effects.PairwiseIndependentPrograms
      (ownProgram trace) (otherProgram trace)) :
    Effects.recover
        (runSelective trace world Effects.identityAccumulator).2
        (runSelective trace world Effects.identityAccumulator).1 =
      runForwards (otherProgram trace) world := by
  simpa [Effects.identityAccumulator, Effects.recover] using
    selective_recovery_general trace world Effects.identityAccumulator hpair
      (fun effect _ => identityAccumulator_commutes effect)

end Cordis.Integrated
