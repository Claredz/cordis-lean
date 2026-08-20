import Mathlib

/-!
# Cordis.Effects.Basic

An effect supplies the inverse that is valid at the point where the effect was
run.  No global injectivity, surjectivity, or two-sided inverse is assumed.
-/

namespace Cordis.Effects

universe u

variable {Γ : Type u}

structure RawEffect (Γ : Type u) where
  run : Γ → Γ × (Γ → Γ)

namespace RawEffect

def Witnessed (e : RawEffect Γ) : Prop :=
  ∀ γ, let result := e.run γ; result.2 result.1 = γ

end RawEffect

structure WitnessedEffect (Γ : Type u) extends RawEffect Γ where
  witness : toRawEffect.Witnessed

namespace WitnessedEffect

abbrev toRaw (e : WitnessedEffect Γ) : RawEffect Γ := e.toRawEffect

theorem undo_run (e : WitnessedEffect Γ) (γ : Γ) :
    (e.run γ).2 (e.run γ).1 = γ := by
  exact e.witness γ

end WitnessedEffect

abbrev Accumulator (Γ : Type u) := Γ → Γ

def identityAccumulator : Accumulator Γ := id

def recover (acc : Accumulator Γ) (γ : Γ) : Γ := acc γ

def track (e : WitnessedEffect Γ) (γ : Γ) (acc : Accumulator Γ) :
    Γ × Accumulator Γ :=
  let result := e.run γ
  (result.1, fun final => acc (result.2 final))

def trackRaw (e : RawEffect Γ) (γ : Γ) (acc : Accumulator Γ) :
    Γ × Accumulator Γ :=
  let result := e.run γ
  (result.1, fun final => acc (result.2 final))

/-- **Effects theorem.** Tracking one witnessed effect preserves recovery. -/
theorem recover_track (e : WitnessedEffect Γ) (γ : Γ) (acc : Accumulator Γ) :
    recover (track e γ acc).2 (track e γ acc).1 = recover acc γ := by
  simp only [track, recover]
  rw [e.undo_run]

def comp (first second : WitnessedEffect Γ) : WitnessedEffect Γ where
  run γ :=
    let firstResult := first.run γ
    let secondResult := second.run firstResult.1
    (secondResult.1, fun final => firstResult.2 (secondResult.2 final))
  witness γ := by
    dsimp
    rw [second.undo_run, first.undo_run]

/-- **Effects theorem.** Sequential composition remains witnessed. -/
theorem witnessed_comp (first second : WitnessedEffect Γ) :
    (comp first second).toRaw.Witnessed :=
  (comp first second).witness

end Cordis.Effects
