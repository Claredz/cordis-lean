import Cordis.Effects.Basic

/-!
# Cordis.Effects.Program

Finite programs thread a shared world together with an accumulated LIFO undo.
-/

namespace Cordis.Effects

universe u

variable {Γ : Type u}

def runProgram : List (WitnessedEffect Γ) → Γ → Accumulator Γ →
    Γ × Accumulator Γ
  | [], γ, acc => (γ, acc)
  | effect :: rest, γ, acc =>
      let next := track effect γ acc
      runProgram rest next.1 next.2

def Sound (origin current : Γ) (acc : Accumulator Γ) : Prop :=
  recover acc current = origin

/-- **Effects theorem.** One tracked step preserves the accumulator invariant. -/
theorem soundnessInvariant_preserved (effect : WitnessedEffect Γ)
    (origin current : Γ) (acc : Accumulator Γ)
    (h : Sound origin current acc) :
    Sound origin (track effect current acc).1 (track effect current acc).2 := by
  unfold Sound
  rw [recover_track]
  exact h

/-- **Effects theorem.** A finite program preserves the meaning of its incoming
accumulator. -/
theorem runProgram_accumulator_correct (program : List (WitnessedEffect Γ))
    (γ : Γ) (acc : Accumulator Γ) :
    recover (runProgram program γ acc).2 (runProgram program γ acc).1 =
      recover acc γ := by
  induction program generalizing γ acc with
  | nil => rfl
  | cons effect rest ih =>
      simp only [runProgram]
      rw [ih]
      exact recover_track effect γ acc

/-- **Effects theorem.** Running a finite program and applying its accumulated
inverse returns exactly to the initial world. -/
theorem reverse_runProgram_exact (program : List (WitnessedEffect Γ)) (γ : Γ) :
    recover (runProgram program γ identityAccumulator).2
      (runProgram program γ identityAccumulator).1 = γ := by
  rw [runProgram_accumulator_correct]
  rfl

/-- **Effects theorem.** Every executed finite prefix can be rolled back exactly. -/
theorem rollback_prefix_exact (program : List (WitnessedEffect Γ))
    (prefixLength : Nat) (γ : Γ) :
    recover (runProgram (program.take prefixLength) γ identityAccumulator).2
      (runProgram (program.take prefixLength) γ identityAccumulator).1 = γ :=
  reverse_runProgram_exact (program.take prefixLength) γ

end Cordis.Effects
