import Cordis.Effects.Program

/-!
# Cordis.Effects.Counterexamples

Checked witnesses showing why arbitrary candidate inverses cannot enter the
witnessed calculus.
-/

namespace Cordis.Effects.Counterexamples

open Cordis.Effects

def invalidIncrement : RawEffect Nat where
  run n := (n + 1, id)

/-- The candidate inverse fails already at input zero. -/
theorem invalid_inverse_not_witnessed : ¬ invalidIncrement.Witnessed := by
  intro h
  have atZero := h 0
  norm_num [invalidIncrement] at atZero

/-- Unchecked tracking with the same invalid inverse breaks recovery. -/
theorem invalid_inverse_breaks_accumulator :
    recover (trackRaw invalidIncrement 0 identityAccumulator).2
      (trackRaw invalidIncrement 0 identityAccumulator).1 ≠ 0 := by
  norm_num [trackRaw, invalidIncrement, recover, identityAccumulator]

end Cordis.Effects.Counterexamples
