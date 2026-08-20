import Cordis.Effects

namespace Cordis.Examples

open Cordis

def increment : Effects.WitnessedEffect Nat where
  run n := (n + 1, Nat.pred)
  witness n := by simp [Effects.RawEffect.Witnessed]

def twiceResult : Nat × Effects.Accumulator Nat :=
  Effects.runProgram [increment, increment] 0 Effects.identityAccumulator

example : twiceResult.1 = 2 := by native_decide

example : Effects.recover twiceResult.2 twiceResult.1 = 0 := by native_decide

#eval twiceResult.1
#eval Effects.recover twiceResult.2 twiceResult.1

end Cordis.Examples
