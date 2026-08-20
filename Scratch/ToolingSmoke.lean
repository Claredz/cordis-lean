import Mathlib

#check Relation.TransGen
#check Nat.add_comm

namespace ToolingSmoke

theorem add_comm (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b

end ToolingSmoke
