import Cordis.Effects.Program

/-!
# Cordis.Effects.Independence

These paper-style hypotheses are deliberately stronger than witnessed
reversibility.  They describe when effects belonging to different components
may be reordered or selectively erased.
-/

namespace Cordis.Effects

universe u

variable {Γ : Type u}

def forward (effect : WitnessedEffect Γ) (γ : Γ) : Γ :=
  (effect.run γ).1

def inverseAt (effect : WitnessedEffect Γ) (γ : Γ) : Γ → Γ :=
  (effect.run γ).2

structure IndependentEffects (left right : WitnessedEffect Γ) : Prop where
  transformations_commute : Function.Commute (forward left) (forward right)
  left_inverse_stable :
    ∀ γ final, inverseAt left (forward right γ) final = inverseAt left γ final
  right_inverse_stable :
    ∀ γ final, inverseAt right (forward left γ) final = inverseAt right γ final
  left_undo_commutes_with_right :
    ∀ γ final,
      inverseAt left γ (forward right final) =
        forward right (inverseAt left γ final)
  right_undo_commutes_with_left :
    ∀ γ final,
      inverseAt right γ (forward left final) =
        forward left (inverseAt right γ final)

def PairwiseIndependentPrograms (left right : List (WitnessedEffect Γ)) : Prop :=
  ∀ l ∈ left, ∀ r ∈ right, IndependentEffects l r

theorem IndependentEffects.symm {left right : WitnessedEffect Γ}
    (h : IndependentEffects left right) : IndependentEffects right left where
  transformations_commute := h.transformations_commute.symm
  left_inverse_stable := h.right_inverse_stable
  right_inverse_stable := h.left_inverse_stable
  left_undo_commutes_with_right := h.right_undo_commutes_with_left
  right_undo_commutes_with_left := h.left_undo_commutes_with_right

theorem PairwiseIndependentPrograms.symm {left right : List (WitnessedEffect Γ)}
    (h : PairwiseIndependentPrograms left right) :
    PairwiseIndependentPrograms right left := by
  intro r hr l hl
  exact (h l hl r hr).symm

end Cordis.Effects
