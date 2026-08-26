/-
ADR-01 feasibility spike: explicit equivalence specifications and a
relation-parametric law layer over raw effect functions.

Validation status at creation:
* manually type-audited against Lean 4 core syntax;
* NOT compiler-validated, because Lean and Lake were unavailable in the
  creation environment;
* compilation in the project's pinned Lean toolchain is a mandatory
  implementation gate before this spike may be imported by production code.

This file is deliberately independent of Mathlib. Names are illustrative;
the interfaces and laws recorded by ADR-01 are normative, not these exact names.
-/

universe u v

namespace CordisADR01

/-- An explicit equivalence value. It is passed as data rather than installed as
    a global `Setoid` instance, because the same carrier may have several
    simultaneous relations (`≃`, the two paper uses of `≈`, and conjunctions). -/
structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- Heterogeneous relation preservation. -/
def RespectsOn {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop)
    (f : α → β) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

/-- A state transformer preserves the selected relation. -/
def Respects {α : Type u} (S : RelSpec α) (f : α → α) : Prop :=
  RespectsOn S.rel S.rel f

/-- Definition 36's same-input, pointwise relation between maps. -/
def PointwiseRel {α : Type u} (S : RelSpec α)
    (f g : α → α) : Prop :=
  ∀ x, S.rel (f x) (g x)

/-- A useful derived lifting for composition proofs: related inputs are sent by
    possibly different maps to related outputs. -/
def CrossRel {α : Type u} (S : RelSpec α)
    (f g : α → α) : Prop :=
  ∀ {x y}, S.rel x y → S.rel (f x) (g y)

theorem crossRel_of_respects_pointwise {α : Type u}
    {S : RelSpec α} {f g : α → α}
    (hf : Respects S f) (hfg : PointwiseRel S f g) :
    CrossRel S f g := by
  intro x y hxy
  exact S.trans (hf hxy) (hfg y)

theorem pointwiseRel_of_crossRel {α : Type u}
    {S : RelSpec α} {f g : α → α}
    (hfg : CrossRel S f g) : PointwiseRel S f g := by
  intro x
  exact hfg (S.refl x)

theorem respects_of_crossRel_self {α : Type u}
    {S : RelSpec α} {f : α → α}
    (hff : CrossRel S f f) : Respects S f := by
  intro x y hxy
  exact hff hxy

/-- The raw, computational result of one effect application. -/
structure EffectResult (Γ : Type u) where
  state : Γ
  undo : Γ → Γ

/-- The raw effect carrier remains an ordinary function. -/
abbrev Effect (Γ : Type u) := Γ → EffectResult Γ

namespace EffectResult

/-- The output lifting required by Definitions 36-37: successor states are
    related and the selected inverses are pointwise related. -/
def Rel {Γ : Type u} (S : RelSpec Γ)
    (x y : EffectResult Γ) : Prop :=
  S.rel x.state y.state ∧ PointwiseRel S x.undo y.undo

end EffectResult

/-- The full law record for a raw effect at one selected equivalence.

    `run_respects` includes selected-inverse coherence across related inputs;
    `undo_respects` says every inverse returned by an actual run preserves the
    relation; `recovers` is the non-vacuous, run-indexed recovery witness. -/
structure IsLawfulEffect {Γ : Type u}
    (S : RelSpec Γ) (e : Effect Γ) : Prop where
  run_respects : RespectsOn S.rel (EffectResult.Rel S) e
  undo_respects : ∀ γ, Respects S (e γ).undo
  recovers : ∀ γ, S.rel ((e γ).undo (e γ).state) γ

/-- Optional proof-carrying view. Raw functions and `IsLawfulEffect` remain the
    primary API so exact algebra does not depend on proof-field equality. -/
structure LawfulEffect {Γ : Type u} (S : RelSpec Γ) where
  run : Effect Γ
  lawful : IsLawfulEffect S run

/-- Execute `first`, then `second`, composing inverses in reverse order. -/
def seqRun {Γ : Type u} (first second : Effect Γ) : Effect Γ :=
  fun γ =>
    let r₁ := first γ
    let r₂ := second r₁.state
    { state := r₂.state
      undo := fun x => r₁.undo (r₂.undo x) }

/-- The relation-parametric law layer is closed under raw sequential
    composition. The raw computation remains the exact `seqRun` definition. -/
theorem seqRun_lawful {Γ : Type u} {S : RelSpec Γ}
    {first second : Effect Γ}
    (hfirst : IsLawfulEffect S first)
    (hsecond : IsLawfulEffect S second) :
    IsLawfulEffect S (seqRun first second) := by
  refine {
    run_respects := ?_
    undo_respects := ?_
    recovers := ?_
  }
  · intro x y hxy
    have h₁ : EffectResult.Rel S (first x) (first y) :=
      hfirst.run_respects hxy
    have h₂ : EffectResult.Rel S
        (second (first x).state) (second (first y).state) :=
      hsecond.run_respects h₁.1
    refine ⟨h₂.1, ?_⟩
    intro z
    have hinner : S.rel
        ((second (first x).state).undo z)
        ((second (first y).state).undo z) := h₂.2 z
    have hleft : S.rel
        ((first x).undo ((second (first x).state).undo z))
        ((first x).undo ((second (first y).state).undo z)) :=
      hfirst.undo_respects x hinner
    have hright : S.rel
        ((first x).undo ((second (first y).state).undo z))
        ((first y).undo ((second (first y).state).undo z)) :=
      h₁.2 ((second (first y).state).undo z)
    exact S.trans hleft hright
  · intro γ x y hxy
    exact hfirst.undo_respects γ
      (hsecond.undo_respects (first γ).state hxy)
  · intro γ
    have hsecondRecovery : S.rel
        ((second (first γ).state).undo
          (second (first γ).state).state)
        (first γ).state :=
      hsecond.recovers (first γ).state
    have hlifted : S.rel
        ((first γ).undo
          ((second (first γ).state).undo
            (second (first γ).state).state))
        ((first γ).undo (first γ).state) :=
      hfirst.undo_respects γ hsecondRecovery
    exact S.trans hlifted (hfirst.recovers γ)

def lawfulSeq {Γ : Type u} {S : RelSpec Γ}
    (first second : LawfulEffect S) : LawfulEffect S where
  run := seqRun first.run second.run
  lawful := seqRun_lawful first.lawful second.lawful

/-- Equality is one explicit specialization, not the globally installed
    relation on the carrier. -/
def equality (α : Type u) : RelSpec α where
  rel := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

/-- The repaired, non-vacuous equality reading of Definition 8. -/
def PaperWitness {Γ : Type u} (e : Effect Γ) : Prop :=
  ∀ γ, (e γ).undo (e γ).state = γ

/-- Equality specialization recovers the repaired Definition 8 witness exactly.
    The other law fields become automatic congruence of equality. -/
theorem lawful_equality_iff {Γ : Type u} (e : Effect Γ) :
    IsLawfulEffect (equality Γ) e ↔ PaperWitness e := by
  constructor
  · intro h γ
    exact h.recovers γ
  · intro h
    refine {
      run_respects := ?_
      undo_respects := ?_
      recovers := h
    }
    · intro x y hxy
      cases hxy
      exact ⟨rfl, fun _ => rfl⟩
    · intro γ x y hxy
      cases hxy
      rfl

/-- Kernel equivalence of a concrete observation. -/
def observation {Γ : Type u} {Ω : Type v}
    (observe : Γ → Ω) : RelSpec Γ where
  rel := fun x y => observe x = observe y
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

theorem recovers_observation {Γ : Type u} {Ω : Type v}
    (observe : Γ → Ω) (e : Effect Γ)
    (h : IsLawfulEffect (observation observe) e) (γ : Γ) :
    observe ((e γ).undo (e γ).state) = observe γ :=
  h.recovers γ

/-- Relations may also be combined explicitly when a theorem genuinely needs
    both observations. No refinement between the two is inferred. -/
def conjunction {Γ : Type u}
    (S T : RelSpec Γ) : RelSpec Γ where
  rel := fun x y => S.rel x y ∧ T.rel x y
  refl := fun x => ⟨S.refl x, T.refl x⟩
  symm := fun h => ⟨S.symm h.1, T.symm h.2⟩
  trans := fun h₁ h₂ =>
    ⟨S.trans h₁.1 h₂.1, T.trans h₁.2 h₂.2⟩

end CordisADR01
