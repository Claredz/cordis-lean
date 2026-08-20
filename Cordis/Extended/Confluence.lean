import Cordis.Extended.CoreCommutation
import Cordis.Integrated

/-!
# Cordis.Extended.Confluence

This file records the exact confluence boundary.  It supplies a reusable Newman
interface and a checked commuting fragment.  Full Core local confluence is not
asserted: dependent critical-pair enumeration remains separate work.
-/

namespace Cordis.Extended

open Cordis

variable {α : Type*}
variable {FiberId Key : Type*}

def Joinable (relation : α → α → Prop) (left right : α) : Prop :=
  ∃ join, Relation.ReflTransGen relation left join ∧
    Relation.ReflTransGen relation right join

def LocalConfluent (relation : α → α → Prop) : Prop :=
  ∀ ⦃root left right⦄, relation root left → relation root right →
    Joinable relation left right

def Confluent (relation : α → α → Prop) : Prop :=
  ∀ ⦃root left right⦄,
    Relation.ReflTransGen relation root left →
    Relation.ReflTransGen relation root right →
    Joinable relation left right

/-- Minimal project-local Newman lemma, stated at one accessible root. -/
theorem newman_at {relation : α → α → Prop} {root : α}
    (termination : Acc (fun child parent => relation parent child) root)
    (hlocal : LocalConfluent relation) :
    ∀ ⦃left right⦄,
      Relation.ReflTransGen relation root left →
      Relation.ReflTransGen relation root right →
      Joinable relation left right := by
  induction termination with
  | intro root descendants ih =>
      intro left right hleft hright
      rcases Relation.ReflTransGen.cases_head hleft with hrootLeft | ⟨left₁, hstepLeft, hleftTail⟩
      · subst left
        exact ⟨right, hright, Relation.ReflTransGen.refl⟩
      rcases Relation.ReflTransGen.cases_head hright with hrootRight | ⟨right₁, hstepRight, hrightTail⟩
      · subst right
        exact ⟨left, Relation.ReflTransGen.refl, hleft⟩
      rcases hlocal hstepLeft hstepRight with ⟨middle, hleftMiddle, hrightMiddle⟩
      have confluenceLeft := ih left₁ hstepLeft
      have confluenceRight := ih right₁ hstepRight
      rcases confluenceLeft hleftTail hleftMiddle with
        ⟨leftJoin, hleftJoin, hmiddleLeftJoin⟩
      rcases confluenceRight hrightTail hrightMiddle with
        ⟨rightJoin, hrightJoin, hmiddleRightJoin⟩
      rcases confluenceLeft
          (hleftMiddle.trans hmiddleLeftJoin)
          (hleftMiddle.trans hmiddleRightJoin) with
        ⟨finalJoin, hleftFinal, hrightFinal⟩
      exact ⟨finalJoin, hleftJoin.trans hleftFinal,
        hrightJoin.trans hrightFinal⟩

/-- A global well-founded relation plus local confluence is confluent. -/
theorem newman {relation : α → α → Prop}
    (termination : WellFounded (fun child parent => relation parent child))
    (hlocal : LocalConfluent relation) :
    Confluent relation := by
  intro root
  exact newman_at (termination.apply root) hlocal

/-- **Extended theorem (Core commuting fragment).** Static independence and
Core well-formedness construct the two residual steps and their common join. -/
theorem steps_on_independent_fibers_commute
    [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Core.Spec Key}
    {root leftState rightState : Core.State FiberId Key}
    {left right : FiberId}
    (wf : Core.WellFormed spec root)
    (leftStep : Core.StepAt spec left root leftState)
    (rightStep : Core.StepAt spec right root rightState)
    (independent : CoreIndependent spec root left right) :
    Joinable (Core.Step spec) leftState rightState := by
  rcases independent_stepAt_commute wf leftStep rightStep independent with
    ⟨join, rightResidual, leftResidual⟩
  exact ⟨join,
    Relation.ReflTransGen.single ⟨right, rightResidual⟩,
    Relation.ReflTransGen.single ⟨left, leftResidual⟩⟩

/-- The local-confluence obligation restricted to peaks whose actors coincide
or are statically independent.  This is the checked noninterfering fragment;
only distinct priority-related actors remain as Core critical pairs. -/
def NoninterferingLocalConfluentAt
    [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Core.Spec Key) (root : Core.State FiberId Key) : Prop :=
  ∀ {leftState rightState : Core.State FiberId Key} (left right : FiberId),
    Core.StepAt spec left root leftState →
    Core.StepAt spec right root rightState →
    (left = right ∨ CoreIndependent spec root left right) →
    Joinable (Core.Step spec) leftState rightState

/-- **Extended theorem (local-confluence fragment).** Every same-actor or
independent-actor one-step peak from a well-formed root is joinable. -/
theorem core_noninterfering_local_confluent_at
    [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Core.Spec Key} {root : Core.State FiberId Key}
    (wf : Core.WellFormed spec root) :
    NoninterferingLocalConfluentAt spec root := by
  intro leftState rightState left right leftStep rightStep hactors
  rcases hactors with hsame | hindependent
  · subst right
    have hstates := stepAt_deterministic leftStep rightStep
    subst rightState
    exact ⟨leftState, Relation.ReflTransGen.refl,
      Relation.ReflTransGen.refl⟩
  · exact steps_on_independent_fibers_commute wf leftStep rightStep
      hindependent

/-- **Extended theorem (conditional Core confluence).** Once dependent critical
pairs establish local confluence, frozen Core termination supplies confluence
from every well-formed acyclic initial state. -/
theorem core_confluent_if_local
    [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Core.Spec Key} {root : Core.State FiberId Key}
    (wf : Core.WellFormed spec root) (acyclic : Core.PriorityAcyclic spec root)
    (hlocal : LocalConfluent (Core.Step spec)) :
    ∀ ⦃left right⦄,
      Relation.ReflTransGen (Core.Step spec) root left →
      Relation.ReflTransGen (Core.Step spec) root right →
      Joinable (Core.Step spec) left right :=
  newman_at (Core.lifecycle_terminates wf acyclic) hlocal

/-- Core independence alone says nothing about a shared effect world. -/
def IntegratedConfluenceBoundary (Γ : Type*) : Prop :=
  ∀ left right : Effects.WitnessedEffect Γ,
    Effects.IndependentEffects left right

end Cordis.Extended
