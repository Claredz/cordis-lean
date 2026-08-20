import Cordis.Integrated.Step

/-!
# Cordis.Integrated.Termination

Integrated normalization uses a genuine finite-stuttering refinement: the
first lexicographic component is the frozen Core lifecycle measure, and the
second is the total number of remaining effect iterations.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}
variable [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]
variable (spec : FiberId → Core.Spec Key)
variable (program : FiberId → List (Effects.WitnessedEffect Γ))

def remainingAt (s : State FiberId Key Γ) (p : FiberId) : Nat :=
  match s.phase p with
  | .reloading _ remaining _ => remaining.length
  | _ => 0

def remainingTotal (s : State FiberId Key Γ) : Nat :=
  ∑ p : FiberId, remainingAt s p

/-- Each Iter rule strictly reduces the finite stuttering budget. -/
theorem iter_remainingTotal_decreases
    {p : FiberId} {s : State FiberId Key Γ}
    {v : Core.View Key FiberId} {effect : Effects.WitnessedEffect Γ}
    {rest : List (Effects.WitnessedEffect Γ)} {acc : Effects.Accumulator Γ}
    {next : Γ × Effects.Accumulator Γ}
    (hp : s.phase p = .reloading v (effect :: rest) acc) :
    remainingTotal ((s.setPhase p (.reloading v rest next.2)).setWorld next.1) <
      remainingTotal s := by
  classical
  let newer := (s.setPhase p (.reloading v rest next.2)).setWorld next.1
  have hnewp : remainingAt newer p = rest.length := by
    simp [newer, remainingAt]
  have holdp : remainingAt s p = (effect :: rest).length := by
    simp [remainingAt, hp]
  have hother :
      (∑ q ∈ (Finset.univ.erase p), remainingAt newer q) =
        ∑ q ∈ (Finset.univ.erase p), remainingAt s q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hne : q ≠ p := (Finset.mem_erase.mp hq).1
    simp [newer, remainingAt, State.setPhase_other _ hne]
  have hnewDecompose :=
    Finset.sum_erase_add Finset.univ (remainingAt newer) (Finset.mem_univ p)
  have holdDecompose :=
    Finset.sum_erase_add Finset.univ (remainingAt s) (Finset.mem_univ p)
  unfold remainingTotal
  rw [← hnewDecompose, ← holdDecompose, hother, hnewp, holdp]
  simp

private theorem stutter_remainingTotal_decreases
    {p : FiberId} {s t : State FiberId Key Γ}
    (h : StepAt spec program p s t) (hstutter : erase t = erase s) :
    remainingTotal t < remainingTotal s := by
  cases h with
  | begin hp _ =>
      have heq := congrArg (fun state => state.phase p) hstutter
      simp [erasePhase, hp] at heq
  | iter hp _ _ =>
      exact iter_remainingTotal_decreases hp
  | finish hp _ =>
      have heq := congrArg (fun state => state.phase p) hstutter
      simp [erasePhase, hp] at heq
  | divert hp _ =>
      have heq := congrArg (fun state => state.phase p) hstutter
      simp [erasePhase, hp] at heq
  | leave hp _ =>
      have heq := congrArg (fun state => state.phase p) hstutter
      simp [erasePhase, hp] at heq
  | unload hp _ =>
      have heq := congrArg (fun state => state.phase p) hstutter
      simp [erasePhase, hp] at heq

noncomputable def refinementMeasure
    (registered : Finset FiberId)
  (acyclic : WellFounded (Core.PrioritySuccOn spec registered))
    (s : State FiberId Key Γ) : Nat × Nat :=
  (Core.lifecycleMeasure (spec := spec) registered acyclic (erase s), remainingTotal s)

def RefinementOrder
    (registered : Finset FiberId)
    (acyclic : WellFounded (Core.PrioritySuccOn spec registered))
    (t s : State FiberId Key Γ) : Prop :=
  Prod.Lex Nat.lt Nat.lt
    (refinementMeasure spec registered acyclic t)
    (refinementMeasure spec registered acyclic s)

theorem refinementOrder_wellFounded
    (registered : Finset FiberId)
    (acyclic : WellFounded (Core.PrioritySuccOn spec registered)) :
    WellFounded (RefinementOrder spec registered acyclic :
      State FiberId Key Γ → State FiberId Key Γ → Prop) := by
  exact InvImage.wf (refinementMeasure spec registered acyclic)
    (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Every integrated step decreases the Core/Iter lexicographic measure. -/
theorem step_decreases_refinementMeasure
    {s t : State FiberId Key Γ}
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s))
    (h : Step spec program s t) :
    RefinementOrder spec (erase s).registered acyclic t s := by
  rcases h with ⟨p, hp⟩
  rcases hp.project with hstutter | hcore
  · have hremaining := stutter_remainingTotal_decreases spec program hp hstutter
    have hfirst :
        Core.lifecycleMeasure (spec := spec) (erase s).registered acyclic (erase t) =
          Core.lifecycleMeasure (spec := spec) (erase s).registered acyclic (erase s) := by
      rw [hstutter]
    unfold RefinementOrder refinementMeasure
    rw [hfirst]
    exact Prod.Lex.right _ hremaining
  · have hfirst := Core.step_decreases_measure wf acyclic ⟨p, hcore⟩
    unfold RefinementOrder refinementMeasure
    exact Prod.Lex.left _ _ hfirst

/-- **Integrated theorem.** Finite programs add only finitely many Core
stutters, so integrated normalization remains accessible. -/
theorem lifecycle_terminates
    {s : State FiberId Key Γ}
    (wf : CoreWellFormed spec s)
    (acyclic : Core.PriorityAcyclic spec (erase s)) :
    Acc (fun t' t => Step spec program t t') s := by
  let relation : State FiberId Key Γ → State FiberId Key Γ → Prop :=
    RefinementOrder (Γ := Γ) spec (erase s).registered acyclic
  let motive : State FiberId Key Γ → Prop := fun current =>
    CoreWellFormed spec current →
    (erase current).registered = (erase s).registered →
    Acc (fun t' t => Step spec program t t') current
  have all : ∀ current, motive current := fun root =>
    (refinementOrder_wellFounded (Γ := Γ) spec (erase s).registered acyclic).induction
      (C := motive) root (fun current ih hwf hregistered => by
        apply Acc.intro current
        intro next hstep
        have hregistered' : current.registered = s.registered := hregistered
        have hac : Core.PriorityAcyclic spec (erase current) := by
          unfold Core.PriorityAcyclic
          change WellFounded (Core.PrioritySuccOn spec current.registered)
          rw [hregistered']
          exact acyclic
        have hdecrease := step_decreases_refinementMeasure spec program hwf hac hstep
        have hdecrease' : relation next current := by
          simpa [relation, hregistered'] using hdecrease
        have hwfNext := Step.preserve_coreWellFormed spec program hwf hstep
        have hregNext : (erase next).registered = (erase s).registered := by
          rcases hstep with ⟨p, hp⟩
          exact hp.registered_eq.trans hregistered
        exact ih next hdecrease' hwfNext hregNext)
  exact all s wf rfl

end Cordis.Integrated
