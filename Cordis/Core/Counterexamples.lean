import Cordis.Core.Reachability

/-! # Checked Core counterexamples and boundary witnesses -/

namespace Cordis.Core.Counterexamples

open Cordis.Core

/-- A two-node catalog in which each fiber provides its own key and depends on
the other fiber's key. -/
def cycleSpec (p : Bool) : Spec Bool :=
  { deps := {!p}, provs := {p} }

def cycleView (p k : Bool) : Option Bool :=
  if k = !p then some (!p) else none

def cycleState : State Bool Bool :=
  { registered := {false, true}
    phase := fun p => .unloading (cycleView p)
    retired := ∅ }

theorem cycleState_wellFormed : WellFormed cycleSpec cycleState := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q _ _ hpq
    simp only [cycleSpec, Finset.disjoint_singleton]
    exact hpq
  · intro p hp
    simp [cycleState] at hp
  · intro p v hv k
    have hv' : v = cycleView p := by
      simpa [cycleState, committedView] using hv.symm
    subst v
    simp [cycleSpec, cycleView]
  · intro p v hv k q hq
    have hv' : v = cycleView p := by
      simpa [cycleState, committedView] using hv.symm
    subst v
    simp only [cycleView] at hq
    split at hq
    · subst k
      have hq' : q = !p := Option.some.inj hq.symm
      subst q
      simp [CommittedProviderValid, cycleState, installed, cycleSpec]
    · simp at hq

theorem cycleState_not_quiet : ¬ quiet cycleSpec cycleState := by
  intro hq
  have := hq false
  simp [LocallyQuiet, cycleState] at this

theorem cycleState_no_step : ¬ ∃ s', Step cycleSpec cycleState s' := by
  rintro ⟨s', p, hp⟩
  cases hp with
  | begin hphase _ => simp [cycleState] at hphase
  | finish hphase _ => simp [cycleState] at hphase
  | divert hphase _ => simp [cycleState] at hphase
  | leave hphase _ => simp [cycleState] at hphase
  | unload _ hu =>
      apply hu
      refine ⟨!p, cycleView (!p), p, ?_, ?_⟩
      · simp [cycleState, committedView]
      · simp [cycleView]

/-- Mechanical counterexample required by the model boundary: without
Priority acyclicity, a well-formed non-quiet state can deadlock. -/
theorem cyclic_dependency_deadlock :
    ∃ s : State Bool Bool,
      WellFormed cycleSpec s ∧ ¬ quiet cycleSpec s ∧ ¬ ∃ s', Step cycleSpec s s' :=
  ⟨cycleState, cycleState_wellFormed, cycleState_not_quiet, cycleState_no_step⟩

/-- One unloading provider: committed validity holds while target validity
does not. -/
def unloadingState : State Bool Unit :=
  { registered := {false}
    phase := fun p => if p = false then .unloading (fun _ => none) else .inactive
    retired := ∅ }

def unloadingSpec (_ : Bool) : Spec Unit := { provs := {()} }

theorem committed_not_target :
    CommittedProviderValid unloadingSpec unloadingState false () ∧
      ¬ TargetProviderValid unloadingSpec unloadingState false () := by
  constructor
  · simp [CommittedProviderValid, unloadingState, unloadingSpec, installed]
  · simp [TargetProviderValid, unloadingState, unloadingSpec, active]

/-- Both active fibers provide the same key.  Unique resolution refuses to
choose and registered single-source is false. -/
def ambiguousSpec (_ : Bool) : Spec Unit := { provs := {()} }

def ambiguousState : State Bool Unit :=
  { registered := {false, true}
    phase := fun _ => .active (fun _ => none)
    retired := ∅ }

theorem ambiguous_candidates :
    TargetProviderValid ambiguousSpec ambiguousState false () ∧
      TargetProviderValid ambiguousSpec ambiguousState true () := by
  simp [TargetProviderValid, ambiguousSpec, ambiguousState, active]

theorem ambiguous_not_singleSource : ¬ SingleSource ambiguousSpec ambiguousState := by
  intro hs
  have h := hs (p := false) (q := true) (by simp [ambiguousState])
    (by simp [ambiguousState]) (by decide)
  simpa [ambiguousSpec] using h

theorem ambiguous_provider_none : provider ambiguousSpec ambiguousState () = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro p hp
  have hu := (provider_eq_some_iff.mp hp).2
  cases p
  · exact Bool.noConfusion (hu true ambiguous_candidates.2)
  · exact Bool.noConfusion (hu false ambiguous_candidates.1)

theorem ambiguous_multi_provider_resolution :
    provider ambiguousSpec ambiguousState () = none ∧
      ¬ SingleSource ambiguousSpec ambiguousState :=
  ⟨ambiguous_provider_none, ambiguous_not_singleSource⟩

end Cordis.Core.Counterexamples
