import Std

/-!
  DeepSeek Harness BP-01 bootstrap contract.

  This file is intentionally a small, standalone smoke-test mirror for the
  executable blueprint.  It is not the production formalization and it does
  not claim to prove the whole paper.  The production package should port the
  declarations into the module tree described by BP-01, while retaining this
  file (or an equivalent fixture) as a regression test.
-/

namespace DeepSeekHarness

universe u v w

inductive EvidenceStatus where
  | pending
  | aligned
  | interfacePassed
  | kernelProved
  | executableTested
  | seamOnly
  | deferred
deriving Repr, DecidableEq

structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RespectsOn {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop) (f : α → β) : Prop :=
  ∀ ⦃x y⦄, R x y → S (f x) (f y)

def PointwiseRel {α : Type u} {β : Type v}
    (R : β → β → Prop) (f g : α → β) : Prop :=
  ∀ x, R (f x) (g x)

def CrossRel {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop)
    (f g : α → β) : Prop :=
  ∀ ⦃x y⦄, R x y → S (f x) (g y)

def EqRel (α : Type u) : RelSpec α where
  rel := Eq
  refl := fun x => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂

inductive EffectResult (S : Type u) where
  | success (state : S) (undo : S → S)

abbrev Effect (S : Type u) := S → EffectResult S

def resultState {S : Type u} : EffectResult S → S
  | .success s _ => s

def resultUndo {S : Type u} : EffectResult S → S → S
  | .success _ u => u

def composeUndo {S : Type u} (outer inner : S → S) : S → S :=
  fun s => outer (inner s)

def seqRun {S : Type u} (first second : Effect S) (s : S) : EffectResult S :=
  match first s with
  | .success s₁ u₁ =>
      match second s₁ with
      | .success s₂ u₂ => .success s₂ (composeUndo u₁ u₂)

structure IsLawfulEffect {S : Type u}
    (R : S → S → Prop) (e : Effect S) : Prop where
  undo_respects : ∀ s, RespectsOn R R (resultUndo (e s))
  recovers : ∀ s, R (resultUndo (e s) (resultState (e s))) s

structure OpResult (S : Type u) (O : Type v) where
  state : S
  undo : S → S
  outcome : O

abbrev PartialOp (S : Type u) (O : Type v) :=
  S → Option (OpResult S O)

inductive ExecResult (S : Type u) (E : Type v) where
  | success (state : S) (undo : S → S)
  | failure (error : E) (boundary : S) (prefixUndo : S → S)

def successToExec {S : Type u} {E : Type v} :
    EffectResult S → ExecResult S E
  | .success state undo => .success state undo

inductive StageResult (S : Type u) (E : Type v) (Q : Type w) where
  | halt (state : S) (undo : S → S)
  | yield (state : S) (undo : S → S) (next : Q)
  | raise (error : E)

structure RankedIterator (S : Type u) (E : Type v) (Q : Type w) where
  root : Q
  rank : Q → Nat
  run : Q → S → StageResult S E Q
  next_lt : ∀ {q s s' u q'},
    run q s = .yield s' u q' → rank q' < rank q

def execFrom {S : Type u} {E : Type v} {Q : Type w}
    (it : RankedIterator S E Q) (q : Q) (s : S) : ExecResult S E :=
  match h : it.run q s with
  | .halt s' u => .success s' u
  | .raise e => .failure e s id
  | .yield s' u q' =>
      match execFrom it q' s' with
      | .success sf uf => .success sf (composeUndo u uf)
      | .failure e boundary prefix =>
          .failure e boundary (composeUndo u prefix)
termination_by it.rank q
decreasing_by
  exact it.next_lt h

structure RegistryLike (K : Type u) (V : Type v) (R : Type w)
    [DecidableEq K] where
  empty : R
  lookup : R → K → Option V
  insert : R → K → V → R
  erase : R → K → R
  dom : R → List K
  dom_nodup : ∀ r, (dom r).Nodup
  lookup_empty : ∀ k, lookup empty k = none
  lookup_insert_eq : ∀ r k v, lookup (insert r k v) k = some v

structure AlphaAction (N : Type u) (X : Type v) where
  act : Equiv.Perm N → X → X
  act_id : ∀ x, act Equiv.refl x = x
  act_comp : ∀ (p q : Equiv.Perm N) x,
    act (p.trans q) x = act p (act q x)
  act_inv : ∀ (p : Equiv.Perm N) x,
    act p.symm (act p x) = x

structure StateLike (S : Type u) (O : Type v) where
  project : S → O

structure ObservationProfile (S : Type u) (O : Type v) where
  stateRel : RelSpec S
  obsRel : RelSpec O
  project : S → O
  project_respects : RespectsOn stateRel.rel obsRel.rel project

/-! A small executable example.  Its labels are explicit so a later alpha
    action can be non-trivial; this first smoke test only exercises effects. -/
abbrev CounterState := Int × Int

def inc₁ : Effect CounterState := fun s =>
  .success (s.1 + 1, s.2) (fun t => (t.1 - 1, t.2))

def inc₂ : Effect CounterState := fun s =>
  .success (s.1, s.2 + 1) (fun t => (t.1, t.2 - 1))

def counterStateOf {S : Type u} : EffectResult S → S := resultState

example (s : CounterState) :
    counterStateOf (inc₁ s) = (s.1 + 1, s.2) := by
  rfl

example (s : CounterState) :
    resultUndo (inc₁ s) (counterStateOf (inc₁ s)) = s := by
  cases s
  simp [inc₁, counterStateOf, resultUndo, resultState]

def demoState : CounterState := (0, 0)

def demoSuccess : CounterState :=
  counterStateOf (seqRun inc₁ inc₂ demoState)

#eval demoSuccess

end DeepSeekHarness
