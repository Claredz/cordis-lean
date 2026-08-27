/-
  ADR-05 BD-ITER compiler spike.

  The paper writes an iterator as the recursive equation

      μ I. Γ → Γ × (Γ → Γ) × Maybe I

  and extends it with Either for failure.  This spike deliberately does not
  put that equation, or a State → State closure, inside the ADR-03 state.
  Instead it uses an executable ranked continuation machine.  A node may
  choose its successor from the current state, but every chosen successor has
  strictly smaller rank.  Thus execution and the fold of inverse functions
  are ordinary well-founded recursion, while a finite length certificate is
  available for T66.

  Validation target: Lean 4.33.0 / the pinned project environment.
  No proof placeholder is used.
-/

import Mathlib.Tactic

universe u v w

namespace CordisADR05

section Core

variable {Γ : Type u} {Ξ : Type v} {Q : Type w}

/- A successful stage either terminates (`halt`) or chooses a dynamically
   state-dependent continuation node (`yield`).  `raise` carries no new state:
   as in the paper, L-Raise later receives the accumulator for the successful
   prefix. -/
inductive StageResult (Γ : Type u) (Ξ : Type v) (Q : Type w) where
  | halt (state : Γ) (undo : Γ → Γ)
  | yield (state : Γ) (undo : Γ → Γ) (next : Q)
  | raise (error : Ξ)

/- A ranked machine is the finite/terminating profile selected by ADR-05.
   `Q` is a control-code type, not a recursive State or Fiber type.  The
   successor can depend on the input state, preserving the paper's
   state-dependent `Maybe I` continuation. -/
structure RankedIterator (Γ : Type u) (Ξ : Type v) (Q : Type w) where
  root : Q
  rank : Q → Nat
  run : Q → Γ → StageResult Γ Ξ Q
  next_lt : ∀ {q γ δ undo q'},
    run q γ = .yield δ undo q' → rank q' < rank q

/- The failure result retains both the state at the failing boundary and the
   inverse for the already successful prefix.  It is intentionally not an
   Option/identity default. -/
inductive ExecResult (Γ : Type u) (Ξ : Type v) where
  | success (state : Γ) (undo : Γ → Γ)
  | failure (error : Ξ) (state : Γ) (undo : Γ → Γ)

def composeUndo (outer inner : Γ → Γ) : Γ → Γ := outer ∘ inner

@[simp] theorem composeUndo_apply (outer inner : Γ → Γ) (x : Γ) :
    composeUndo outer inner x = outer (inner x) := rfl

@[simp] theorem composeUndo_id_left (f : Γ → Γ) :
    composeUndo id f = f := by
  funext x
  rfl

@[simp] theorem composeUndo_id_right (f : Γ → Γ) :
    composeUndo f id = f := by
  funext x
  rfl

theorem composeUndo_assoc (a b c : Γ → Γ) :
    composeUndo (composeUndo a b) c = composeUndo a (composeUndo b c) := by
  funext x
  rfl

/- D52's recursive fold.  The first inverse is applied after all inverses of
   its continuation, hence the order `outer ∘ inner` is LIFO. -/
def execFrom (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) : ExecResult Γ Ξ :=
  match h : it.run q γ with
  | .raise error => .failure error γ id
  | .halt δ undo => .success δ undo
  | .yield δ undo next =>
      match execFrom it next δ with
      | .success final innerUndo =>
          .success final (composeUndo undo innerUndo)
      | .failure error final innerUndo =>
          .failure error final (composeUndo undo innerUndo)
termination_by it.rank q
decreasing_by
  exact it.next_lt h

def exec (it : RankedIterator Γ Ξ Q) (γ : Γ) : ExecResult Γ Ξ :=
  execFrom it it.root γ

@[simp] theorem execFrom_raise
    (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) (error : Ξ)
    (h : it.run q γ = .raise error) :
    execFrom it q γ = .failure error γ id := by
  rw [execFrom.eq_1, h]

@[simp] theorem execFrom_halt
    (it : RankedIterator Γ Ξ Q) (q : Q) (γ δ : Γ) (undo : Γ → Γ)
    (h : it.run q γ = .halt δ undo) :
    execFrom it q γ = .success δ undo := by
  rw [execFrom.eq_1, h]

/- A plain witnessed effect is the one-node, terminating specialization. -/
def plainEffect (e : Γ → Γ × (Γ → Γ)) : RankedIterator Γ Ξ Unit where
  root := ()
  rank := fun _ => 0
  run := fun _ γ =>
    let result := e γ
    .halt result.1 result.2
  next_lt := by
    intro q γ δ undo next h
    cases h

@[simp] theorem exec_plainEffect (e : Γ → Γ × (Γ → Γ)) (γ : Γ) :
    exec (Ξ := Ξ) (plainEffect (Ξ := Ξ) e) γ =
      .success (e γ).1 (e γ).2 := by
  unfold exec
  rw [execFrom.eq_1]
  rfl

/- Exact stage count is a semantic quantity; the rank supplies a cheap
   executable upper bound.  We count the current stage, so the bound is
   `rank + 1`.  This convention is recorded explicitly because the paper's
   `len` prose is ambiguous about whether it counts edges or stages. -/
def stageCountFrom (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) : Nat :=
  match h : it.run q γ with
  | .raise _ => 1
  | .halt _ _ => 1
  | .yield δ _ next => 1 + stageCountFrom it next δ
termination_by it.rank q
decreasing_by
  exact it.next_lt h

theorem stageCountFrom_le (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) :
    stageCountFrom it q γ ≤ it.rank q + 1 := by
  rw [stageCountFrom.eq_1]
  split
  case h_1 => omega
  case h_2 => omega
  case h_3 δ undo next h =>
    have hlt : it.rank next < it.rank q := it.next_lt h
    have hcount := stageCountFrom_le it next δ
    omega
termination_by it.rank q
decreasing_by
  exact hlt

def edgeLengthBound (it : RankedIterator Γ Ξ Q) (q : Q) : Nat := it.rank q

def stageLengthBound (it : RankedIterator Γ Ξ Q) (q : Q) : Nat :=
  edgeLengthBound it q + 1

/- Reach is the least continuation closure over every possible input state,
   not merely the nodes visited by one selected run. -/
def hasNext (it : RankedIterator Γ Ξ Q) (q q' : Q) : Prop :=
  ∃ γ δ undo, it.run q γ = .yield δ undo q'

inductive Reach (it : RankedIterator Γ Ξ Q) : Q → Q → Prop where
  | refl (q : Q) : Reach it q q
  | tail {q q' q'' : Q} :
      hasNext it q q' → Reach it q' q'' → Reach it q q''

def reachableFromRoot (it : RankedIterator Γ Ξ Q) (q : Q) : Prop :=
  Reach it it.root q

theorem reach_rank_le (it : RankedIterator Γ Ξ Q) {q q' : Q}
    (hreach : Reach it q q') : it.rank q' ≤ it.rank q := by
  induction hreach with
  | refl => exact Nat.le_refl _
  | @tail q q' q'' hnext hrest ih =>
      rcases hnext with ⟨γ, δ, undo, hrun⟩
      exact le_trans ih (Nat.le_of_lt (it.next_lt hrun))

def UniformlyBounded (it : RankedIterator Γ Ξ Q) (K : Nat) : Prop :=
  ∀ q γ, reachableFromRoot it q → stageCountFrom it q γ ≤ K

theorem root_uniformlyBounded (it : RankedIterator Γ Ξ Q) :
    UniformlyBounded it (stageLengthBound it it.root) := by
  intro q γ hroot
  exact le_trans (stageCountFrom_le it q γ)
    (Nat.add_le_add_right (reach_rank_le it hroot) 1)

/- A partial projection used by failure-aware semantics.  It exposes only
   successful completions; a failed iterator is not silently totalized. -/
def execOption (it : RankedIterator Γ Ξ Q) (γ : Γ) :
    Option (Γ × (Γ → Γ)) :=
  match exec it γ with
  | .success state undo => some (state, undo)
  | .failure _ _ _ => none

@[simp] theorem execOption_raise
    (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) (error : Ξ)
    (h : it.run q γ = .raise error) :
    execOption
      { root := q
        rank := it.rank
        run := it.run
        next_lt := it.next_lt } γ = none := by
  unfold execOption exec
  rw [execFrom_raise
    { root := q
      rank := it.rank
      run := it.run
      next_lt := it.next_lt } q γ error h]

/- Successful stage graphs are used for the failure-safe form of D60's
   transformation generators.  A forward edge records a successful state
   transition; an inverse edge records the returned undo applied at the
   corresponding output. -/
def successfulAt (it : RankedIterator Γ Ξ Q) (q : Q)
    (γ δ : Γ) (undo : Γ → Γ) : Prop :=
  it.run q γ = .halt δ undo ∨
    ∃ next, it.run q γ = .yield δ undo next

def generatorEdge (it : RankedIterator Γ Ξ Q) (x y : Γ) : Prop :=
  ∃ q, reachableFromRoot it q ∧
    ((∃ undo, successfulAt it q x y undo) ∨
      (∃ δ undo, successfulAt it q δ x undo ∧ undo x = y))

inductive TransformClosure (it : RankedIterator Γ Ξ Q) : Γ → Γ → Prop where
  | refl (x : Γ) : TransformClosure it x x
  | generator {x y : Γ} : generatorEdge it x y → TransformClosure it x y
  | trans {x y z : Γ} :
      TransformClosure it x y → TransformClosure it y z →
      TransformClosure it x z

theorem transformClosure_refl (it : RankedIterator Γ Ξ Q) (x : Γ) :
    TransformClosure it x x := .refl x

theorem transformClosure_trans (it : RankedIterator Γ Ξ Q)
    {x y z : Γ} (hxy : TransformClosure it x y)
    (hyz : TransformClosure it y z) : TransformClosure it x z :=
  .trans hxy hyz

/- Relation-parametric stage observations.  ADR-01 supplies the selected
   state relation; errors are exact by default, but the definition accepts a
   separate error relation for a later diagnostic-observation profile. -/
def PointwiseRel (R : Γ → Γ → Prop) (f g : Γ → Γ) : Prop :=
  ∀ ⦃x y : Γ⦄, R x y → R (f x) (g y)

def StageRel (R : Γ → Γ → Prop) (E : Ξ → Ξ → Prop)
    (a b : StageResult Γ Ξ Q) : Prop :=
  match a, b with
  | .raise e, .raise e' => E e e'
  | .halt x f, .halt y g => R x y ∧ PointwiseRel R f g
  | .yield x f q, .yield y g q' =>
      R x y ∧ PointwiseRel R f g ∧ q = q'
  | _, _ => False

/- The continuation component can be compared by a genuine bisimulation
   relation instead of equality.  `StageRel` above is the same-node
   specialization (`C := Eq`) used by the local lawfulness predicate. -/
def StageRelC (R : Γ → Γ → Prop) (E : Ξ → Ξ → Prop)
    (C : Q → Q → Prop) (a b : StageResult Γ Ξ Q) : Prop :=
  match a, b with
  | .raise e, .raise e' => E e e'
  | .halt x f, .halt y g => R x y ∧ PointwiseRel R f g
  | .yield x f q, .yield y g q' =>
      R x y ∧ PointwiseRel R f g ∧ C q q'
  | _, _ => False

def IteratorBisim (R : Γ → Γ → Prop) (E : Ξ → Ξ → Prop)
    (C : Q → Q → Prop) (a b : RankedIterator Γ Ξ Q) : Prop :=
  C a.root b.root ∧
    ∀ q q' x y, C q q' → R x y →
      StageRelC R E C (a.run q x) (b.run q' y)

def ExecRel (R : Γ → Γ → Prop) (E : Ξ → Ξ → Prop)
    (a b : ExecResult Γ Ξ) : Prop :=
  match a, b with
  | .success x f, .success y g => R x y ∧ PointwiseRel R f g
  | .failure e x f, .failure e' y g =>
      E e e' ∧ R x y ∧ PointwiseRel R f g
  | _, _ => False

def StepLawful (R : Γ → Γ → Prop) (E : Ξ → Ξ → Prop)
    (it : RankedIterator Γ Ξ Q) : Prop :=
  ∀ q ⦃x y : Γ⦄, R x y →
    StageRel R E (it.run q x) (it.run q y)

def InverseProper (R : Γ → Γ → Prop) (γ δ : Γ) (undo : Γ → Γ) : Prop :=
  R (undo δ) γ

def StageWitness (R : Γ → Γ → Prop) (it : RankedIterator Γ Ξ Q) : Prop :=
  ∀ q γ, match h : it.run q γ with
    | .raise _ => True
    | .halt δ undo => InverseProper R γ δ undo
    | .yield δ undo _ => InverseProper R γ δ undo

/- The fold has the same orientation as D52: if a prefix undo is `u` and the
   continuation undo is `r`, the total undo is `u ∘ r`. -/
def foldUndo : List (Γ → Γ) → Γ → Γ
  | [], x => x
  | undo :: rest, x => undo (foldUndo rest x)

@[simp] theorem foldUndo_cons (undo : Γ → Γ) (rest : List (Γ → Γ)) :
    foldUndo (undo :: rest) = composeUndo undo (foldUndo rest) := by
  rfl

end Core

section SmokeTests

/- A concrete two-stage machine demonstrates a dynamic continuation and the
   LIFO accumulator without putting either code or undo in RawState. -/
def twoStage (first second : Nat → Nat × (Nat → Nat)) :
    RankedIterator Nat String Bool where
  root := false
  rank := fun q => if q then 0 else 1
  run := fun q γ =>
    if q then
      let result := second γ
      .halt result.1 result.2
    else
      let result := first γ
      .yield result.1 result.2 true
  next_lt := by
    intro q γ δ undo next h
    by_cases hq : q
    · simp [hq] at h
    · simp [hq] at h
      rcases h with ⟨_, _, hnext⟩
      rw [hnext]
      simp [hq]

example (first second : Nat → Nat × (Nat → Nat)) (γ : Nat) :
    ∃ final undo,
      exec (twoStage first second) γ = .success final undo := by
  refine ⟨(second (first γ).1).1,
    (first γ).2 ∘ (second (first γ).1).2, ?_⟩
  simp [exec, execFrom, twoStage, composeUndo]

def twoStageFail (first : Nat → Nat × (Nat → Nat)) (error : String) :
    RankedIterator Nat String Bool where
  root := false
  rank := fun q => if q then 0 else 1
  run := fun q γ =>
    if q then
      .raise error
    else
      let result := first γ
      .yield result.1 result.2 true
  next_lt := by
    intro q γ δ undo next h
    by_cases hq : q
    · simp [hq] at h
    · simp [hq] at h
      rcases h with ⟨_, _, hnext⟩
      rw [hnext]
      simp [hq]

example (first : Nat → Nat × (Nat → Nat)) (error : String) (γ : Nat) :
    exec (twoStageFail first error) γ =
      .failure error (first γ).1 (first γ).2 := by
  simp [exec, execFrom, twoStageFail, composeUndo]

example (γ : Nat) :
    stageCountFrom (plainEffect (Ξ := String) (fun n => (n + 1, fun x => x - 1))) () γ = 1 := by
  simp [stageCountFrom, plainEffect]

end SmokeTests

end CordisADR05
