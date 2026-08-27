/-
  ADR-06 closure spike: equivalence and equivariance contracts.

  This is intentionally standalone.  It canonicalizes the two map liftings
  that had been conflated in ADR-05:

    PointwiseRel R f g := same-input relation,  ∀ z, R (f z) (g z)
    CrossRel     R f g := related-input relation,
                           ∀ {x y}, R x y → R (f x) (g y)

  This is a standalone compiler mirror for ADR-06.  It does not redeclare the
  production modules and it does not change the accepted ADR-01 carrier.  The
  iterator relator uses PointwiseRel; inverse composition uses the bridge from
  Respects + PointwiseRel to CrossRel.  A finite countermodel at the end shows
  that individual inverse properness does not imply selected-inverse coherence.
-/

import Mathlib.Tactic

universe u v w

namespace CordisADR06

/-! --------------------------------------------------------------------------
    Explicit relation layer (ADR-01 names made canonical)
    -------------------------------------------------------------------------- -/

structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RespectsOn {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop) (f : α → β) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

def Respects {α : Type u} (R : RelSpec α) (f : α → α) : Prop :=
  RespectsOn R.rel R.rel f

/- Same-input pointwise relation.  This is the canonical `PointwiseRel`. -/
def PointwiseRel {α : Type u} (R : RelSpec α) (f g : α → α) : Prop :=
  ∀ z, R.rel (f z) (g z)

/- Heterogeneous form used when the input index is not the state carrier. -/
def SamePointwiseRel {ι : Type u} {α : Type v}
    (S : α → α → Prop) (f g : ι → α) : Prop :=
  ∀ z, S (f z) (g z)

/- Cross-input lifting.  It is deliberately not called PointwiseRel. -/
def CrossRel {α : Type u} (R : RelSpec α) (f g : α → α) : Prop :=
  ∀ {x y}, R.rel x y → R.rel (f x) (g y)

theorem crossRel_of_respects_pointwise {α : Type u}
    {R : RelSpec α} {f g : α → α}
    (hf : Respects R f) (hfg : PointwiseRel R f g) :
    CrossRel R f g := by
  intro x y hxy
  exact R.trans (hf hxy) (hfg y)

theorem pointwiseRel_of_crossRel {α : Type u}
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : PointwiseRel R f g := by
  intro z
  exact hfg (R.refl z)

theorem respects_of_crossRel_self {α : Type u}
    {R : RelSpec α} {f : α → α}
    (hff : CrossRel R f f) : Respects R f := by
  intro x y hxy
  exact hff hxy

/- For an equivalence, a cross-input lifting already entails properness of
   both maps.  This is recorded explicitly so the directional/directed case
   cannot be confused with the equivalence case. -/
theorem respects_left_of_crossRel {α : Type u}
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : Respects R f := by
  intro x y hxy
  have h₁ : R.rel (f x) (g y) := hfg hxy
  have h₂ : R.rel (g y) (f y) :=
    R.symm ((pointwiseRel_of_crossRel hfg) y)
  exact R.trans h₁ h₂

theorem respects_right_of_crossRel {α : Type u}
    {R : RelSpec α} {f g : α → α}
    (hfg : CrossRel R f g) : Respects R g := by
  intro x y hxy
  have h₁ : R.rel (g x) (f x) :=
    R.symm ((pointwiseRel_of_crossRel hfg) x)
  have h₂ : R.rel (f x) (g y) := hfg hxy
  exact R.trans h₁ h₂

/- The second bridge is the one normally used in the right-to-left direction;
   spelling it out avoids relying on implicit symmetry in later proofs. -/
theorem crossRel_of_pointwise_respects {α : Type u}
    {R : RelSpec α} {f g : α → α}
    (hf : Respects R f) (hfg : PointwiseRel R f g) : CrossRel R f g :=
  crossRel_of_respects_pointwise hf hfg

theorem respects_id {α : Type u} (R : RelSpec α) : Respects R id := by
  intro x y hxy
  exact hxy

theorem respects_comp {α : Type u} {R : RelSpec α}
    {f g : α → α} (hf : Respects R f) (hg : Respects R g) :
    Respects R (f ∘ g) := by
  intro x y hxy
  exact hf (hg hxy)

theorem pointwiseRel_refl {α : Type u} (R : RelSpec α) (f : α → α) :
    PointwiseRel R f f := by
  intro x
  exact R.refl (f x)

theorem pointwiseRel_symm {α : Type u} {R : RelSpec α}
    {f g : α → α} (h : PointwiseRel R f g) :
    PointwiseRel R g f := by
  intro x
  exact R.symm (h x)

theorem pointwiseRel_trans {α : Type u} {R : RelSpec α}
    {f g h : α → α} (h₁ : PointwiseRel R f g)
    (h₂ : PointwiseRel R g h) : PointwiseRel R f h := by
  intro x
  exact R.trans (h₁ x) (h₂ x)

theorem compose_pointwiseRel {α : Type u}
    {R : RelSpec α} {f g h k : α → α}
    (hf : Respects R f) (hfg : PointwiseRel R f g)
    (hhk : PointwiseRel R h k) :
    PointwiseRel R (f ∘ h) (g ∘ k) := by
  intro z
  exact R.trans (hf (hhk z)) (hfg (k z))

/- A tagged optional result relation.  Constructor tags are never silently
   identified; this is the common partial/failure relator. -/
def OptionRel {α : Type u} (R : α → α → Prop) :
    Option α → Option α → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

theorem optionRel_none_none {α : Type u} {R : α → α → Prop} :
    OptionRel R none none := by
  trivial

theorem optionRel_some {α : Type u} {R : α → α → Prop}
    {x y : α} (h : R x y) : OptionRel R (some x) (some y) := h

theorem optionRel_map {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : RelSpec β}
    {f g : α → β} (hfg : RespectsOn R S.rel f)
    (hpoint : SamePointwiseRel S.rel f g)
    {x y : α} (hxy : R x y) :
    OptionRel S.rel (some (f x)) (some (g y)) := by
  exact S.trans (hfg hxy) (hpoint y)

/- Explicit observation pullbacks keep D33's boundary visible. -/
def PullbackRel {State Obs : Type u} (project : State → Obs)
    (S : RelSpec Obs) : State → State → Prop :=
  fun x y => S.rel (project x) (project y)

def CoreStateObs {State Obs : Type u} (project : State → Obs)
    (S : RelSpec Obs) : RelSpec State where
  rel := PullbackRel project S
  refl := fun x => S.refl (project x)
  symm := by intro x y h; exact S.symm h
  trans := by intro x y z h₁ h₂; exact S.trans h₁ h₂

structure ObservationFamily (State : Type u) where
  core : RelSpec State
  lifecycle : RelSpec State
  eraseControl : RelSpec State
  opTestEq : RelSpec State

def StoreObs {K V : Type u} (S : RelSpec V)
    (x y : K → Option V) : Prop :=
  ∀ k, OptionRel S.rel (x k) (y k)

/- Flat StoreObs above is only a readable adapter.  The production coeffect
   substrate is dependent; this shell keeps the per-key relation explicit
   without assuming a finite-domain or lookup implementation here. -/
def DepStore {K : Type u} (V : K → Type v) :=
  ∀ k, Option (V k)

def DepStoreObs {K : Type u} {V : K → Type v}
    (keyRel : ∀ k, RelSpec (V k))
    (x y : DepStore V) : Prop :=
  ∀ k, OptionRel (keyRel k).rel (x k) (y k)

def NameRenaming (State Name : Type u) :=
  Equiv.Perm Name → State → State

/-! --------------------------------------------------------------------------
    Raw effects, witnesses, and relation-level independence
    -------------------------------------------------------------------------- -/

structure EffectResult (Γ : Type u) where
  state : Γ
  undo : Γ → Γ

abbrev Effect (Γ : Type u) := Γ → EffectResult Γ

def EffectResultRel {Γ : Type u} (R : RelSpec Γ)
    (x y : EffectResult Γ) : Prop :=
  R.rel x.state y.state ∧ PointwiseRel R x.undo y.undo

def optionRelSpec {α : Type u} (R : RelSpec α) : RelSpec (Option α) where
  rel := OptionRel R.rel
  refl := by
    intro x
    cases x with
    | none => trivial
    | some a => exact R.refl a
  symm := by
    intro x y h
    cases x <;> cases y <;> simp [OptionRel] at h ⊢
    · exact R.symm h
  trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp [OptionRel] at hxy hyz ⊢
    · exact R.trans hxy hyz

def depStoreObsSpec {K : Type u} {V : K → Type v}
    (keyRel : ∀ k, RelSpec (V k)) : RelSpec (DepStore V) where
  rel := DepStoreObs keyRel
  refl := by
    intro x k
    exact (optionRelSpec (keyRel k)).refl (x k)
  symm := by
    intro x y h k
    exact (optionRelSpec (keyRel k)).symm (h k)
  trans := by
    intro x y z hxy hyz k
    exact (optionRelSpec (keyRel k)).trans (hxy k) (hyz k)

def effectResultRelSpec {Γ : Type u} (R : RelSpec Γ) :
    RelSpec (EffectResult Γ) where
  rel := EffectResultRel R
  refl := by
    intro x
    exact ⟨R.refl x.state, pointwiseRel_refl R x.undo⟩
  symm := by
    intro x y h
    exact ⟨R.symm h.1, pointwiseRel_symm h.2⟩
  trans := by
    intro x y z hxy hyz
    exact ⟨R.trans hxy.1 hyz.1, pointwiseRel_trans hxy.2 hyz.2⟩

structure IsLawfulEffect {Γ : Type u}
    (R : RelSpec Γ) (e : Effect Γ) : Prop where
  run_respects : RespectsOn R.rel (EffectResultRel R) e
  undo_respects : ∀ γ, Respects R (e γ).undo
  recovers : ∀ γ, R.rel ((e γ).undo (e γ).state) γ

structure LawfulEffect {Γ : Type u} (R : RelSpec Γ) where
  run : Effect Γ
  lawful : IsLawfulEffect R run

def seqRun {Γ : Type u} (first second : Effect Γ) : Effect Γ :=
  fun γ =>
    let r₁ := first γ
    let r₂ := second r₁.state
    { state := r₂.state
      undo := fun x => r₁.undo (r₂.undo x) }

theorem seqRun_lawful {Γ : Type u} {R : RelSpec Γ}
    {first second : Effect Γ}
    (hfirst : IsLawfulEffect R first)
    (hsecond : IsLawfulEffect R second) :
    IsLawfulEffect R (seqRun first second) := by
  refine { run_respects := ?_, undo_respects := ?_, recovers := ?_ }
  · intro x y hxy
    have h₁ : EffectResultRel R (first x) (first y) :=
      hfirst.run_respects hxy
    have h₂ : EffectResultRel R
        (second (first x).state) (second (first y).state) :=
      hsecond.run_respects h₁.1
    refine ⟨h₂.1, ?_⟩
    intro z
    have hinner : R.rel
        ((second (first x).state).undo z)
        ((second (first y).state).undo z) := h₂.2 z
    have hleft : R.rel
        ((first x).undo ((second (first x).state).undo z))
        ((first x).undo ((second (first y).state).undo z)) :=
      hfirst.undo_respects x hinner
    have hright : R.rel
        ((first x).undo ((second (first y).state).undo z))
        ((first y).undo ((second (first y).state).undo z)) :=
      h₁.2 ((second (first y).state).undo z)
    exact R.trans hleft hright
  · intro γ x y hxy
    exact hfirst.undo_respects γ
      (hsecond.undo_respects (first γ).state hxy)
  · intro γ
    have hsecondRecovery : R.rel
        ((second (first γ).state).undo
          (second (first γ).state).state)
        (first γ).state := hsecond.recovers (first γ).state
    have hlifted : R.rel
        ((first γ).undo
          ((second (first γ).state).undo
            (second (first γ).state).state))
        ((first γ).undo (first γ).state) :=
      hfirst.undo_respects γ hsecondRecovery
    exact R.trans hlifted (hfirst.recovers γ)

def equality (α : Type u) : RelSpec α where
  rel := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

def PaperWitness {Γ : Type u} (e : Effect Γ) : Prop :=
  ∀ γ, (e γ).undo (e γ).state = γ

theorem lawful_equality_iff {Γ : Type u} (e : Effect Γ) :
    IsLawfulEffect (equality Γ) e ↔ PaperWitness e := by
  constructor
  · intro h γ
    exact h.recovers γ
  · intro h
    refine { run_respects := ?_, undo_respects := ?_, recovers := h }
    · intro x y hxy
      cases hxy
      exact ⟨rfl, fun _ => rfl⟩
    · intro γ x y hxy
      cases hxy
      rfl

def CommuteUpTo {Γ : Type u} (R : RelSpec Γ)
    (f g : Γ → Γ) : Prop :=
  PointwiseRel R (f ∘ g) (g ∘ f)

def selectedUndo {Γ : Type u} (e : Effect Γ) (γ : Γ) : Γ → Γ :=
  (e γ).undo

/- D19 clause (2): a foreign transformation must not change which inverse an
   effect selects, modulo the selected relation. -/
def SelectedInverseStable {Γ : Type u} (R : RelSpec Γ)
    (e : Effect Γ) (foreign : Γ → Γ) : Prop :=
  ∀ γ, PointwiseRel R
    (selectedUndo e (foreign γ)) (selectedUndo e γ)

structure IndependenceContract {Γ : Type u}
    (R : RelSpec Γ) (e₁ e₂ : Effect Γ)
    (M₁ M₂ : (Γ → Γ) → Prop) : Prop where
  commute : ∀ {f g}, M₁ f → M₂ g → CommuteUpTo R f g
  proper₁ : ∀ {f}, M₁ f → Respects R f
  proper₂ : ∀ {g}, M₂ g → Respects R g
  stable₁₂ : ∀ {g}, M₂ g → SelectedInverseStable R e₁ g
  stable₂₁ : ∀ {f}, M₁ f → SelectedInverseStable R e₂ f

/- A predicate-only M₁/M₂ is a convenient local adapter, but it can be made
   vacuous by choosing the empty predicate.  Trusted D19 instances therefore
   carry explicit submonoid closure and generator-inclusion witnesses. -/
structure TransformationMonoidProfile (Γ : Type u) where
  mem : (Γ → Γ) → Prop
  id_mem : mem id
  comp_mem : ∀ {f g : Γ → Γ}, mem f → mem g → mem (f ∘ g)

structure GeneratedEffectProfile (Γ : Type u) (e : Effect Γ) where
  monoid : TransformationMonoidProfile Γ
  forward_mem : monoid.mem (fun γ => (e γ).state)
  inverse_mem : ∀ γ, monoid.mem (e γ).undo

structure GeneratedIndependenceContract {Γ : Type u}
    {R : RelSpec Γ} {e₁ e₂ : Effect Γ}
    (P₁ : GeneratedEffectProfile Γ e₁)
    (P₂ : GeneratedEffectProfile Γ e₂) : Prop where
  commute : ∀ {f g}, P₁.monoid.mem f → P₂.monoid.mem g → CommuteUpTo R f g
  proper₁ : ∀ {f}, P₁.monoid.mem f → Respects R f
  proper₂ : ∀ {g}, P₂.monoid.mem g → Respects R g
  stable₁₂ : ∀ {g}, P₂.monoid.mem g → SelectedInverseStable R e₁ g
  stable₂₁ : ∀ {f}, P₁.monoid.mem f → SelectedInverseStable R e₂ f

/-! --------------------------------------------------------------------------
    Partial operations and the repaired L35 contract
    -------------------------------------------------------------------------- -/

structure OpResult (Γ : Type u) (Ω : Type v) where
  state : Γ
  undo : Γ → Γ
  outcome : Ω

abbrev PartialOp (Γ : Type u) (Ω : Type v) := Γ → Option (OpResult Γ Ω)

def WeakOperationRespects {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω) : Prop :=
  ∀ {x y}, R.rel x y →
    match op x, op y with
    | none, none => True
    | some a, some b =>
        R.rel a.state b.state ∧
        a.outcome = b.outcome ∧
        Respects R a.undo ∧ Respects R b.undo
    | _, _ => False

def SelectedInverseCoherent {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω) : Prop :=
  ∀ {x y a b}, R.rel x y → op x = some a → op y = some b →
    PointwiseRel R a.undo b.undo

def OperationRecovers {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω) : Prop :=
  ∀ {x a}, op x = some a → R.rel (a.undo a.state) x

def OperationRespects {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω) : Prop :=
  WeakOperationRespects R op ∧ SelectedInverseCoherent R op ∧
    OperationRecovers R op

theorem operationRespects_implies_weak {Γ : Type u} {Ω : Type v}
    {R : RelSpec Γ} {op : PartialOp Γ Ω}
    (h : OperationRespects R op) : WeakOperationRespects R op := h.1

theorem operationRespects_implies_coherent {Γ : Type u} {Ω : Type v}
    {R : RelSpec Γ} {op : PartialOp Γ Ω}
    (h : OperationRespects R op) : SelectedInverseCoherent R op := h.2.1

/- D39's second clause is not implied by state/inverse congruence alone.  The
   following predicates expose common-definedness, exact outcome stability,
   and selected-inverse stability under every foreign monoid map.  Outcomes
   are equality-specialized here; a future outcome relation must be supplied
   explicitly rather than inferred from R. -/
def DefinedAt {Γ : Type u} {Ω : Type v}
    (op : PartialOp Γ Ω) (γ : Γ) : Prop :=
  ∃ r, op γ = some r

def DefinednessStable {Γ : Type u} {Ω : Type v}
    (op : PartialOp Γ Ω) (foreign : Γ → Γ) : Prop :=
  ∀ γ, DefinedAt op (foreign γ) ↔ DefinedAt op γ

def OutcomeStable {Γ : Type u} {Ω : Type v}
    (op : PartialOp Γ Ω) (foreign : Γ → Γ) : Prop :=
  ∀ {γ : Γ} {a b : OpResult Γ Ω},
    op (foreign γ) = some a → op γ = some b → a.outcome = b.outcome

def SelectedInverseStableOp {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω) (foreign : Γ → Γ) : Prop :=
  ∀ {γ : Γ} {a b : OpResult Γ Ω},
    op (foreign γ) = some a → op γ = some b →
      PointwiseRel R a.undo b.undo

structure OperationForeignStability {Γ : Type u} {Ω : Type v}
    (R : RelSpec Γ) (op : PartialOp Γ Ω)
    (M : TransformationMonoidProfile Γ) : Prop where
  definedness : ∀ {h}, M.mem h → DefinednessStable op h
  outcome : ∀ {h}, M.mem h → OutcomeStable op h
  selected_inverse : ∀ {h}, M.mem h → SelectedInverseStableOp R op h

structure OperationIndependenceContract {Γ : Type u} {Ω₁ Ω₂ : Type v}
    (R : RelSpec Γ)
    (op₁ : PartialOp Γ Ω₁) (op₂ : PartialOp Γ Ω₂)
    (M₁ M₂ : TransformationMonoidProfile Γ) : Prop where
  commute : ∀ {f g}, M₁.mem f → M₂.mem g → CommuteUpTo R f g
  proper₁ : ∀ {f}, M₁.mem f → Respects R f
  proper₂ : ∀ {g}, M₂.mem g → Respects R g
  left : OperationForeignStability R op₁ M₂
  right : OperationForeignStability R op₂ M₁

/-! --------------------------------------------------------------------------
    Ranked iterator and its relational output contract
    -------------------------------------------------------------------------- -/

inductive StageResult (Γ : Type u) (Ξ : Type v) (Q : Type w) where
  | halt (state : Γ) (undo : Γ → Γ)
  | yield (state : Γ) (undo : Γ → Γ) (next : Q)
  | raise (error : Ξ)

structure RankedIterator (Γ : Type u) (Ξ : Type v) (Q : Type w) where
  root : Q
  rank : Q → Nat
  run : Q → Γ → StageResult Γ Ξ Q
  next_lt : ∀ {q γ δ undo q'},
    run q γ = .yield δ undo q' → rank q' < rank q

inductive ExecResult (Γ : Type u) (Ξ : Type v) where
  | success (state : Γ) (undo : Γ → Γ)
  | failure (error : Ξ) (state : Γ) (undo : Γ → Γ)

def composeUndo {Γ : Type u} (outer inner : Γ → Γ) : Γ → Γ :=
  outer ∘ inner

def execFrom {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (it : RankedIterator Γ Ξ Q) (q : Q) (γ : Γ) : ExecResult Γ Ξ :=
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

def exec {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (it : RankedIterator Γ Ξ Q) (γ : Γ) : ExecResult Γ Ξ :=
  execFrom it it.root γ

/- The same-input output relation for an execution result. -/
def ExecRel {Γ : Type u} {Ξ : Type v}
    (R : RelSpec Γ) (E : RelSpec Ξ)
    (a b : ExecResult Γ Ξ) : Prop :=
  match a, b with
  | .success x f, .success y g => R.rel x y ∧ PointwiseRel R f g
  | .failure e x f, .failure e' y g =>
      E.rel e e' ∧ R.rel x y ∧ PointwiseRel R f g
  | _, _ => False

def execRelSpec {Γ : Type u} {Ξ : Type v}
    (R : RelSpec Γ) (E : RelSpec Ξ) : RelSpec (ExecResult Γ Ξ) where
  rel := ExecRel R E
  refl := by
    intro x
    cases x with
    | success state undo =>
        exact ⟨R.refl state, pointwiseRel_refl R undo⟩
    | failure error state undo =>
        exact ⟨E.refl error, R.refl state, pointwiseRel_refl R undo⟩
  symm := by
    intro x y h
    cases x <;> cases y <;> simp [ExecRel] at h ⊢
    · exact ⟨R.symm h.1, pointwiseRel_symm h.2⟩
    · exact ⟨E.symm h.1, R.symm h.2.1, pointwiseRel_symm h.2.2⟩
  trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;>
      simp [ExecRel] at hxy hyz ⊢
    · exact ⟨R.trans hxy.1 hyz.1, pointwiseRel_trans hxy.2 hyz.2⟩
    · exact ⟨E.trans hxy.1 hyz.1, R.trans hxy.2.1 hyz.2.1,
        pointwiseRel_trans hxy.2.2 hyz.2.2⟩

def StageRelC {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (a b : StageResult Γ Ξ Q) : Prop :=
  match a, b with
  | .raise e, .raise e' => E.rel e e'
  | .halt x f, .halt y g => R.rel x y ∧ PointwiseRel R f g
  | .yield x f q, .yield y g q' =>
      R.rel x y ∧ PointwiseRel R f g ∧ C q q'
  | _, _ => False

/- A directional simulation.  Keeping this name separate from bisimulation is
   important: the execution theorem below only consumes the forward direction. -/
def IteratorSimulation {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (a b : RankedIterator Γ Ξ Q) : Prop :=
  C a.root b.root ∧
    ∀ q q' x y, C q q' → R.rel x y →
      StageRelC R E C (a.run q x) (b.run q' y)

/- A genuine bisimulation is a pair of simulations. -/
def IteratorBisim {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (a b : RankedIterator Γ Ξ Q) : Prop :=
  IteratorSimulation R E C a b ∧
    IteratorSimulation R E (fun q q' => C q' q) b a

/- D60's foreign-map clause compares the complete yielded package: state,
   selected inverse, and continuation.  It is stronger than inverse-only
   stability and deliberately remains parameterized by the continuation
   relation C. -/
def ContinuationStable {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (it : RankedIterator Γ Ξ Q) (foreign : Γ → Γ) : Prop :=
  ∀ q γ, StageRelC R E C
    (it.run q (foreign γ)) (it.run q γ)

/- Each inverse selected by a stage is required to preserve R.  This is what
   lets a same-input inverse relation compose across related boundary states. -/
def StageInverseProper {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) : StageResult Γ Ξ Q → Prop
  | .raise _ => True
  | .halt _ undo => Respects R undo
  | .yield _ undo _ => Respects R undo

def IteratorInverseProper {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (it : RankedIterator Γ Ξ Q) : Prop :=
  ∀ q γ, StageInverseProper R (it.run q γ)

structure IteratorIndependenceContract {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (a b : RankedIterator Γ Ξ Q)
    (M₁ M₂ : TransformationMonoidProfile Γ) : Prop where
  commute : ∀ {f g}, M₁.mem f → M₂.mem g → CommuteUpTo R f g
  proper₁ : ∀ {f}, M₁.mem f → Respects R f
  proper₂ : ∀ {g}, M₂.mem g → Respects R g
  inverse_proper₁ : IteratorInverseProper R a
  inverse_proper₂ : IteratorInverseProper R b
  stable₁₂ : ∀ {g}, M₂.mem g → ContinuationStable R E C a g
  stable₂₁ : ∀ {f}, M₁.mem f →
    ContinuationStable R E (fun q q' => C q' q) b f

/- The local inverse witness required by D51/D52.  A raise has no successful
   state and therefore carries no invented recovery equation. -/
def StageWitness {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (γ : Γ) : StageResult Γ Ξ Q → Prop
  | .raise _ => True
  | .halt δ undo => R.rel (undo δ) γ
  | .yield δ undo _ => R.rel (undo δ) γ

def IteratorWitness {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (it : RankedIterator Γ Ξ Q) : Prop :=
  ∀ q γ, StageWitness R γ (it.run q γ)

/- Same-node stage relation used by the local step law.  The continuation code
   is compared by ordinary equality here; StageRelC supports a wider C. -/
def StageRel {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ)
    (a b : StageResult Γ Ξ Q) : Prop :=
  StageRelC R E (fun q q' => q = q') a b

def StepLawful {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (it : RankedIterator Γ Ξ Q) : Prop :=
  ∀ q ⦃x y : Γ⦄, R.rel x y → StageRel R E (it.run q x) (it.run q y)

theorem iteratorSimulation_self_of_stepLawful
    {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ)
    (it : RankedIterator Γ Ξ Q)
    (hstep : StepLawful R E it) :
    IteratorSimulation R E (fun q q' => q = q') it it := by
  constructor
  · rfl
  · intro q q' x y hq hxy
    subst q'
    exact hstep q hxy

/- A compact law bundle used at trusted iterator boundaries.  The execution
   transport proof below deliberately takes the components separately so that
   a caller can supply a reachable-indexed refinement instead of this
   conservative all-node contract. -/
structure IteratorLawful {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (R : RelSpec Γ) (E : RelSpec Ξ) (it : RankedIterator Γ Ξ Q) : Prop where
  step_lawful : StepLawful R E it
  inverse_proper : IteratorInverseProper R it
  witness : IteratorWitness R it

/- D52 recovery closure: a stage witness plus inverse properness gives a
   relation-level recovery theorem for the complete (possibly failing) run. -/
theorem execFrom_witness
    {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (it : RankedIterator Γ Ξ Q) (R : RelSpec Γ)
    (hW : IteratorWitness R it)
    (hP : IteratorInverseProper R it)
    (q : Q) (γ : Γ) :
    match execFrom it q γ with
    | .success δ undo => R.rel (undo δ) γ
    | .failure _ δ undo => R.rel (undo δ) γ := by
  rw [execFrom.eq_1]
  cases hrun : it.run q γ with
  | raise error =>
      simp [hrun]
      exact R.refl γ
  | halt δ undo =>
      have hw := hW q γ
      rw [hrun] at hw
      change R.rel (undo δ) γ at hw
      exact hw
  | yield δ undo next =>
      have ih := execFrom_witness it R hW hP next δ
      simp [hrun]
      cases hnext : execFrom it next δ with
      | success final innerUndo =>
          have hi : R.rel (innerUndo final) δ := by
            simpa [hnext] using ih
          have hp := hP q γ
          rw [hrun] at hp
          have hp' : Respects R undo := by
            change ∀ {x y : Γ}, R.rel x y → R.rel (undo x) (undo y) at hp ⊢
            exact hp
          have hm := hp' hi
          have hw := hW q γ
          rw [hrun] at hw
          exact R.trans hm hw
      | failure error final innerUndo =>
          have hi : R.rel (innerUndo final) δ := by
            simpa [hnext] using ih
          have hp := hP q γ
          rw [hrun] at hp
          have hp' : Respects R undo := by
            change ∀ {x y : Γ}, R.rel x y → R.rel (undo x) (undo y) at hp ⊢
            exact hp
          have hm := hp' hi
          have hw := hW q γ
          rw [hrun] at hw
          exact R.trans hm hw
termination_by it.rank q
decreasing_by
  exact it.next_lt hrun

/- A helper for the yield branch of the execution-transport proof. -/
theorem yield_undo_transport {Γ : Type u}
    {R : RelSpec Γ} {f g h k : Γ → Γ}
    (hf : Respects R f) (hfg : PointwiseRel R f g)
    (hhk : PointwiseRel R h k) :
    PointwiseRel R (composeUndo f h) (composeUndo g k) := by
  exact compose_pointwiseRel hf hfg hhk

/- Coupled execution transport.  The induction measure is the sum of the two
   ranks; hence no equality of ranks is required by a continuation bisimulation. -/
theorem execFrom_rel
    {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (a b : RankedIterator Γ Ξ Q)
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (hsim : IteratorSimulation R E C a b)
    (hproperA : IteratorInverseProper R a)
    (hproperB : IteratorInverseProper R b)
    (q q' : Q) (x y : Γ) (hc : C q q') (hxy : R.rel x y) :
    ExecRel R E (execFrom a q x) (execFrom b q' y) := by
  rw [execFrom.eq_1, execFrom.eq_1]
  have hs := hsim.2 q q' x y hc hxy
  cases ha : a.run q x with
  | raise ea =>
      cases hb : b.run q' y with
      | raise eb =>
          have he : E.rel ea eb := by simpa [ha, hb, StageRelC] using hs
          exact ⟨he, hxy, by intro z; exact R.refl z⟩
      | halt δ' undo' =>
          simp [ha, hb, StageRelC] at hs
      | yield δ' undo' next' =>
          simp [ha, hb, StageRelC] at hs
  | halt δ undo =>
      cases hb : b.run q' y with
      | raise eb =>
          simp [ha, hb, StageRelC] at hs
      | halt δ' undo' =>
          have hout : R.rel δ δ' ∧ PointwiseRel R undo undo' := by
            simpa [ha, hb, StageRelC] using hs
          exact hout
      | yield δ' undo' next' =>
          simp [ha, hb, StageRelC] at hs
  | yield δ undo next =>
      cases hb : b.run q' y with
      | raise eb =>
          simp [ha, hb, StageRelC] at hs
      | halt δ' undo' =>
          simp [ha, hb, StageRelC] at hs
      | yield δ' undo' next' =>
          have hout : R.rel δ δ' ∧ PointwiseRel R undo undo' ∧ C next next' := by
            simpa [ha, hb, StageRelC] using hs
          have hnextA : a.rank next < a.rank q := a.next_lt ha
          have hnextB : b.rank next' < b.rank q' := b.next_lt hb
          have ih := execFrom_rel a b R E C hsim hproperA hproperB
            next next' δ δ' hout.2.2 hout.1
          simp [ha, hb]
          cases hca : execFrom a next δ with
          | success finalA innerA =>
              cases hcb : execFrom b next' δ' with
              | success finalB innerB =>
                  have hexec : ExecRel R E
                      (.success finalA innerA) (.success finalB innerB) := by
                    simpa [hca, hcb] using ih
                  have hproperUndoA : Respects R undo := by
                    have hp := hproperA q x
                    rw [ha] at hp
                    change ∀ {u v : Γ}, R.rel u v → R.rel (undo u) (undo v) at hp ⊢
                    exact hp
                  exact ⟨hexec.1,
                    yield_undo_transport hproperUndoA hout.2.1 hexec.2⟩
              | failure eb finalB innerB =>
                  simp [hca, hcb, ExecRel] at ih
          | failure ea finalA innerA =>
              cases hcb : execFrom b next' δ' with
              | success finalB innerB =>
                  simp [hca, hcb, ExecRel] at ih
              | failure eb finalB innerB =>
                  have hexec : ExecRel R E
                      (.failure ea finalA innerA) (.failure eb finalB innerB) := by
                    simpa [hca, hcb] using ih
                  have hproperUndoA : Respects R undo := by
                    have hp := hproperA q x
                    rw [ha] at hp
                    change ∀ {u v : Γ}, R.rel u v → R.rel (undo u) (undo v) at hp ⊢
                    exact hp
                  exact ⟨hexec.1, hexec.2.1,
                    yield_undo_transport hproperUndoA hout.2.1 hexec.2.2⟩
termination_by a.rank q + b.rank q'
decreasing_by omega

theorem exec_rel
    {Γ : Type u} {Ξ : Type v} {Q : Type w}
    (a b : RankedIterator Γ Ξ Q)
    (R : RelSpec Γ) (E : RelSpec Ξ) (C : Q → Q → Prop)
    (hsim : IteratorSimulation R E C a b)
    (hproperA : IteratorInverseProper R a)
    (hproperB : IteratorInverseProper R b)
    {x y : Γ} (hxy : R.rel x y) :
    ExecRel R E (exec a x) (exec b y) := by
  exact execFrom_rel a b R E C hsim hproperA hproperB
    a.root b.root x y hsim.1 hxy

/-! --------------------------------------------------------------------------
    Generic alpha actions and transport of states, inverse witnesses, iterators,
    and traces
    -------------------------------------------------------------------------- -/

structure AlphaAction (N : Type u) (X : Type v) where
  act : Equiv.Perm N → X → X
  act_id : ∀ x, act (Equiv.refl N) x = x
  act_comp : ∀ (χ ψ : Equiv.Perm N) x,
    act (χ * ψ) x = act χ (act ψ x)
  act_inv : ∀ (χ : Equiv.Perm N) x, act χ.symm (act χ x) = x

def AlphaInvariant {N : Type u} {X : Type v}
    (A : AlphaAction N X) (R : X → X → Prop) : Prop :=
  ∀ χ x y, R x y ↔ R (A.act χ x) (A.act χ y)

def renameUndo {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N) (undo : X → X) : X → X :=
  fun z => A.act χ (undo (A.act χ.symm z))

theorem renameUndo_apply {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N) (undo : X → X) (z : X) :
    renameUndo A χ undo z = A.act χ (undo (A.act χ.symm z)) := rfl

theorem respects_renameUndo {N : Type u} {X : Type v}
    (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (undo : X → X) (hundo : Respects R undo) :
    Respects R (renameUndo A χ undo) := by
  intro x y hxy
  have hxy' : R.rel (A.act χ.symm x) (A.act χ.symm y) :=
    (hinv χ.symm x y).1 hxy
  have hu := hundo hxy'
  exact (hinv χ _ _).1 hu

theorem pointwise_renameUndo {N : Type u} {X : Type v}
    (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    {f g : X → X} (hfg : PointwiseRel R f g) :
    PointwiseRel R (renameUndo A χ f) (renameUndo A χ g) := by
  intro z
  have hfg' := hfg (A.act χ.symm z)
  exact (hinv χ _ _).1 hfg'

def renameStage {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    : StageResult X Ξ Q → StageResult X Ξ Q
  | .raise e => .raise e
  | .halt x undo => .halt (A.act χ x) (renameUndo A χ undo)
  | .yield x undo q => .yield (A.act χ x) (renameUndo A χ undo) q

theorem stageRelC_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X) (E : RelSpec Ξ)
    (C : Q → Q → Prop) (hinv : AlphaInvariant A R.rel)
    (χ : Equiv.Perm N) {s t : StageResult X Ξ Q}
    (h : StageRelC R E C s t) :
    StageRelC R E C (renameStage A χ s) (renameStage A χ t) := by
  cases s with
  | raise e =>
      cases t with
      | raise e' => simpa [StageRelC, renameStage] using h
      | halt y g => simp [StageRelC, renameStage] at h
      | yield y g q' => simp [StageRelC, renameStage] at h
  | halt x f =>
      cases t with
      | raise e' => simp [StageRelC, renameStage] at h
      | halt y g =>
          have hxy : R.rel x y := h.1
          have hfg : PointwiseRel R f g := h.2
          refine ⟨(hinv χ x y).1 hxy, ?_⟩
          exact pointwise_renameUndo A R hinv χ hfg
      | yield y g q' => simp [StageRelC, renameStage] at h
  | yield x f q =>
      cases t with
      | raise e' => simp [StageRelC, renameStage] at h
      | halt y g => simp [StageRelC, renameStage] at h
      | yield y g q' =>
          have hxy : R.rel x y := h.1
          have hfg : PointwiseRel R f g := h.2.1
          refine ⟨(hinv χ x y).1 hxy, ?_, h.2.2⟩
          exact pointwise_renameUndo A R hinv χ hfg

def renameIterator {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) : RankedIterator X Ξ Q where
  root := it.root
  rank := it.rank
  run := fun q x => renameStage A χ (it.run q (A.act χ.symm x))
  next_lt := by
    intro q x δ undo q' h
    cases hrun : it.run q (A.act χ.symm x) with
    | raise e => simp [renameStage, hrun] at h
    | halt s u => simp [renameStage, hrun] at h
    | yield s u n =>
        simp [renameStage, hrun] at h
        have hn : n = q' := by
          have hh := (by simpa using h :
            A.act χ s = δ ∧ renameUndo A χ u = undo ∧ n = q')
          exact hh.2.2
        subst q'
        exact it.next_lt (q := q) (γ := A.act χ.symm x)
          (δ := s) (undo := u) (q' := n) hrun

theorem renameIterator_run_transport {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (q : Q) (x : X) :
    (renameIterator A χ it).run q (A.act χ x) =
      renameStage A χ (it.run q x) := by
  change renameStage A χ
      (it.run q (A.act χ.symm (A.act χ x))) = renameStage A χ (it.run q x)
  rw [A.act_inv]

theorem iteratorSimulation_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X) (E : RelSpec Ξ)
    (C : Q → Q → Prop) (hinv : AlphaInvariant A R.rel)
    (χ : Equiv.Perm N) (a b : RankedIterator X Ξ Q)
    (hsim : IteratorSimulation R E C a b) :
    IteratorSimulation R E C (renameIterator A χ a) (renameIterator A χ b) := by
  constructor
  · exact hsim.1
  · intro q q' x y hc hxy
    have hxy' : R.rel (A.act χ.symm x) (A.act χ.symm y) :=
      (hinv χ.symm x y).1 hxy
    have hs := hsim.2 q q' (A.act χ.symm x) (A.act χ.symm y) hc hxy'
    change StageRelC R E C
      (renameStage A χ (a.run q (A.act χ.symm x)))
      (renameStage A χ (b.run q' (A.act χ.symm y)))
    exact stageRelC_rename A R E C hinv χ hs

theorem iteratorBisim_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X) (E : RelSpec Ξ)
    (C : Q → Q → Prop) (hinv : AlphaInvariant A R.rel)
    (χ : Equiv.Perm N) (a b : RankedIterator X Ξ Q)
    (hbis : IteratorBisim R E C a b) :
    IteratorBisim R E C (renameIterator A χ a) (renameIterator A χ b) := by
  exact ⟨iteratorSimulation_rename A R E C hinv χ a b hbis.1,
    iteratorSimulation_rename A R E (fun q q' => C q' q) hinv χ b a hbis.2⟩

theorem iteratorInverseProper_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q)
    (hproper : IteratorInverseProper R it) :
    IteratorInverseProper R (renameIterator A χ it) := by
  intro q x
  cases hrun : it.run q (A.act χ.symm x) with
  | raise e =>
      simp [renameIterator, renameStage, hrun, StageInverseProper]
  | halt s u =>
      have hu := hproper q (A.act χ.symm x)
      rw [hrun] at hu
      have hu' : Respects R u := by
        change ∀ {p r : X}, R.rel p r → R.rel (u p) (u r) at hu ⊢
        exact hu
      have hren : Respects R (renameUndo A χ u) :=
        respects_renameUndo (A := A) (R := R) (hinv := hinv)
          (χ := χ) (undo := u) hu'
      change StageInverseProper R
        (renameStage A χ (it.run q (A.act χ.symm x)))
      rw [hrun]
      change Respects R (renameUndo A χ u)
      exact hren
  | yield s u n =>
      have hu := hproper q (A.act χ.symm x)
      rw [hrun] at hu
      have hu' : Respects R u := by
        change ∀ {p r : X}, R.rel p r → R.rel (u p) (u r) at hu ⊢
        exact hu
      have hren : Respects R (renameUndo A χ u) :=
        respects_renameUndo (A := A) (R := R) (hinv := hinv)
          (χ := χ) (undo := u) hu'
      change StageInverseProper R
        (renameStage A χ (it.run q (A.act χ.symm x)))
      rw [hrun]
      change Respects R (renameUndo A χ u)
      exact hren

def renameExec {N : Type u} {X : Type v} {Ξ : Type w}
    (A : AlphaAction N X) (χ : Equiv.Perm N) :
    ExecResult X Ξ → ExecResult X Ξ
  | .success x undo => .success (A.act χ x) (renameUndo A χ undo)
  | .failure e x undo => .failure e (A.act χ x) (renameUndo A χ undo)

theorem renameUndo_comp {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    (f g : X → X) :
    renameUndo A χ (f ∘ g) =
      renameUndo A χ f ∘ renameUndo A χ g := by
  funext z
  simp [renameUndo, Function.comp_def, A.act_inv]

theorem alpha_act_inv_right {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N) (x : X) :
    A.act χ (A.act χ.symm x) = x := by
  have h := A.act_comp χ χ.symm x
  have hmul : χ * χ.symm = Equiv.refl N := by
    ext n
    simp
  rw [hmul, A.act_id] at h
  exact h.symm

theorem iteratorWitness_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (hW : IteratorWitness R it) :
    IteratorWitness R (renameIterator A χ it) := by
  intro q x
  change StageWitness R x
    (renameStage A χ (it.run q (A.act χ.symm x)))
  cases hrun : it.run q (A.act χ.symm x) with
  | raise e =>
      simp [renameStage, StageWitness]
  | halt δ undo =>
      have hw := hW q (A.act χ.symm x)
      rw [hrun] at hw
      have hw' := (hinv χ _ _).1 hw
      rw [alpha_act_inv_right] at hw'
      change R.rel
        (A.act χ (undo (A.act χ.symm (A.act χ δ)))) x
      rw [A.act_inv]
      exact hw'
  | yield δ undo next =>
      have hw := hW q (A.act χ.symm x)
      rw [hrun] at hw
      have hw' := (hinv χ _ _).1 hw
      rw [alpha_act_inv_right] at hw'
      change R.rel
        (A.act χ (undo (A.act χ.symm (A.act χ δ)))) x
      rw [A.act_inv]
      exact hw'

theorem stepLawful_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X) (E : RelSpec Ξ)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (hstep : StepLawful R E it) :
    StepLawful R E (renameIterator A χ it) := by
  intro q x y hxy
  have hxy' : R.rel (A.act χ.symm x) (A.act χ.symm y) :=
    (hinv χ.symm x y).1 hxy
  have hs := hstep q hxy'
  change StageRelC R E (fun q q' => q = q')
    (renameStage A χ (it.run q (A.act χ.symm x)))
    (renameStage A χ (it.run q (A.act χ.symm y)))
  exact stageRelC_rename A R E (fun q q' => q = q') hinv χ hs

theorem iteratorLawful_rename {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (R : RelSpec X) (E : RelSpec Ξ)
    (hinv : AlphaInvariant A R.rel) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (hL : IteratorLawful R E it) :
    IteratorLawful R E (renameIterator A χ it) := by
  exact {
    step_lawful := stepLawful_rename A R E hinv χ it hL.step_lawful
    inverse_proper := iteratorInverseProper_rename A R hinv χ it hL.inverse_proper
    witness := iteratorWitness_rename A R hinv χ it hL.witness }

/- Full execution transport is proved by well-founded induction on the
   iterator rank.  The continuation/error payloads remain name-neutral in
   this profile; name-bearing variants must provide corresponding actions. -/
theorem execFrom_rename_transport {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (q : Q) (x : X) :
    execFrom (renameIterator A χ it) q (A.act χ x) =
      renameExec A χ (execFrom it q x) := by
  rw [execFrom.eq_1]
  have hrunTransport := renameIterator_run_transport A χ it q x
  rw [hrunTransport]
  rw [execFrom.eq_1]
  cases hrun : it.run q x with
  | raise e =>
      simp [renameStage, renameExec, hrun]
      apply funext
      intro z
      simp [renameUndo, alpha_act_inv_right]
  | halt δ undo =>
      simp [renameStage, renameExec, hrun]
  | yield δ undo next =>
      simp [renameStage, renameExec, hrun]
      have ih := execFrom_rename_transport A χ it next δ
      rw [ih]
      cases hres : execFrom it next δ with
      | success final innerUndo =>
          simp [hres, renameExec, composeUndo]
          rw [renameUndo_comp]
      | failure error final innerUndo =>
          simp [hres, renameExec, composeUndo]
          rw [renameUndo_comp]
termination_by it.rank q
decreasing_by
  exact it.next_lt hrun

theorem exec_rename_transport {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) (χ : Equiv.Perm N)
    (it : RankedIterator X Ξ Q) (x : X) :
    exec (renameIterator A χ it) (A.act χ x) =
      renameExec A χ (exec it x) := by
  change execFrom (renameIterator A χ it) it.root (A.act χ x) =
    renameExec A χ (execFrom it it.root x)
  exact execFrom_rename_transport A χ it it.root x

/- The recursive evaluator's full equality transport is an explicit boundary
   contract.  It is intentionally not asserted for name-bearing `Q`/`Ξ`; an
   integration profile must either supply opacity or actions on those payloads. -/
def ExecTransportContract {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) : Prop :=
  ∀ (χ : Equiv.Perm N) (it : RankedIterator X Ξ Q) (x : X),
    exec (renameIterator A χ it) (A.act χ x) =
      renameExec A χ (exec it x)

theorem execTransportContract_proof {N : Type u} {X : Type v} {Ξ : Type w} {Q : Type u}
    (A : AlphaAction N X) : @ExecTransportContract N X Ξ Q A := by
  intro χ it x
  exact exec_rename_transport A χ it x

structure Event (N : Type u) (X : Type v) where
  kind : Nat
  state : X
  name : Option N

def renameEvent {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N) (e : Event N X) : Event N X :=
  { kind := e.kind, state := A.act χ e.state, name := e.name.map χ }

theorem renameEvent_id {N : Type u} {X : Type v}
    (A : AlphaAction N X) (e : Event N X) :
    renameEvent A (Equiv.refl N) e = e := by
  cases e with
  | mk kind state name =>
      simp [renameEvent, A.act_id]

theorem renameEvent_comp {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ ψ : Equiv.Perm N) (e : Event N X) :
    renameEvent A (χ * ψ) e = renameEvent A χ (renameEvent A ψ e) := by
  cases e with
  | mk kind state name =>
      simp [renameEvent, A.act_comp]

structure Trace (N : Type u) (X : Type v) where
  events : List (Event N X)

def renameTrace {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ : Equiv.Perm N) (t : Trace N X) : Trace N X :=
  { events := t.events.map (renameEvent A χ) }

theorem renameTrace_id {N : Type u} {X : Type v}
    (A : AlphaAction N X) (t : Trace N X) :
    renameTrace A (Equiv.refl N) t = t := by
  cases t with
  | mk es =>
      unfold renameTrace
      dsimp
      congr 1
      induction es with
      | nil => rfl
      | cons e es ih =>
          simp only [List.map_cons]
          rw [renameEvent_id A e, ih]

theorem renameTrace_comp {N : Type u} {X : Type v}
    (A : AlphaAction N X) (χ ψ : Equiv.Perm N) (t : Trace N X) :
    renameTrace A (χ * ψ) t = renameTrace A χ (renameTrace A ψ t) := by
  cases t with
  | mk es =>
      unfold renameTrace
      dsimp
      congr 1
      induction es with
      | nil => rfl
      | cons e es ih =>
          simp only [List.map_cons]
          rw [renameEvent_comp A χ ψ e, ih]

/-! --------------------------------------------------------------------------
    Finite countermodel: weak inverse properness does not imply selected-
    inverse coherence (the repaired L35 obligation).
    -------------------------------------------------------------------------- -/

inductive Toy where
  | a | b | c
deriving DecidableEq, Repr

def toyObs : Toy → Bool
  | .a => false
  | .b => false
  | .c => true

def toyRel : RelSpec Toy where
  rel x y := toyObs x = toyObs y
  refl := fun x => rfl
  symm := by intro x y h; exact h.symm
  trans := by intro x y z h₁ h₂; exact h₁.trans h₂

def toyG : Toy → Toy := fun _ => .a
def toyG' : Toy → Toy
  | .c => .c
  | _ => .a

theorem toyG_proper : Respects toyRel toyG := by
  intro x y hxy
  rfl

theorem toyG'_proper : Respects toyRel toyG' := by
  intro x y hxy
  cases x <;> cases y <;> simp [toyRel, toyObs, toyG'] at hxy ⊢

def WeakEffectResult : Toy → Toy × (Toy → Toy) := fun x =>
  match x with
  | .a => (.a, toyG)
  | .b => (.b, toyG')
  | .c => (.c, id)

def WeakOperationLaw (e : Toy → Toy × (Toy → Toy)) : Prop :=
  (∀ x, Respects toyRel (e x).2) ∧
  (∀ x, toyRel.rel ((e x).2 (e x).1) x) ∧
  (∀ {x y}, toyRel.rel x y → toyRel.rel (e x).1 (e y).1)

def ToySelectedInverseCoherent (e : Toy → Toy × (Toy → Toy)) : Prop :=
  ∀ {x y}, toyRel.rel x y → PointwiseRel toyRel (e x).2 (e y).2

theorem weakEffectResult_weak : WeakOperationLaw WeakEffectResult := by
  constructor
  · intro x
    cases x
    · exact toyG_proper
    · exact toyG'_proper
    · intro a b hab
      exact hab
  constructor
  · intro x
    cases x <;> simp [WeakEffectResult, toyG, toyG', toyRel, toyObs]
  · intro x y hxy
    cases x <;> cases y <;> simp [WeakEffectResult, toyRel, toyObs] at hxy ⊢

theorem weakEffectResult_not_coherent :
    ¬ ToySelectedInverseCoherent WeakEffectResult := by
  intro h
  have hab : toyRel.rel Toy.a Toy.b := by rfl
  have hc := h (x := Toy.a) (y := Toy.b) hab Toy.c
  simpa [WeakEffectResult, toyG, toyG', toyRel, toyObs] using hc

end CordisADR06
