/-
ADR-02 feasibility spike: finite dependent coeffect stores, semantic versus
executable specifications, checked binding protocols, and an Option-Kleisli
partial-effect companion to ADR-01.

Validation status at creation:
* audited against the current Mathlib `Finmap` and `Finset` APIs;
* Lean and Lake are unavailable in the creation environment;
* compiler validation is therefore pending in the project's pinned
  Lean/Mathlib environment.

This is a standalone architecture spike. Production code will import ADR-01's
relation API instead of repeating the small `RelSpec` definition below.
-/

import Mathlib.Data.Finmap

universe u v w x y

namespace CordisADR02

/-! ## 1. Concrete finite dependent store and two specification layers -/

abbrev Store {K : Type u} (V : K → Type v) := Finmap V
abbrev SemanticSpec (K : Type u) := Set K
abbrev ExecSpec (K : Type u) := Finset K
abbrev Provision (K : Type u) := Finset K

def semanticize {K : Type u} (d : ExecSpec K) : SemanticSpec K :=
  (d : Set K)

def SatisfiesSem {K : Type u} {V : K → Type v}
    (σ : Store V) (d : SemanticSpec K) : Prop :=
  ∀ ⦃k : K⦄, k ∈ d → k ∈ σ

def SatisfiesExec {K : Type u} {V : K → Type v} [DecidableEq K]
    (σ : Store V) (d : ExecSpec K) : Prop :=
  d ⊆ σ.keys

theorem satisfiesExec_iff_semantic {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (d : ExecSpec K) :
    SatisfiesExec σ d ↔ SatisfiesSem σ (semanticize d) := by
  constructor
  · intro h k hk
    exact Finmap.mem_keys.mp (h hk)
  · intro h k hk
    exact Finmap.mem_keys.mpr (h hk)

def satisfiesB {K : Type u} {V : K → Type v} [DecidableEq K]
    (σ : Store V) (d : ExecSpec K) : Bool :=
  decide (SatisfiesExec σ d)

theorem satisfiesB_eq_true_iff {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (d : ExecSpec K) :
    satisfiesB σ d = true ↔ SatisfiesExec σ d := by
  simp [satisfiesB]

inductive Notification where
  | activating
  | deactivating
  | neutral
  deriving DecidableEq, Repr

def ClassifiesSem {K : Type u} {V : K → Type v}
    (before after : Store V) (d : SemanticSpec K) : Notification → Prop
  | .activating => ¬ SatisfiesSem before d ∧ SatisfiesSem after d
  | .deactivating => SatisfiesSem before d ∧ ¬ SatisfiesSem after d
  | .neutral => SatisfiesSem before d ↔ SatisfiesSem after d

def ClassifiesExec {K : Type u} {V : K → Type v} [DecidableEq K]
    (before after : Store V) (d : ExecSpec K) : Notification → Prop
  | .activating => ¬ SatisfiesExec before d ∧ SatisfiesExec after d
  | .deactivating => SatisfiesExec before d ∧ ¬ SatisfiesExec after d
  | .neutral => SatisfiesExec before d ↔ SatisfiesExec after d

def notify {K : Type u} {V : K → Type v} [DecidableEq K]
    (before after : Store V) (d : ExecSpec K) : Notification :=
  if SatisfiesExec before d then
    if SatisfiesExec after d then .neutral else .deactivating
  else if SatisfiesExec after d then .activating else .neutral

theorem notify_classifies_exec {K : Type u} {V : K → Type v}
    [DecidableEq K] (before after : Store V) (d : ExecSpec K) :
    ClassifiesExec before after d (notify before after d) := by
  by_cases hb : SatisfiesExec before d <;>
    by_cases ha : SatisfiesExec after d <;>
    simp [notify, ClassifiesExec, hb, ha]

theorem classifiesExec_iff_semantic {K : Type u} {V : K → Type v}
    [DecidableEq K] (before after : Store V) (d : ExecSpec K)
    (n : Notification) :
    ClassifiesExec before after d n ↔
      ClassifiesSem before after (semanticize d) n := by
  cases n <;>
    simp only [ClassifiesExec, ClassifiesSem, satisfiesExec_iff_semantic]

theorem notify_adequate {K : Type u} {V : K → Type v}
    [DecidableEq K] (before after : Store V) (d : ExecSpec K) :
    ClassifiesSem before after (semanticize d) (notify before after d) :=
  (classifiesExec_iff_semantic before after d _).mp
    (notify_classifies_exec before after d)

/-! ## 2. Raw store operations versus legal binding transitions -/

inductive StoreError where
  | missing
  | alreadyPresent
  deriving DecidableEq, Repr

def provide? {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (value : V k) (σ : Store V) : Option (Store V) :=
  if k ∈ σ then none else some (Finmap.insert k value σ)

def provideE {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (value : V k) (σ : Store V) : Except StoreError (Store V) :=
  if k ∈ σ then .error .alreadyPresent
  else .ok (Finmap.insert k value σ)

/-- On success, revocation returns the new store and the captured old value.
    Absence-guarded re-provision of that value is the successful inverse. -/
def revoke? {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (σ : Store V) : Option (Store V × V k) :=
  match Finmap.lookup k σ with
  | none => none
  | some old => some (Finmap.erase k σ, old)

def revokeE {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (σ : Store V) : Except StoreError (Store V × V k) :=
  match Finmap.lookup k σ with
  | none => .error .missing
  | some old => .ok (Finmap.erase k σ, old)

/-- Proof-indexed successful interface for theorem statements. -/
def provideWith {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (value : V k) (σ : Store V) (_fresh : k ∉ σ) : Store V :=
  Finmap.insert k value σ

theorem provideE_ok_iff_provide_some {K : Type u} {V : K → Type v}
    [DecidableEq K] (k : K) (value : V k) (σ τ : Store V) :
    provideE k value σ = .ok τ ↔ provide? k value σ = some τ := by
  by_cases h : k ∈ σ <;> simp [provideE, provide?, h]

theorem revokeE_ok_iff_revoke_some {K : Type u} {V : K → Type v}
    [DecidableEq K] (k : K) (σ : Store V) (r : Store V × V k) :
    revokeE k σ = .ok r ↔ revoke? k σ = some r := by
  cases h : Finmap.lookup k σ <;> simp [revokeE, revoke?, h]

theorem erase_insert_fresh {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k : K) (value : V k)
    (fresh : k ∉ σ) :
    Finmap.erase k (Finmap.insert k value σ) = σ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = k
  · subst x
    rw [Finmap.lookup_erase]
    exact (Finmap.lookup_eq_none.mpr fresh).symm
  · rw [Finmap.lookup_erase_ne hx]
    rw [Finmap.lookup_insert_of_ne σ hx]

theorem insert_erase_restores {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k : K) (old : V k)
    (found : Finmap.lookup k σ = some old) :
    Finmap.insert k old (Finmap.erase k σ) = σ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = k
  · subst x
    rw [Finmap.lookup_insert]
    exact found.symm
  · rw [Finmap.lookup_insert_of_ne _ hx]
    rw [Finmap.lookup_erase_ne hx]

/-- The inverse returned by successful provide is itself protocol-guarded:
    it revokes only if the key is still present. -/
def undoProvide? {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (σ : Store V) : Option (Store V) :=
  (revoke? k σ).map Prod.fst

/-- The inverse returned by successful revoke is an absence-guarded provide of
    the value captured by the forward run, never an unchecked overwrite. -/
def undoRevoke? {K : Type u} {V : K → Type v} [DecidableEq K]
    (k : K) (old : V k) (σ : Store V) : Option (Store V) :=
  provide? k old σ

theorem undoProvide_recovers {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k : K) (value : V k)
    (fresh : k ∉ σ) :
    undoProvide? k (Finmap.insert k value σ) = some σ := by
  simp [undoProvide?, revoke?, erase_insert_fresh σ k value fresh]

theorem undoRevoke_recovers {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k : K) (old : V k)
    (found : Finmap.lookup k σ = some old) :
    undoRevoke? k old (Finmap.erase k σ) = some σ := by
  simp [undoRevoke?, provide?, Finmap.notMem_erase_self,
    insert_erase_restores σ k old found]

theorem insert_frame {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k j : K) (value : V k)
    (different : j ≠ k) :
    Finmap.lookup j (Finmap.insert k value σ) = Finmap.lookup j σ :=
  Finmap.lookup_insert_of_ne σ different

theorem insert_keys_of_mem {K : Type u} {V : K → Type v}
    [DecidableEq K] (σ : Store V) (k : K) (value : V k)
    (present : k ∈ σ) :
    (Finmap.insert k value σ).keys = σ.keys := by
  ext j
  simp [Finmap.mem_keys, present]

/-! ## 3. The Option-Kleisli partiality companion -/

abbrev PartialMap (α : Type u) (β : Type v) := α → Option β

def pid {α : Type u} : PartialMap α α := some

/-- Execute `first`, then `second`. -/
def pcomp {α : Type u} {β : Type v} {γ : Type w}
    (first : PartialMap α β) (second : PartialMap β γ) : PartialMap α γ :=
  fun x => (first x).bind second

theorem pcomp_left_id {α : Type u} {β : Type v}
    (f : PartialMap α β) : pcomp pid f = f := by
  funext x
  rfl

theorem pcomp_right_id {α : Type u} {β : Type v}
    (f : PartialMap α β) : pcomp f pid = f := by
  funext x
  cases h : f x <;> simp [pcomp, pid, h]

theorem pcomp_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (f : PartialMap α β) (g : PartialMap β γ) (h : PartialMap γ δ) :
    pcomp (pcomp f g) h = pcomp f (pcomp g h) := by
  funext a
  cases hfa : f a with
  | none => simp [pcomp, hfa]
  | some b =>
      cases hgb : g b <;> simp [pcomp, hfa, hgb]

def OptionRel {α : Type u} (R : α → α → Prop) :
    Option α → Option α → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

def PRespects {α : Type u} {β : Type v}
    (R : α → α → Prop) (S : β → β → Prop)
    (f : PartialMap α β) : Prop :=
  ∀ ⦃x y⦄, R x y → OptionRel S (f x) (f y)

def PPointwiseRel {α : Type u} {β : Type v}
    (S : β → β → Prop) (f g : PartialMap α β) : Prop :=
  ∀ x, OptionRel S (f x) (g x)

theorem optionRel_refl {α : Type u} {R : α → α → Prop}
    (hrefl : ∀ x, R x x) (x : Option α) : OptionRel R x x := by
  cases x <;> simp [OptionRel, hrefl]

theorem optionRel_trans {α : Type u} {R : α → α → Prop}
    (htrans : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    {a b c : Option α} :
    OptionRel R a b → OptionRel R b c → OptionRel R a c := by
  cases a <;> cases b <;> cases c <;>
    simp only [OptionRel]
  exact htrans

theorem pcomp_prespects {α : Type u} {R : α → α → Prop}
    {f g : PartialMap α α}
    (hf : PRespects R R f) (hg : PRespects R R g) :
    PRespects R R (pcomp f g) := by
  intro x y hxy
  have h := hf hxy
  cases hx : f x <;> cases hy : f y <;>
    simp [OptionRel, pcomp, hx, hy] at h ⊢
  exact hg h

theorem pcomp_pointwise_cross {α : Type u} {R : α → α → Prop}
    (htrans : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    {f f' g g' : PartialMap α α}
    (hf : PRespects R R f)
    (hff' : PPointwiseRel R f f')
    (hgg' : PPointwiseRel R g g') :
    PPointwiseRel R (pcomp g f) (pcomp g' f') := by
  intro z
  have hg := hgg' z
  cases hgz : g z <;> cases hg'z : g' z <;>
    simp [OptionRel, pcomp, hgz, hg'z] at hg ⊢
  have hleft := hf hg
  exact optionRel_trans htrans hleft (hff' _)

theorem optionRel_bind {α : Type u} {R : α → α → Prop}
    {f : PartialMap α α} (hf : PRespects R R f)
    {a b : Option α} (hab : OptionRel R a b) :
    OptionRel R (a.bind f) (b.bind f) := by
  cases ha : a <;> cases hb : b <;>
    simp [OptionRel, ha, hb] at hab ⊢
  exact hf hab

structure RelSpec (α : Type u) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ ⦃x y⦄, rel x y → rel y x
  trans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z

structure PartialResult (Γ : Type u) (B : Type v) where
  state : Γ
  undo : PartialMap Γ Γ
  outcome : B

abbrev PartialEffect (Γ : Type u) (B : Type v) :=
  Γ → Option (PartialResult Γ B)

/-- Successful effect return. The selected inverse is partial identity. -/
def ppure {Γ : Type u} {B : Type v} (outcome : B) : PartialEffect Γ B :=
  fun state => some {
    state := state
    undo := pid
    outcome := outcome
  }

/-- Outcome-dependent sequencing for D41. If either stage is undefined, the
    big-step mathematical denotation has no successor. On two successes the
    selected inverses compose in reverse execution order. -/
def pbindEffect {Γ : Type u} {B : Type v} {C : Type w}
    (first : PartialEffect Γ B)
    (next : B → PartialEffect Γ C) : PartialEffect Γ C :=
  fun state =>
    match first state with
    | none => none
    | some r₁ =>
        match next r₁.outcome r₁.state with
        | none => none
        | some r₂ => some {
            state := r₂.state
            undo := pcomp r₂.undo r₁.undo
            outcome := r₂.outcome
          }

theorem pbindEffect_second_failure {Γ : Type u} {B : Type v} {C : Type w}
    (first : PartialEffect Γ B) (next : B → PartialEffect Γ C)
    (state : Γ) (r₁ : PartialResult Γ B)
    (hfirst : first state = some r₁)
    (hnext : next r₁.outcome r₁.state = none) :
    pbindEffect first next state = none := by
  simp [pbindEffect, hfirst, hnext]

theorem pbindEffect_left_unit {Γ : Type u} {B : Type v} {C : Type w}
    (outcome : B) (next : B → PartialEffect Γ C) :
    pbindEffect (ppure outcome) next = next outcome := by
  funext state
  cases hnext : next outcome state <;>
    simp [pbindEffect, ppure, hnext, pcomp_right_id]

theorem pbindEffect_right_unit {Γ : Type u} {B : Type v}
    (e : PartialEffect Γ B) :
    pbindEffect e (fun outcome => ppure outcome) = e := by
  funext state
  cases he : e state <;>
    simp [pbindEffect, ppure, he, pcomp_left_id]

theorem pbindEffect_assoc {Γ : Type u} {B : Type v} {C : Type w}
    {D : Type x} (e : PartialEffect Γ B)
    (f : B → PartialEffect Γ C) (g : C → PartialEffect Γ D) :
    pbindEffect (pbindEffect e f) g =
      pbindEffect e (fun outcome => pbindEffect (f outcome) g) := by
  funext state
  cases he : e state with
  | none => simp [pbindEffect, he]
  | some r₁ =>
      cases hf : f r₁.outcome r₁.state with
      | none => simp [pbindEffect, he, hf]
      | some r₂ =>
          cases hg : g r₂.outcome r₂.state <;>
            simp [pbindEffect, he, hf, hg, pcomp_assoc]

namespace PartialResult

def Rel {Γ : Type u} {B : Type v} (S : RelSpec Γ)
    (left right : PartialResult Γ B) : Prop :=
  S.rel left.state right.state ∧
    PPointwiseRel S.rel left.undo right.undo ∧
    left.outcome = right.outcome

end PartialResult

/-- ADR-01's output law lifted through `Option`. `run_respects` gives equal
    definedness and, on success, related states, pointwise-related selected
    inverses, and exact outcomes. -/
structure IsLawfulPartialEffect {Γ : Type u} {B : Type v}
    (S : RelSpec Γ) (e : PartialEffect Γ B) : Prop where
  run_respects : ∀ ⦃x y⦄, S.rel x y →
    OptionRel (PartialResult.Rel S) (e x) (e y)
  undo_respects : ∀ ⦃x⦄ ⦃r : PartialResult Γ B⦄,
    e x = some r → PRespects S.rel S.rel r.undo
  recovers : ∀ ⦃x⦄ ⦃r : PartialResult Γ B⦄,
    e x = some r → OptionRel S.rel (r.undo r.state) (some x)

/-- Evidence needed to restrict a partial effect to a total effect on an
    invariant subtype. Forward totality alone would not make the selected undo
    total on that subtype. -/
structure TotalizableOn {Γ : Type u} {B : Type v}
    (I : Γ → Prop) (e : PartialEffect Γ B) : Prop where
  run_total : ∀ x, I x → ∃ r, e x = some r
  state_closed : ∀ ⦃x⦄ ⦃r : PartialResult Γ B⦄,
    I x → e x = some r → I r.state
  undo_total_closed : ∀ ⦃x⦄ ⦃r : PartialResult Γ B⦄,
    I x → e x = some r → ∀ y, I y →
      ∃ z, r.undo y = some z ∧ I z

theorem pbindEffect_lawful {Γ : Type u} {B : Type v} {C : Type w}
    (S : RelSpec Γ)
    (first : PartialEffect Γ B) (next : B → PartialEffect Γ C)
    (hfirst : IsLawfulPartialEffect S first)
    (hnext : ∀ b, IsLawfulPartialEffect S (next b)) :
    IsLawfulPartialEffect S (pbindEffect first next) := by
  refine {
    run_respects := ?_
    undo_respects := ?_
    recovers := ?_
  }
  · intro x y hxy
    have h₁ := hfirst.run_respects hxy
    cases ex : first x with
    | none =>
        cases ey : first y <;>
          simp [pbindEffect, ex, ey, OptionRel] at h₁ ⊢
    | some r₁ =>
        cases ey : first y with
        | none => simp [ex, ey, OptionRel] at h₁
        | some s₁ =>
            have hrs : PartialResult.Rel S r₁ s₁ := by
              simpa [ex, ey, OptionRel] using h₁
            rcases r₁ with ⟨state₁, undo₁, out₁⟩
            rcases s₁ with ⟨state₂, undo₂, out₂⟩
            change S.rel state₁ state₂ ∧
              PPointwiseRel S.rel undo₁ undo₂ ∧ out₁ = out₂ at hrs
            subst out₂
            have h₂ := (hnext out₁).run_respects hrs.1
            cases en : next out₁ state₁ with
            | none =>
                cases em : next out₁ state₂ <;>
                  simp [pbindEffect, ex, ey, en, em, OptionRel] at h₂ ⊢
            | some r₂ =>
                cases em : next out₁ state₂ with
                | none => simp [en, em, OptionRel] at h₂
                | some s₂ =>
                    have ht : PartialResult.Rel S r₂ s₂ := by
                      simpa [en, em, OptionRel] using h₂
                    simp only [pbindEffect, ex, ey, en, em, OptionRel]
                    refine ⟨ht.1, ?_, ht.2.2⟩
                    exact pcomp_pointwise_cross S.trans
                      (hfirst.undo_respects ex) hrs.2.1 ht.2.1
  · intro x r hr
    cases ex : first x with
    | none => simp [pbindEffect, ex] at hr
    | some r₁ =>
        cases en : next r₁.outcome r₁.state with
        | none => simp [pbindEffect, ex, en] at hr
        | some r₂ =>
            have hrEq : r = {
                state := r₂.state
                undo := pcomp r₂.undo r₁.undo
                outcome := r₂.outcome } := by
              exact Option.some.inj
                (by simpa [pbindEffect, ex, en] using hr.symm)
            subst r
            exact pcomp_prespects
              ((hnext r₁.outcome).undo_respects en)
              (hfirst.undo_respects ex)
  · intro x r hr
    cases ex : first x with
    | none => simp [pbindEffect, ex] at hr
    | some r₁ =>
        cases en : next r₁.outcome r₁.state with
        | none => simp [pbindEffect, ex, en] at hr
        | some r₂ =>
            have hrEq : r = {
                state := r₂.state
                undo := pcomp r₂.undo r₁.undo
                outcome := r₂.outcome } := by
              exact Option.some.inj
                (by simpa [pbindEffect, ex, en] using hr.symm)
            subst r
            have h₂rec := (hnext r₁.outcome).recovers en
            have hlift : OptionRel S.rel
                ((r₂.undo r₂.state).bind r₁.undo)
                ((some r₁.state).bind r₁.undo) :=
              optionRel_bind (hfirst.undo_respects ex) h₂rec
            exact optionRel_trans S.trans hlift (hfirst.recovers ex)

/-! ## 4. Total ADR-01 fragment embeds into the partial companion -/

structure TotalResult (Γ : Type u) (B : Type v) where
  state : Γ
  undo : Γ → Γ
  outcome : B

abbrev TotalEffect (Γ : Type u) (B : Type v) := Γ → TotalResult Γ B

namespace TotalResult

def Rel {Γ : Type u} {B : Type v} (S : RelSpec Γ)
    (left right : TotalResult Γ B) : Prop :=
  S.rel left.state right.state ∧
    (∀ z, S.rel (left.undo z) (right.undo z)) ∧
    left.outcome = right.outcome

end TotalResult

structure IsLawfulTotalEffect {Γ : Type u} {B : Type v}
    (S : RelSpec Γ) (e : TotalEffect Γ B) : Prop where
  run_respects : ∀ ⦃x y⦄, S.rel x y → TotalResult.Rel S (e x) (e y)
  undo_respects : ∀ x ⦃a b⦄, S.rel a b →
    S.rel ((e x).undo a) ((e x).undo b)
  recovers : ∀ x, S.rel ((e x).undo (e x).state) x

def embedTotal {Γ : Type u} {B : Type v}
    (e : TotalEffect Γ B) : PartialEffect Γ B :=
  fun x => some {
    state := (e x).state
    undo := fun y => some ((e x).undo y)
    outcome := (e x).outcome
  }

theorem embedTotal_lawful {Γ : Type u} {B : Type v}
    (S : RelSpec Γ) (e : TotalEffect Γ B)
    (lawful : IsLawfulTotalEffect S e) :
    IsLawfulPartialEffect S (embedTotal e) := by
  refine {
    run_respects := ?_
    undo_respects := ?_
    recovers := ?_
  }
  · intro x y hxy
    have h := lawful.run_respects hxy
    change PartialResult.Rel S _ _
    refine ⟨h.1, ?_, h.2.2⟩
    intro z
    change S.rel ((e x).undo z) ((e y).undo z)
    exact h.2.1 z
  · intro x r hr
    simp only [embedTotal] at hr
    cases hr
    intro a b hab
    exact lawful.undo_respects x hab
  · intro x r hr
    simp only [embedTotal] at hr
    cases hr
    exact lawful.recovers x

/-! ## 5. Typed heterogeneous D24 operations and their key-local lift -/

structure KeyOperation (K : Type u) (V : K → Type v) where
  Op : K → Type w
  Arg : (k : K) → Op k → Type x
  Out : (k : K) → Op k → Type y
  run : (k : K) → (op : Op k) → Arg k op → V k →
    Option (PartialResult (V k) (Out k op))

def liftKey {K : Type u} {V : K → Type v} [DecidableEq K]
    (I : KeyOperation K V) (k : K) (op : I.Op k) (arg : I.Arg k op) :
    PartialEffect (Store V) (I.Out k op) :=
  fun σ =>
    match Finmap.lookup k σ with
    | none => none
    | some local =>
        match I.run k op arg local with
        | none => none
        | some r => some {
            state := Finmap.insert k r.state σ
            undo := fun τ =>
              match Finmap.lookup k τ with
              | none => none
              | some current =>
                  match r.undo current with
                  | none => none
                  | some restored => some (Finmap.insert k restored τ)
            outcome := r.outcome
          }

theorem liftKey_missing {K : Type u} {V : K → Type v} [DecidableEq K]
    (I : KeyOperation K V) (k : K) (op : I.Op k) (arg : I.Arg k op)
    (σ : Store V) (missing : Finmap.lookup k σ = none) :
    liftKey I k op arg σ = none := by
  simp [liftKey, missing]

/-! ## 6. Store observation preserves definedness and satisfaction -/

def StoreObs {K : Type u} {V : K → Type v} [DecidableEq K]
    (R : (k : K) → V k → V k → Prop) (left right : Store V) : Prop :=
  ∀ k, OptionRel (R k) (Finmap.lookup k left) (Finmap.lookup k right)

theorem storeObs_defined_iff {K : Type u} {V : K → Type v}
    [DecidableEq K] {R : (k : K) → V k → V k → Prop}
    {left right : Store V} (h : StoreObs R left right) (k : K) :
    Finmap.lookup k left ≠ none ↔ Finmap.lookup k right ≠ none := by
  have hk := h k
  cases hl : Finmap.lookup k left <;>
    cases hr : Finmap.lookup k right <;>
    simp [hl, hr, OptionRel] at hk ⊢

theorem storeObs_mem_iff {K : Type u} {V : K → Type v}
    [DecidableEq K] {R : (k : K) → V k → V k → Prop}
    {left right : Store V} (h : StoreObs R left right) (k : K) :
    k ∈ left ↔ k ∈ right := by
  have hisSome :
      (Finmap.lookup k left).isSome = true ↔
        (Finmap.lookup k right).isSome = true := by
    have hk := h k
    cases hl : Finmap.lookup k left <;>
      cases hr : Finmap.lookup k right <;>
      simp [hl, hr, OptionRel] at hk ⊢
  calc
    k ∈ left ↔ (Finmap.lookup k left).isSome = true :=
      Finmap.lookup_isSome.symm
    _ ↔ (Finmap.lookup k right).isSome = true := hisSome
    _ ↔ k ∈ right := Finmap.lookup_isSome

theorem storeObs_satisfiesSem_iff {K : Type u} {V : K → Type v}
    [DecidableEq K] {R : (k : K) → V k → V k → Prop}
    {left right : Store V} (h : StoreObs R left right)
    (d : SemanticSpec K) :
    SatisfiesSem left d ↔ SatisfiesSem right d := by
  constructor
  · intro hs k hk
    exact (storeObs_mem_iff h k).mp (hs hk)
  · intro hs k hk
    exact (storeObs_mem_iff h k).mpr (hs hk)

end CordisADR02
