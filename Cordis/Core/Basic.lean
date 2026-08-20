import Mathlib

/-!
# Cordis Core: lifecycle and dependency calculus

This file contains only the simplified lifecycle calculus.  It deliberately
does not model effects, iterators, asynchronous work, or orchestration.

The two provider predicates below are intentionally different.  A committed
binding may point at an unloading (and hence still installed) provider, while
a newly computed target may only select an active provider.
-/

namespace Cordis.Core

variable {FiberId Key : Type*}

/-- Static declaration for one fiber. -/
structure Spec (Key : Type*) where
  deps : Finset Key := ∅
  provs : Finset Key := ∅

/-- A committed dependency view.  Keys outside `deps` map to `none`. -/
abbrev View (Key FiberId : Type*) := Key → Option FiberId

/-- The four Core lifecycle phases. -/
inductive Phase (Key FiberId : Type*) where
  | inactive
  | reloading (view : View Key FiberId)
  | active (view : View Key FiberId)
  | unloading (view : View Key FiberId)

/-- Dynamic Core state.  `spec` is an external static catalog and is therefore
fixed by construction during lifecycle normalization. -/
structure State (FiberId Key : Type*) [DecidableEq FiberId] where
  registered : Finset FiberId
  phase : FiberId → Phase Key FiberId
  retired : Finset FiberId

namespace State

variable [DecidableEq FiberId]

/-- Replace the lifecycle phase of exactly one fiber. -/
def setPhase (s : State FiberId Key) (p : FiberId) (ph : Phase Key FiberId) :
    State FiberId Key :=
  { s with phase := Function.update s.phase p ph }

@[simp] theorem setPhase_registered (s : State FiberId Key) (p) (ph) :
    (s.setPhase p ph).registered = s.registered := rfl

@[simp] theorem setPhase_retired (s : State FiberId Key) (p) (ph) :
    (s.setPhase p ph).retired = s.retired := rfl

@[simp] theorem setPhase_self (s : State FiberId Key) (p) (ph) :
    (s.setPhase p ph).phase p = ph := by simp [setPhase]

@[simp] theorem setPhase_other (s : State FiberId Key) {p q} (h : q ≠ p) (ph) :
    (s.setPhase p ph).phase q = s.phase q := by simp [setPhase, h]

end State

/-- A fiber is installed throughout Reloading, Active, and Unloading. -/
def installed [DecidableEq FiberId] (s : State FiberId Key) (p : FiberId) : Prop :=
  s.phase p ≠ .inactive

/-- Only `Phase.active` is active. -/
def active [DecidableEq FiberId] (s : State FiberId Key) (p : FiberId) : Prop :=
  ∃ v, s.phase p = .active v

/-- The view retained by an installed fiber. -/
def committedView [DecidableEq FiberId] (s : State FiberId Key) (p : FiberId) :
    Option (View Key FiberId) :=
  match s.phase p with
  | .inactive => none
  | .reloading v | .active v | .unloading v => some v

@[simp] theorem committedView_eq_none_iff [DecidableEq FiberId]
    (s : State FiberId Key) (p : FiberId) :
    committedView s p = none ↔ s.phase p = .inactive := by
  cases h : s.phase p <;> simp [committedView, h]

theorem installed_iff_committedView_isSome [DecidableEq FiberId]
    (s : State FiberId Key) (p : FiberId) :
    installed s p ↔ (committedView s p).isSome := by
  cases h : s.phase p <;> simp [installed, committedView, h]

theorem active_installed [DecidableEq FiberId] {s : State FiberId Key} {p : FiberId} :
    active s p → installed s p := by
  rintro ⟨v, hv⟩
  simp [active, installed, hv]

/-- Validity used by committed dependency views. -/
def CommittedProviderValid [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key)
    (p : FiberId) (k : Key) : Prop :=
  p ∈ s.registered ∧ installed s p ∧ k ∈ (spec p).provs

/-- Validity used while computing a new target. -/
def TargetProviderValid [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key)
    (p : FiberId) (k : Key) : Prop :=
  p ∈ s.registered ∧ active s p ∧ k ∈ (spec p).provs

theorem targetProviderValid_committedProviderValid
    [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p : FiberId} {k : Key} :
    TargetProviderValid spec s p k → CommittedProviderValid spec s p k := by
  rintro ⟨hp, ha, hk⟩
  exact ⟨hp, active_installed ha, hk⟩

/-- Unique-candidate provider resolution.  In particular, malformed states
with two active candidates resolve to `none`; enumeration order is irrelevant. -/
noncomputable def provider [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) (k : Key) : Option FiberId :=
  by
    classical
    exact if h : ∃! p, TargetProviderValid spec s p k then some h.choose else none

theorem provider_eq_some_iff [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {k : Key} {p : FiberId} :
    provider spec s k = some p ↔
      TargetProviderValid spec s p k ∧
        ∀ q, TargetProviderValid spec s q k → q = p := by
  classical
  simp only [provider]
  split_ifs with h
  · constructor
    · intro heq
      have hp : h.choose = p := Option.some.inj heq
      subst p
      exact ⟨h.choose_spec.1, h.choose_spec.2⟩
    · rintro ⟨hp, hu⟩
      exact congrArg some (h.unique h.choose_spec.1 hp)
  · constructor
    · simp
    · rintro ⟨hp, hu⟩
      exact (h ⟨p, hp, hu⟩).elim

theorem provider_sound [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {k : Key} {p : FiberId}
    (h : provider spec s k = some p) : TargetProviderValid spec s p k :=
  (provider_eq_some_iff.mp h).1

/-- Every declared dependency presently has a unique active provider. -/
def dependenciesSatisfied [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) (p : FiberId) : Prop :=
  ∀ k ∈ (spec p).deps, ∃ q, provider spec s k = some q

/-- The exact new committed view, if all dependencies are satisfied. -/
noncomputable def targetView [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) (p : FiberId) :
    Option (View Key FiberId) :=
  by
    classical
    exact
      if hp : p ∈ s.registered ∧ p ∉ s.retired ∧ dependenciesSatisfied spec s p then
        some (fun k => if k ∈ (spec p).deps then provider spec s k else none)
      else none

/-- The propositional readiness condition underlying `targetView`. -/
def TargetReady [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) (p : FiberId) : Prop :=
  p ∈ s.registered ∧ p ∉ s.retired ∧ dependenciesSatisfied spec s p

theorem targetView_eq_none_iff_not_ready [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p : FiberId} :
    targetView spec s p = none ↔ ¬ TargetReady spec s p := by
  classical
  simp [targetView, TargetReady]

theorem targetView_isSome_iff_ready [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p : FiberId} :
    (targetView spec s p).isSome ↔ TargetReady spec s p := by
  classical
  simp [targetView, TargetReady]

theorem targetView_eq_some_iff [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p : FiberId}
    {v : View Key FiberId} :
    targetView spec s p = some v ↔
      p ∈ s.registered ∧ p ∉ s.retired ∧ dependenciesSatisfied spec s p ∧
      v = fun k => if k ∈ (spec p).deps then provider spec s k else none := by
  classical
  simp only [targetView]
  split_ifs with h
  · simp [h, eq_comm]
  · constructor
    · simp
    · rintro ⟨hr, hn, hs, -⟩
      exact (h ⟨hr, hn, hs⟩).elim

theorem targetView_binding [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p q : FiberId}
    {k : Key} {v : View Key FiberId}
    (ht : targetView spec s p = some v) (hv : v k = some q) :
    k ∈ (spec p).deps ∧ TargetProviderValid spec s q k := by
  classical
  rcases targetView_eq_some_iff.mp ht with ⟨_, _, _, rfl⟩
  have hk : k ∈ (spec p).deps := by
    by_contra hnot
    simp [hnot] at hv
  refine ⟨hk, provider_sound ?_⟩
  simpa [hk] using hv

theorem targetView_covers [DecidableEq FiberId] [DecidableEq Key]
    {spec : FiberId → Spec Key} {s : State FiberId Key} {p : FiberId}
    {v : View Key FiberId} (ht : targetView spec s p = some v) (k : Key) :
    (∃ q, v k = some q) ↔ k ∈ (spec p).deps := by
  classical
  rcases targetView_eq_some_iff.mp ht with ⟨_, _, hs, rfl⟩
  constructor
  · rintro ⟨q, hq⟩
    by_contra hk
    simp [hk] at hq
  · intro hk
    rcases hs k hk with ⟨q, hq⟩
    exact ⟨q, by simpa [hk] using hq⟩

/-- Registered single-source provision.  Unregistered catalog entries do not
participate. -/
def SingleSource [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) : Prop :=
  ∀ ⦃p q⦄, p ∈ s.registered → q ∈ s.registered → p ≠ q →
    Disjoint (spec p).provs (spec q).provs

/-- The Core invariant.  Acyclicity is deliberately not a field. -/
structure WellFormed [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) : Prop where
  singleSource : SingleSource spec s
  unregistered_inactive : ∀ p, p ∉ s.registered → s.phase p = .inactive
  committed_covers : ∀ p v, committedView s p = some v →
    ∀ k, (∃ q, v k = some q) ↔ k ∈ (spec p).deps
  committed_valid : ∀ p v, committedView s p = some v →
    ∀ k q, v k = some q → CommittedProviderValid spec s q k

/-- Direct static provider-to-consumer priority edge for one registered set. -/
def PriorityOn [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (registered : Finset FiberId)
    (providerId consumerId : FiberId) : Prop :=
  providerId ∈ registered ∧ consumerId ∈ registered ∧
    ∃ k, k ∈ (spec providerId).provs ∧ k ∈ (spec consumerId).deps

/-- State-indexed spelling of `PriorityOn`. -/
def Priority [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key)
    (providerId consumerId : FiberId) : Prop :=
  PriorityOn spec s.registered providerId consumerId

def PrioritySuccOn [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (registered : Finset FiberId)
    (consumer providerId : FiberId) : Prop :=
  PriorityOn spec registered providerId consumer

/-- Successor orientation used for well-founded induction: following an edge
from a provider to one of its consumers. -/
def PrioritySucc [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key)
    (consumer providerId : FiberId) : Prop :=
  PrioritySuccOn spec s.registered consumer providerId

/-- Acyclicity is an explicit theorem hypothesis, not part of `WellFormed`. -/
def PriorityAcyclic [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Spec Key) (s : State FiberId Key) : Prop :=
  WellFounded (PrioritySuccOn spec s.registered)

end Cordis.Core
