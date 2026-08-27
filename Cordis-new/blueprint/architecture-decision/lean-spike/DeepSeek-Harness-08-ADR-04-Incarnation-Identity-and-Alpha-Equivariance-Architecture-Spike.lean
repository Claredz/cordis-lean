/-
  ADR-04 BD-NAMES compiler spike.
  This file intentionally contains only the name/identity boundary; lifecycle,
  iterator, staging, and control semantics remain external contracts.  It is a
  standalone mirror and must not be imported beside production modules that
  declare the same names.

  Validation: checked with Lean 4.33.0 / Lake 5.0.0-src+d8b1897 in the pinned
  project environment on 2026-08-26; exit code 0 (warnings only).
-/

import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Dedup

universe u

namespace CordisADR04

noncomputable section

/- `IncarnationId` is intentionally an abstract theorem-level type parameter.
   An integration module may instantiate it with an opaque nominal/token type;
   the spike does not identify it with a runtime atom or loader entry. -/
variable {IncarnationId Key Payload Atom Generation : Type u}
variable [DecidableEq IncarnationId] [DecidableEq Key]

abbrev ParentRef (N : Type u) := Option N

structure NameCell (N K P : Type u) [DecidableEq K] where
  parent : ParentRef N
  view : Finmap (fun _ : K => N)
  payload : P

abbrev NameRegistry (N K P : Type u) [DecidableEq N] [DecidableEq K] :=
  Finmap (fun _ : N => NameCell N K P)

structure NameLedger (N : Type u) [DecidableEq N] where
  everIssued : Finset N

/-! Freshness is a witness/allocator interface, not a hidden deterministic
    counter.  A finite specialization may legitimately report exhaustion. -/
structure FreshSupply (N : Type u) [DecidableEq N] where
  choose : Finset N → Option N
  choose_fresh : ∀ used n, choose used = some n → n ∉ used
  choose_some_if_available : ∀ used, (∃ n, n ∉ used) →
    ∃ n, choose used = some n

def CurrentFresh (r : NameRegistry IncarnationId Key Payload) (n : IncarnationId) : Prop :=
  n ∉ r.keys

def EverFresh (ledger : NameLedger IncarnationId) (n : IncarnationId) : Prop :=
  n ∉ ledger.everIssued

def LedgerSound (r : NameRegistry IncarnationId Key Payload) (ledger : NameLedger IncarnationId) : Prop :=
  r.keys ⊆ ledger.everIssued

def ParentAllowed (r : NameRegistry IncarnationId Key Payload) : ParentRef IncarnationId → Prop
  | none => True
  | some p => p ∈ r.keys

def AllocationStep (old new : Finset IncarnationId) (n : IncarnationId) : Prop :=
  n ∉ old ∧ new = insert n old

def AllocationAllowed (r : NameRegistry IncarnationId Key Payload)
    (ledger : NameLedger IncarnationId) (parent : ParentRef IncarnationId) (n : IncarnationId) : Prop :=
  CurrentFresh r n ∧ EverFresh ledger n ∧ ParentAllowed r parent

structure RegistrationWitness (r : NameRegistry IncarnationId Key Payload)
    (ledger : NameLedger IncarnationId) (parent : ParentRef IncarnationId) (n : IncarnationId) : Type u where
  currentFresh : CurrentFresh r n
  everFresh : EverFresh ledger n
  parentAllowed : ParentAllowed r parent

def allocateLedger (ledger : NameLedger IncarnationId) (n : IncarnationId) : Option (NameLedger IncarnationId) :=
  if n ∈ ledger.everIssued then none
  else some { everIssued := insert n ledger.everIssued }

theorem allocateLedger_success (ledger : NameLedger IncarnationId) (n : IncarnationId)
    (h : EverFresh ledger n) :
    allocateLedger ledger n = some { everIssued := insert n ledger.everIssued } := by
  change n ∉ ledger.everIssued at h
  simp [allocateLedger, h]

theorem allocateLedger_failure (ledger : NameLedger IncarnationId) (n : IncarnationId)
    (h : ¬ EverFresh ledger n) :
    allocateLedger ledger n = none := by
  simp [allocateLedger, EverFresh] at h ⊢
  exact h

theorem allocationStep_insert (old : Finset IncarnationId) (n : IncarnationId)
    (h : n ∉ old) : AllocationStep old (insert n old) n := by
  exact ⟨h, rfl⟩

def renameFinset (χ : Equiv.Perm IncarnationId) (s : Finset IncarnationId) : Finset IncarnationId :=
  s.map χ.toEmbedding

theorem mem_renameFinset_iff (χ : Equiv.Perm IncarnationId) (s : Finset IncarnationId) (n : IncarnationId) :
    n ∈ renameFinset χ s ↔ χ.symm n ∈ s := by
  simp [renameFinset]

def mapValues (χ : Equiv.Perm IncarnationId) (m : Finmap (fun _ : Key => IncarnationId)) :
    Finmap (fun _ : Key => IncarnationId) :=
  Finmap.keysLookupEquiv.symm
    ⟨(m.keys, fun k => (m.lookup k).map χ),
      by
        intro k
        simp [Finmap.lookup_isSome, Finmap.mem_keys]
    ⟩

theorem mapValues_lookup (χ : Equiv.Perm IncarnationId)
    (m : Finmap (fun _ : Key => IncarnationId)) (k : Key) :
    (mapValues χ m).lookup k = (m.lookup k).map χ := by
  simp [mapValues]

def renameParent (χ : Equiv.Perm IncarnationId) (p : ParentRef IncarnationId) : ParentRef IncarnationId :=
  p.map χ

theorem renameParent_root (χ : Equiv.Perm IncarnationId) : renameParent χ none = none := by
  rfl

def renameCell (χ : Equiv.Perm IncarnationId) (c : NameCell IncarnationId Key Payload) :
    NameCell IncarnationId Key Payload :=
  { parent := renameParent χ c.parent
    view := mapValues χ c.view
    payload := c.payload }

def renameRegistry (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) : NameRegistry IncarnationId Key Payload :=
  Finmap.keysLookupEquiv.symm
    ⟨(r.keys.map χ.toEmbedding,
      fun n => (r.lookup (χ.symm n)).map (renameCell χ)),
      by
        intro n
        simp [Finmap.lookup_isSome, Finmap.mem_keys]
    ⟩

theorem renameRegistry_lookup (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) (n : IncarnationId) :
    (renameRegistry χ r).lookup n = (r.lookup (χ.symm n)).map (renameCell χ) := by
  simp [renameRegistry]

theorem renameRegistry_keys (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) :
    (renameRegistry χ r).keys = renameFinset χ r.keys := by
  simp [renameRegistry, renameFinset]

def renameLedger (χ : Equiv.Perm IncarnationId) (ledger : NameLedger IncarnationId) : NameLedger IncarnationId :=
  { everIssued := renameFinset χ ledger.everIssued }

theorem ledgerSound_rename (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) (ledger : NameLedger IncarnationId)
    (h : LedgerSound r ledger) :
    LedgerSound (renameRegistry χ r) (renameLedger χ ledger) := by
  intro n hn
  rw [renameRegistry_keys] at hn
  change n ∈ renameFinset χ ledger.everIssued
  rw [mem_renameFinset_iff]
  exact h ((mem_renameFinset_iff χ r.keys n).mp hn)

theorem everFresh_implies_currentFresh
    (r : NameRegistry IncarnationId Key Payload) (ledger : NameLedger IncarnationId)
    (hsound : LedgerSound r ledger) (n : IncarnationId) (hfresh : EverFresh ledger n) :
    CurrentFresh r n := by
  intro hn
  exact hfresh (hsound hn)

theorem allocationAllowed_of_everFresh
    (r : NameRegistry IncarnationId Key Payload) (ledger : NameLedger IncarnationId)
    (hsound : LedgerSound r ledger) (parent : ParentRef IncarnationId) (n : IncarnationId)
    (hparent : ParentAllowed r parent) (hfresh : EverFresh ledger n) :
    AllocationAllowed r ledger parent n := by
  exact ⟨everFresh_implies_currentFresh r ledger hsound n hfresh, hfresh, hparent⟩

theorem parentAllowed_rename_iff (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) (p : ParentRef IncarnationId) :
    ParentAllowed (renameRegistry χ r) (renameParent χ p) ↔
      ParentAllowed r p := by
  cases p <;> simp [ParentAllowed, renameParent, renameRegistry_keys,
    renameFinset]

structure NamedBoundary (N K P : Type u) [DecidableEq N] [DecidableEq K] where
  registry : NameRegistry N K P
  ledger : NameLedger N
  registry_subset_ledger : LedgerSound registry ledger

def renameBoundary (χ : Equiv.Perm IncarnationId)
    (b : NamedBoundary IncarnationId Key Payload) : NamedBoundary IncarnationId Key Payload :=
  { registry := renameRegistry χ b.registry
    ledger := renameLedger χ b.ledger
    registry_subset_ledger := ledgerSound_rename χ b.registry b.ledger
      b.registry_subset_ledger }

theorem renameBoundary_registry_lookup (χ : Equiv.Perm IncarnationId)
    (b : NamedBoundary IncarnationId Key Payload) (n : IncarnationId) :
    (renameBoundary χ b).registry.lookup n =
      (b.registry.lookup (χ.symm n)).map (renameCell χ) := by
  exact renameRegistry_lookup χ b.registry n

theorem renameBoundary_sound (χ : Equiv.Perm IncarnationId)
    (b : NamedBoundary IncarnationId Key Payload) :
    LedgerSound (renameBoundary χ b).registry (renameBoundary χ b).ledger := by
  exact (renameBoundary χ b).registry_subset_ledger

def checkRegistration (b : NamedBoundary IncarnationId Key Payload) (n : IncarnationId)
    (c : NameCell IncarnationId Key Payload) :
    Option (RegistrationWitness b.registry b.ledger c.parent n) := by
  classical
  if hissued : n ∈ b.ledger.everIssued then
    exact none
  else if hcurrent : n ∈ b.registry.keys then
    exact none
  else if hparent : ParentAllowed b.registry c.parent then
    exact some
      { currentFresh := hcurrent
        everFresh := hissued
        parentAllowed := hparent }
  else
    exact none

def registerFresh (b : NamedBoundary IncarnationId Key Payload) (n : IncarnationId)
    (c : NameCell IncarnationId Key Payload)
    (w : RegistrationWitness b.registry b.ledger c.parent n) :
    NamedBoundary IncarnationId Key Payload :=
  match w with
  | ⟨_currentFresh, _everFresh, _parentAllowed⟩ =>
      { registry := Finmap.insert n c b.registry
        ledger := { everIssued := insert n b.ledger.everIssued }
        registry_subset_ledger := by
          intro k hk
          have hk' : k = n ∨ k ∈ b.registry.keys := by
            simpa [Finmap.mem_keys] using hk
          rcases hk' with rfl | hold
          · simp
          · exact Finset.mem_insert_of_mem (b.registry_subset_ledger hold) }

def tryRegisterFresh (b : NamedBoundary IncarnationId Key Payload) (n : IncarnationId)
    (c : NameCell IncarnationId Key Payload) : Option (NamedBoundary IncarnationId Key Payload) :=
  (checkRegistration b n c).map (fun w => registerFresh b n c w)

theorem checkRegistration_success (b : NamedBoundary IncarnationId Key Payload) (n : IncarnationId)
    (c : NameCell IncarnationId Key Payload)
    (w : RegistrationWitness b.registry b.ledger c.parent n) :
    checkRegistration b n c = some w := by
  classical
  simp only [checkRegistration]
  split <;> rename_i hissued
  · exact False.elim (w.everFresh hissued)
  · split <;> rename_i hcurrent
    · exact False.elim (w.currentFresh hcurrent)
    · split <;> rename_i hparent
      · rfl
      · exact False.elim (hparent w.parentAllowed)

theorem currentFresh_rename_iff (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) (n : IncarnationId) :
    CurrentFresh (renameRegistry χ r) (χ n) ↔ CurrentFresh r n := by
  simp [CurrentFresh, renameRegistry_keys, renameFinset]

theorem everFresh_rename_iff (χ : Equiv.Perm IncarnationId)
    (ledger : NameLedger IncarnationId) (n : IncarnationId) :
    EverFresh (renameLedger χ ledger) (χ n) ↔ EverFresh ledger n := by
  simp [EverFresh, renameLedger, renameFinset]

theorem allocationStep_rename (χ : Equiv.Perm IncarnationId)
    (old new : Finset IncarnationId) (n : IncarnationId)
    (h : AllocationStep old new n) :
    AllocationStep (renameFinset χ old) (renameFinset χ new) (χ n) := by
  rcases h with ⟨hfresh, hnew⟩
  subst hnew
  constructor
  · simpa [renameFinset] using (show χ n ∉ old.map χ.toEmbedding from by
      simpa [renameFinset] using hfresh)
  · simp [renameFinset]

theorem renameFinset_id (s : Finset IncarnationId) :
    renameFinset (Equiv.refl IncarnationId) s = s := by
  simp [renameFinset]

theorem renameLedger_id (ledger : NameLedger IncarnationId) :
    renameLedger (Equiv.refl IncarnationId) ledger = ledger := by
  cases ledger
  simp [renameLedger, renameFinset]

theorem mapValues_id (m : Finmap (fun _ : Key => IncarnationId)) :
    mapValues (Equiv.refl IncarnationId) m = m := by
  apply Finmap.ext_lookup
  intro k
  simp [mapValues]

theorem renameCell_id (c : NameCell IncarnationId Key Payload) :
    renameCell (Equiv.refl IncarnationId) c = c := by
  cases c with
  | mk parent view payload =>
      simp [renameCell, renameParent, mapValues_id]

theorem renameRegistry_id (r : NameRegistry IncarnationId Key Payload) :
    renameRegistry (Equiv.refl IncarnationId) r = r := by
  apply Finmap.ext_lookup
  intro n
  rw [renameRegistry_lookup]
  cases h : r.lookup n with
  | none => simp [h]
  | some c => simp [h, renameCell_id]

structure RuntimeIdentity (A G : Type u) where
  atom : A
  generation : G

/-! These wrappers deliberately keep catalog/configuration identity, runtime atom
    identity, and theorem-level incarnation identity as different types. -/
structure ComponentId (C : Type u) where
  raw : C

structure EntryId (E : Type u) where
  raw : E

structure RealmId (R : Type u) where
  raw : R

structure RuntimeRefinement (N A G : Type u) where
  encode : RuntimeIdentity A G → N
  injective : Function.Injective encode

theorem runtime_reuse_separates (R : RuntimeRefinement IncarnationId Atom Generation)
    {a : Atom} {g₁ g₂ : Generation} (h : g₁ ≠ g₂) :
    R.encode ⟨a, g₁⟩ ≠ R.encode ⟨a, g₂⟩ := by
  intro heq
  apply h
  exact congrArg RuntimeIdentity.generation (R.injective heq)

def NoReuse {N : Type u} (allocations : List N) : Prop :=
  allocations.Pairwise (· ≠ ·)

structure AllocationTrace where
  allocations : List IncarnationId
  noReuse : NoReuse allocations

structure StepLabel (N K : Type u) [DecidableEq N] [DecidableEq K] where
  actor : Option N
  parent : Option N
  allocations : List N
  references : Finset N
  dependencyKeys : Finset K

def renameStepLabel (χ : Equiv.Perm IncarnationId)
    (label : StepLabel IncarnationId Key) : StepLabel IncarnationId Key :=
  { actor := label.actor.map χ
    parent := label.parent.map χ
    allocations := label.allocations.map χ
    references := renameFinset χ label.references
    dependencyKeys := label.dependencyKeys }

def BoundaryStepRelation (N K P : Type u) [DecidableEq N] [DecidableEq K] :=
  NamedBoundary N K P → StepLabel N K →
    NamedBoundary N K P → Prop

def StepEquivariant (step : BoundaryStepRelation IncarnationId Key Payload) : Prop :=
  ∀ (χ : Equiv.Perm IncarnationId) (before after : NamedBoundary IncarnationId Key Payload)
    (label : StepLabel IncarnationId Key),
    step before label after →
      step (renameBoundary χ before) (renameStepLabel χ label)
        (renameBoundary χ after)

def TraceHasFiniteNames {N : Type u} [DecidableEq N] (names : Set N) : Prop :=
  ∃ support : Finset N, names ⊆ (support : Set N)

def renameNameSet (χ : Equiv.Perm IncarnationId) (s : Set IncarnationId) : Set IncarnationId :=
  { n | χ.symm n ∈ s }

theorem finiteNames_rename (χ : Equiv.Perm IncarnationId) (s : Set IncarnationId)
    (h : TraceHasFiniteNames s) :
    TraceHasFiniteNames (renameNameSet χ s) := by
  rcases h with ⟨support, hsupport⟩
  refine ⟨renameFinset χ support, ?_⟩
  intro n hn
  exact (mem_renameFinset_iff χ support n).mpr (hsupport hn)

theorem noReuse_map (χ : Equiv.Perm IncarnationId) (xs : List IncarnationId)
    (h : NoReuse xs) : NoReuse (xs.map χ) := by
  induction xs with
  | nil => simp [NoReuse]
  | cons x xs ih =>
      simp only [List.map_cons, NoReuse, List.pairwise_cons] at h ⊢
      constructor
      · intro y hy heq
        rcases List.mem_map.1 hy with ⟨z, hz, rfl⟩
        apply h.1 z hz
        exact χ.injective heq
      · exact ih h.2

def OptionNamesSubset {N : Type u} (o : Option N) (s : Set N) : Prop :=
  ∀ n, o = some n → n ∈ s

def ListNamesSubset {N : Type u} (xs : List N) (s : Set N) : Prop :=
  ∀ n, n ∈ xs → n ∈ s

def LabelNamesSubset {N K : Type u} [DecidableEq N] [DecidableEq K]
    (label : StepLabel N K) (s : Set N) : Prop :=
  OptionNamesSubset label.actor s ∧
  OptionNamesSubset label.parent s ∧
  ListNamesSubset label.allocations s ∧
  (∀ n, n ∈ label.references → n ∈ s)

def BoundaryNamesSupported {N K P : Type u} [DecidableEq N] [DecidableEq K]
    (s : Set N) (b : NamedBoundary N K P) : Prop :=
  (∀ n, n ∈ b.registry.keys → n ∈ s) ∧
  (∀ n, n ∈ b.ledger.everIssued → n ∈ s) ∧
  (∀ n c, b.registry.lookup n = some c →
    OptionNamesSubset c.parent s ∧
      ∀ k m, c.view.lookup k = some m → m ∈ s)

def TraceFieldsSupported {N K : Type u} [DecidableEq N] [DecidableEq K]
    (names : Set N) (allocations : List N)
    (labels : List (StepLabel N K)) : Prop :=
  ListNamesSubset allocations names ∧
    ∀ label, label ∈ labels → LabelNamesSubset label names

structure NameTrace (N K P : Type u) [DecidableEq N] [DecidableEq K] where
  names : Set N
  boundaries : List (NamedBoundary N K P)
  allocations : List N
  labels : List (StepLabel N K)
  initialIssued : Finset N
  initialIssuedSupported : ∀ n, n ∈ initialIssued → n ∈ names
  finiteNames : TraceHasFiniteNames names
  noReuse : NoReuse allocations
  fieldsSupported : TraceFieldsSupported names allocations labels
  boundariesSupported : ∀ b, b ∈ boundaries → BoundaryNamesSupported names b
  allocationsComplete : allocations = labels.flatMap (fun label => label.allocations)
  allocationsFresh : ∀ n, n ∈ allocations → n ∉ initialIssued

def TraceRenameSpec (χ : Equiv.Perm IncarnationId)
    (before after : NameTrace IncarnationId Key Payload) : Prop :=
  after.names = renameNameSet χ before.names ∧
  after.boundaries = before.boundaries.map (renameBoundary χ) ∧
  after.allocations = before.allocations.map χ ∧
  after.labels = before.labels.map (renameStepLabel χ) ∧
  after.initialIssued = renameFinset χ before.initialIssued

def TraceEquivariant
    (rel : NameTrace IncarnationId Key Payload → NameTrace IncarnationId Key Payload → Prop) : Prop :=
  ∀ (χ : Equiv.Perm IncarnationId) (before after : NameTrace IncarnationId Key Payload),
    rel before after →
      ∃ before' after', TraceRenameSpec χ before before' ∧
        TraceRenameSpec χ after after' ∧ rel before' after'

def ParentClosed (r : NameRegistry IncarnationId Key Payload) : Prop :=
  ∀ ⦃child parent : IncarnationId⦄ ⦃c : NameCell IncarnationId Key Payload⦄,
    r.lookup child = some c → c.parent = some parent → parent ∈ r.keys

def ParentAcyclic (r : NameRegistry IncarnationId Key Payload) : Prop :=
  ∀ n, ¬ Relation.TransGen
    (fun child parent => ∃ c, r.lookup child = some c ∧ c.parent = some parent) n n

def ParentForest (r : NameRegistry IncarnationId Key Payload) : Prop :=
  ParentClosed r ∧ ParentAcyclic r

def NameWF (r : NameRegistry IncarnationId Key Payload) (ledger : NameLedger IncarnationId) : Prop :=
  LedgerSound r ledger ∧ ParentForest r

def AlphaRenamed (χ : Equiv.Perm IncarnationId)
    (r r' : NameRegistry IncarnationId Key Payload) : Prop :=
  ∀ n, r'.lookup (χ n) = (r.lookup n).map (renameCell χ)

theorem renameRegistry_is_alpha (χ : Equiv.Perm IncarnationId)
    (r : NameRegistry IncarnationId Key Payload) :
    AlphaRenamed χ r (renameRegistry χ r) := by
  intro n
  have h := renameRegistry_lookup χ r (χ n)
  rw [χ.symm_apply_apply] at h
  exact h

def WFEquivariant : Prop :=
  ∀ (χ : Equiv.Perm IncarnationId) (r : NameRegistry IncarnationId Key Payload)
    (ledger : NameLedger IncarnationId),
    NameWF r ledger → NameWF (renameRegistry χ r) (renameLedger χ ledger)

end
end CordisADR04
