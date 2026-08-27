/-
ADR-03 feasibility spike: a positive finite registry state shell for the
unified context/state decision.  The spike deliberately keeps lifecycle,
iterator, staging, control, naming, and scoped-realm choices abstract.

Validation status at creation:
* audited against the paper and the ADR-01/ADR-02 boundaries;
* Lean and Lake are unavailable in the creation environment;
* compiler validation is therefore pending in the project's pinned
  Lean/Mathlib environment.

This file is intentionally standalone.  Production files should import the
Store and StoreObs APIs selected by ADR-02 and the relation API selected by
ADR-01 rather than duplicate their definitions.
-/

import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Dedup

universe u v w

namespace CordisADR03

noncomputable section

variable {Ambient IncarnationId Key ComponentCode BehaviorCode AccumulatorCode Life : Type u}
variable {Value : Key → Type v}
variable [DecidableEq Key] [DecidableEq IncarnationId]

/-! ## 1. Parameters, stores, lifecycle policy, and provider views -/

abbrev Store (Value : Key → Type v) := Finmap Value

structure LifecyclePolicy (Life : Type u) where
  installed : Life → Bool
  providesNow : Life → Bool
  committedVisible : Life → Bool

structure ProviderView (IncarnationId Key : Type u) [DecidableEq Key] where
  domain : Finset Key
  providers : Finmap (fun _ : Key => IncarnationId)
  keys_eq_domain : providers.keys = domain

/-! A fiber carries data and codes, never a RawState-indexed closure. -/
structure FiberCell (IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u)
    [DecidableEq Key] where
  component : ComponentCode
  behavior : BehaviorCode
  requirements : Finset Key
  provisions : Finset Key
  parent : Option IncarnationId
  localStore : Store Value
  retired : Bool
  lifecycle : Life
  accumulator : Option AccumulatorCode
  committed : Option (ProviderView IncarnationId Key)

abbrev Fiber (IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] :=
  FiberCell IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

abbrev Registry (IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] :=
  Finmap (fun _ : IncarnationId =>
    Fiber IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life)

structure RawState (Ambient IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] where
  ambient : Ambient
  registry : Registry IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

local notation "FiberT" =>
  Fiber IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life
local notation "RegistryT" =>
  Registry IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life
local notation "RawStateT" =>
  RawState Ambient IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life

def emptyRaw (ambient : Ambient) : RawStateT :=
  { ambient := ambient, registry := ∅ }

def contributesNow (policy : LifecyclePolicy Life) (c : FiberT) : Prop :=
  -- Retirement is intentionally absent: O-Retire may leave an Active fiber
  -- contributing until L-Leave changes the lifecycle predicate.
  policy.providesNow c.lifecycle = true

/-! ## 2. Derived active coeffect projection -/

def activeUnionAux (policy : LifecyclePolicy Life) (r : RegistryT) :
    List IncarnationId → Store Value → Store Value
  | [], acc => acc
  | n :: ns, acc =>
      match Finmap.lookup n r with
      | none => activeUnionAux policy r ns acc
      | some c =>
          let next := if policy.providesNow c.lifecycle then acc ∪ c.localStore else acc
          activeUnionAux policy r ns next

def activeUnion (policy : LifecyclePolicy Life) (s : RawStateT) : Store Value :=
  -- This finite-list traversal is a semantic representative.  Production
  -- code should replace it with `Finmap.foldl` plus the absorbing-Option
  -- commutativity proof described by ADR-03.
  activeUnionAux policy s.registry s.registry.keys.toList ∅

/-! The production proof must establish this contract from disjointness. -/
def ActiveUnionIndependent (policy : LifecyclePolicy Life) (s : RawStateT) : Prop :=
  ∀ (l₁ l₂ : List IncarnationId),
    List.Perm l₁ l₂ →
      activeUnionAux policy s.registry l₁ ∅ =
        activeUnionAux policy s.registry l₂ ∅

def seededCoeffect (seed : Store Value) (policy : LifecyclePolicy Life)
    (s : RawStateT) : Store Value :=
  seed ∪ activeUnion policy s

theorem seededCoeffect_empty (seed : Store Value) (policy : LifecyclePolicy Life)
    (ambient : Ambient) :
    seededCoeffect seed policy (emptyRaw ambient : RawStateT) = seed := by
  simp [seededCoeffect, activeUnion, activeUnionAux, emptyRaw]

/-! ## 3. Well-formedness predicates and provider relation -/

def ParentEdge (r : RegistryT) (child parent : IncarnationId) : Prop :=
  ∃ c, Finmap.lookup child r = some c ∧ c.parent = some parent

def ParentClosed (r : RegistryT) : Prop :=
  ∀ ⦃child parent : IncarnationId⦄,
    ParentEdge r child parent → ∃ c, Finmap.lookup parent r = some c

def ParentAcyclic (r : RegistryT) : Prop :=
  ∀ n, ¬ Relation.TransGen (ParentEdge r) n n

def TableConfined (r : RegistryT) : Prop :=
  ∀ n c, Finmap.lookup n r = some c →
    ∀ k, k ∈ c.localStore → k ∈ c.provisions

def ProvisionDisjoint (r : RegistryT) : Prop :=
  ∀ ⦃n m : IncarnationId⦄ ⦃c₁ c₂ : FiberT⦄,
    n ≠ m → Finmap.lookup n r = some c₁ →
      Finmap.lookup m r = some c₂ → Disjoint c₁.provisions c₂.provisions

def LifecycleCoherent (policy : LifecyclePolicy Life) (r : RegistryT) : Prop :=
  ∀ n c, Finmap.lookup n r = some c →
    (policy.installed c.lifecycle = true →
      c.accumulator.isSome ∧ c.committed.isSome) ∧
    (c.accumulator.isSome → policy.installed c.lifecycle = true) ∧
    (c.committed.isSome → policy.installed c.lifecycle = true) ∧
    (policy.providesNow c.lifecycle = true →
      policy.installed c.lifecycle = true ∧ c.accumulator.isSome) ∧
    (policy.committedVisible c.lifecycle = true →
      c.committed.isSome ∧ c.accumulator.isSome)

def CommittedViewClosed (r : RegistryT) : Prop :=
  ∀ n c view, Finmap.lookup n r = some c → c.committed = some view →
    view.domain = c.requirements

def CommittedProvidersClosed (policy : LifecyclePolicy Life) (r : RegistryT) : Prop :=
  ∀ n c view, Finmap.lookup n r = some c → c.committed = some view →
    ∀ k m, k ∈ view.domain → Finmap.lookup k view.providers = some m →
      ∃ providerCell, Finmap.lookup m r = some providerCell ∧
        policy.installed providerCell.lifecycle = true

def WellFormed (policy : LifecyclePolicy Life) (s : RawStateT) : Prop :=
  ParentClosed s.registry ∧
  ParentAcyclic s.registry ∧
  TableConfined s.registry ∧
  ProvisionDisjoint s.registry ∧
  LifecycleCoherent policy s.registry ∧
  CommittedViewClosed s.registry ∧
  CommittedProvidersClosed policy s.registry

def ValidState (policy : LifecyclePolicy Life) :=
  { s : RawStateT // WellFormed policy s }

def ProvidesNow (policy : LifecyclePolicy Life) (r : RegistryT)
    (n : IncarnationId) (k : Key) : Prop :=
  ∃ c, Finmap.lookup n r = some c ∧
    contributesNow policy c ∧ k ∈ c.localStore

def ProviderOf (policy : LifecyclePolicy Life) (r : RegistryT)
    (k : Key) (n : IncarnationId) : Prop :=
  ProvidesNow policy r n k

theorem active_provider_unique (policy : LifecyclePolicy Life) (r : RegistryT)
    (hconf : TableConfined r) (hprov : ProvisionDisjoint r)
    {n m : IncarnationId} {k : Key}
    (hn : ProvidesNow policy r n k) (hm : ProvidesNow policy r m k) :
    n = m := by
  rcases hn with ⟨c₁, hn₁, hactive₁, hk₁⟩
  rcases hm with ⟨c₂, hn₂, hactive₂, hk₂⟩
  by_contra hne
  have hp₁ : k ∈ c₁.provisions := hconf n c₁ hn₁ k hk₁
  have hp₂ : k ∈ c₂.provisions := hconf m c₂ hn₂ k hk₂
  have hd : Disjoint c₁.provisions c₂.provisions := hprov hne hn₁ hn₂
  have hfalse : False := (Finset.disjoint_left.mp hd) hp₁ hp₂
  exact hfalse.elim

noncomputable def providerOf (policy : LifecyclePolicy Life) (s : RawStateT)
    (k : Key) : Option IncarnationId := by
  classical
  if h : ∃ n, ProviderOf policy s.registry k n then
    exact some (Classical.choose h)
  else
    exact none

/-! ## 4. Target/committed lookup shells -/

def targetEligible (_policy : LifecyclePolicy Life) (c : FiberT) : Prop :=
  -- An unretired Inactive fiber still has a target and may reload.
  c.retired = false

def TargetViewValid (policy : LifecyclePolicy Life) (r : RegistryT)
    (n : IncarnationId) (view : ProviderView IncarnationId Key) : Prop :=
  ∃ c, Finmap.lookup n r = some c ∧ targetEligible policy c ∧
    view.domain = c.requirements ∧
    ∀ k, k ∈ c.requirements →
      ∃ m, Finmap.lookup k view.providers = some m ∧
        ProvidesNow policy r m k

noncomputable def targetView (policy : LifecyclePolicy Life) (s : RawStateT)
    (n : IncarnationId) : Option (ProviderView IncarnationId Key) := by
  classical
  if h : ∃ view, TargetViewValid policy s.registry n view then
    exact some (Classical.choose h)
  else
    exact none

def GlobalLookup (policy : LifecyclePolicy Life) (s : RawStateT) (k : Key) :
    Option (Value k) :=
  Finmap.lookup k (activeUnion policy s)

def CommittedLookup (s : RawStateT) (n : IncarnationId) (k : Key) :
    Option (Value k) :=
  match Finmap.lookup n s.registry with
  | none => none
  | some c =>
      match c.committed with
      | none => none
      | some view =>
          match Finmap.lookup k view.providers with
          | none => none
          | some provider =>
              match Finmap.lookup provider s.registry with
              | none => none
              | some providerCell => Finmap.lookup k providerCell.localStore

def ReliedOn (policy : LifecyclePolicy Life) (r : RegistryT)
    (provider : IncarnationId) : Prop :=
  ∃ consumer c view k,
    consumer ≠ provider ∧
    Finmap.lookup consumer r = some c ∧
    policy.installed c.lifecycle = true ∧
    c.committed = some view ∧
    Finmap.lookup k view.providers = some provider

/-! ## 5. Pure registry updates and frame laws -/

def insertFiber (n : IncarnationId) (c : FiberT) (s : RawStateT) : RawStateT :=
  { s with registry := Finmap.insert n c s.registry }

def modifyFiber (n : IncarnationId) (f : FiberT → FiberT) (s : RawStateT) : RawStateT :=
  match Finmap.lookup n s.registry with
  | none => s
  | some c => insertFiber n (f c) s

def removeFiber (n : IncarnationId) (s : RawStateT) : RawStateT :=
  { s with registry := Finmap.erase n s.registry }

theorem insertFiber_ambient (n : IncarnationId) (c : FiberT) (s : RawStateT) :
    (insertFiber n c s).ambient = s.ambient := rfl

theorem modifyFiber_ambient (n : IncarnationId) (f : FiberT → FiberT) (s : RawStateT) :
    (modifyFiber n f s).ambient = s.ambient := by
  simp only [modifyFiber]
  split <;> rfl

theorem removeFiber_ambient (n : IncarnationId) (s : RawStateT) :
    (removeFiber n s).ambient = s.ambient := rfl

theorem insertFiber_same (n : IncarnationId) (c : FiberT) (s : RawStateT) :
    Finmap.lookup n (insertFiber n c s).registry = some c := by
  simp [insertFiber]

theorem insertFiber_frame (n m : IncarnationId) (c : FiberT) (s : RawStateT)
    (hne : m ≠ n) :
    Finmap.lookup m (insertFiber n c s).registry = Finmap.lookup m s.registry := by
  simp [insertFiber, Finmap.lookup_insert_of_ne s.registry hne]

theorem removeFiber_frame (n m : IncarnationId) (s : RawStateT)
    (hne : m ≠ n) :
    Finmap.lookup m (removeFiber n s).registry = Finmap.lookup m s.registry := by
  simp [removeFiber, Finmap.lookup_erase_ne hne]

/-! ## 6. D32 tracking and external actor-indexed semantics -/

structure TrackedContext (Ambient IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] where
  state : RawState Ambient IncarnationId Key Value
    ComponentCode BehaviorCode AccumulatorCode Life
  accumulator : AccumulatorCode

local notation "TrackedContextT" =>
  TrackedContext Ambient IncarnationId Key Value
    ComponentCode BehaviorCode AccumulatorCode Life

def TrackedCoeffect (policy : LifecyclePolicy Life) (ctx : TrackedContextT) :
    Store Value :=
  activeUnion policy ctx.state

/-! This relation is deliberately provisional: later ADRs may add iterator,
failure, and control outcome witnesses without changing the state carrier. -/
structure ActionSemantics (Ambient IncarnationId Key : Type u) (Value : Key → Type v)
    (ComponentCode BehaviorCode AccumulatorCode Life : Type u) [DecidableEq Key] where
  forward : IncarnationId → BehaviorCode →
    RawState Ambient IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life →
    RawState Ambient IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life →
    AccumulatorCode → Prop
  inverse : IncarnationId → AccumulatorCode →
    RawState Ambient IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life →
    RawState Ambient IncarnationId Key Value ComponentCode BehaviorCode AccumulatorCode Life → Prop

local notation "ActionSemanticsT" =>
  ActionSemantics Ambient IncarnationId Key Value
    ComponentCode BehaviorCode AccumulatorCode Life

/-! A later ADR supplies the relation between these code denotations and the
ADR-01 state equivalence; it is intentionally not a field of RawState. -/
def CodeDenotationRespect (R : RawStateT → RawStateT → Prop)
    (sem : ActionSemanticsT) : Prop :=
  ∀ n b s₁ s₂ t₁ t₂ a,
    R s₁ s₂ → sem.forward n b s₁ t₁ a → sem.forward n b s₂ t₂ a → R t₁ t₂

def WFPreserving (sem : ActionSemanticsT) (wf : RawStateT → Prop) : Prop :=
  (∀ n b s t a, wf s → sem.forward n b s t a → wf t) ∧
  (∀ n a s t, wf s → sem.inverse n a s t → wf t)

abbrev StateMap (State : Type*) := State → State
abbrev ControlEdit (State : Type*) := State → State

def composeStep (edit : ControlEdit RawStateT) (body : StateMap RawStateT) :
    StateMap RawStateT :=
  edit ∘ body

omit [DecidableEq IncarnationId] in
theorem composeStep_apply (edit : ControlEdit RawStateT) (body : StateMap RawStateT)
    (s : RawStateT) :
    composeStep edit body s = edit (body s) := rfl

/-! ## 7. ADR-01/ADR-02 observation boundary -/

def OptionRel {α : Type w} (R : α → α → Prop) :
    Option α → Option α → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

def StoreObs (R : (k : Key) → Value k → Value k → Prop)
    (left right : Store Value) : Prop :=
  ∀ k, OptionRel (R k) (Finmap.lookup k left) (Finmap.lookup k right)

def CoreStateObs (R : (k : Key) → Value k → Value k → Prop)
    (policy : LifecyclePolicy Life) (s t : RawStateT) : Prop :=
  StoreObs R (activeUnion policy s) (activeUnion policy t)

def AmbientObs (A : Ambient → Ambient → Prop)
    (R : (k : Key) → Value k → Value k → Prop)
    (policy : LifecyclePolicy Life) (s t : RawStateT) : Prop :=
  A s.ambient t.ambient ∧ CoreStateObs R policy s t

/-! ## 8. Simple boundary and contract declarations -/

def ActiveUnionContract (policy : LifecyclePolicy Life) : Prop :=
  ∀ s : RawStateT, WellFormed policy s → ActiveUnionIndependent policy s

def ProviderUniqueContract (policy : LifecyclePolicy Life) : Prop :=
  ∀ s : RawStateT, WellFormed policy s →
    ∀ {n m k}, ProvidesNow policy s.registry n k →
      ProvidesNow policy s.registry m k → n = m

end
end CordisADR03
