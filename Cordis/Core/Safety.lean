import Cordis.Core.Preservation

/-! # Core theorems: provider and withdrawal safety -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Spec Key} {s s' : State FiberId Key}

/-- Registered single-source implies uniqueness of target candidates. -/
theorem targetProviderValid_unique (wf : WellFormed spec s)
    {p q : FiberId} {k : Key}
    (hp : TargetProviderValid spec s p k)
    (hq : TargetProviderValid spec s q k) : p = q := by
  by_contra hpq
  rcases hp with ⟨hpreg, _, hpk⟩
  rcases hq with ⟨hqreg, _, hqk⟩
  exact Finset.disjoint_left.mp (wf.singleSource hpreg hqreg hpq) hpk hqk

theorem provider_complete_of_candidate (wf : WellFormed spec s)
    {p : FiberId} {k : Key} (hp : TargetProviderValid spec s p k) :
    provider spec s k = some p := by
  exact provider_eq_some_iff.mpr ⟨hp, fun q hq => targetProviderValid_unique wf hq hp⟩

/-- Under the invariant, any available target equals the retained committed
view.  Registered single-source is what rules out a different provider ID. -/
theorem targetView_eq_committed (wf : WellFormed spec s)
    {p : FiberId} {committed target : View Key FiberId}
    (hc : committedView s p = some committed)
    (ht : targetView spec s p = some target) : target = committed := by
  funext k
  by_cases hk : k ∈ (spec p).deps
  · rcases (wf.committed_covers p committed hc k).mpr hk with ⟨q, hq⟩
    rcases (targetView_covers ht k).mpr hk with ⟨r, hr⟩
    have qv := wf.committed_valid p committed hc k q hq
    have rv := (targetView_binding ht hr).2
    have : r = q := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (wf.singleSource rv.1 qv.1 hne) rv.2.2 qv.2.2
    subst r
    rw [hq, hr]
  · have hcn : committed k = none := by
      cases h : committed k with
      | none => rfl
      | some q => exact (hk ((wf.committed_covers p committed hc k).mp ⟨q, h⟩)).elim
    have htn : target k = none := by
      cases h : target k with
      | none => rfl
      | some q => exact (hk (targetView_binding ht h).1).elim
    rw [hcn, htn]

private theorem committed_consumer_registered (wf : WellFormed spec s)
    {c : FiberId} {v : View Key FiberId}
    (hv : committedView s c = some v) : c ∈ s.registered := by
  by_contra hc
  have hi := wf.unregistered_inactive c hc
  simp [committedView, hi] at hv

/-- Core theorem: every committed binding induces a static Priority edge. -/
theorem committed_implies_priority (wf : WellFormed spec s)
    {c p : FiberId} {v : View Key FiberId} {k : Key}
    (hv : committedView s c = some v) (hb : v k = some p) :
    Priority spec s p c := by
  rcases wf.committed_valid c v hv k p hb with ⟨hpreg, _, hprov⟩
  exact ⟨hpreg, committed_consumer_registered wf hv, k, hprov,
    (wf.committed_covers c v hv k).mp ⟨p, hb⟩⟩

/-- Core theorem: a retained committed consumer blocks physical unload. -/
theorem unload_blocked_by_committed_consumer
    {c p : FiberId} {v : View Key FiberId} {k : Key}
    (hv : committedView s c = some v) (hb : v k = some p) :
    ¬ unloadable s p := by
  intro hu
  exact hu ⟨c, v, k, hv, hb⟩

/-- Core theorem: target resolution never selects an unloading provider. -/
theorem target_never_selects_unloading
    {p : FiberId} {k : Key} {v : View Key FiberId}
    (hp : s.phase p = .unloading v) : provider spec s k ≠ some p := by
  intro hprovider
  rcases provider_sound hprovider with ⟨_, ⟨w, hw⟩, _⟩
  rw [hp] at hw
  cases hw

/-- Core theorem: the Unload rule's guard rules out every committed consumer. -/
theorem unload_implies_no_committed_consumer
    {p : FiberId} (h : StepAt spec p s s') :
    (∃ v, s.phase p = .unloading v ∧ s'.phase p = .inactive) →
      ¬ reliedUpon s p := by
  rintro ⟨v, hp, hp'⟩
  cases h with
  | begin hphase _ => simp [hphase] at hp
  | finish hphase _ => simp [hphase] at hp
  | divert _ _ => simp at hp'
  | leave _ _ => simp at hp'
  | unload _ hu => exact hu

end Cordis.Core
