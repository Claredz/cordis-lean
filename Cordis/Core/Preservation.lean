import Cordis.Core.Step

/-! # Core theorem: lifecycle preservation -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable {spec : FiberId → Spec Key}

private theorem committedView_setPhase_other
    (s : State FiberId Key) {p q : FiberId} (h : q ≠ p) (ph : Phase Key FiberId) :
    committedView (s.setPhase p ph) q = committedView s q := by
  simp only [committedView, State.setPhase_other s h ph]

private theorem installed_setPhase_other
    (s : State FiberId Key) {p q : FiberId} (h : q ≠ p) (ph : Phase Key FiberId) :
    installed (s.setPhase p ph) q ↔ installed s q := by
  simp only [installed, State.setPhase_other s h ph]

private theorem valid_after_installed_change
    {s : State FiberId Key} {p : FiberId} {new : Phase Key FiberId}
    (hnew : new ≠ .inactive) :
    ∀ {q k}, CommittedProviderValid spec s q k →
      CommittedProviderValid spec (s.setPhase p new) q k := by
  intro q k h
  rcases h with ⟨hqreg, hqinst, hk⟩
  refine ⟨by simpa using hqreg, ?_, hk⟩
  by_cases hqp : q = p
  · subst q
    simpa [installed] using hnew
  · exact (installed_setPhase_other s hqp new).2 hqinst

private theorem valid_after_begin
    {s : State FiberId Key} {p r : FiberId} {k : Key} {v : View Key FiberId}
    (hp : s.phase p = .inactive)
    (h : CommittedProviderValid spec s r k) :
    CommittedProviderValid spec (s.setPhase p (.reloading v)) r k := by
  rcases h with ⟨hrreg, hrinst, hk⟩
  refine ⟨by simpa using hrreg, ?_, hk⟩
  have hrp : r ≠ p := by
    rintro rfl
    exact hrinst (by simpa [installed] using hp)
  exact (installed_setPhase_other s hrp (.reloading v)).2 hrinst

/-- Core theorem: Begin preserves `WellFormed`. -/
theorem StepAt.begin_preserve_wellFormed
    {s : State FiberId Key} {p : FiberId} {v : View Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = .inactive)
    (ht : targetView spec s p = some v) :
    WellFormed spec (s.setPhase p (.reloading v)) := by
  let s' := s.setPhase p (.reloading v)
  have hpreg : p ∈ s.registered := (targetView_eq_some_iff.mp ht).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [SingleSource, s'] using wf.singleSource
  · intro q hq
    have hqold : q ∉ s.registered := by simpa [s'] using hq
    have hne : q ≠ p := fun heq => by subst q; exact hqold hpreg
    simpa [s', State.setPhase_other s hne] using wf.unregistered_inactive q hqold
  · intro q w hview k
    by_cases hqp : q = p
    · subst q
      have : v = w := by simpa [s', committedView] using hview
      subst w
      exact targetView_covers ht k
    · exact wf.committed_covers q w
        (by simpa [s', committedView_setPhase_other s hqp] using hview) k
  · intro q w hview k r hbind
    by_cases hqp : q = p
    · subst q
      have : v = w := by simpa [s', committedView] using hview
      subst w
      exact valid_after_begin hp (targetProviderValid_committedProviderValid
        (targetView_binding ht hbind).2)
    · have hold := wf.committed_valid q w
        (by simpa [s', committedView_setPhase_other s hqp] using hview) k r hbind
      exact valid_after_begin hp hold

private theorem preserve_installed_to_installed
    {s : State FiberId Key} {p : FiberId} {old new : Phase Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = old)
    (hold : old ≠ .inactive) (hnew : new ≠ .inactive)
    (hviewp : committedView (s.setPhase p new) p = committedView s p) :
    WellFormed spec (s.setPhase p new) := by
  let s' := s.setPhase p new
  have hpreg : p ∈ s.registered := by
    by_contra hn
    have := wf.unregistered_inactive p hn
    rw [hp] at this
    exact hold this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [SingleSource, s'] using wf.singleSource
  · intro q hq
    have hqold : q ∉ s.registered := by simpa [s'] using hq
    have hne : q ≠ p := fun heq => by subst q; exact hqold hpreg
    simpa [s', State.setPhase_other s hne] using wf.unregistered_inactive q hqold
  · intro q w hview k
    by_cases hqp : q = p
    · subst q
      exact wf.committed_covers p w (by simpa [s'] using hviewp ▸ hview) k
    · exact wf.committed_covers q w
        (by simpa [s', committedView_setPhase_other s hqp] using hview) k
  · intro q w hview k r hbind
    have oldview : committedView s q = some w := by
      by_cases hqp : q = p
      · subst q
        simpa [s'] using hviewp ▸ hview
      · simpa [s', committedView_setPhase_other s hqp] using hview
    exact valid_after_installed_change hnew
      (wf.committed_valid q w oldview k r hbind)

/-- Core theorem: Finish preserves `WellFormed`. -/
theorem StepAt.finish_preserve_wellFormed
    {s : State FiberId Key} {p : FiberId} {v : View Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = .reloading v) :
    WellFormed spec (s.setPhase p (.active v)) := by
  apply preserve_installed_to_installed wf hp (by simp) (by simp)
  simp [committedView, hp]

/-- Core theorem: Divert preserves `WellFormed`. -/
theorem StepAt.divert_preserve_wellFormed
    {s : State FiberId Key} {p : FiberId} {v : View Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = .reloading v) :
    WellFormed spec (s.setPhase p (.unloading v)) := by
  apply preserve_installed_to_installed wf hp (by simp) (by simp)
  simp [committedView, hp]

/-- Core theorem: Leave preserves `WellFormed`. -/
theorem StepAt.leave_preserve_wellFormed
    {s : State FiberId Key} {p : FiberId} {v : View Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = .active v) :
    WellFormed spec (s.setPhase p (.unloading v)) := by
  apply preserve_installed_to_installed wf hp (by simp) (by simp)
  simp [committedView, hp]

/-- Core theorem: Unload preserves `WellFormed`. -/
theorem StepAt.unload_preserve_wellFormed
    {s : State FiberId Key} {p : FiberId} {v : View Key FiberId}
    (wf : WellFormed spec s) (hp : s.phase p = .unloading v)
    (hu : unloadable s p) :
    WellFormed spec (s.setPhase p .inactive) := by
  let s' := s.setPhase p (.inactive : Phase Key FiberId)
  have hpreg : p ∈ s.registered := by
    by_contra hn
    have := wf.unregistered_inactive p hn
    simp [hp] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [SingleSource, s'] using wf.singleSource
  · intro q hq
    have hqold : q ∉ s.registered := by simpa [s'] using hq
    by_cases hqp : q = p
    · subst q
      simp [s']
    · simpa [s', State.setPhase_other s hqp] using wf.unregistered_inactive q hqold
  · intro q w hview k
    have hqp : q ≠ p := by
      rintro rfl
      simp [s', committedView] at hview
    exact wf.committed_covers q w
      (by simpa [s', committedView_setPhase_other s hqp] using hview) k
  · intro q w hview k r hbind
    have hqp : q ≠ p := by
      rintro rfl
      simp [s', committedView] at hview
    have oldview : committedView s q = some w := by
      simpa [s', committedView_setPhase_other s hqp] using hview
    rcases wf.committed_valid q w oldview k r hbind with ⟨hrreg, hrinst, hrprov⟩
    refine ⟨by simpa [s'] using hrreg, ?_, hrprov⟩
    by_cases hrp : r = p
    · subst r
      exact (hu ⟨q, w, k, oldview, hbind⟩).elim
    · exact (installed_setPhase_other s hrp .inactive).2 hrinst

/-- Core theorem: every lifecycle step preserves the invariant. -/
theorem Step.preserve_wellFormed {s s' : State FiberId Key}
    (wf : WellFormed spec s) (h : Step spec s s') : WellFormed spec s' := by
  rcases h with ⟨p, h⟩
  cases h with
  | begin hp ht => exact StepAt.begin_preserve_wellFormed wf hp ht
  | finish hp _ => exact StepAt.finish_preserve_wellFormed wf hp
  | divert hp _ => exact StepAt.divert_preserve_wellFormed wf hp
  | leave hp _ => exact StepAt.leave_preserve_wellFormed wf hp
  | unload hp hu => exact StepAt.unload_preserve_wellFormed wf hp hu

end Cordis.Core
