import Cordis.Extended

/-!
# Cordis.Examples.Schedules

Concrete finite-universe schedules for the Core lifecycle.
-/

namespace Cordis.Examples

open Cordis

def noDepSpec (p : Fin 2) : Core.Spec Unit where
  deps := ∅
  provs := ∅

def emptyView : Core.View Unit (Fin 2) := fun _ => none

def initial : Core.State (Fin 2) Unit where
  registered := Finset.univ
  phase := fun _ => .inactive
  retired := ∅

def leftReloading : Core.State (Fin 2) Unit :=
  initial.setPhase 0 (.reloading emptyView)

def leftActive : Core.State (Fin 2) Unit :=
  leftReloading.setPhase 0 (.active emptyView)

def rightReloading : Core.State (Fin 2) Unit :=
  initial.setPhase 1 (.reloading emptyView)

def rightActive : Core.State (Fin 2) Unit :=
  rightReloading.setPhase 1 (.active emptyView)

def leftThenRightReloading : Core.State (Fin 2) Unit :=
  leftActive.setPhase 1 (.reloading emptyView)

def rightThenLeftReloading : Core.State (Fin 2) Unit :=
  rightActive.setPhase 0 (.reloading emptyView)

def bothActive : Core.State (Fin 2) Unit :=
  leftThenRightReloading.setPhase 1 (.active emptyView)

def rightFinal : Core.State (Fin 2) Unit :=
  rightThenLeftReloading.setPhase 0 (.active emptyView)

private theorem coreState_ext
    {s t : Core.State (Fin 2) Unit}
    (hregistered : s.registered = t.registered)
    (hphase : s.phase = t.phase) (hretired : s.retired = t.retired) : s = t := by
  cases s
  cases t
  simp_all

theorem rightFinal_eq_bothActive : rightFinal = bothActive := by
  apply coreState_ext
  · rfl
  · funext p
    fin_cases p <;>
      simp [rightFinal, bothActive, rightThenLeftReloading, rightActive,
        rightReloading, leftThenRightReloading, leftActive, leftReloading,
        initial, Core.State.setPhase]
  · rfl

theorem noDepTarget (s : Core.State (Fin 2) Unit) (p : Fin 2)
    (hregistered : p ∈ s.registered) (hretired : p ∉ s.retired) :
    Core.targetView noDepSpec s p = some emptyView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨hregistered, hretired, ?_, ?_⟩
  · intro key hkey
    simp [noDepSpec] at hkey
  · funext key
    simp [noDepSpec, emptyView]

theorem initial_target (p : Fin 2) :
    Core.targetView noDepSpec initial p = some emptyView := by
  apply noDepTarget
  · simp [initial]
  · simp [initial]

theorem leftReloading_target (p : Fin 2) :
    Core.targetView noDepSpec leftReloading p = some emptyView := by
  apply noDepTarget
  · simp [leftReloading, initial]
  · simp [leftReloading, initial]

theorem leftActive_target (p : Fin 2) :
    Core.targetView noDepSpec leftActive p = some emptyView := by
  apply noDepTarget
  · simp [leftActive, leftReloading, initial]
  · simp [leftActive, leftReloading, initial]

theorem rightReloading_target (p : Fin 2) :
    Core.targetView noDepSpec rightReloading p = some emptyView := by
  apply noDepTarget
  · simp [rightReloading, initial]
  · simp [rightReloading, initial]

theorem rightActive_target (p : Fin 2) :
    Core.targetView noDepSpec rightActive p = some emptyView := by
  apply noDepTarget
  · simp [rightActive, rightReloading, initial]
  · simp [rightActive, rightReloading, initial]

theorem leftThenRightReloading_target (p : Fin 2) :
    Core.targetView noDepSpec leftThenRightReloading p = some emptyView := by
  apply noDepTarget
  · simp [leftThenRightReloading, leftActive, leftReloading, initial]
  · simp [leftThenRightReloading, leftActive, leftReloading, initial]

theorem rightThenLeftReloading_target (p : Fin 2) :
    Core.targetView noDepSpec rightThenLeftReloading p = some emptyView := by
  apply noDepTarget
  · simp [rightThenLeftReloading, rightActive, rightReloading, initial]
  · simp [rightThenLeftReloading, rightActive, rightReloading, initial]

/-- Explicit Begin→Finish chain for fiber zero. -/
theorem chain_schedule :
    Relation.ReflTransGen (Core.Step noDepSpec) initial leftActive := by
  apply Relation.ReflTransGen.head
  · exact ⟨0, Core.StepAt.begin rfl (initial_target 0)⟩
  · apply Relation.ReflTransGen.single
    exact ⟨0, Core.StepAt.finish rfl (leftReloading_target 0)⟩

/-- Left-first arm of the concrete diamond. -/
theorem diamond_left_schedule :
    Relation.ReflTransGen (Core.Step noDepSpec) initial bothActive := by
  apply chain_schedule.trans
  apply Relation.ReflTransGen.head
  · exact ⟨1, Core.StepAt.begin rfl (leftActive_target 1)⟩
  · apply Relation.ReflTransGen.single
    exact ⟨1, Core.StepAt.finish rfl (leftThenRightReloading_target 1)⟩

/-- Right-first arm of the same concrete diamond. -/
theorem diamond_right_schedule :
    Relation.ReflTransGen (Core.Step noDepSpec) initial bothActive := by
  have schedule :
      Relation.ReflTransGen (Core.Step noDepSpec) initial rightFinal := by
    apply Relation.ReflTransGen.head
    · exact ⟨1, Core.StepAt.begin rfl (initial_target 1)⟩
    · apply Relation.ReflTransGen.head
      · exact ⟨1, Core.StepAt.finish rfl (rightReloading_target 1)⟩
      · apply Relation.ReflTransGen.head
        · exact ⟨0, Core.StepAt.begin rfl (rightActive_target 0)⟩
        · apply Relation.ReflTransGen.single
          exact ⟨0, Core.StepAt.finish rfl (rightThenLeftReloading_target 0)⟩
  rw [rightFinal_eq_bothActive] at schedule
  exact schedule

theorem bothActive_quiet : Core.quiet noDepSpec bothActive := by
  intro p
  have hphase : bothActive.phase p = .active emptyView := by
    fin_cases p <;>
      simp [bothActive, leftThenRightReloading, leftActive, leftReloading,
        initial, Core.State.setPhase]
  rw [show Core.LocallyQuiet noDepSpec bothActive p =
      (Core.targetView noDepSpec bothActive p = some emptyView) by
        simp [Core.LocallyQuiet, hphase]]
  apply noDepTarget
  · simp [bothActive, leftThenRightReloading, leftActive, leftReloading, initial]
  · simp [bothActive, leftThenRightReloading, leftActive, leftReloading, initial]

end Cordis.Examples
