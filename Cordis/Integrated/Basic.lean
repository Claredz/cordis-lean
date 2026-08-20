import Cordis.Core
import Cordis.Effects

/-!
# Cordis.Integrated.Basic

The integrated state enriches lifecycle phases with finite effect programs and
their accumulated undo, while retaining a first-class erasure to `Cordis.Core`.
-/

namespace Cordis.Integrated

open Cordis

universe u

variable {FiberId Key : Type*} {Γ : Type u}

inductive Phase (Γ : Type u) (Key FiberId : Type*) where
  | inactive
  | reloading (view : Core.View Key FiberId)
      (remaining : List (Effects.WitnessedEffect Γ))
      (accumulator : Effects.Accumulator Γ)
  | active (view : Core.View Key FiberId)
      (accumulator : Effects.Accumulator Γ)
  | unloading (view : Core.View Key FiberId)
      (accumulator : Effects.Accumulator Γ)

structure State (FiberId Key : Type*) (Γ : Type u) [DecidableEq FiberId] where
  registered : Finset FiberId
  phase : FiberId → Phase Γ Key FiberId
  retired : Finset FiberId
  world : Γ

namespace State

variable [DecidableEq FiberId]

def setPhase (s : State FiberId Key Γ) (p : FiberId) (ph : Phase Γ Key FiberId) :
    State FiberId Key Γ :=
  { s with phase := Function.update s.phase p ph }

def setWorld (s : State FiberId Key Γ) (world : Γ) : State FiberId Key Γ :=
  { s with world }

@[simp] theorem setPhase_registered (s : State FiberId Key Γ) (p) (ph) :
    (s.setPhase p ph).registered = s.registered := rfl

@[simp] theorem setPhase_retired (s : State FiberId Key Γ) (p) (ph) :
    (s.setPhase p ph).retired = s.retired := rfl

@[simp] theorem setPhase_world (s : State FiberId Key Γ) (p) (ph) :
    (s.setPhase p ph).world = s.world := rfl

@[simp] theorem setPhase_self (s : State FiberId Key Γ) (p) (ph) :
    (s.setPhase p ph).phase p = ph := by simp [setPhase]

@[simp] theorem setPhase_other (s : State FiberId Key Γ) {p q} (h : q ≠ p) (ph) :
    (s.setPhase p ph).phase q = s.phase q := by simp [setPhase, h]

@[simp] theorem setWorld_registered (s : State FiberId Key Γ) (world) :
    (s.setWorld world).registered = s.registered := rfl

@[simp] theorem setWorld_retired (s : State FiberId Key Γ) (world) :
    (s.setWorld world).retired = s.retired := rfl

@[simp] theorem setWorld_phase (s : State FiberId Key Γ) (world) :
    (s.setWorld world).phase = s.phase := rfl

@[simp] theorem setWorld_world (s : State FiberId Key Γ) (world) :
    (s.setWorld world).world = world := rfl

end State

def erasePhase : Phase Γ Key FiberId → Core.Phase Key FiberId
  | .inactive => .inactive
  | .reloading view _ _ => .reloading view
  | .active view _ => .active view
  | .unloading view _ => .unloading view

def erase [DecidableEq FiberId] (s : State FiberId Key Γ) : Core.State FiberId Key where
  registered := s.registered
  phase p := erasePhase (s.phase p)
  retired := s.retired

@[simp] theorem erase_registered [DecidableEq FiberId] (s : State FiberId Key Γ) :
    (erase s).registered = s.registered := rfl

@[simp] theorem erase_retired [DecidableEq FiberId] (s : State FiberId Key Γ) :
    (erase s).retired = s.retired := rfl

@[simp] theorem erase_phase [DecidableEq FiberId] (s : State FiberId Key Γ) (p) :
    (erase s).phase p = erasePhase (s.phase p) := rfl

@[simp] theorem erase_setWorld [DecidableEq FiberId]
    (s : State FiberId Key Γ) (world : Γ) : erase (s.setWorld world) = erase s := rfl

@[simp] theorem erase_setPhase [DecidableEq FiberId]
    (s : State FiberId Key Γ) (p : FiberId) (ph : Phase Γ Key FiberId) :
    erase (s.setPhase p ph) = (erase s).setPhase p (erasePhase ph) := by
  unfold erase State.setPhase Core.State.setPhase
  congr 1
  funext q
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

theorem core_setPhase_eq_self [DecidableEq FiberId]
    (s : Core.State FiberId Key) (p : FiberId) (ph : Core.Phase Key FiberId)
    (h : s.phase p = ph) : s.setPhase p ph = s := by
  cases s with
  | mk registered phase retired =>
      simp only [Core.State.setPhase] at h ⊢
      have hfun : Function.update phase p ph = phase := by
        funext q
        by_cases hq : q = p
        · subst q
          simp [h]
        · simp [hq]
      simp [hfun]

def CoreWellFormed [DecidableEq FiberId] [DecidableEq Key]
    (spec : FiberId → Core.Spec Key) (s : State FiberId Key Γ) : Prop :=
  Core.WellFormed spec (erase s)

end Cordis.Integrated
