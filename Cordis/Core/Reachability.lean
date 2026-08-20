import Cordis.Core.Termination

/-! # Core theorem: quiet-state reachability -/

namespace Cordis.Core

variable {FiberId Key : Type*} [DecidableEq FiberId] [DecidableEq Key]
variable [Fintype FiberId]
variable {spec : FiberId → Spec Key} {s : State FiberId Key}

private theorem acc_reaches_quiet
    (acc : Acc (fun t' t : State FiberId Key => Step spec t t') s)
    (wf : WellFormed spec s) (acyclic : PriorityAcyclic spec s) :
    ∃ q, Relation.ReflTransGen (Step spec) s q ∧ quiet spec q := by
  induction acc with
  | intro s next ih =>
      by_cases hq : quiet spec s
      · exact ⟨s, .refl, hq⟩
      · rcases not_quiet_has_step wf acyclic hq with ⟨s', hs'⟩
        have wf' := Step.preserve_wellFormed wf hs'
        have hreg := Step.registered_eq spec hs'
        have acyclic' : PriorityAcyclic spec s' := by
          simpa [PriorityAcyclic, hreg] using acyclic
        rcases ih s' hs' wf' acyclic' with ⟨q, hreach, hquiet⟩
        exact ⟨q, hreach.head hs', hquiet⟩

/-- Core theorem: every well-formed acyclic lifecycle state reaches a quiet
state by finitely many Core steps. -/
theorem exists_quiet_reachable (wf : WellFormed spec s)
    (acyclic : PriorityAcyclic spec s) :
    ∃ q, Relation.ReflTransGen (Step spec) s q ∧ quiet spec q :=
  acc_reaches_quiet (lifecycle_terminates wf acyclic) wf acyclic

end Cordis.Core
