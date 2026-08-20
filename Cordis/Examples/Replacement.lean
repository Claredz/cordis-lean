import Cordis.Extended.Orchestration

namespace Cordis.Examples

open Cordis

variable {FiberId Key : Type*}

/-- A provider replacement example exposes the complete quiet-only five-stage
derivation, including both integrated `ReflTransGen` normalization schedules. -/
theorem checked_replacement_schedule
    [Fintype FiberId] [DecidableEq FiberId] [DecidableEq Key]
    {Γ : Type*} {spec : FiberId → Core.Spec Key}
    {program : FiberId → List (Effects.WitnessedEffect Γ)}
    {state : Extended.OrchState FiberId Key Γ} {old fresh : FiberId}
    (compatible : Extended.ReplacementCompatible spec program state old fresh) :
    ∃ derivation : Extended.ReplacementDerivation spec program state old fresh,
      Core.quiet spec (Integrated.erase derivation.final.lifecycle) :=
  Extended.provider_replacement_reaches_quiet compatible

end Cordis.Examples
