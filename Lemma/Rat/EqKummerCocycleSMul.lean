import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.Kummer


namespace Definitions
end Definitions
open Definitions
open groupCohomology groupCohomology.Kummer


/-- ported from external source -/
@[path]
private lemma main
  [Field k] [Field Ω] [Algebra k Ω]
  {α : Ωˣ}
-- given
  (g σ : Ω ≃ₐ[k] Ω) :
-- imply
  kummerCocycle (g • α) (g * σ * g⁻¹) = g • kummerCocycle α σ := by
-- proof
  rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div, ← mul_smul, ← mul_smul,
      inv_mul_cancel_right]


-- created on 2026-10-24
