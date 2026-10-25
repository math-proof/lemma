import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.Kummer
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open groupCohomology groupCohomology.Kummer
open Int


/--
[groupCohomology_Kummer_kummerCocycle_conj](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_Kummer_kummerCocycle_conj.lean)
-/
@[path]
private lemma main
  {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {α : Ωˣ}
-- given
  (g σ : Ω ≃ₐ[k] Ω) :
-- imply
  kummerCocycle (g • α) (g * σ * g⁻¹) = g • kummerCocycle α σ := by
-- proof
  rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div, ← mul_smul, ← mul_smul,
    inv_mul_cancel_right]


-- created on 2026-10-24
