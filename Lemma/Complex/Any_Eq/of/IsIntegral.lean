import Mathlib
import sympy.Basic


/--
[exists_integralClosure_coe_eq_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_integralClosure_coe_eq_of_isIntegral.lean)
-/
@[path]
private lemma main
  {z : ℂ}
-- given
  (hz : IsIntegral ℤ z) :
-- imply
  ∃ a : integralClosure ℤ ℂ, (a : ℂ) = z :=
-- proof
  ⟨⟨z, (mem_integralClosure_iff ℤ ℂ).mpr hz⟩, rfl⟩


-- created on 2026-10-03
