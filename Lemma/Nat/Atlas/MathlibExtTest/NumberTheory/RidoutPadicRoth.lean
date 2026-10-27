import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.RidoutPadicRoth
open MathlibExtTest MathlibExtTest.NumberTheory MathlibExtTest.NumberTheory.RidoutPadicRoth


namespace MathlibExtTest.NumberTheory.RidoutPadicRoth

/--
[sqrt_two_isAlgebraic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RidoutPadicRoth.lean)
-/
@[path]
lemma sqrt_two_isAlgebraic
-- imply
  IsAlgebraic ℚ (Real.sqrt 2) := by
-- proof
  apply IsIntegral.isAlgebraic
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
    Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end MathlibExtTest.NumberTheory.RidoutPadicRoth


-- created on 2026-10-23
