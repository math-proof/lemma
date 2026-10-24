/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ThueSiegelRoth.lean -/


import Lemma.Nat.ThueSiegelRoth
import Mathlib.RingTheory.Algebraic.Integral


namespace MathlibExtTest.NumberTheory.ThueSiegelRoth

open MathlibExt.NumberTheory.ThueSiegelRothWanted

-- Roth's theorem applies to `√2` with exponent `2 + 1/2`.
example : Set.Finite {q : ℚ |
    |Real.sqrt 2 - (q : ℝ)| <
      1 / Real.rpow (q.den : ℝ) (2 + (1 / 2 : ℝ))} := by
  apply thue_siegel_roth (Real.sqrt 2)
  · apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · exact irrational_sqrt_two
  · norm_num

end MathlibExtTest.NumberTheory.ThueSiegelRoth
