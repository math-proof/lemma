/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/ArcsinDivSinIntegral.lean -/


import sympy.atlas.Analysis.Calculus.ArcsinDivSinIntegral


namespace MathlibExtTest.Analysis.Calculus.ArcsinDivSinIntegral

open scoped BigOperators Interval

-- Multiplying the evaluation by `√2` clears both irrational denominators.
example :
    Real.sqrt 2 * (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      -2 * Real.sqrt 2 *
          (∑' n : ℕ, (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) -
        Real.pi ^ 2 / 2 +
        (1 / 8 : ℝ) *
          ((∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) +
            ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2)) := by
  rw [MetaMathlibExt.arcsin_div_sin_integral]
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt]

end MathlibExtTest.Analysis.Calculus.ArcsinDivSinIntegral
