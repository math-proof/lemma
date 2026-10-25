import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Ex_3_8
open Chapter3
open MeasureTheory


namespace Chapter3

/--
[trigBasis_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_8.lean)
-/
@[path]
lemma trigBasis_one
  {x : ℝ} :
-- imply
  trigBasis 1 x = 1 := by
-- proof
  simp [trigBasis]

end Chapter3

namespace Chapter3

/--
[trigBasis_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_8.lean)
-/
@[path]
lemma trigBasis_bounded
  {j : ℕ}
  {x : ℝ} :
-- imply
  |trigBasis j x| ≤ Real.sqrt 2 := by
-- proof
  unfold trigBasis
  split_ifs
  · simp
  · simp
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg 2) (Real.abs_cos_le_one _)
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg 2) (Real.abs_sin_le_one _)

end Chapter3


-- created on 2026-10-23
