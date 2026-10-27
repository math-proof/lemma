import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Problem_4_3
open Matrix Real Finset MeasureTheory Chapter4 Chapter4.Problem43


namespace Chapter4.Problem43

/--
[sq_le_of_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_3.lean)
-/
@[path]
lemma sq_le_of_abs_le
  {x y : ℝ}
-- given
  (h : |x| ≤ y) :
-- imply
  x ^ 2 ≤ y ^ 2 := by
-- proof
  nlinarith [sq_abs x, sq_abs y, abs_nonneg x]

end Chapter4.Problem43

namespace Chapter4.Problem43

/--
[oracle_sv_error_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_3.lean)
-/
@[path]
lemma oracle_sv_error_sq
  {sigmaHat sigmaStar τ : ℝ}
-- given
  (hperturb : |sigmaHat - sigmaStar| ≤ τ) :
-- imply
  ((sigmaHat + sigmaStar) / 2 - sigmaStar) ^ 2 ≤ τ ^ 2 / 4 := by
-- proof
  have h1 : (sigmaHat + sigmaStar) / 2 - sigmaStar = (sigmaHat - sigmaStar) / 2 := by ring
  rw [h1]
  have h2 : ((sigmaHat - sigmaStar) / 2) ^ 2 = (sigmaHat - sigmaStar) ^ 2 / 4 := by ring
  rw [h2]
  linarith [sq_le_of_abs_le hperturb]

end Chapter4.Problem43

namespace Chapter4.Problem43

/--
[problem_4_3_part2_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_3.lean)
-/
@[path]
lemma problem_4_3_part2_closed_form
  {sigmaHat sigmaStar t : ℝ}
-- given
  (_hnn_hat : 0 ≤ sigmaHat)
  (hnn_star : 0 ≤ sigmaStar)
  (ht : t = (sigmaHat - sigmaStar) / 2) :
-- imply
  max (sigmaHat - t) 0 = (sigmaHat + sigmaStar) / 2 := by
-- proof
  rw [ht]
  have h : sigmaHat - (sigmaHat - sigmaStar) / 2 =
    (sigmaHat + sigmaStar) / 2 := by ring
  rw [h]; exact max_eq_left (by linarith)
end Chapter4.Problem43



-- created on 2026-10-23
