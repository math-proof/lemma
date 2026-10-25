import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
open MeasureTheory Set Chapter3


namespace Chapter3

/--
[sobolevCoeff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Def_3_10.lean)
-/
@[path]
lemma sobolevCoeff_nonneg
  {β : ℝ}
  {j : ℕ}
-- given
  (_hβ : 0 ≤ β) :
-- imply
  0 ≤ sobolevCoeff β j := by
-- proof
  unfold sobolevCoeff
  split
  · exact Real.rpow_nonneg (Nat.cast_nonneg j) β
  · exact Real.rpow_nonneg (Nat.cast_nonneg (j - 1)) β

end Chapter3

namespace Chapter3

/--
[sobolevCoeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Def_3_10.lean)
-/
@[path]
lemma sobolevCoeff_one
  {β : ℝ}
-- given
  (hβ : β ≠ 0) :
-- imply
  sobolevCoeff β 1 = 0 := by
-- proof
  unfold sobolevCoeff
  simp [Real.zero_rpow hβ]

end Chapter3


-- created on 2026-10-23
