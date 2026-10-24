import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
open Chapter3


namespace Chapter3

/--
[MSE_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Remark_3_1.lean)
-/
@[path]
lemma MSE_nonneg
  {n : ℕ}
  {fhat f : Fin n → ℝ} :
-- imply
  0 ≤ MSE fhat f := by
-- proof
  unfold MSE
  apply mul_nonneg
  · apply div_nonneg zero_le_one (Nat.cast_nonneg n)
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Chapter3


-- created on 2026-10-23
