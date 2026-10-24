import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Background_Weyl
open Matrix Real Finset


/--
[matrixOpNorm_neg_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Weyl.lean)
-/
@[path]
lemma matrixOpNorm_neg_sub
  {d T : ℕ}
  {A B : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  matrixOpNorm (B - A) = matrixOpNorm (A - B) := by
-- proof
  unfold matrixOpNorm
  rw [show B - A = -(A - B) from (neg_sub A B).symm, map_neg,
    show (-toEuclideanLin (A - B)).toContinuousLinearMap =
      -(toEuclideanLin (A - B)).toContinuousLinearMap from map_neg _ _,
    ContinuousLinearMap.opNorm_neg]
/-- **Weyl's bound on singular values.** For any matrices `A` and `B`,
$\sigma_k(A) \le \sigma_k(B) + \|A - B\|_{op}$. -/


-- created on 2026-10-23
