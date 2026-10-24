import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.EuclideanBridge
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators EuclideanBridge


/--
[euclideanToFun_funToEuclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean)
-/
@[path]
private lemma euclideanToFun_funToEuclidean_eq
  {d : ℕ}
  {v : Fin d → ℝ} :
-- imply
  euclideanToFun (funToEuclidean v) = v := by
-- proof
  apply EuclideanBridge.euclideanToFun_funToEuclidean v

/--
[funToEuclidean_euclideanToFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean)
-/
@[path]
private lemma funToEuclidean_euclideanToFun_eq
  {d : ℕ}
  {v : EuclideanSpace ℝ (Fin d)} :
-- imply
  funToEuclidean (euclideanToFun v) = v := by
-- proof
  apply EuclideanBridge.funToEuclidean_euclideanToFun v

/--
[euclideanToFun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean)
-/
@[path]
private lemma euclideanToFun_apply_eq
  {d : ℕ}
  {v : EuclideanSpace ℝ (Fin d)}
  {i : Fin d} :
-- imply
  euclideanToFun v i = v i := by
-- proof
  apply EuclideanBridge.euclideanToFun_apply v i

/--
[funToEuclidean_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean)
-/
@[path]
private lemma funToEuclidean_apply_eq
  {d : ℕ}
  {v : Fin d → ℝ}
  {i : Fin d} :
-- imply
  funToEuclidean v i = v i := by
-- proof
  apply EuclideanBridge.funToEuclidean_apply v i


-- created on 2026-10-23
