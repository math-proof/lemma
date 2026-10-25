import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapLambertProduct
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[tsum_sixVertexGapLambertTerm_eq_two_mul_alternatingLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapLambertProduct.lean)
-/
@[path]
private lemma tsum_sixVertexGapLambertTerm_eq_two_mul_alternatingLog_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  (∑' n : ℕ, sixVertexGapLambertTerm lam n) = 2 * sixVertexGapAlternatingLogSeries lam := by
-- proof
  apply StatMech.FrontierD.tsum_sixVertexGapLambertTerm_eq_two_mul_alternatingLog hlam

/--
[sixVertexAntiferroelectricGapRate_eq_logProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapLambertProduct.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapRate_eq_logProduct_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexAntiferroelectricGapRate lam = lam - 2 * Real.log 2 + 4 * sixVertexGapAlternatingLogSeries lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapRate_eq_logProduct hlam


-- created on 2026-10-23
