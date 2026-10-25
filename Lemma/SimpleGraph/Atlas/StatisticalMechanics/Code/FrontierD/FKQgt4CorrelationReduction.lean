import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CorrelationReduction
open StatMech StatMech.FrontierD


/--
[eq_of_windingSectorBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma eq_of_windingSectorBounds_eq
  {xiInv R : ℝ}
-- given
  (h : FKQgt4WindingSectorBounds xiInv R) :
-- imply
  xiInv = R := by
-- proof
  apply StatMech.FrontierD.eq_of_windingSectorBounds h

/--
[fkQgt4_inverseCorrelation_eq_sixVertexGapRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma fkQgt4_inverseCorrelation_eq_sixVertexGapRate_eq
  {q xiInv : ℝ}
-- given
  (h : FKQgt4WindingSectorBounds xiInv (fkQgt4SixVertexGapRate q)) :
-- imply
  xiInv = fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_inverseCorrelation_eq_sixVertexGapRate h

/--
[fkQgt4SixVertexGapRate_pos_of_inverseCorrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_pos_of_inverseCorrelation_eq
  {q xiInv : ℝ}
-- given
  (hxi : 0 < xiInv)
  (h : FKQgt4WindingSectorBounds xiInv (fkQgt4SixVertexGapRate q)) :
-- imply
  0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_pos_of_inverseCorrelation hxi h

/--
[fkQgt4_sub_four_eq_four_mul_sinh_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma fkQgt4_sub_four_eq_four_mul_sinh_sq_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  q - 4 = 4 * Real.sinh (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4_sub_four_eq_four_mul_sinh_sq hq

/--
[sqrt_fkQgt4_sub_four_eq_two_mul_sinh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma sqrt_fkQgt4_sub_four_eq_two_mul_sinh_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  Real.sqrt (q - 4) = 2 * Real.sinh (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) := by
-- proof
  apply StatMech.FrontierD.sqrt_fkQgt4_sub_four_eq_two_mul_sinh hq

/--
[fkQgt4_exponentialScale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CorrelationReduction.lean)
-/
@[path]
private lemma fkQgt4_exponentialScale_eq_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  Real.pi ^ 2 / Real.sqrt (q - 4) = Real.pi ^ 2 / (2 * Real.sinh (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_exponentialScale_eq hq


-- created on 2026-10-23
