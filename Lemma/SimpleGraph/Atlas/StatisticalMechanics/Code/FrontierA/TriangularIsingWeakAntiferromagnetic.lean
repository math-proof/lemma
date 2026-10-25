import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
open StatMech StatMech.FrontierA


/--
[triangular_cosine_combination_le_zero_of_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingWeakAntiferromagnetic.lean)
-/
@[path]
private lemma triangular_cosine_combination_le_zero_of_sum_nonneg_eq
  {s r : Real}
  {p q : Real}
-- given
  (hr : r < 0)
  (hsum : 0 <= s + 2 * r) :
-- imply
  s * (Real.cos p + Real.cos q) + r * Real.cos (p + q) <= 2 * s + r := by
-- proof
  apply StatMech.FrontierA.triangular_cosine_combination_le_zero_of_sum_nonneg hr hsum p q

/--
[triangular_hyperbolic_lower_pos_of_weak_neg_large](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingWeakAntiferromagnetic.lean)
-/
@[path]
private lemma triangular_hyperbolic_lower_pos_of_weak_neg_large_eq
  {x y : Real}
-- given
  (hx : 0 < x)
  (hyUpper : y < 0)
  (hlarge : Real.sinh x < -2 * Real.sinh y) :
-- imply
  0 < Real.cosh x ^ 2 * Real.cosh y + Real.sinh x ^ 2 * Real.sinh y + Real.sinh x ^ 2 / (2 * Real.sinh y) + Real.sinh y := by
-- proof
  apply StatMech.FrontierA.triangular_hyperbolic_lower_pos_of_weak_neg_large hx hyUpper hlarge

/--
[triangularIsingSymbol_pos_of_gt_neg_one_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingWeakAntiferromagnetic.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_of_gt_neg_one_noncritical_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (_hJ : -1 < J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  0 < triangularIsingSymbol beta beta (beta * J) p q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_of_gt_neg_one_noncritical hbeta _hJ hcrit p q

/--
[triangularIsing_logSymbol_analyticAt_of_gt_neg_one_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingWeakAntiferromagnetic.lean)
-/
@[path]
private lemma triangularIsing_logSymbol_analyticAt_of_gt_neg_one_noncritical_eq
  {beta J : Real}
  {p q : Real}
-- given
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
-- imply
  AnalyticAt Real (fun b : Real => Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
-- proof
  apply StatMech.FrontierA.triangularIsing_logSymbol_analyticAt_of_gt_neg_one_noncritical hbeta hJ hcrit p q


-- created on 2026-10-23
