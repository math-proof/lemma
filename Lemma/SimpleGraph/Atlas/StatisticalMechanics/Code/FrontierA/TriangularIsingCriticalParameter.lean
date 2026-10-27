import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
open Filter Topology StatMech StatMech.FrontierA


/--
[hasDerivAt_real_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma hasDerivAt_real_tanh_eq
  {x : ℝ} :
-- imply
  HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_real_tanh x

/--
[differentiable_real_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma differentiable_real_tanh_eq :
-- imply
  Differentiable ℝ Real.tanh := by
-- proof
  apply StatMech.FrontierA.differentiable_real_tanh

/--
[differentiableAt_triangularIsingCriticalPolynomialAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma differentiableAt_triangularIsingCriticalPolynomialAlong_eq
  {J β : ℝ} :
-- imply
  DifferentiableAt ℝ (triangularIsingCriticalPolynomialAlong J) β := by
-- proof
  apply StatMech.FrontierA.differentiableAt_triangularIsingCriticalPolynomialAlong J β

/--
[differentiableAt_triangularIsingCriticalFactorAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma differentiableAt_triangularIsingCriticalFactorAlong_eq
  {J β : ℝ} :
-- imply
  DifferentiableAt ℝ (triangularIsingCriticalFactorAlong J) β := by
-- proof
  apply StatMech.FrontierA.differentiableAt_triangularIsingCriticalFactorAlong J β

/--
[continuous_triangularIsingZeroModePrefactorAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma continuous_triangularIsingZeroModePrefactorAlong_eq
  {J : ℝ} :
-- imply
  Continuous (triangularIsingZeroModePrefactorAlong J) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingZeroModePrefactorAlong J

/--
[deriv_triangularIsingCriticalPolynomialAlong_neg_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma deriv_triangularIsingCriticalPolynomialAlong_neg_at_root_eq
  {β J : ℝ}
-- given
  (hβ : 0 < β)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate β (β * J) = 1) :
-- imply
  deriv (triangularIsingCriticalPolynomialAlong J) β < 0 := by
-- proof
  apply StatMech.FrontierA.deriv_triangularIsingCriticalPolynomialAlong_neg_at_root hβ hJ hroot

/--
[triangularIsing_zeroMode_eq_polynomialAlong_sq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma triangularIsing_zeroMode_eq_polynomialAlong_sq_mul_eq
  {J β : ℝ} :
-- imply
  triangularIsingSymbol β β (β * J) 0 0 = triangularIsingCriticalPolynomialAlong J β ^ 2 * triangularIsingZeroModePrefactorAlong J β := by
-- proof
  apply StatMech.FrontierA.triangularIsing_zeroMode_eq_polynomialAlong_sq_mul J β

/--
[triangularIsing_zeroMode_quadratic_tendsto_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma triangularIsing_zeroMode_quadratic_tendsto_at_root_eq
  {β J : ℝ}
-- given
  (hβ : 0 < β)
  (hroot : triangularIsingCriticalRate β (β * J) = 1) :
-- imply
  Tendsto (fun t : ℝ => triangularIsingSymbol (β + t) (β + t) ((β + t) * J) 0 0 / t ^ 2) (𝓝[≠] 0) (𝓝 (deriv (triangularIsingCriticalPolynomialAlong J) β ^ 2 * triangularIsingZeroModePrefactorAlong J β)) := by
-- proof
  apply StatMech.FrontierA.triangularIsing_zeroMode_quadratic_tendsto_at_root hβ hroot

/--
[triangularIsing_zeroMode_quadratic_limit_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean)
-/
@[path]
private lemma triangularIsing_zeroMode_quadratic_limit_pos_eq
  {β J : ℝ}
-- given
  (hβ : 0 < β)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate β (β * J) = 1) :
-- imply
  0 < deriv (triangularIsingCriticalPolynomialAlong J) β ^ 2 * triangularIsingZeroModePrefactorAlong J β := by
-- proof
  apply StatMech.FrontierA.triangularIsing_zeroMode_quadratic_limit_pos hβ hJ hroot


-- created on 2026-10-23
