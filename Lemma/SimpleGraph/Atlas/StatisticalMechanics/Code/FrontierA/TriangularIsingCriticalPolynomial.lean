import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalPolynomial
open StatMech StatMech.FrontierA


/--
[triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq_eq
  {x y : ℝ} :
-- imply
  triangularIsingHighTempSymbol x x y 0 0 = triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingHighTempSymbol_zero_eq_criticalPolynomial_sq x y

/--
[triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul_eq
  {x y : ℝ} :
-- imply
  triangularIsingSymbol x x y 0 0 = triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) ^ 2 * (Real.cosh x ^ 4 * Real.cosh y ^ 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul x y

/--
[triangularIsingSymbol_zero_iff_criticalPolynomial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingSymbol_zero_iff_criticalPolynomial_zero_eq
  {x y : ℝ} :
-- imply
  triangularIsingSymbol x x y 0 0 = 0 ↔ triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_zero_iff_criticalPolynomial_zero x y

/--
[triangularIsingCriticalPolynomial_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalPolynomial_eq_zero_iff_eq
  {t r : ℝ}
-- given
  (hden : 1 + 2 * t - t ^ 2 ≠ 0) :
-- imply
  triangularIsingCriticalPolynomial t r = 0 ↔ r = (1 - 2 * t - t ^ 2) / (1 + 2 * t - t ^ 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalPolynomial_eq_zero_iff hden

/--
[triangularIsingCriticalCompanion_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalCompanion_pos_eq
  {t r : ℝ}
-- given
  (ht0 : 0 < t)
  (ht1 : t < 1)
  (hr0 : -1 < r)
  (hr1 : r < 1) :
-- imply
  0 < triangularIsingCriticalCompanion t r := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalCompanion_pos ht0 ht1 hr0 hr1

/--
[sinh_two_mul_eq_two_tanh_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma sinh_two_mul_eq_two_tanh_div_eq
  {x : ℝ} :
-- imply
  Real.sinh (2 * x) = 2 * Real.tanh x / (1 - Real.tanh x ^ 2) := by
-- proof
  apply StatMech.FrontierA.sinh_two_mul_eq_two_tanh_div x

/--
[criticalRate_sub_one_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma criticalRate_sub_one_factor_eq
  {t r : ℝ}
-- given
  (ht : 1 - t ^ 2 ≠ 0)
  (hr : 1 - r ^ 2 ≠ 0) :
-- imply
  (2 * t / (1 - t ^ 2)) ^ 2 + 2 * (2 * t / (1 - t ^ 2)) * (2 * r / (1 - r ^ 2)) - 1 = -triangularIsingCriticalPolynomial t r * triangularIsingCriticalCompanion t r / ((1 - t ^ 2) ^ 2 * (1 - r ^ 2)) := by
-- proof
  apply StatMech.FrontierA.criticalRate_sub_one_factor ht hr

/--
[triangularIsingCriticalRate_sub_one_eq_polynomial_mul_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalRate_sub_one_eq_polynomial_mul_factor_eq
  {x y : ℝ} :
-- imply
  triangularIsingCriticalRate x y - 1 = triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) * triangularIsingCriticalFactor x y := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalRate_sub_one_eq_polynomial_mul_factor x y

/--
[triangularIsingCriticalFactor_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalFactor_neg_eq
  {x y : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  triangularIsingCriticalFactor x y < 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalFactor_neg hx

/--
[triangularIsingCriticalPolynomial_zero_iff_rate_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalPolynomial_zero_iff_rate_eq_one_eq
  {x y : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  triangularIsingCriticalPolynomial (Real.tanh x) (Real.tanh y) = 0 ↔ triangularIsingCriticalRate x y = 1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hx

/--
[triangularIsingSymbol_zero_iff_criticalRate_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingSymbol_zero_iff_criticalRate_eq_one_eq
  {x y : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  triangularIsingSymbol x x y 0 0 = 0 ↔ triangularIsingCriticalRate x y = 1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_zero_iff_criticalRate_eq_one hx

/--
[triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg_eq
  {J : ℝ}
-- given
  (hJ : 0 ≤ J) :
-- imply
  StrictMonoOn (fun β : ℝ => triangularIsingCriticalRate β (β * J)) (Set.Ioi 0) := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalRateAlong_strictMonoOn_of_nonneg hJ

/--
[continuous_triangularIsingCriticalRateAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma continuous_triangularIsingCriticalRateAlong_eq
  {J : ℝ} :
-- imply
  Continuous fun β : ℝ => triangularIsingCriticalRate β (β * J) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingCriticalRateAlong J

/--
[existsUnique_triangularIsingCriticalRate_eq_one_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma existsUnique_triangularIsingCriticalRate_eq_one_of_nonneg_eq
  {J : ℝ}
-- given
  (hJ : 0 ≤ J) :
-- imply
  ∃! β : ℝ, 0 < β ∧ triangularIsingCriticalRate β (β * J) = 1 := by
-- proof
  apply StatMech.FrontierA.existsUnique_triangularIsingCriticalRate_eq_one_of_nonneg hJ

/--
[existsUnique_triangularIsingSymbol_zero_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma existsUnique_triangularIsingSymbol_zero_of_nonneg_eq
  {J : ℝ}
-- given
  (hJ : 0 ≤ J) :
-- imply
  ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
-- proof
  apply StatMech.FrontierA.existsUnique_triangularIsingSymbol_zero_of_nonneg hJ

/--
[sinh_scale_ratio_derivNumerator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma sinh_scale_ratio_derivNumerator_pos_eq
  {a x : ℝ}
-- given
  (ha0 : 0 < a)
  (ha1 : a < 1)
  (hx : 0 < x) :
-- imply
  0 < Real.cosh x * Real.sinh (a * x) - a * Real.sinh x * Real.cosh (a * x) := by
-- proof
  apply StatMech.FrontierA.sinh_scale_ratio_derivNumerator_pos ha0 ha1 hx

/--
[sinh_scale_ratio_strictMonoOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma sinh_scale_ratio_strictMonoOn_eq
  {a : ℝ}
-- given
  (ha0 : 0 < a)
  (ha1 : a < 1) :
-- imply
  StrictMonoOn (fun x : ℝ => Real.sinh x / Real.sinh (a * x)) (Set.Ioi 0) := by
-- proof
  apply StatMech.FrontierA.sinh_scale_ratio_strictMonoOn ha0 ha1

/--
[triangularIsingCriticalRate_eq_one_unique_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalRate_eq_one_unique_of_neg_eq
  {J β₁ β₂ : ℝ}
-- given
  (hJlo : -1 < J)
  (hJhi : J < 0)
  (hβ₁ : 0 < β₁)
  (hβ₂ : 0 < β₂)
  (hone₁ : triangularIsingCriticalRate β₁ (β₁ * J) = 1)
  (hone₂ : triangularIsingCriticalRate β₂ (β₂ * J) = 1) :
-- imply
  β₁ = β₂ := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalRate_eq_one_unique_of_neg hJlo hJhi hβ₁ hβ₂ hone₁ hone₂

/--
[exists_triangularIsingCriticalRate_gt_one_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma exists_triangularIsingCriticalRate_gt_one_of_neg_eq
  {J : ℝ}
-- given
  (hJlo : -1 < J)
  (hJhi : J < 0) :
-- imply
  ∃ β : ℝ, 0 < β ∧ 1 < triangularIsingCriticalRate β (β * J) := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingCriticalRate_gt_one_of_neg hJlo hJhi

/--
[existsUnique_triangularIsingCriticalRate_eq_one_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma existsUnique_triangularIsingCriticalRate_eq_one_of_neg_eq
  {J : ℝ}
-- given
  (hJlo : -1 < J)
  (hJhi : J < 0) :
-- imply
  ∃! β : ℝ, 0 < β ∧ triangularIsingCriticalRate β (β * J) = 1 := by
-- proof
  apply StatMech.FrontierA.existsUnique_triangularIsingCriticalRate_eq_one_of_neg hJlo hJhi

/--
[existsUnique_triangularIsingSymbol_zero_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma existsUnique_triangularIsingSymbol_zero_of_neg_eq
  {J : ℝ}
-- given
  (hJlo : -1 < J)
  (hJhi : J < 0) :
-- imply
  ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
-- proof
  apply StatMech.FrontierA.existsUnique_triangularIsingSymbol_zero_of_neg hJlo hJhi

/--
[existsUnique_triangularIsingSymbol_zero_of_gt_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma existsUnique_triangularIsingSymbol_zero_of_gt_neg_one_eq
  {J : ℝ}
-- given
  (hJ : -1 < J) :
-- imply
  ∃! β : ℝ, 0 < β ∧ triangularIsingSymbol β β (β * J) 0 0 = 0 := by
-- proof
  apply StatMech.FrontierA.existsUnique_triangularIsingSymbol_zero_of_gt_neg_one hJ

/--
[hasDerivAt_triangularIsingCriticalRateAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma hasDerivAt_triangularIsingCriticalRateAlong_eq
  {β J : ℝ} :
-- imply
  HasDerivAt (fun b : ℝ => triangularIsingCriticalRate b (b * J)) (triangularIsingCriticalRateAlongDeriv β J) β := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_triangularIsingCriticalRateAlong β J

/--
[triangularIsingCriticalRateAlongDeriv_pos_at_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalPolynomial.lean)
-/
@[path]
private lemma triangularIsingCriticalRateAlongDeriv_pos_at_root_eq
  {β J : ℝ}
-- given
  (hβ : 0 < β)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate β (β * J) = 1) :
-- imply
  0 < triangularIsingCriticalRateAlongDeriv β J := by
-- proof
  apply StatMech.FrontierA.triangularIsingCriticalRateAlongDeriv_pos_at_root hβ hJ hroot


-- created on 2026-10-23
