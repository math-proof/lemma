import Mathlib
import sympy.Basic
import sympy.functions.special.ArcsinTaylorSeries

open SpecialFunctions.ArcsinTaylorSeries

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma central_binomial_coeff_nonneg_le
-- given
  (n : ℕ) :
-- imply
  0 ≤ centralBinomialCoeff n := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.centralBinomialCoeff_nonneg n

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma central_binomial_coeff_le_one_le
-- given
  (n : ℕ) :
-- imply
  centralBinomialCoeff n ≤ 1 := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.centralBinomialCoeff_le_one n

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma arcsin_series_eq_arcsin_is :
-- imply
  Set.EqOn arcsinSeries Real.arcsin (Set.Ioo (-1 : ℝ) 1) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.arcsinSeries_eq_arcsin

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma arcsin_integral_series_term_eq_eq
-- given
  (n : ℕ)
  (t : ℝ) :
-- imply
  centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2
    = (Nat.choose (2 * n) n : ℝ) * t ^ (2 * n + 1) /
      ((2 : ℝ) ^ (2 * n) * ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.arcsinIntegralSeries_term_eq n t

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma norm_arcsin_integral_series_term_le_le
-- given
  (t : ℝ)
  (ht : ‖t‖ ≤ 1)
  (k : ℕ) :
-- imply
  ‖centralBinomialCoeff k * t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 2‖ ≤
    (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.norm_arcsinIntegralSeries_term_le t ht k

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma summable_arcsin_integral_series_term_is
-- given
  (t : ℝ)
  (ht : ‖t‖ ≤ 1) :
-- imply
  Summable (fun n : ℕ =>
    centralBinomialCoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.summable_arcsinIntegralSeries_term t ht

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma arcsin_integral_series_zero_eq :
-- imply
  arcsinIntegralSeries 0 = 0 := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.arcsinIntegralSeries_zero

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma continuous_on_arcsin_integral_series_is :
-- imply
  ContinuousOn arcsinIntegralSeries (Set.Icc (-1 : ℝ) 1) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.continuousOn_arcsinIntegralSeries

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma summable_arcsin_series_term_is
-- given
  (y : ℝ)
  (hy : ‖y‖ < 1) :
-- imply
  Summable (fun n : ℕ =>
    centralBinomialCoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.summable_arcsinSeries_term hy

/--
[ArcsinTaylorSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinTaylorSeries.lean)
-/
@[path]
private lemma has_deriv_at_arcsin_integral_series_is
-- given
  (y : ℝ)
  (hy : ‖y‖ < 1)
  (hy0 : y ≠ 0) :
-- imply
  HasDerivAt arcsinIntegralSeries (Real.arcsin y / y) y := by
-- proof
  apply SpecialFunctions.ArcsinTaylorSeries.hasDerivAt_arcsinIntegralSeries hy hy0

-- created on 2026-10-10
