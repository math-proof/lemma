import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.KaluzaCoefficientBounds
open MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted


/--
[HasPositiveLogConvexCoefficients.coeff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/KaluzaCoefficientBounds.lean)
-/
@[path]
private lemma HasPositiveLogConvexCoefficients_coeff_pos_eq
  {f : PowerSeries ℝ}
  {n : ℕ}
-- given
  (hf : HasPositiveLogConvexCoefficients f) :
-- imply
  0 < PowerSeries.coeff n f := by
-- proof
  apply MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted.HasPositiveLogConvexCoefficients.coeff_pos hf n

/--
[HasPositiveLogConvexCoefficients.sq_coeff_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/KaluzaCoefficientBounds.lean)
-/
@[path]
private lemma HasPositiveLogConvexCoefficients_sq_coeff_succ_le_eq
  {f : PowerSeries ℝ}
  {n : ℕ}
-- given
  (hf : HasPositiveLogConvexCoefficients f) :
-- imply
  (PowerSeries.coeff (n + 1) f) ^ 2 ≤ PowerSeries.coeff n f * PowerSeries.coeff (n + 2) f := by
-- proof
  apply MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted.HasPositiveLogConvexCoefficients.sq_coeff_succ_le hf n

/--
[kaluza_coeff_inv_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/KaluzaCoefficientBounds.lean)
-/
@[path]
private lemma kaluza_coeff_inv_bounds_eq
  {f : PowerSeries ℝ}
-- given
  (hf : HasPositiveLogConvexCoefficients f) :
-- imply
  PowerSeries.coeff 0 (f⁻¹) = (PowerSeries.coeff 0 f)⁻¹ ∧
    0 < PowerSeries.coeff 0 (f⁻¹) ∧
    ∀ n : ℕ, 1 ≤ n →
    -(PowerSeries.coeff n f) / (PowerSeries.coeff 0 f) ^ 2 ≤
    PowerSeries.coeff n (f⁻¹) ∧
    PowerSeries.coeff n (f⁻¹) ≤ 0 := by
-- proof
  apply MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted.kaluza_coeff_inv_bounds f hf


-- created on 2026-10-20
