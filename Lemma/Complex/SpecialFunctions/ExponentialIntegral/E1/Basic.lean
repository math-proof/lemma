import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.ExponentialIntegral.E1.Basic
open Complex


/--
[integrableOn_exp_neg_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
private lemma integrableOn_exp_neg_mul_pow_eq
  {n : ℕ} :
-- imply
  MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) := by
-- proof
  apply Complex.integrableOn_exp_neg_mul_pow n

/--
[integral_exp_neg_mul_pow_Ioi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
private lemma integral_exp_neg_mul_pow_Ioi_eq
  {n : ℕ} :
-- imply
  ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ n = (n.factorial : ℝ) := by
-- proof
  apply Complex.integral_exp_neg_mul_pow_Ioi n

/--
[integral_remainder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/Basic.lean)
-/
@[path]
private lemma integral_remainder_bound_eq
  {z : ℂ}
-- given
  (hz : z ≠ 0)
  (hargLower : Real.pi / 2 ≤ |z.arg|)
  (hargUpper : |z.arg| < Real.pi) :
-- imply
  ‖Complex.exp (-z) / z^2 *
    ∫ t : ℝ in Set.Ioi 0,
    (Real.exp (-t) : ℂ) * (t : ℂ)^2 / ((t : ℂ) + z)‖
    ≤ (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
-- proof
  apply Complex.integral_remainder_bound z hz hargLower hargUpper


-- created on 2026-10-20
