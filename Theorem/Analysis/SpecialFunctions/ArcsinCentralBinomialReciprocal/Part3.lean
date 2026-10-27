import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part4


namespace MetaMathlibExt

theorem Dterm_zero (x : ℝ) : Dterm x 0 = 0 := by simp [Dterm]

-- key bound for n ≥ 1
theorem Dterm_bound (x : ℝ) (hx0 : x ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ‖Dterm x n‖ ≤ (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
  have hratio := ratio_le n hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
  have hd : dcoef n = ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ) := by
    simp only [dcoef]; field_simp
  have hnorm : ‖Dterm x n‖ = 2 * (((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) * (n : ℝ)) * |x| ^ (2 * n - 1) := by
    simp only [Dterm, show n ≠ 0 by omega, ↓reduceIte]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [abs_of_nonneg (dcoef_nonneg n)]
    rw [abs_pow, hd]
  rw [hnorm]
  have hle2 : (2:ℝ) * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ))) ≤ 4 := by linarith
  have hpow_abs : |x| ^ (2 * n - 1) = (|x| ^ 2) ^ n / |x| := by
    have h1 : |x| ^ (2 * n) = (|x| ^ 2) ^ n := by rw [← pow_mul]
    have h2 : 2 * n = (2 * n - 1) + 1 := by omega
    have h3 : |x| ^ (2 * n) = |x| ^ (2 * n - 1) * |x| := by conv_lhs => rw [h2]; rw [pow_succ]
    have hne : |x| ≠ 0 := ne_of_gt habs
    have h4 : |x| ^ (2 * n - 1) = |x| ^ (2 * n) / |x| := by
      field_simp
      exact h3.symm
    rw [h4, h1]
  rw [hpow_abs]
  have hsq : (|x| ^ 2) ^ n = (x ^ 2) ^ n := by rw [sq_abs]
  rw [hsq]
  have hpos : (0:ℝ) ≤ (x ^ 2) ^ n / |x| := by positivity
  calc 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ)) * ((x ^ 2) ^ n / |x|)
      ≤ (4 * (n : ℝ)) * ((x ^ 2) ^ n / |x|) := by
        have h4 : 2 * ((4 ^ n : ℝ) / ((n : ℝ) * (Nat.choose (2 * n) n : ℝ)) * (n : ℝ))
            ≤ 4 * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_right hle2 (le_of_lt hnR)
          linarith
        exact mul_le_mul_of_nonneg_right h4 hpos
    _ = (4 / |x|) * ((n : ℝ) * (x ^ 2) ^ n) := by ring
    _ ≤ (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (n : ℝ) * (x ^ 2) ^ n ≤ ((n : ℝ) + 1) * (x ^ 2) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sq_nonneg x) n)
        exact this

theorem summable_Dterm (x : ℝ) (hx : |x| < 1) : Summable (Dterm x) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : Dterm 0 = fun _ => 0 := by
      funext n
      by_cases h : n = 0
      · simp [Dterm, h]
      · simp [Dterm, h, zero_pow (by omega : 2 * n - 1 ≠ 0)]
    rw [h0]; exact summable_zero
  · have hx2 : x ^ 2 < 1 := by nlinarith [hx, abs_nonneg x, sq_abs x]
    have hnn : 0 ≤ x ^ 2 := sq_nonneg x
    have hgeom := summable_succ_mul_geom (x ^ 2) hnn hx2
    have hC : Summable (fun n : ℕ => (4 / |x|) * (((n : ℝ) + 1) * (x ^ 2) ^ n)) :=
      hgeom.mul_left _
    apply Summable.of_norm_bounded hC
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [Dterm_zero, norm_zero]
      positivity
    · exact Dterm_bound x hx0 n (by omega)

end MetaMathlibExt
