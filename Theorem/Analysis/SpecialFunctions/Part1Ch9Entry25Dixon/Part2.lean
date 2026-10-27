/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry25Dixon

open scoped Topology

open Filter

noncomputable section

theorem dixon_zpow_eq (x theta : ℝ) (j : ℕ) :
    ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) =
      ((x ^ (j + 1) : ℝ) : ℂ) *
        ((Real.cos (((j + 1 : ℕ) : ℝ) * theta) : ℂ) +
         (Real.sin (((j + 1 : ℕ) : ℝ) * theta) : ℂ) * Complex.I) := by
  rw [mul_pow, ← Complex.ofReal_pow]
  congr 1
  rw [← Complex.exp_nat_mul]
  have e := dixon_exp_polar' (((j + 1 : ℕ) : ℝ) * theta)
  convert e using 2
  push_cast; ring

theorem dixon_Lterm_re (x theta : ℝ) (j : ℕ) :
    (dixonL ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) j).re
      = chapter9DilogCosTerm x theta j := by
  unfold dixonL chapter9DilogCosTerm
  simp only
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re, dixon_zpow_eq]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dixon_Lterm_im (x theta : ℝ) (j : ℕ) :
    (dixonL ((x : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) j).im
      = chapter9DilogSinTerm x theta j := by
  unfold dixonL chapter9DilogSinTerm
  simp only
  rw [← Complex.ofReal_pow, Complex.div_ofReal_im, dixon_zpow_eq]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dixon_norm_Lterm_le (u : ℂ) (hu : ‖u‖ ≤ 1) (j : ℕ) :
    ‖dixonL u j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hpow : ‖u‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hu
  unfold dixonL
  rw [norm_div, Complex.norm_pow]
  have hden : ‖((((j + 1 : ℕ) : ℝ) : ℂ) ^ 2)‖ = ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hden]
  exact div_le_div_of_nonneg_right hpow hk.le

theorem dixon_summable_Lterm (u : ℂ) (hu : ‖u‖ ≤ 1) : Summable (dixonL u) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift (dixon_norm_Lterm_le u hu)

theorem dixon_one_sub_mem_slitPlane (x theta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta) :
    (1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [dixon_re_one_sub_z]
  linarith

theorem dixon_log_one_sub_z_re (x theta : ℝ)
    (hAx : 0 < 1 - 2 * x * Real.cos theta + x ^ 2) :
    (Complex.log (1 - (x : ℂ) * Complex.exp (Complex.I * theta))).re
      = Real.log (1 - 2 * x * Real.cos theta + x ^ 2) / 2 := by
  rw [Complex.log_re]
  have hnorm : ‖(1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)‖
      = Real.sqrt (1 - 2 * x * Real.cos theta + x ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, dixon_normSq_one_sub_z]
  rw [hnorm, Real.log_sqrt hAx.le]

theorem dixon_log_one_sub_z_im (x theta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta) :
    (Complex.log (1 - (x : ℂ) * Complex.exp (Complex.I * theta))).im
      = -Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) := by
  rw [Complex.log_im]
  have hre_pos : (0 : ℝ) < 1 - x * Real.cos theta := by linarith
  have harg_bound : |((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg|
      < Real.pi / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]
    left
    rw [dixon_re_one_sub_z]
    exact hre_pos
  have htan : Real.tan (((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg)
      = -(x * Real.sin theta / (1 - x * Real.cos theta)) := by
    rw [Complex.tan_arg, dixon_im_one_sub_z, dixon_re_one_sub_z]
    ring
  have h1 := abs_lt.mp harg_bound
  have h2 : Real.arctan (Real.tan
      (((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg))
      = ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).arg :=
    Real.arctan_tan h1.1 h1.2
  rw [htan, Real.arctan_neg] at h2
  exact h2.symm

end
end Entry25Dixon
end Ramanujan.Part1Ch9
end
