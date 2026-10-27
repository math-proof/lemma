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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon
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

/-- Complex polar form of `exp (I * t)`. -/
theorem dixon_exp_polar (t : ℝ) : Complex.exp (Complex.I * (t : ℂ)) =
    ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem dixon_exp_polar' (t : ℝ) : Complex.exp ((t : ℂ) * Complex.I) =
    ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm]; exact dixon_exp_polar t

theorem dixon_re_z (x theta : ℝ) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re = x * Real.cos theta := by
  rw [dixon_exp_polar]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dixon_im_z (x theta : ℝ) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).im = x * Real.sin theta := by
  rw [dixon_exp_polar]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem dixon_re_one_sub_z (x theta : ℝ) :
    ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).re
      = 1 - x * Real.cos theta := by
  rw [Complex.sub_re, Complex.one_re, dixon_re_z]

theorem dixon_im_one_sub_z (x theta : ℝ) :
    ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta)).im
      = -(x * Real.sin theta) := by
  rw [Complex.sub_im, Complex.one_im, dixon_im_z]; ring

theorem dixon_normSq_one_sub_z (x theta : ℝ) :
    Complex.normSq ((1 : ℂ) - (x : ℂ) * Complex.exp (Complex.I * theta))
      = 1 - 2 * x * Real.cos theta + x ^ 2 := by
  rw [Complex.normSq_apply, dixon_re_one_sub_z, dixon_im_one_sub_z]
  have h := Real.sin_sq_add_cos_sq theta
  nlinarith [h, sq_nonneg (x * Real.cos theta), sq_nonneg (x * Real.sin theta)]

/-- The hypothesis `hxy` says `z + w = z * w`. -/
theorem dixon_zw_mul (x y theta phi : ℝ)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        (x * y : ℝ) * Complex.exp (Complex.I * (theta + phi))) :
    (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)) := by
  rw [hxy]
  push_cast
  have hexp : Complex.exp (Complex.I * ((theta : ℂ) + phi)) =
      Complex.exp (Complex.I * theta) * Complex.exp (Complex.I * phi) := by
    rw [mul_add, Complex.exp_add]
  rw [hexp]
  ring

theorem dixon_norm_z (x theta : ℝ) (hx0 : 0 ≤ x) :
    ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ = x := by
  have e : ‖Complex.exp (Complex.I * (theta : ℂ))‖ = 1 := by
    rw [mul_comm Complex.I]
    exact Complex.norm_exp_ofReal_mul_I theta
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, e, mul_one]

theorem dixon_z_ne_one (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi))) :
    (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1 := by
  intro hz
  have h2 : (1 : ℂ) + (y : ℂ) * Complex.exp (Complex.I * phi) =
      (1 : ℂ) * ((y : ℂ) * Complex.exp (Complex.I * phi)) := by
    rw [← hz]; exact h
  rw [one_mul] at h2
  have h1 : (1 : ℂ) = 0 := by
    have h3 := congrArg (· - (y : ℂ) * Complex.exp (Complex.I * phi)) h2
    simp at h3
  exact one_ne_zero h1

theorem dixon_w_eq_div (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)))
    (hz : (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1) :
    (y : ℂ) * Complex.exp (Complex.I * phi) =
      ((x : ℂ) * Complex.exp (Complex.I * theta)) /
        (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) := by
  have hsub : ((x : ℂ) * Complex.exp (Complex.I * theta)) - 1 ≠ 0 :=
    sub_ne_zero.mpr hz
  have key : ((y : ℂ) * Complex.exp (Complex.I * phi)) *
      (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) =
        (x : ℂ) * Complex.exp (Complex.I * theta) := by
    linear_combination -h
  exact (eq_div_iff hsub).mpr key

theorem dixon_re_le_half (x y theta phi : ℝ)
    (h : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        ((x : ℂ) * Complex.exp (Complex.I * theta)) *
        ((y : ℂ) * Complex.exp (Complex.I * phi)))
    (hw : ‖(y : ℂ) * Complex.exp (Complex.I * phi)‖ ≤ 1) :
    (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2 := by
  have hz1 : (x : ℂ) * Complex.exp (Complex.I * theta) ≠ 1 :=
    dixon_z_ne_one x y theta phi h
  have hw_eq : (y : ℂ) * Complex.exp (Complex.I * phi) =
      ((x : ℂ) * Complex.exp (Complex.I * theta)) /
        (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) :=
    dixon_w_eq_div x y theta phi h hz1
  have hpos : (0 : ℝ) < ‖((x : ℂ) * Complex.exp (Complex.I * theta)) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hle : ‖(x : ℂ) * Complex.exp (Complex.I * theta)‖ ≤
      ‖((x : ℂ) * Complex.exp (Complex.I * theta)) - 1‖ := by
    rw [hw_eq, norm_div, div_le_one hpos] at hw
    exact hw
  have hsq : Complex.normSq ((x : ℂ) * Complex.exp (Complex.I * theta)) ≤
      Complex.normSq (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) := by
    have e1 := Complex.sq_norm ((x : ℂ) * Complex.exp (Complex.I * theta))
    have e2 := Complex.sq_norm (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1)
    rw [← e1, ← e2]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at hsq
  nlinarith [hsq]

theorem dixon_side_nonvanish (x theta : ℝ)
    (hre : (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2) :
    1 - x * Real.cos theta ≠ 0 := by
  rw [dixon_re_z] at hre
  intro hcon
  linarith

theorem dixon_Ax_expand (x theta : ℝ) : 1 - 2 * x * Real.cos theta + x ^ 2 =
    (1 - x * Real.cos theta) ^ 2 + (x * Real.sin theta) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq theta
  linear_combination (-(x ^ 2)) * h

theorem dixon_side_pos (x theta : ℝ)
    (hre : (((x : ℂ) * Complex.exp (Complex.I * theta)) : ℂ).re ≤ 1 / 2) :
    0 < 1 - 2 * x * Real.cos theta + x ^ 2 := by
  rw [dixon_re_z] at hre
  rw [dixon_Ax_expand]
  have hcos : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta := by linarith
  have h4 : (1 / 2 : ℝ) ^ 2 ≤ (1 - x * Real.cos theta) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hcos 2
  have hnn : (0 : ℝ) ≤ (x * Real.sin theta) ^ 2 := sq_nonneg _
  norm_num at h4 ⊢
  linarith

theorem dixon_aux_summable_inv_sq_shift :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2))) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h2
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem dixon_norm_dilogCos_le (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (j : ℕ) :
    ‖chapter9DilogCosTerm rho angle j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hcos : |Real.cos ((((j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := Real.abs_cos_le_one _
  have hpow : rho ^ (j + 1) ≤ 1 := pow_le_one₀ h0 h1
  have hnn : (0 : ℝ) ≤ rho ^ (j + 1) := pow_nonneg h0 _
  unfold chapter9DilogCosTerm
  simp only
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  calc |rho ^ (j + 1) * Real.cos _|
      = rho ^ (j + 1) * |Real.cos _| := by rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ 1 * 1 := mul_le_mul hpow hcos (abs_nonneg _) zero_le_one
    _ = 1 := mul_one 1

theorem dixon_norm_dilogSin_le (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (j : ℕ) :
    ‖chapter9DilogSinTerm rho angle j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
  have hk : (0 : ℝ) < ((((j + 1 : ℕ) : ℝ) ^ 2)) := by positivity
  have hsin : |Real.sin ((((j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := Real.abs_sin_le_one _
  have hpow : rho ^ (j + 1) ≤ 1 := pow_le_one₀ h0 h1
  have hnn : (0 : ℝ) ≤ rho ^ (j + 1) := pow_nonneg h0 _
  unfold chapter9DilogSinTerm
  simp only
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  calc |rho ^ (j + 1) * Real.sin _|
      = rho ^ (j + 1) * |Real.sin _| := by rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ 1 * 1 := mul_le_mul hpow hsin (abs_nonneg _) zero_le_one
    _ = 1 := mul_one 1

theorem dixon_summable_dilogCos (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    Summable (chapter9DilogCosTerm rho angle) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift
    (dixon_norm_dilogCos_le rho angle h0 h1)

theorem dixon_summable_dilogSin (rho angle : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    Summable (chapter9DilogSinTerm rho angle) :=
  Summable.of_norm_bounded dixon_aux_summable_inv_sq_shift
    (dixon_norm_dilogSin_le rho angle h0 h1)

end
end Entry25Dixon
end Ramanujan.Part1Ch9
end
