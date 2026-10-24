import Mathlib
import Lemma.Definitions.Def_TateCurve_QSeries

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section Ultrametric

theorem nnnorm_one_sub_of_one_lt {x : K} (hx : 1 < ‖x‖₊) : ‖1 - x‖₊ = ‖x‖₊ := by
  have h : ‖(1 : K)‖₊ ≠ ‖-x‖₊ := by
    rw [nnnorm_neg, nnnorm_one]
    exact ne_of_lt hx
  rw [sub_eq_add_neg, nnnorm_add_eq_max_of_nnnorm_ne_nnnorm h, nnnorm_neg, nnnorm_one]
  exact max_eq_right hx.le

theorem one_sub_ne_zero_of_one_lt {x : K} (hx : 1 < ‖x‖₊) : (1 : K) - x ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, nnnorm_one] at hx
  exact lt_irrefl 1 hx

end Ultrametric

section RationalFunctions

def xfun (w : K) : K := w / (1 - w) ^ 2

def yfun (w : K) : K := w ^ 2 / (1 - w) ^ 3

@[simp] theorem xfun_zero : xfun (0 : K) = 0 := by simp [xfun]

@[simp] theorem yfun_zero : yfun (0 : K) = 0 := by simp [yfun]

theorem xfun_inv {w : K} (hw0 : w ≠ 0) (hw1 : w ≠ 1) : xfun w⁻¹ = xfun w := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hvw : w⁻¹ * w = 1 := inv_mul_cancel₀ hw0
  have hv1 : (1 : K) - w⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hw1
    rw [← inv_inv w, ← h, inv_one]
  rw [xfun, xfun, div_eq_div_iff (pow_ne_zero 2 hv1) (pow_ne_zero 2 h1)]

  linear_combination (w - w⁻¹) * hvw

theorem yfun_inv {w : K} (hw0 : w ≠ 0) (hw1 : w ≠ 1) : yfun w⁻¹ = -yfun w - xfun w := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hvw : w⁻¹ * w = 1 := inv_mul_cancel₀ hw0
  have hv1 : (1 : K) - w⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hw1
    rw [← inv_inv w, ← h, inv_one]

  have hx3 : xfun w = w * (1 - w) / (1 - w) ^ 3 := by
    rw [xfun, div_eq_div_iff (pow_ne_zero 2 h1) (pow_ne_zero 3 h1)]
    ring
  have hrhs : -yfun w - xfun w = -w / (1 - w) ^ 3 := by
    rw [yfun, hx3, ← neg_div, ← sub_div, div_eq_div_iff (pow_ne_zero 3 h1) (pow_ne_zero 3 h1)]
    ring
  rw [hrhs, yfun, div_eq_div_iff (pow_ne_zero 3 hv1) (pow_ne_zero 3 h1)]

  linear_combination (-(w⁻¹ ^ 2) - w⁻¹ * w ^ 2 + 3 * (w⁻¹ * w) - w) * hvw

theorem nnnorm_xfun_of_lt_one {w : K} (hw : ‖w‖₊ < 1) : ‖xfun w‖₊ = ‖w‖₊ := by
  rw [xfun, nnnorm_div, nnnorm_pow, nnnorm_one_sub_of_lt_one hw, one_pow, div_one]

theorem nnnorm_xfun_of_one_lt {w : K} (hw : 1 < ‖w‖₊) : ‖xfun w‖₊ = ‖w‖₊⁻¹ := by
  have hw0 : ‖w‖₊ ≠ 0 := (zero_lt_one.trans hw).ne'
  rw [xfun, nnnorm_div, nnnorm_pow, nnnorm_one_sub_of_one_lt hw]
  have h2 : ‖w‖₊ ^ 2 = ‖w‖₊ * ‖w‖₊ := by ring
  rw [h2, div_mul_eq_div_div, div_self hw0, one_div]

theorem nnnorm_yfun_of_lt_one {w : K} (hw : ‖w‖₊ < 1) : ‖yfun w‖₊ = ‖w‖₊ ^ 2 := by
  rw [yfun, nnnorm_div, nnnorm_pow, nnnorm_pow, nnnorm_one_sub_of_lt_one hw, one_pow, div_one]

theorem nnnorm_yfun_of_one_lt {w : K} (hw : 1 < ‖w‖₊) : ‖yfun w‖₊ = ‖w‖₊⁻¹ := by
  have hw0 : ‖w‖₊ ≠ 0 := (zero_lt_one.trans hw).ne'
  rw [yfun, nnnorm_div, nnnorm_pow, nnnorm_pow, nnnorm_one_sub_of_one_lt hw]
  have h3 : ‖w‖₊ ^ 3 = ‖w‖₊ ^ 2 * ‖w‖₊ := by ring
  rw [h3, div_mul_eq_div_div, div_self (pow_ne_zero 2 hw0), one_div]

end RationalFunctions

section Terms

variable (q u : K)

def xTerm (n : ℤ) : K := xfun (q ^ n * u)

def yTerm (n : ℤ) : K := yfun (q ^ n * u)

@[simp] theorem xTerm_zero : xTerm q u 0 = xfun u := by rw [xTerm, zpow_zero, one_mul]

@[simp] theorem yTerm_zero : yTerm q u 0 = yfun u := by rw [yTerm, zpow_zero, one_mul]

variable {q u}

theorem summable_comp_zpow_mul [CompleteSpace K] {F : K → K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hu0 : u ≠ 0) (hF₁ : ∀ w : K, ‖w‖₊ < 1 → ‖F w‖₊ ≤ ‖w‖₊)
    (hF₂ : ∀ w : K, 1 < ‖w‖₊ → ‖F w‖₊ ≤ ‖w‖₊⁻¹) :
    Summable fun n : ℤ => F (q ^ n * u) := by
  have hq' : ‖q‖ < 1 := by exact_mod_cast hq
  have hu' : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq'
  apply Summable.of_nat_of_neg_add_one
  ·
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have hlim : Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖u‖) atTop (nhds 0) := by
      simpa using hpow.mul_const ‖u‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hlim.eventually_lt_const one_pos] with n hn
    have hn' : ‖q ^ (n : ℤ) * u‖₊ < 1 := by
      rw [nnnorm_mul, nnnorm_zpow, zpow_natCast]
      exact_mod_cast hn
    calc ‖F (q ^ (n : ℤ) * u)‖ ≤ ‖q ^ (n : ℤ) * u‖ := by exact_mod_cast hF₁ _ hn'
      _ = ‖q‖ ^ n * ‖u‖ := by rw [norm_mul, norm_zpow, zpow_natCast]
  ·

    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have hlim : Tendsto (fun n : ℕ => ‖q‖ ^ n * ‖u‖⁻¹) atTop (nhds 0) := by
      simpa using hpow.mul_const ‖u‖⁻¹
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hpow.eventually_lt_const hu'] with n hn

    have hqpos : (0 : ℝ≥0) < ‖q‖₊ := by simpa [pos_iff_ne_zero] using hq0
    have hqn : (0 : ℝ≥0) < ‖q‖₊ ^ (n + 1) := pow_pos hqpos _
    have hnlt : ‖q‖₊ ^ (n + 1) < ‖u‖₊ := by
      have h1 : ‖q‖₊ ^ (n + 1) ≤ ‖q‖₊ ^ n :=
        pow_le_pow_of_le_one zero_le hq.le (Nat.le_succ n)
      exact h1.trans_lt (by exact_mod_cast hn)
    have hexp : q ^ (-((n : ℤ) + 1)) = (q ^ (n + 1) : K)⁻¹ := by
      rw [show -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, zpow_neg, zpow_natCast]
    have hval : ‖q ^ (-((n : ℤ) + 1)) * u‖₊ = (‖q‖₊ ^ (n + 1))⁻¹ * ‖u‖₊ := by
      rw [hexp, nnnorm_mul, nnnorm_inv, nnnorm_pow]
    have hgt : 1 < ‖q ^ (-((n : ℤ) + 1)) * u‖₊ := by
      rw [hval]
      calc (1 : ℝ≥0) = (‖q‖₊ ^ (n + 1))⁻¹ * ‖q‖₊ ^ (n + 1) := (inv_mul_cancel₀ hqn.ne').symm
        _ < (‖q‖₊ ^ (n + 1))⁻¹ * ‖u‖₊ :=
            mul_lt_mul_of_pos_left hnlt (pos_iff_ne_zero.mpr (inv_ne_zero hqn.ne'))
    have hbound : ‖F (q ^ (-((n : ℤ) + 1)) * u)‖₊ ≤ ‖q‖₊ ^ n * ‖u‖₊⁻¹ := by
      refine (hF₂ _ hgt).trans ?_
      rw [hval, mul_inv, inv_inv]
      exact mul_le_mul_left (pow_le_pow_of_le_one zero_le hq.le (Nat.le_succ n)) _
    calc ‖F (q ^ (-((n : ℤ) + 1)) * u)‖ ≤ ((‖q‖₊ ^ n * ‖u‖₊⁻¹ : ℝ≥0) : ℝ) := by
          exact_mod_cast hbound
      _ = ‖q‖ ^ n * ‖u‖⁻¹ := by push_cast; ring

theorem summable_xTerm [CompleteSpace K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    Summable (xTerm q u) :=
  summable_comp_zpow_mul hq0 hq hu0 (fun _ hw => (nnnorm_xfun_of_lt_one hw).le)
    (fun _ hw => (nnnorm_xfun_of_one_lt hw).le)

theorem summable_yTerm [CompleteSpace K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    Summable (yTerm q u) :=
  summable_comp_zpow_mul hq0 hq hu0
    (fun w hw => by
      rw [nnnorm_yfun_of_lt_one hw]
      calc ‖w‖₊ ^ 2 ≤ ‖w‖₊ ^ 1 := pow_le_pow_of_le_one zero_le hw.le one_le_two
        _ = ‖w‖₊ := pow_one _)
    (fun _ hw => (nnnorm_yfun_of_one_lt hw).le)

end Terms

section PointSeries

variable [CompleteSpace K] (q u : K)

noncomputable def s₁ : K := coeffSum (fun n => n) q

noncomputable def pointX : K := (∑' n : ℤ, xTerm q u n) - 2 * s₁ q

noncomputable def pointY : K := (∑' n : ℤ, yTerm q u n) + s₁ q

variable {q u}

theorem nnnorm_s₁_le (hq : ‖q‖₊ < 1) : ‖s₁ q‖₊ ≤ ‖q‖₊ :=
  nnnorm_coeffSum_le _ hq

end PointSeries

end TateCurve
