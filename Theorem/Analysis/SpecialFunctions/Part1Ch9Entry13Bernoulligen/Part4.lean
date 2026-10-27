/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part4
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

theorem entry13w_re (r x : ℝ) : (entry13w r x).re = r * Real.cos x := by
  unfold entry13w
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem entry13w_im (r x : ℝ) : (entry13w r x).im = r * Real.sin x := by
  unfold entry13w
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem entry13w_norm {r : ℝ} (hr0 : 0 ≤ r) (x : ℝ) :
    ‖entry13w r x‖ = r := by
  unfold entry13w
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    Real.norm_of_nonneg hr0, mul_one]

theorem entry13w_pow (r x : ℝ) (n : ℕ) :
    entry13w r x ^ n =
      ((r ^ n : ℝ) : ℂ) * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
  unfold entry13w
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  ring

theorem entry13w_pow_div_re (r x : ℝ) (n : ℕ) :
    (entry13w r x ^ n / (n : ℂ)).re
      = r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) := by
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [entry13w_pow]
    have hcast : ((((n : ℝ))) : ℂ) = (n : ℂ) := Complex.ofReal_natCast n
    have hdiv : ((((r ^ n : ℝ)) : ℂ)
          * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) / (n : ℂ))
        = ((((r ^ n / (n : ℝ) : ℝ))) : ℂ)
          * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_div, hcast]
      ring
    rw [hdiv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re]
    simp only [zero_mul, sub_zero]
    ring

theorem entry13_norm_one_sub_w (r x : ℝ) :
    ‖(1 : ℂ) - entry13w r x‖ ^ 2 = entry13D r x := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((1 : ℂ) - entry13w r x).re = 1 - r * Real.cos x := by
    simp [Complex.sub_re, entry13w_re]
  have him : ((1 : ℂ) - entry13w r x).im = -(r * Real.sin x) := by
    simp [Complex.sub_im, entry13w_im]
  rw [hre, him]
  unfold entry13D
  have hsq := Real.sin_sq_add_cos_sq x
  linear_combination (r ^ 2) * hsq

theorem entry13_neglog_re (r x : ℝ) :
    (-Complex.log (1 - entry13w r x)).re = entry13c1closed r x := by
  have hnorm : ‖(1 : ℂ) - entry13w r x‖ ^ 2 = entry13D r x :=
    entry13_norm_one_sub_w r x
  have hlog : Real.log (entry13D r x)
      = 2 * Real.log ‖(1 : ℂ) - entry13w r x‖ := by
    conv_lhs => rw [← hnorm]
    rw [Real.log_pow]
    norm_num
  rw [Complex.neg_re, Complex.log_re]
  unfold entry13c1closed
  rw [hlog]
  ring

theorem entry13_H1_unshifted {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ => r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ))
      (entry13c1closed r x) := by
  have hnorm : ‖entry13w r x‖ < 1 := by
    rw [entry13w_norm hr0 x]
    exact hr1
  have h := Complex.hasSum_taylorSeries_neg_log hnorm
  have hr := Complex.hasSum_re h
  rw [entry13_neglog_re] at hr
  have hterm : ∀ n : ℕ, r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ)
      = (entry13w r x ^ n / (n : ℂ)).re :=
    fun n => (entry13w_pow_div_re r x n).symm
  exact HasSum.congr_fun hr hterm

theorem entry13_H1_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun k : ℕ => r ^ (k + 1) * chapter9ClausenTerm 1 x k)
      (entry13c1closed r x) := by
  have hr2 := entry13_H1_unshifted hr0 hr1 x
  have hshift := (hasSum_nat_add_iff'
    (f := fun n : ℕ => r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ))
    (g := entry13c1closed r x) 1).mpr hr2
  rw [Finset.sum_range_one] at hshift
  simp only [Nat.cast_zero, pow_zero, zero_mul, Real.cos_zero, div_zero,
    sub_zero] at hshift
  have hT : ∀ k : ℕ, r ^ (k + 1) * chapter9ClausenTerm 1 x k
      = r ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro k
    have hne : ¬Even (1 : ℕ) := by
      rw [Nat.even_iff]
      decide
    unfold chapter9ClausenTerm
    simp only [hne, ite_false, pow_one]
    ring
  exact HasSum.congr_fun hshift hT

theorem entry13_H1_tsum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    entry13cm 1 r x = entry13c1closed r x :=
  (entry13_H1_hasSum hr0 hr1 x).tsum_eq

/-! ## Helper H2: derivatives in `x` -/

theorem entry13D_hasDerivAt (r x : ℝ) :
    HasDerivAt (fun x => entry13D r x) (2 * r * Real.sin x) x := by
  have hcos : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have hmul : HasDerivAt (fun y => 2 * r * Real.cos y)
      (2 * r * (-Real.sin x)) x :=
    HasDerivAt.const_mul (2 * r) hcos
  have h1 : HasDerivAt (fun y => 1 - 2 * r * Real.cos y)
      (0 - 2 * r * (-Real.sin x)) x :=
    (hasDerivAt_const x (1 : ℝ)).sub hmul
  have h2 : HasDerivAt (fun y => 1 - 2 * r * Real.cos y + r ^ 2)
      ((0 - 2 * r * (-Real.sin x)) + 0) x :=
    h1.add (hasDerivAt_const x (r ^ 2))
  have hderiv : (0 - 2 * r * (-Real.sin x)) + 0 = 2 * r * Real.sin x := by
    ring
  rw [hderiv] at h2
  have hfun : (fun y => 1 - 2 * r * Real.cos y + r ^ 2)
      = (fun x => entry13D r x) := by
    unfold entry13D
    rfl
  rw [hfun] at h2
  exact h2

theorem entry13c1closed_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun x => entry13c1closed r x) (-entry13K r x) x := by
  have hD := entry13D_hasDerivAt r x
  have hne : entry13D r x ≠ 0 := entry13D_ne_zero hr0 hr1 x
  have hlog := hD.log hne
  have hmul := HasDerivAt.const_mul (-(1 / 2) : ℝ) hlog
  have hderiv : (-(1 / 2) : ℝ) * ((2 * r * Real.sin x) / entry13D r x)
      = -(r * Real.sin x / entry13D r x) := by
    ring
  rw [hderiv] at hmul
  have hfun : (fun y => (-(1 / 2) : ℝ) * Real.log (entry13D r y))
      = (fun x => entry13c1closed r x) := by
    unfold entry13c1closed
    rfl
  have hK : -(r * Real.sin x / entry13D r x) = -entry13K r x := by
    unfold entry13K
    rfl
  rw [hfun, hK] at hmul
  exact hmul

theorem entry13_clausenTerm_norm_le_one (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9ClausenTerm m x k‖ ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ m) := by
    apply one_le_pow₀
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos := chapter9ClausenTerm_base_pos m k
  have h2 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) ≤ 1 := by
    rw [div_le_one hpos]
    exact hbase
  exact le_trans (chapter9ClausenTerm_norm_bound m x k) h2

theorem entry13_sin_term_hasDerivAt (m k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => Real.sin (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))
      (Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)) x := by
  set C : ℝ := ((k + 1 : ℕ) : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by
    rw [hC]
    have h0 : (0 : ℕ) < k + 1 := by omega
    exact_mod_cast h0
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  have hlin : HasDerivAt (fun y : ℝ => C * y) C x := by
    have h := HasDerivAt.const_mul C (hasDerivAt_id x)
    simpa using h
  have hsin : HasDerivAt (fun y => Real.sin (C * y) / C ^ (m + 1))
      (Real.cos (C * x) * C / C ^ (m + 1)) x :=
    HasDerivAt.div_const hlin.sin (C ^ (m + 1))
  have hpow : C ^ (m + 1) = C ^ m * C := pow_succ C m
  have hCm0 : C ^ m ≠ 0 := pow_ne_zero m hC0
  have hderiv : Real.cos (C * x) * C / C ^ (m + 1)
      = Real.cos (C * x) / C ^ m := by
    rw [hpow, div_eq_div_iff (mul_ne_zero hCm0 hC0) hCm0]
    ring
  rw [hderiv] at hsin
  exact hsin

theorem entry13_cos_term_hasDerivAt (m k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => Real.cos (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))
      (-(Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m))) x := by
  set C : ℝ := ((k + 1 : ℕ) : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by
    rw [hC]
    have h0 : (0 : ℕ) < k + 1 := by omega
    exact_mod_cast h0
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  have hlin : HasDerivAt (fun y : ℝ => C * y) C x := by
    have h := HasDerivAt.const_mul C (hasDerivAt_id x)
    simpa using h
  have hcos : HasDerivAt (fun y => Real.cos (C * y) / C ^ (m + 1))
      ((-Real.sin (C * x)) * C / C ^ (m + 1)) x :=
    HasDerivAt.div_const hlin.cos (C ^ (m + 1))
  have hpow : C ^ (m + 1) = C ^ m * C := pow_succ C m
  have hCm0 : C ^ m ≠ 0 := pow_ne_zero m hC0
  have hderiv : (-Real.sin (C * x)) * C / C ^ (m + 1)
      = -(Real.sin (C * x) / C ^ m) := by
    rw [← neg_div, hpow, div_eq_div_iff (mul_ne_zero hCm0 hC0) hCm0]
    ring
  rw [hderiv] at hcos
  exact hcos

theorem entry13eps_eq_one_of_even (m : ℕ) (hm : Even (m + 1)) :
    entry13eps m = 1 := by
  unfold entry13eps
  simp only [hm, ite_true]

theorem entry13eps_eq_neg_one_of_odd (m : ℕ) (hm : ¬Even (m + 1)) :
    entry13eps m = -1 := by
  unfold entry13eps
  simp only [hm, ite_false]

theorem entry13_not_even_of_even_succ (m : ℕ) (hm : Even (m + 1)) :
    ¬Even m := by
  obtain ⟨t, ht⟩ := hm
  rintro ⟨s, hs⟩
  omega

theorem entry13_even_of_not_even_succ (m : ℕ) (hm : ¬Even (m + 1)) :
    Even m := by
  rcases Nat.even_or_odd m with h | h
  · exact h
  · exfalso
    apply hm
    obtain ⟨s, hs⟩ := h
    exact ⟨s + 1, by omega⟩

theorem entry13_clausenTerm_succ_hasDerivAt (m k : ℕ) (r x : ℝ) :
    HasDerivAt (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
      (entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m x k)) x := by
  by_cases hm : Even (m + 1)
  · have hmnot := entry13_not_even_of_even_succ m hm
    have heps := entry13eps_eq_one_of_even m hm
    rw [heps, one_mul]
    have hfun : (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
        = (fun y => r ^ (k + 1)
          * (Real.sin (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))) := by
      funext y
      congr 1
      unfold chapter9ClausenTerm
      simp only [hm, ite_true]
    rw [hfun]
    have hbase := entry13_sin_term_hasDerivAt m k x
    have h := HasDerivAt.const_mul (r ^ (k + 1)) hbase
    have hderiv : r ^ (k + 1)
          * (Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m))
        = r ^ (k + 1) * chapter9ClausenTerm m x k := by
      congr 1
      unfold chapter9ClausenTerm
      simp only [hmnot, ite_false]
    rw [hderiv] at h
    exact h
  · have hme := entry13_even_of_not_even_succ m hm
    have heps := entry13eps_eq_neg_one_of_odd m hm
    rw [heps]
    have hfun : (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
        = (fun y => r ^ (k + 1)
          * (Real.cos (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))) := by
      funext y
      congr 1
      unfold chapter9ClausenTerm
      simp only [hm, ite_false]
    rw [hfun]
    have hbase := entry13_cos_term_hasDerivAt m k x
    have h := HasDerivAt.const_mul (r ^ (k + 1)) hbase
    have hderiv : r ^ (k + 1)
          * (-(Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)))
        = -1 * (r ^ (k + 1) * chapter9ClausenTerm m x k) := by
      have hT : chapter9ClausenTerm m x k
          = Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m) := by
        unfold chapter9ClausenTerm
        simp only [hme, ite_true]
      rw [hT]
      ring
    rw [hderiv] at h
    exact h

theorem entry13_geom_succ_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => r ^ (k + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)

theorem entry13_cm_succ_hasDerivAt (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (fun y => entry13cm (m + 1) r y)
      (entry13eps m * entry13cm m r x) x := by
  have hsum := entry13_geom_succ_summable hr0 hr1
  have hterm : ∀ k (y : ℝ), HasDerivAt
      (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
      (entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k)) y :=
    fun k y => entry13_clausenTerm_succ_hasDerivAt m k r y
  have heps : ‖entry13eps m‖ = 1 := by
    unfold entry13eps
    split_ifs <;> simp
  have hbound : ∀ k (y : ℝ),
      ‖entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k)‖
        ≤ r ^ (k + 1) := by
    intro k y
    rw [norm_mul, heps, one_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr0 (k + 1))]
    have hT := entry13_clausenTerm_norm_le_one m y k
    have hnn : (0 : ℝ) ≤ r ^ (k + 1) := pow_nonneg hr0 _
    have hle := mul_le_mul_of_nonneg_left hT hnn
    rwa [mul_one] at hle
  have h0 : Summable
      (fun k : ℕ => r ^ (k + 1) * chapter9ClausenTerm (m + 1) 0 k) := by
    apply Summable.of_norm_bounded hsum
    intro k
    change ‖r ^ (k + 1) * chapter9ClausenTerm (m + 1) 0 k‖ ≤ r ^ (k + 1)
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr0 (k + 1))]
    have hT := entry13_clausenTerm_norm_le_one (m + 1) 0 k
    have hnn : (0 : ℝ) ≤ r ^ (k + 1) := pow_nonneg hr0 _
    have hle := mul_le_mul_of_nonneg_left hT hnn
    rwa [mul_one] at hle
  have h := hasDerivAt_tsum (u := fun k : ℕ => r ^ (k + 1))
    (g := fun k y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
    (g' := fun k y => entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k))
    (y₀ := (0 : ℝ)) hsum hterm hbound h0 x
  rw [tsum_mul_left] at h
  have hfun : (fun z => ∑' k : ℕ,
        r ^ (k + 1) * chapter9ClausenTerm (m + 1) z k)
      = (fun y => entry13cm (m + 1) r y) := rfl
  have hderiv : entry13eps m
        * (∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k)
      = entry13eps m * entry13cm m r x := rfl
  rw [hfun, hderiv] at h
  exact h

theorem entry13_C_eq_cm (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    entry13C m r x = entry13cm m r x := by
  unfold entry13C
  by_cases hm : m = 1
  · subst hm
    simp only [ite_true]
    exact (entry13_H1_tsum hr0 hr1 x).symm
  · simp only [hm, ite_false]

theorem entry13_C_one_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13C 1 r y) (-entry13K r x) x := by
  have hfun : (fun y => entry13C 1 r y) = (fun y => entry13c1closed r y) := by
    funext y
    unfold entry13C
    simp only [ite_true]
  rw [hfun]
  exact entry13c1closed_hasDerivAt hr0 hr1 x

theorem entry13_C_succ_hasDerivAt (j : ℕ) (hj : 1 ≤ j) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (fun y => entry13C (j + 1) r y)
      (entry13eps j * entry13C j r x) x := by
  have hne : j + 1 ≠ 1 := by omega
  have hfun : (fun y => entry13C (j + 1) r y)
      = (fun y => entry13cm (j + 1) r y) := by
    funext y
    unfold entry13C
    simp only [hne, ite_false]
  rw [hfun]
  have h := entry13_cm_succ_hasDerivAt j hr0 hr1 x
  have hC : entry13cm j r x = entry13C j r x :=
    (entry13_C_eq_cm j hr0 hr1 x).symm
  rw [hC] at h
  exact h

/-! ## Helper H3: the exact identity for fixed `r` -/

theorem entry13_odd_of_even_succ (j : ℕ) (h : Even (j + 1)) : Odd j := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t - 1, by omega⟩

theorem entry13_consec_even (j : ℕ) : Even ((j - 1) * j) := by
  rcases Nat.even_or_odd j with h | h
  · exact h.mul_left (j - 1)
  · obtain ⟨s, hs⟩ := h
    have h1 : Even (j - 1) := ⟨s, by omega⟩
    exact h1.mul_right j

theorem entry13_tri_succ (j : ℕ) (hj : 1 ≤ j) :
    j * (j + 1) / 2 = (j - 1) * j / 2 + j := by
  obtain ⟨a, ha⟩ := entry13_consec_even j
  have h1 : j * (j + 1) = (j - 1) * j + 2 * j := by
    have h2 : j - 1 + 2 = j + 1 := by omega
    calc j * (j + 1) = (j + 1) * j := mul_comm _ _
      _ = (j - 1 + 2) * j := by rw [h2]
      _ = (j - 1) * j + 2 * j := by ring
  have hmul : j * (j + 1) = 2 * (a + j) := by
    rw [h1, ha]
    ring
  have hA : j * (j + 1) / 2 = a + j := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (a + j) (by norm_num : (0 : ℕ) < 2)
  have hB : (j - 1) * j / 2 = a := by
    rw [ha, ← two_mul]
    exact Nat.mul_div_cancel_left a (by norm_num : (0 : ℕ) < 2)
  rw [hA, hB]

theorem entry13s_succ (j : ℕ) (hj : 1 ≤ j) :
    entry13s j = entry13s (j - 1) * (-1 : ℝ) ^ j := by
  have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  unfold entry13s
  rw [hj1, entry13_tri_succ j hj, pow_add]

theorem entry13eps_eq (j : ℕ) : entry13eps j = -(-1 : ℝ) ^ j := by
  unfold entry13eps
  by_cases h : Even (j + 1)
  · simp only [h, ite_true]
    have hj : Odd j := entry13_odd_of_even_succ j h
    rw [hj.neg_one_pow, neg_neg]
  · simp only [h, ite_false]
    have hj : Even j := entry13_even_of_not_even_succ j h
    rw [hj.neg_one_pow]

theorem entry13_sign_cancel (j : ℕ) (hj : 1 ≤ j) :
    entry13s j * entry13eps j = -entry13s (j - 1) := by
  rw [entry13s_succ j hj, entry13eps_eq j]
  have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
    rw [← pow_add]
    have hev : Even (j + j) := ⟨j, rfl⟩
    exact hev.neg_one_pow
  rw [mul_neg, mul_assoc, hsq, mul_one]

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
