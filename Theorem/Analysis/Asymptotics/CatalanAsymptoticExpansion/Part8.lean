/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part8
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_localResidual_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpLocalResidual α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  have hO := (catalanExp_logRemainder_isBigO α β M).sub
    (catalanExp_shiftRemainder_isBigO α β M)
  apply hO.congr' _ (Filter.EventuallyEq.rfl)
  have hball : ∀ᶠ y : ℝ in nhds 0, |y| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with y hy
    simpa [Metric.mem_ball, Real.dist_eq] using hy
  filter_upwards [hball] with y hy
  have hy' : 0 < 1 + y := by linarith [neg_lt_of_abs_lt hy]
  unfold catalanExpLocalResidual catalanExpLogStep
  rw [show catalanExpBernoulliSum α β M (y / (1 + y)) -
          catalanExpBernoulliSum α β M y =
        catalanExpShiftTaylor α β M y + catalanExpShiftRemainder α β M y by
      linarith [catalanExp_shift_sub_eq_remainder α β M y hy']]
  rw [catalanExp_shiftTaylor_eq_diffTaylor α β M y,
    ← catalanExp_logTaylor_combination α β M y]
  unfold catalanExpLogRemainder
  ring

lemma catalanExp_sum_range_inv_sq (n N : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) =
      ∑ i ∈ Finset.Ioc (n - 1) ((n - 1) + N), (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show n - 1 + (N + 1) = (n - 1 + N) + 1 by omega,
        Finset.sum_Ioc_succ_top (by omega : n - 1 ≤ n - 1 + N)]
      rw [show N + n = n - 1 + N + 1 by omega]

lemma catalanExp_sum_range_inv_sq_le (n N : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 / (n : ℝ) := by
  calc
    (∑ k ∈ Finset.range N, (((k + n : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ i ∈ Finset.Ioc (n - 1) ((n - 1) + N), (((i : ℕ) : ℝ) ^ 2)⁻¹ :=
      catalanExp_sum_range_inv_sq n N (by omega)
    _ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (((n - 1 + N : ℕ) : ℝ))⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (by omega)
    _ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ :=
      sub_le_self _ (inv_nonneg.mpr (by positivity))
    _ ≤ 2 / (n : ℝ) := by
      rw [← one_div]
      have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply (div_le_div_iff₀ hn1pos hnpos).2
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith

lemma catalanExp_tendsto_nat_pow_mul_of_diff_isBigO (e : ℕ → ℝ) (M : ℕ)
    (he : Filter.Tendsto e Filter.atTop (nhds 0))
    (hd : (fun n : ℕ => e (n + 1) - e n) =O[Filter.atTop]
      fun n : ℕ => (((n : ℝ) ^ (M + 2))⁻¹)) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ M * e n) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hCO⟩ := hd.exists_pos
  have hbound := hCO.bound
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨N, hN⟩ := hbound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _)
      _ (tendsto_const_div_atTop_nhds_zero_nat (2 * C))
  filter_upwards [Filter.eventually_ge_atTop (max N 2)] with n hn
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let A : ℝ := C * (((n : ℝ) ^ M)⁻¹)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hmajor : ∀ k : ℕ,
      |e (k + n + 1) - e (k + n)| ≤ A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro k
    have hnkn : N ≤ k + n := hnN.trans (by omega)
    have hkpos : (0 : ℝ) < k + n := by exact_mod_cast (by omega : 0 < k + n)
    have hraw := hN (k + n) hnkn
    have hraw' : |e (k + n + 1) - e (k + n)| ≤
        C * (((k + n : ℝ) ^ (M + 2))⁻¹) := by
      simpa only [Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hkpos,
        Nat.cast_add, Nat.cast_ofNat] using hraw
    have hle : (((k + n : ℝ) ^ M)⁻¹) ≤ (((n : ℝ) ^ M)⁻¹) := by
      apply (inv_le_inv₀ (pow_pos hkpos M) (pow_pos hnpos M)).2
      exact pow_le_pow_left₀ (le_of_lt hnpos) (by exact_mod_cast (show n ≤ k + n by omega)) M
    calc
      |e (k + n + 1) - e (k + n)| ≤ C * (((k + n : ℝ) ^ (M + 2))⁻¹) := hraw'
      _ = C * (((k + n : ℝ) ^ M)⁻¹) * (((k + n : ℝ) ^ 2)⁻¹) := by
        rw [show M + 2 = M + 2 by rfl, pow_add, mul_inv]
        ring
      _ ≤ C * (((n : ℝ) ^ M)⁻¹) * (((k + n : ℝ) ^ 2)⁻¹) := by
        gcongr
      _ = A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
        simp only [A, Nat.cast_add]
  have htail : |e n| ≤ A * (2 / (n : ℝ)) := by
    have htel (L : ℕ) :
        (∑ k ∈ Finset.range L, (e (k + n + 1) - e (k + n))) = e (L + n) - e n := by
      have h := Finset.sum_range_sub (fun k => e (k + n)) L
      simpa only [Nat.add_assoc, Nat.add_comm n 1, Nat.zero_add] using h
    have hfinite (L : ℕ) : |e (L + n) - e n| ≤ A * (2 / (n : ℝ)) := by
      rw [← htel L]
      calc
        |∑ k ∈ Finset.range L, (e (k + n + 1) - e (k + n))| ≤
            ∑ k ∈ Finset.range L, |e (k + n + 1) - e (k + n)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range L, A * (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hmajor k
        _ = A * ∑ k ∈ Finset.range L, (((k + n : ℕ) : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
        _ ≤ A * (2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (catalanExp_sum_range_inv_sq_le n L hn2) hAnonneg
    have hlim : Filter.Tendsto (fun L : ℕ => |e (L + n) - e n|)
        Filter.atTop (nhds |e n|) := by
      have h := (he.comp (Filter.tendsto_add_atTop_nat n)).sub_const (e n)
      simpa using h.abs
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)
  calc
    ‖(n : ℝ) ^ M * e n‖ = (n : ℝ) ^ M * |e n| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hnpos M)]
    _ ≤ (n : ℝ) ^ M * (A * (2 / (n : ℝ))) := by gcongr
    _ = (2 * C) / (n : ℝ) := by
      dsimp [A]
      field_simp

/--
An all-orders Bernoulli-polynomial expansion obtained from a logarithmic
first-difference equation. The normalization `u n → 0` fixes the otherwise
undetermined additive constant. Its coefficients use Mathlib's
`Polynomial.bernoulli`, evaluated by `Polynomial.aeval`.
-/
theorem _root_.Real.tendsto_pow_mul_sub_bernoulli_sum_of_log_diff
    {u : ℕ → ℝ} (α β c : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hstep : ∀ᶠ n : ℕ in Filter.atTop,
      u (n + 1) - u n =
        Real.log (1 + α / (n + c : ℝ)) - Real.log (1 + β / (n + c : ℝ)) +
          (β - α) * Real.log (1 + 1 / (n + c : ℝ))) :
    ∀ M : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + c : ℝ) ^ M *
            (u n - ∑ j ∈ Finset.range M,
              (-1 : ℝ) ^ (j + 2) *
                (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
                  Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
                  ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                (1 / (n + c : ℝ) ^ (j + 1))))
        Filter.atTop (nhds 0) := by
  intro M
  let x : ℕ → ℝ := fun n => (n : ℝ) + c
  let y : ℕ → ℝ := fun n => 1 / x n
  let e : ℕ → ℝ := fun n => u n - catalanExpBernoulliSum α β M (y n)
  have hxtop : Filter.Tendsto x Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have hy : Filter.Tendsto y Filter.atTop (nhds 0) := by
    exact hxtop.const_div_atTop 1
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖(n : ℝ)‖) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have hx_equiv : Asymptotics.IsEquivalent Filter.atTop x (fun n : ℕ => (n : ℝ)) := by
    simpa only [x] using
      (Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm (c := c))
  have hsum0 : Filter.Tendsto
      (fun n : ℕ => catalanExpBernoulliSum α β M (y n)) Filter.atTop (nhds 0) := by
    unfold catalanExpBernoulliSum
    convert tendsto_finsetSum (Finset.range M) (fun j hj =>
      tendsto_const_nhds.mul (hy.pow (j + 1))) using 1
    all_goals simp
  have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
    simpa only [e, sub_zero] using hu.sub hsum0
  have hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      e (n + 1) - e n = catalanExpLocalResidual α β M (y n) := by
    have hxpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < x n :=
      hxtop.eventually (Filter.eventually_gt_atTop 0)
    filter_upwards [hstep, hxpos] with n hn hnpos
    have hxne : x n ≠ 0 := ne_of_gt hnpos
    have hxone : x n + 1 ≠ 0 := ne_of_gt (by linarith)
    have hx_succ : x (n + 1) = x n + 1 := by
      dsimp [x]
      push_cast
      ring
    have hyden : 1 + 1 / x n ≠ 0 := by positivity
    have hy_succ : y (n + 1) = y n / (1 + y n) := by
      dsimp only [y]
      rw [hx_succ]
      field_simp [hxne, hxone, hyden]
    have hn' : u (n + 1) - u n = catalanExpLogStep α β (y n) := by
      rw [hn]
      unfold catalanExpLogStep
      dsimp [x, y]
      congr 1
      all_goals ring_nf
    dsimp [e]
    rw [hy_succ]
    unfold catalanExpLocalResidual
    linear_combination hn'
  have hdiff_shift : (fun n : ℕ => e (n + 1) - e n) =O[Filter.atTop]
      fun n : ℕ => (y n) ^ (M + 2) := by
    have hcomp := (catalanExp_localResidual_isBigO α β M).comp_tendsto hy
    apply hcomp.congr'
    · filter_upwards [hdiff] with n hn
      simpa only [Function.comp_apply] using hn.symm
    · exact Filter.EventuallyEq.rfl
  have hshift_nat : (fun n : ℕ => (y n) ^ (M + 2)) =O[Filter.atTop]
      fun n : ℕ => (((n : ℝ) ^ (M + 2))⁻¹) := by
    have h := ((hx_equiv.pow (M + 2)).inv).isBigO
    apply h.congr
    · intro n
      simp only [x, y, Pi.pow_apply, Pi.inv_apply, one_div, inv_pow]
    · intro n
      simp only [Pi.pow_apply, Pi.inv_apply]
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ M * e n)
      Filter.atTop (nhds 0) :=
    catalanExp_tendsto_nat_pow_mul_of_diff_isBigO e M he (hdiff_shift.trans hshift_nat)
  have hmul := (hx_equiv.pow M).isBigO.mul
    (Asymptotics.isBigO_refl e Filter.atTop)
  have hresult : Filter.Tendsto (fun n : ℕ => x n ^ M * e n)
      Filter.atTop (nhds 0) := by
    apply hmul.trans_tendsto
    simpa only [Pi.pow_apply, Pi.mul_apply] using hnat
  simpa only [x, y, e, catalanExpBernoulliSum, catalanExpBernoulliCoeff,
    one_div_pow, Nat.add_assoc] using hresult

lemma catalanExp_shifted_log_eq (c : ℝ) (n : ℕ) (hn : 0 < n)
    (hx : 0 < (n : ℝ) + c) :
    Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n) =
      Real.log ((catalan n : ℝ) *
        ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) +
        (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := catalanExp_catalan_pos n
  have hP : 0 < Real.pi * ((n : ℝ) + c) ^ 3 :=
    mul_pos Real.pi_pos (pow_pos hx 3)
  have hQ : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hF : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hsP : Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hP
  have hsQ : Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hQ
  rw [Real.log_div (mul_ne_zero hC.ne' hsP) hF,
    Real.log_div (mul_ne_zero hC.ne' (mul_ne_zero hnR.ne' hsQ)) hF,
    Real.log_div hx.ne' hnR.ne', Real.log_mul hC.ne' hsP,
    Real.log_mul hC.ne' (mul_ne_zero hnR.ne' hsQ),
    Real.log_mul hnR.ne' hsQ, Real.log_sqrt hP.le, Real.log_sqrt hQ.le,
    Real.log_mul Real.pi_ne_zero (pow_ne_zero 3 hx.ne'),
    Real.log_mul Real.pi_ne_zero hnR.ne', Real.log_pow, Real.log_pow]
  ring

theorem catalanExp_shifted_log_tendsto_zero (c : ℝ) :
    Filter.Tendsto (fun n : ℕ =>
      Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n))
      Filter.atTop (nhds 0) := by
  have hcdiv : Filter.Tendsto (fun n : ℕ => c / (n : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat c
  have hratio : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + c) / n)
      Filter.atTop (nhds 1) := by
    have hsum : Filter.Tendsto (fun n : ℕ => 1 + c / (n : ℝ))
        Filter.atTop (nhds 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hcdiv
    have heq : (fun n : ℕ => ((n : ℝ) + c) / n) =ᶠ[Filter.atTop]
        (fun n : ℕ => 1 + c / (n : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    exact Filter.Tendsto.congr' heq.symm hsum
  have hlog : Filter.Tendsto (fun n : ℕ =>
      Real.log (((n : ℝ) + c) / n)) Filter.atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have hcorr : Filter.Tendsto (fun n : ℕ =>
      (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ =>
      Real.log ((catalan n : ℝ) *
        Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n)) =ᶠ[Filter.atTop]
      (fun n : ℕ =>
        Real.log ((catalan n : ℝ) *
          ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) +
          (3 / 2 : ℝ) * Real.log (((n : ℝ) + c) / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hx
    exact catalanExp_shifted_log_eq c n (by omega) hx
  exact Filter.Tendsto.congr' heq.symm <| by
    simpa only [add_zero] using catalanExp_first_log_tendsto_zero.add hcorr

lemma catalanExp_base_log_step (n : ℕ) (hn : 0 < n) :
    Real.log ((catalan (n + 1) : ℝ) *
        ((n + 1 : ℝ) * Real.sqrt (Real.pi * (n + 1 : ℝ))) /
          (4 : ℝ) ^ (n + 1)) -
      Real.log ((catalan n : ℝ) *
        ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n) =
      Real.log ((n : ℝ) + 1 / 2) - Real.log ((n : ℝ) + 2) +
        (3 / 2 : ℝ) *
          (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hC := catalanExp_catalan_pos n
  have hCs := catalanExp_catalan_pos (n + 1)
  have hPn : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hPns : 0 < Real.pi * ((n : ℝ) + 1) := mul_pos Real.pi_pos hn1R
  have hsPn : Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPn
  have hsPns : Real.sqrt (Real.pi * ((n : ℝ) + 1)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPns
  have hcatlog : Real.log (catalan (n + 1) : ℝ) -
      Real.log (catalan n : ℝ) =
      Real.log 4 + Real.log ((n : ℝ) + 1 / 2) -
        Real.log ((n : ℝ) + 2) := by
    rw [← Real.log_div hCs.ne' hC.ne', catalanExp_catalan_succ_ratio]
    have hrewrite : 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2) =
        4 * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 2)) := by ring
    rw [hrewrite, Real.log_mul (by norm_num) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  rw [Real.log_div (mul_ne_zero hCs.ne' (mul_ne_zero hn1R.ne' hsPns))
      (by positivity),
    Real.log_div (mul_ne_zero hC.ne' (mul_ne_zero hnR.ne' hsPn))
      (by positivity),
    Real.log_mul hCs.ne' (mul_ne_zero hn1R.ne' hsPns),
    Real.log_mul hC.ne' (mul_ne_zero hnR.ne' hsPn),
    Real.log_mul hn1R.ne' hsPns, Real.log_mul hnR.ne' hsPn,
    Real.log_sqrt hPns.le, Real.log_sqrt hPn.le,
    Real.log_mul Real.pi_ne_zero hn1R.ne',
    Real.log_mul Real.pi_ne_zero hnR.ne', Real.log_pow, Real.log_pow]
  push_cast
  linear_combination hcatlog

lemma catalanExp_shifted_log_step (c : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.log ((catalan (n + 1) : ℝ) *
          Real.sqrt (Real.pi * ((n + 1 : ℝ) + c) ^ 3) /
            (4 : ℝ) ^ (n + 1)) -
        Real.log ((catalan n : ℝ) *
          Real.sqrt (Real.pi * ((n : ℝ) + c) ^ 3) / (4 : ℝ) ^ n) =
        Real.log (1 + (1 / 2 - c) / (n + c : ℝ)) -
          Real.log (1 + (2 - c) / (n + c : ℝ)) +
          (3 / 2 : ℝ) * Real.log (1 + 1 / (n + c : ℝ)) := by
  have hxTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) + c)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,
    hxTop.eventually (Filter.eventually_gt_atTop 0)] with n hn hx
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : 0 < (n : ℝ) + c + 1 := by linarith
  have hshiftSucc := catalanExp_shifted_log_eq c (n + 1) (by omega)
    (by push_cast; linarith)
  push_cast at hshiftSucc
  have hbase := catalanExp_base_log_step n hn0
  rw [hshiftSucc, catalanExp_shifted_log_eq c n hn0 hx]
  have ha : 1 + (1 / 2 - c) / ((n : ℝ) + c) =
      ((n : ℝ) + 1 / 2) / ((n : ℝ) + c) := by
    field_simp
    ring
  have hb : 1 + (2 - c) / ((n : ℝ) + c) =
      ((n : ℝ) + 2) / ((n : ℝ) + c) := by
    field_simp
    ring
  have hone : 1 + 1 / ((n : ℝ) + c) =
      ((n : ℝ) + c + 1) / ((n : ℝ) + c) := by
    field_simp
  rw [ha, hb, hone, show (n : ℝ) + 1 + c = (n : ℝ) + c + 1 by ring,
    Real.log_div hx1.ne' hn1R.ne', Real.log_div hx.ne' hnR.ne',
    Real.log_div (by positivity) hx.ne', Real.log_div (by positivity) hx.ne',
    Real.log_div hx1.ne' hx.ne']
  linear_combination hbase

/--
The all-orders logarithmic asymptotic expansion of the Catalan numbers at an
arbitrary real shift, with coefficients given by differences of Bernoulli polynomials.
-/
theorem _root_.tendsto_pow_mul_log_catalan_sub_bernoulli_sum (c : ℝ) :
    ∀ M : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + c : ℝ) ^ M *
            (Real.log ((catalan n : ℝ) *
                Real.sqrt (Real.pi * (n + c : ℝ) ^ 3) / (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range M,
                (-1 : ℝ) ^ (j + 2) *
                  (Polynomial.aeval (1 / 2 - c) (Polynomial.bernoulli (j + 2)) -
                    Polynomial.aeval (2 - c) (Polynomial.bernoulli (j + 2))) /
                    ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                  (1 / (n + c : ℝ) ^ (j + 1))))
        Filter.atTop (nhds 0) := by
  refine Real.tendsto_pow_mul_sub_bernoulli_sum_of_log_diff
    (u := fun n : ℕ => Real.log ((catalan n : ℝ) *
      Real.sqrt (Real.pi * (n + c : ℝ) ^ 3) / (4 : ℝ) ^ n))
    (1 / 2 - c) (2 - c) c (catalanExp_shifted_log_tendsto_zero c) ?_
  filter_upwards [catalanExp_shifted_log_step c] with n hn
  simpa only [Nat.cast_add, Nat.cast_one,
    show (2 - c) - (1 / 2 - c) = (3 / 2 : ℝ) by ring] using hn

lemma catalanExp_first_log_eventuallyEq :
    (fun n : ℕ => Real.log ((catalan n : ℝ) *
      Real.sqrt (Real.pi * (n : ℝ) ^ 3) / (4 : ℝ) ^ n)) =ᶠ[Filter.atTop]
    (fun n : ℕ => Real.log ((catalan n : ℝ) *
      ((n : ℝ) * Real.sqrt (Real.pi * n)) / (4 : ℝ) ^ n)) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have h := catalanExp_shifted_log_eq 0 n hn0 (by positivity)
  simpa only [add_zero, div_self hnR, Real.log_one, mul_zero, add_zero] using h

lemma catalanExp_first_sum_eq (m n : ℕ) :
    (∑ j ∈ Finset.range m,
      (-1 : ℝ) ^ (j + 2) *
        (catalanExpBernoulliPolynomialEval (j + 2) (1 / 2) -
          catalanExpBernoulliPolynomialEval (j + 2) 2) /
          ((j + 1 : ℕ) * (j + 2 : ℕ)) *
        (1 / (n : ℝ) ^ (j + 1))) =
      ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ (j + 2) *
          ((((2 : ℝ) ^ (j + 1))⁻¹ - 2) *
              (bernoulli (j + 2) : ℝ) - (j + 1 : ℕ) - 1) /
            ((j + 1 : ℕ) * (j + 2 : ℕ)) *
          (1 / ((n : ℝ) ^ (j + 1))) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [catalanExp_first_bernoulli_difference]

lemma catalanExp_sum_range_two_mul {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      conv_lhs =>
        rw [show 2 * (m + 1) = 2 * m + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      simp only [add_assoc]

lemma catalanExp_second_sum_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0)
    (m n : ℕ) :
    (∑ j ∈ Finset.range (2 * m),
      (-1 : ℝ) ^ (j + 2) *
        (catalanExpBernoulliPolynomialEval (j + 2) (-1 / 4) -
          catalanExpBernoulliPolynomialEval (j + 2) (5 / 4)) /
          ((j + 1 : ℕ) * (j + 2 : ℕ)) *
        (1 / ((n : ℝ) + 3 / 4) ^ (j + 1))) =
      ∑ j ∈ Finset.range m,
        ((2 : ℝ) ^ (4 * (j + 1) + 2))⁻¹ *
          (4 - (E (2 * (j + 1)) : ℝ)) / (j + 1 : ℕ) *
          (1 / ((n : ℝ) + 3 / 4) ^ (2 * (j + 1))) := by
  rw [catalanExp_sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [catalanExp_second_odd_bernoulli_difference r]
  simp only [mul_zero, zero_div, zero_mul, zero_add]
  have hcoef := catalanExp_second_even_coefficient E hE (r + 1) (by omega)
  have hmul := congrArg
    (fun z : ℝ => z * (1 / ((n : ℝ) + 3 / 4) ^ (2 * (r + 1)))) hcoef
  convert hmul using 1

/--
The two Stirling-type asymptotic expansions of the Catalan numbers, in
logarithmic form: with `C n = catalan n`, `log (C n * n * √(π * n) / 4 ^ n)`
is asymptotic to `∑_{k=1}^{m} (-1)^{k+1} ((2^{-k} - 2) B_{k+1} - k - 1) /
(k (k + 1)) n^{-k}` with remainder `o(n^{-m})` for every `m`, and
`log (C n * √(π * (n + 3/4)^3) / 4 ^ n)` is asymptotic to
`∑_{k=1}^{m} 2^{-4k-2} (4 - E_{2k}) / k (n + 3/4)^{-2k}` with remainder
`o((n + 3/4)^{-2m})` for every `m`. The sequence `E` is pinned down by the
Euler-number recurrence `E 0 = 1`, `∑_j C(n,2j) E_{n-2j} = 0` for `n > 0`
(giving `E = 1, 0, -1, 0, 5, ...`), and `bernoulli` is the Bernoulli-number
sequence. The `k = 1` term of the first expansion is `-9 / (8n)`, matching
the classical `C_n = 4^n / (√π n^{3/2}) (1 - 9/(8n) + ...)`.

Source: Neven Elezović, "Asymptotic Expansions of Central Binomial
Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014),
Article 14.2.1, Catalan Stirling-type theorem (unlabeled, equation 42),
lines 626–637,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex

Proves `Wanted` entry `catalan_stirling_asymptotic_expansions`.

Proof: The Catalan recurrence gives a logarithmic first-difference equation.
Telescoping its Bernoulli-polynomial expansion yields both all-orders formulas.
-/
theorem catalan_stirling_asymptotic_expansions
    (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) :
    ((∀ m : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n : ℝ) ^ m *
            (Real.log
                ((catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
                  (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range m,
                (-1 : ℝ) ^ (j + 2) *
                  ((((2 : ℝ) ^ (j + 1))⁻¹ - 2) *
                      (bernoulli (j + 2) : ℝ) - (j + 1 : ℕ) - 1) /
                    ((j + 1 : ℕ) * (j + 2 : ℕ)) *
                  (1 / ((n : ℝ) ^ (j + 1)))))
        Filter.atTop (nhds 0)) ∧
    (∀ m : ℕ,
      Filter.Tendsto
        (fun n : ℕ =>
          (n + 3 / 4 : ℝ) ^ (2 * m) *
            (Real.log
                ((catalan n : ℝ) *
                    Real.sqrt (Real.pi * (n + 3 / 4 : ℝ) ^ 3) /
                  (4 : ℝ) ^ n) -
              ∑ j ∈ Finset.range m,
                ((2 : ℝ) ^ (4 * (j + 1) + 2))⁻¹ *
                  (4 - (E (2 * (j + 1)) : ℝ)) / (j + 1 : ℕ) *
                  (1 / ((n + 3 / 4 : ℝ) ^ (2 * (j + 1))))))
        Filter.atTop (nhds 0))) := by
  constructor
  · intro m
    have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum 0 m
    simp only [← catalanExp_bernoulliPolynomialEval_eq] at h
    refine h.congr' ?_
    filter_upwards [catalanExp_first_log_eventuallyEq] with n hlog
    simp only [add_zero, sub_zero] at *
    rw [hlog, catalanExp_first_sum_eq]
  · intro m
    have h := tendsto_pow_mul_log_catalan_sub_bernoulli_sum (3 / 4) (2 * m)
    simp only [← catalanExp_bernoulliPolynomialEval_eq] at h
    refine h.congr' ?_
    filter_upwards with n
    norm_num only [show (1 / 2 : ℝ) - 3 / 4 = -1 / 4 by norm_num,
      show (2 : ℝ) - 3 / 4 = 5 / 4 by norm_num]
    rw [show -(1 / 4 : ℝ) = -1 / 4 by norm_num]
    rw [catalanExp_second_sum_eq E hE m n]

end MetaMathlibExt
