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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part3
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_log_sub_taylor_isBigO (a : ℝ) (N : ℕ) :
    (fun y : ℝ => Real.log (1 + a * y) - catalanExpLogTaylor a N y) =O[nhds 0]
      fun y : ℝ => y ^ (N + 1) := by
  apply Asymptotics.IsBigO.of_bound (2 * |a| ^ (N + 1))
  have hlim : Filter.Tendsto (fun y : ℝ => a * y) (nhds 0) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (Filter.tendsto_id :
      Filter.Tendsto (fun y : ℝ => y) (nhds 0) (nhds 0)))
  have hevent : ∀ᶠ y : ℝ in nhds 0, |a * y| < 1 / 2 := by
    have h := hlim.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    simpa [Metric.mem_ball, Real.dist_eq] using h
  filter_upwards [hevent] with y hy
  have hlog := Real.abs_log_sub_add_sum_range_le
    (x := -(a * y)) (by simpa only [abs_neg] using hy.trans (by norm_num)) N
  have hsum : (∑ i ∈ Finset.range N, (-(a * y)) ^ (i + 1) / (i + 1 : ℕ)) =
      -catalanExpLogTaylor a N y := by
    rw [catalanExpLogTaylor, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [neg_pow, mul_pow, pow_succ]
    ring
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum, show 1 - -(a * y) = 1 + a * y by ring] at hlog
  simp only [abs_neg] at hlog
  calc
    ‖Real.log (1 + a * y) - catalanExpLogTaylor a N y‖
        = |-catalanExpLogTaylor a N y + Real.log (1 + a * y)| := by
          rw [Real.norm_eq_abs]
          congr 1
          ring
    _ ≤ |a * y| ^ (N + 1) / (1 - |a * y|) := hlog
    _ ≤ 2 * |a * y| ^ (N + 1) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg (abs_nonneg (a * y)) (N + 1)]
    _ = (2 * |a| ^ (N + 1)) * ‖y ^ (N + 1)‖ := by
      rw [abs_mul, mul_pow, Real.norm_eq_abs, abs_pow]
      ring

lemma catalanExp_choose_neg_nat (k l : ℕ) (hk : 1 ≤ k) :
    Ring.choose (-(k : ℝ)) l =
      (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) := by
  rw [Ring.choose_neg]
  have hcast : (k : ℝ) + l - 1 = ((k + l - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k + l)]
    push_cast
    rfl
  rw [hcast, Ring.choose_natCast]
  change Int.negOnePow (l : ℤ) • (((k + l - 1).choose l : ℕ) : ℝ) =
    (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ)
  rw [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

lemma catalanExp_binomial_partialSum (k N : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    (binomialSeries ℝ (-(k : ℝ))).partialSum N y =
      ∑ l ∈ Finset.range N,
        (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) * y ^ l := by
  simp only [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
    binomialSeries, FormalMultilinearSeries.coeff_ofScalars]
  apply Finset.sum_congr rfl
  intro l hl
  rw [catalanExp_choose_neg_nat k l hk]
  ring

end MetaMathlibExt
