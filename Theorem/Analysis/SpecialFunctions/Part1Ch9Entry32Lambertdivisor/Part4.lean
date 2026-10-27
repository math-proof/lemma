/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part4
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem finite_ode_S32 (N : ℕ) (z : ℝ) :
    2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z
      = 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1) := by
  induction N with
  | zero =>
    have hS : S32partial 1 z = 1 := by
      unfold S32partial
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [aCoeff32_zero]
    have hD : S32partialDeriv 1 z = 0 := by
      unfold S32partialDeriv
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    rw [hS, hD]
    have ha0 : aCoeff32 0 = 1 := aCoeff32_zero
    rw [ha0]
    push_cast
    ring
  | succ n ih =>
    have hS : S32partial (n + 1 + 1) z
        = S32partial (n + 1) z + aCoeff32 (n + 1) * z ^ (n + 1) := by
      unfold S32partial
      rw [Finset.sum_range_succ]
    have hD : S32partialDeriv (n + 1 + 1) z
        = S32partialDeriv (n + 1) z
          + aCoeff32 (n + 1) * ((n + 1 : ℕ) : ℝ) * z ^ (n + 1 - 1) := by
      unfold S32partialDeriv
      rw [Finset.sum_range_succ]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub] at hD
    have hpow1 : z ^ (n + 1 + 1) = z ^ (n + 1) * z := pow_succ z (n + 1)
    have hpow2 : z * z ^ n = z ^ (n + 1) := by
      rw [← pow_succ']
    have hrec := aCoeff32_rec n
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast] at hD
    push_cast at ⊢
    rw [hS, hD, hpow1, ← hpow2]
    linear_combination ih + (z * z ^ n) * hrec

theorem err32_tendsto_zero {z : ℝ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 0) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hz
  have hbase := summable_succ_mul_succ_pow32 (r := ‖z‖) hr
  have hsum : Summable
      (fun N : ℕ => 4 * ‖z‖ * (((N : ℝ) + 1) * ((N : ℝ) + 2) * ‖z‖ ^ N)) :=
    hbase.mul_left (4 * ‖z‖)
  have htend := hsum.tendsto_atTop_zero
  refine squeeze_zero_norm ?_ htend
  intro N
  have ha := aCoeff32_le N
  have han := aCoeff32_nonneg N
  have hN1 : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hN2 : (0:ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hle1 : ((N : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by linarith) hN1
  have hnorm : ‖2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1)‖
      = 2 * ((N : ℝ) + 1) * aCoeff32 N * ‖z‖ ^ (N + 1) := by
    have hnn : (0:ℝ) ≤ 2 * ((N : ℝ) + 1) * aCoeff32 N := by positivity
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm]
  have hpow : ‖z‖ ^ (N + 1) = ‖z‖ * ‖z‖ ^ N := pow_succ' ‖z‖ N
  rw [hpow]
  calc 2 * ((N : ℝ) + 1) * aCoeff32 N * (‖z‖ * ‖z‖ ^ N)
      ≤ 2 * ((N : ℝ) + 1) * (2 * ((N : ℝ) + 1)) * (‖z‖ * ‖z‖ ^ N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left ha (by positivity)
    _ = 4 * ‖z‖ * (((N : ℝ) + 1) ^ 2 * ‖z‖ ^ N) := by ring
    _ ≤ 4 * ‖z‖ * (((N : ℝ) + 1) * ((N : ℝ) + 2) * ‖z‖ ^ N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hle1 (by positivity)

theorem mem_Ioo_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z ∈ Set.Ioo (-r) r := by
  refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith [hz], ?_⟩
  have habs : |z| < (‖z‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    linarith [hz]
  rw [abs_lt] at habs
  rw [Set.mem_Ioo]
  constructor <;> linarith [habs.1, habs.2]

theorem S32_hasDerivAt_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    HasDerivAt S32 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1)) z := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hz
  exact S32_hasDerivAt_of_mem hr0 hr1 hy

theorem F32_hasDerivAt_of_norm_lt_one {s : ℝ} (hs : ‖s‖ < 1) :
    HasDerivAt F32 (∑' k : ℕ, aCoeff32 k * s ^ (2 * k)) s := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hs
  exact F32_hasDerivAt_of_mem hr0 hr1 hy

theorem G32_hasDerivAt_of_norm_lt_one {t : ℝ} (ht : ‖t‖ < 1) :
    HasDerivAt G32
      (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) t := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one ht
  exact G32_hasDerivAt_of_mem hr0 hr1 hy

theorem summable_S32deriv_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => aCoeff32 k * (k : ℝ) * z ^ (k - 1)) := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hz
  have hrN : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hbase := summable_succ_mul_succ_pow32 (r := r) hrN
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r)) := by
    have heq : (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r))
        = fun k : ℕ => (2 / r)
          * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k) := by
      funext k
      field_simp
    rw [heq]
    exact hbase.mul_left (2 / r)
  apply Summable.of_norm_bounded hu
  intro k
  exact S32_majorant hr0 hr1 k z hy

theorem ode_S32_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z = 1 := by
  have hSsum := summable_S32_of_norm_lt_one hz
  have hDsum := summable_S32deriv_of_norm_lt_one hz
  have hHas := S32_hasDerivAt_of_norm_lt_one hz
  have hDeriv : deriv S32 z
      = ∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1) :=
    hHas.deriv
  have hS_tend : Tendsto (fun M : ℕ => S32partial M z) atTop (𝓝 (S32 z)) := by
    have h := hSsum.hasSum.tendsto_sum_nat
    have e1 : (fun M : ℕ => ∑ k ∈ Finset.range M, aCoeff32 k * z ^ k)
        = fun M : ℕ => S32partial M z := by
      funext M
      rfl
    have e2 : (∑' k : ℕ, aCoeff32 k * z ^ k) = S32 z := rfl
    rw [e1, e2] at h
    exact h
  have hD_tend : Tendsto (fun M : ℕ => S32partialDeriv M z) atTop
      (𝓝 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))) := by
    have h := hDsum.hasSum.tendsto_sum_nat
    have e1 : (fun M : ℕ => ∑ k ∈ Finset.range M,
          aCoeff32 k * (k : ℝ) * z ^ (k - 1))
        = fun M : ℕ => S32partialDeriv M z := by
      funext M
      rfl
    rw [e1] at h
    exact h
  have hSucc : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hS_succ : Tendsto (fun N : ℕ => S32partial (N + 1) z) atTop
      (𝓝 (S32 z)) :=
    hS_tend.comp hSucc
  have hD_succ : Tendsto (fun N : ℕ => S32partialDeriv (N + 1) z) atTop
      (𝓝 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))) :=
    hD_tend.comp hSucc
  rw [← hDeriv] at hD_succ
  have hLHS : Tendsto
      (fun N : ℕ => 2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z)
      atTop (𝓝 (2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z)) := by
    apply Tendsto.add
    · exact tendsto_const_nhds.mul hD_succ
    · exact tendsto_const_nhds.mul hS_succ
  have herr := err32_tendsto_zero hz
  have hRHS : Tendsto
      (fun N : ℕ => 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := h1.sub herr
    simpa [sub_zero] using h
  have hEq : ∀ N : ℕ,
      (2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z)
        = (1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1)) :=
    fun N => finite_ode_S32 N z
  have hLHS2 : Tendsto
      (fun N : ℕ => 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 (2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z)) :=
    Tendsto.congr hEq hLHS
  exact tendsto_nhds_unique hLHS2 hRHS

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
