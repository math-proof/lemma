/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin.Part13
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_taylorRemainder_analytic (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (lkTaylorRemainder t) z := by
  unfold lkTaylorRemainder
  fun_prop

lemma lk_secondSlope_continuous (t : ℝ) : Continuous (lkSecondSlope t) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact (lk_taylorRemainder_analytic t 0).hasFPowerSeriesAt
      |>.has_fpower_series_iterate_dslope_fslope 2 |>.continuousAt
  · rw [lkSecondSlope, show (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t) =
        dslope (dslope (lkTaylorRemainder t) 0) 0 by rfl]
    apply (continuousAt_dslope_of_ne hz).2
    exact (continuousAt_dslope_of_ne hz).2 (lk_taylorRemainder_analytic t z).continuousAt

@[simp]
lemma lk_taylorRemainder_zero (t : ℝ) : lkTaylorRemainder t 0 = 0 := by
  simp [lkTaylorRemainder]

lemma lk_deriv_taylorRemainder_zero (t : ℝ) :
    deriv (lkTaylorRemainder t) 0 = 0 := by
  unfold lkTaylorRemainder
  simp (disch := fun_prop)

lemma lk_secondSlope_mul_sq (t : ℝ) (z : ℂ) :
    z ^ 2 * lkSecondSlope t z = lkTaylorRemainder t z := by
  have h := pow_sub_smul_iterate_dslope_of_zero
    (f := lkTaylorRemainder t) (a := (0 : ℂ)) 2 (fun k hk ↦ ?_) z
  · simpa [lkSecondSlope, lk_taylorRemainder_zero t] using h
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [lk_taylorRemainder_zero t]
    · simp [lk_deriv_taylorRemainder_zero t]

lemma lk_secondSlope_of_ne (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    lkSecondSlope t z = lkTaylorRemainder t z / z ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hz)).2
  simpa [mul_comm] using lk_secondSlope_mul_sq t z

@[simp]
lemma lk_secondSlope_zero (t : ℝ) :
    lkSecondSlope t 0 = -((t : ℂ) ^ 2) / 2 := by
  have hp := (lk_taylorRemainder_analytic t 0).hasFPowerSeriesAt
  have h := (hp.has_fpower_series_iterate_dslope_fslope 2).coeff_zero
    (fun _ ↦ (1 : ℂ))
  rw [show (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t) =
    lkSecondSlope t by rfl] at h
  rw [← h]
  suffices iteratedDeriv 2 (lkTaylorRemainder t) 0 = -((t : ℂ) ^ 2) by simp [this]
  let a : ℂ := Complex.I * (t : ℂ)
  let f : ℂ → ℂ := fun z ↦ Complex.exp (a * z)
  let c : ℂ → ℂ := fun _ ↦ 1
  let l : ℂ → ℂ := fun z ↦ a * z
  change iteratedDeriv 2 (fun z ↦ (f z - c z) - l z) 0 = -((t : ℂ) ^ 2)
  have hfd : ContDiffAt ℂ 2 f 0 := by dsimp only [f]; fun_prop
  have hcd : ContDiffAt ℂ 2 c 0 := by dsimp only [c]; fun_prop
  have hld : ContDiffAt ℂ 2 l 0 := by dsimp only [l]; fun_prop
  have hsplit : iteratedDeriv 2 (fun z ↦ (f z - c z) - l z) 0 =
      (iteratedDeriv 2 f 0 - iteratedDeriv 2 c 0) - iteratedDeriv 2 l 0 := by
    calc
      _ = iteratedDeriv 2 (fun z ↦ f z - c z) 0 - iteratedDeriv 2 l 0 :=
        iteratedDeriv_sub (hfd.sub hcd) hld
      _ = _ := by
        congr 1
        exact iteratedDeriv_sub hfd hcd
  rw [hsplit]
  have hf : iteratedDeriv 2 f 0 = a ^ 2 := by
    rw [show iteratedDeriv 2 f = fun z ↦ a ^ 2 * Complex.exp (a * z) from
      iteratedDeriv_cexp_const_mul 2 a]
    simp
  have hc : iteratedDeriv 2 c 0 = 0 := by
    dsimp only [c]
    rw [iteratedDeriv_const]
    norm_num
  have hl : iteratedDeriv 2 l 0 = 0 := by
    rw [show l = fun z ↦ a * id z by rfl, iteratedDeriv_const_mul a (by fun_prop)]
    rw [iteratedDeriv_id]
    norm_num
  rw [hf, hc, hl, sub_zero]
  dsimp only [a]
  rw [mul_pow, Complex.I_sq]
  ring

end MetaMathlibExt
