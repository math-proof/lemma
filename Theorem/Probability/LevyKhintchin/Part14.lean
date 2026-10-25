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
import Def.Probability.LevyKhintchin.Part14
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_canonicalIntegrand_continuous (t : ℝ) :
    Continuous (lkCanonicalIntegrand t) := by
  unfold lkCanonicalIntegrand
  exact ((by fun_prop : Continuous fun x : ℝ ↦ ((1 + x ^ 2 : ℝ) : ℂ)).mul
    ((lk_secondSlope_continuous t).comp (by fun_prop))).add (by fun_prop)

lemma lk_weight_mul_canonicalIntegrand (t x : ℝ) :
    (lkCanonicalWeight x : ℂ) * lkCanonicalIntegrand t x = lkSmoothJump t x := by
  by_cases hx : x = 0
  · subst x
    simp [lkCanonicalWeight, lkCanonicalIntegrand, lkSmoothJump]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hd : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  rw [lkCanonicalIntegrand, lk_secondSlope_of_ne t hxC]
  unfold lkTaylorRemainder lkSmoothJump lkCanonicalWeight
  push_cast
  field_simp [hxC, hd]
  ring_nf

lemma lk_norm_secondSlope_le_of_abs_le_one (t : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖lkSecondSlope t (x : ℂ)‖ ≤ t ^ 2 * Real.exp |t| := by
  by_cases hx0 : x = 0
  · subst x
    change ‖lkSecondSlope t 0‖ ≤ t ^ 2 * Real.exp |t|
    have hexp : Real.exp |t| ≥ 1 := Real.one_le_exp (abs_nonneg t)
    rw [lk_secondSlope_zero]
    norm_num [sq_abs]
    nlinarith [sq_nonneg t]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  rw [lk_secondSlope_of_ne t hxC]
  rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (Complex.I * (t : ℂ) * (x : ℂ)) 2
  norm_num [Finset.sum_range_succ] at hrem
  change ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ /
    |x| ^ 2 ≤ t ^ 2 * Real.exp |t|
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  have hrem' : ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ ≤
      (|t| * |x|) ^ 2 * Real.exp (|t| * |x|) := by
    calc
      _ = ‖Complex.exp (Complex.I * ↑t * ↑x) - (1 + Complex.I * ↑t * ↑x)‖ := by
        congr 1
        ring
      _ ≤ _ := hrem
  calc
    ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ / |x| ^ 2 ≤
        ((|t| * |x|) ^ 2 * Real.exp (|t| * |x|)) / |x| ^ 2 := by gcongr
    _ = t ^ 2 * Real.exp (|t| * |x|) := by
      rw [mul_pow, sq_abs]
      field_simp
    _ ≤ t ^ 2 * Real.exp |t| := by
      gcongr
      exact mul_le_of_le_one_right (abs_nonneg t) hx

lemma lk_norm_canonicalIntegrand_le (t x : ℝ) :
    ‖lkCanonicalIntegrand t x‖ ≤
      max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := by
  by_cases hx : |x| ≤ 1
  · calc
      ‖lkCanonicalIntegrand t x‖ ≤
          |1 + x ^ 2| * ‖lkSecondSlope t (x : ℂ)‖ + |t| * |x| := by
        unfold lkCanonicalIntegrand
        calc
          _ ≤ ‖((1 + x ^ 2 : ℝ) : ℂ) * lkSecondSlope t (x : ℂ)‖ +
              ‖Complex.I * (t : ℂ) * (x : ℂ)‖ := norm_add_le _ _
          _ = _ := by
            simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_I, one_mul]
      _ ≤ 2 * (t ^ 2 * Real.exp |t|) + |t| := by
        have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
        have hq := lk_norm_secondSlope_le_of_abs_le_one t hx
        have hxnon : 0 ≤ x ^ 2 := sq_nonneg x
        have hone : |1 + x ^ 2| ≤ 2 := by
          rw [abs_of_nonneg (by linarith : 0 ≤ 1 + x ^ 2)]
          linarith
        exact add_le_add
          (mul_le_mul hone hq (norm_nonneg _) (by positivity))
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hx (abs_nonneg t))
      _ = 2 * t ^ 2 * Real.exp |t| + |t| := by ring
      _ ≤ max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := le_max_left _ _
  · have hx1 : 1 < |x| := lt_of_not_ge hx
    have hw : (1 / 2 : ℝ) ≤ lkCanonicalWeight x := by
      unfold lkCanonicalWeight
      rw [le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
      have hx2 : 1 < x ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith
    have hjump : ‖lkSmoothJump t x‖ ≤ 2 + |t| := by
      unfold lkSmoothJump
      calc
        ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 -
            Complex.I * ↑t * ↑x / ((1 + x ^ 2 : ℝ) : ℂ)‖ ≤
            ‖Complex.exp (Complex.I * ↑t * ↑x) - 1‖ +
              ‖Complex.I * ↑t * ↑x / ((1 + x ^ 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + |t| := by
          have hexp : ‖Complex.exp (Complex.I * ↑t * ↑x) - 1‖ ≤ 2 := by
            calc
              _ ≤ ‖Complex.exp (Complex.I * ↑t * ↑x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by
                rw [show Complex.I * (t : ℂ) * (x : ℂ) =
                    ((t * x : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring]
                rw [Complex.norm_exp_ofReal_mul_I]
                norm_num [Complex.norm_def]
          have hfrac : ‖Complex.I * ↑t * ↑x /
              ((1 + x ^ 2 : ℝ) : ℂ)‖ ≤ |t| := by
            simp only [norm_div, Complex.norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
            apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
            have hxle : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
            nlinarith [abs_nonneg t]
          linarith
    have hweight : 0 < lkCanonicalWeight x :=
      (by norm_num : 0 < (1 / 2 : ℝ)).trans_le hw
    have heq := congrArg norm (lk_weight_mul_canonicalIntegrand t x)
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hweight] at heq
    calc
      ‖lkCanonicalIntegrand t x‖ = ‖lkSmoothJump t x‖ / lkCanonicalWeight x := by
        rw [← heq]
        field_simp
      _ ≤ (2 + |t|) / (1 / 2 : ℝ) :=
        div_le_div₀ (by positivity) hjump (by norm_num) hw
      _ = 4 + 2 * |t| := by ring
      _ ≤ max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := le_max_right _ _

end MetaMathlibExt
