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
import Def.Probability.LevyKhintchin.Part16
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_inverse_mul_smoothJump {x t : ℝ} (hx : x ≠ 0) :
    ((lkInverseCanonicalWeight x).toReal : ℂ) * lkSmoothJump t x =
      lkCanonicalIntegrand t x := by
  rw [lk_inverseCanonicalWeight_toReal_of_ne hx]
  rw [← lk_weight_mul_canonicalIntegrand t x]
  unfold lkCanonicalWeight
  push_cast
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hd : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  field_simp [hxC, hd]

lemma lk_integral_smoothJump_levyMeasure (K : FiniteMeasure ℝ) (t : ℝ) :
    (∫ x, lkSmoothJump t x ∂lkLevyMeasure K) =
      ∫ x, lkCanonicalIntegrand t x ∂
        ((K : Measure ℝ).restrict ({0} : Set ℝ)ᶜ) := by
  rw [lkLevyMeasure, integral_withDensity_eq_integral_toReal_smul
    lk_inverseCanonicalWeight_measurable
    (ae_of_all (K : Measure ℝ) lk_inverseCanonicalWeight_lt_top)]
  rw [← integral_indicator (measurableSet_singleton 0).compl]
  apply integral_congr_ae
  exact ae_of_all (K : Measure ℝ) fun x ↦ by
    by_cases hx : x = 0
    · subst x
      simp [lkInverseCanonicalWeight]
    · rw [Set.indicator_of_mem (show x ∈ ({0} : Set ℝ)ᶜ by simpa)]
      change (lkInverseCanonicalWeight x).toReal • lkSmoothJump t x = _
      rw [Complex.real_smul]
      exact lk_inverse_mul_smoothJump hx

lemma lk_integral_canonical_eq_atom_add_smooth
    (K : FiniteMeasure ℝ) (t : ℝ) :
    (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) =
      -(((K : Measure ℝ).real {0} : ℂ) * (t : ℂ) ^ 2 / 2) +
        ∫ x, lkSmoothJump t x ∂lkLevyMeasure K := by
  have hint : Integrable (lkCanonicalIntegrand t) (K : Measure ℝ) :=
    (lkCanonicalIntegrandBCF t).integrable (K : Measure ℝ)
  rw [← integral_add_compl (measurableSet_singleton 0) hint]
  rw [integral_singleton, lk_canonicalIntegrand_zero,
    lk_integral_smoothJump_levyMeasure]
  simp only [Complex.real_smul]
  ring

end MetaMathlibExt
