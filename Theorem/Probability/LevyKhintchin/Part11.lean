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
import Def.Probability.LevyKhintchin.Part11
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_canonicalBase_le (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    (lkCanonicalBase ρ hρ : Measure ℝ) ≤ ρ := by
  change ρ.withDensity (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞)) ≤ ρ
  simpa using withDensity_mono (μ := ρ)
    (ae_of_all ρ fun x ↦ lk_canonicalWeightNN_le_one x)

lemma lk_canonicalMeasure_apply_le (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ)
    (n : ℕ) (s : Set ℝ) :
    ((lkCanonicalMeasure ρ hρ n s : ℝ≥0) : ℝ) ≤
      (n + 1 : ℝ) * ρ.real s := by
  rw [lkCanonicalMeasure, FiniteMeasure.smul_apply]
  change (((n + 1 : ℝ≥0) * lkCanonicalBase ρ hρ s : ℝ≥0) : ℝ) ≤ _
  push_cast
  gcongr
  rw [← FiniteMeasure.measureReal_eq_coe_coeFn]
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top ρ s) ((lk_canonicalBase_le ρ hρ) s)

lemma lk_canonicalBase_mass (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    ((lkCanonicalBase ρ hρ).mass : ℝ) = ∫ x, lkCanonicalWeight x ∂ρ := by
  rw [show ((lkCanonicalBase ρ hρ).mass : ℝ) =
      (ρ.withDensity (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞))).real Set.univ by rfl]
  rw [Measure.real, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x ↦ (lkCanonicalWeightNN x : ℝ)) ρ := by
    apply (integrable_const (c := (1 : ℝ))).mono
    · exact (by
        simpa only [lk_coe_canonicalWeightNN] using (show Continuous lkCanonicalWeight by
          unfold lkCanonicalWeight
          exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2))
            fun x : ℝ ↦ by positivity)
        : Continuous fun x : ℝ ↦ (lkCanonicalWeightNN x : ℝ)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        change |lkCanonicalWeight x| ≤ |(1 : ℝ)|
        simpa [abs_of_nonneg (lkCanonicalWeight_nonneg x)] using lkCanonicalWeight_le_one x
  rw [lintegral_coe_eq_integral _ hint, ENNReal.toReal_ofReal]
  · rfl
  · exact integral_nonneg fun x ↦ lkCanonicalWeight_nonneg x

lemma lk_canonicalMeasure_mass (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ)
    (n : ℕ) :
    ((lkCanonicalMeasure ρ hρ n).mass : ℝ) =
      (n + 1 : ℝ) * ∫ x, lkCanonicalWeight x ∂ρ := by
  rw [lkCanonicalMeasure, FiniteMeasure.mass, FiniteMeasure.smul_apply]
  simp only [smul_eq_mul, NNReal.coe_mul]
  rw [← FiniteMeasure.mass, lk_canonicalBase_mass]
  push_cast
  rfl

lemma lk_canonicalWeight_integrable (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    Integrable lkCanonicalWeight ρ := by
  apply (integrable_const (c := (1 : ℝ))).mono
  · exact (show Continuous lkCanonicalWeight by
      unfold lkCanonicalWeight
      exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2))
        fun x : ℝ ↦ by positivity).aestronglyMeasurable
  · exact ae_of_all ρ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (lkCanonicalWeight_nonneg x), norm_one]
      exact lkCanonicalWeight_le_one x

lemma lk_integral_canonicalWeight_le_sinc (ρ : Measure ℝ)
    (hρ : IsProbabilityMeasure ρ) :
    ∫ x, lkCanonicalWeight x ∂ρ ≤ 32 * ∫ x, 1 - Real.sinc x ∂ρ := by
  rw [← integral_const_mul]
  apply integral_mono (lk_canonicalWeight_integrable ρ hρ)
    ((integrable_const _).sub Real.integrable_sinc |>.const_mul 32)
  intro x
  change lkCanonicalWeight x ≤ 32 * (1 - Real.sinc x)
  nlinarith [lk_canonicalWeight_div_32_le_one_sub_sinc x]

lemma lk_canonicalMeasure_mass_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    ((lkCanonicalMeasure ρ hprob n).mass : ℝ) ≤
      16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by
  rw [lk_canonicalMeasure_mass]
  have hw := lk_integral_canonicalWeight_le_sinc ρ hprob
  have hs := lk_scaled_sinc_integral_le hprob hL n hρ
  calc
    (n + 1 : ℝ) * ∫ x, lkCanonicalWeight x ∂ρ ≤
        (n + 1 : ℝ) * (32 * ∫ x, 1 - Real.sinc x ∂ρ) := by gcongr
    _ = 32 * ((n + 1 : ℝ) * ∫ x, 1 - Real.sinc x ∂ρ) := by ring
    _ ≤ 32 * ((1 / 2 : ℝ) *
        ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖) := by gcongr
    _ = 16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by ring

end MetaMathlibExt
