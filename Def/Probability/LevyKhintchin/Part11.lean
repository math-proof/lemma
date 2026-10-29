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
import Theorem.Probability.LevyKhintchin.Part10
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

noncomputable def lkCanonicalBase (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    FiniteMeasure ℝ := by
  letI := hρ
  let m := ρ.withDensity fun x ↦ (lkCanonicalWeightNN x : ENNReal)
  have hm : IsFiniteMeasure m := by
    apply isFiniteMeasure_withDensity
    apply (lt_of_le_of_lt (b := ∫⁻ _ : ℝ in Set.univ, (1 : ENNReal) ∂ρ) ?_
      (by
        rw [lintegral_one, Measure.restrict_univ]
        exact measure_lt_top ρ Set.univ)).ne
    simpa only [Measure.restrict_univ, lintegral_one] using
      (lintegral_mono lk_canonicalWeightNN_le_one :
        (∫⁻ x, (lkCanonicalWeightNN x : ENNReal) ∂ρ) ≤ ∫⁻ _ : ℝ, (1 : ENNReal) ∂ρ)
  exact ⟨m, hm⟩

noncomputable def lkCanonicalMeasure (ρ : Measure ℝ)
    (hρ : IsProbabilityMeasure ρ) (n : ℕ) : FiniteMeasure ℝ :=
  (n + 1 : NNReal) • lkCanonicalBase ρ hρ

end MetaMathlibExt
