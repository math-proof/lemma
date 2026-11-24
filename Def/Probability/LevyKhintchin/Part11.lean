module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.IntegralCharFun
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Theorem.Probability.LevyKhintchin.Part10
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
