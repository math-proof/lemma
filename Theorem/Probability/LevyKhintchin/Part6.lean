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
import Def.Probability.LevyKhintchin.Part6
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_exists_probabilityMeasure_charFun {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, charFun (μ : Measure ℝ) t = Complex.exp (lkExponent γ σ ν t) := by
  let μk : ℕ → ProbabilityMeasure ℝ := lkApproxPM γ σ ν hν
  let f : ℝ → ℂ := fun t ↦ Complex.exp (lkExponent γ σ ν t)
  have hf : ContinuousAt f 0 := by
    exact ((by fun_prop : Continuous Complex.exp).comp
      (lk_exponent_continuous hν γ σ)).continuousAt
  have h_tight : IsTightMeasureSet (Set.range fun k ↦ (μk k : Measure ℝ)) := by
    apply isTightMeasureSet_of_tendsto_charFun hf
    intro t
    exact lk_charFun_truncatedLaw_tendsto hν γ σ t
  let _ := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure ℝ)
  have h_compact : IsCompact (closure (Set.range μk)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [show {x : Measure ℝ | ∃ μ ∈ Set.range μk, (μ : Measure ℝ) = x} =
        Set.range (fun k ↦ (μk k : Measure ℝ)) by
      ext x
      constructor
      · rintro ⟨μ, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨μk k, ⟨k, rfl⟩, rfl⟩]
    exact h_tight
  obtain ⟨μ, -, r, hr, hμ⟩ := h_compact.isSeqCompact
    (fun k ↦ subset_closure (Set.mem_range_self k))
  refine ⟨μ, fun t ↦ ?_⟩
  have h_char := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμ t
  have h_sub := (lk_charFun_truncatedLaw_tendsto hν γ σ t).comp hr.tendsto_atTop
  exact tendsto_nhds_unique h_char h_sub

end MetaMathlibExt
