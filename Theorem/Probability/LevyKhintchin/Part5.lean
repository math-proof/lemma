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
import Def.Probability.LevyKhintchin.Part5
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lkTruncatedLaw_probability {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) (k : ℕ) :
    IsProbabilityMeasure (lkTruncatedLaw γ σ ν k) := by
  let h_trunc := lk_restrict_away_zero_finite hν k
  let h_cp := @lk_compoundPoisson_probability (lkTruncate ν k) h_trunc
  unfold lkTruncatedLaw
  have h_left : IsProbabilityMeasure
      (lkCompoundPoisson (lkTruncate ν k) ∗ Measure.dirac (γ - lkCompensation ν k)) := by
    infer_instance
  exact @Measure.probabilitymeasure_of_probabilitymeasures_conv ℝ _ _ _ _ h_left
    (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (lkVariance σ))

lemma lk_charFun_truncatedLaw {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ t : ℝ) (k : ℕ) :
    charFun (lkTruncatedLaw γ σ ν k) t =
      Complex.exp (lkExponent γ σ (lkTruncate ν k) t) := by
  let h_trunc := lk_restrict_away_zero_finite hν k
  let h_cp := @lk_compoundPoisson_probability (lkTruncate ν k) h_trunc
  let h_left : IsProbabilityMeasure
      (lkCompoundPoisson (lkTruncate ν k) ∗ Measure.dirac (γ - lkCompensation ν k)) := by
    infer_instance
  let h_gauss := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (lkVariance σ)
  unfold lkTruncatedLaw
  rw [charFun_conv, charFun_conv, lk_charFun_compoundPoisson, charFun_dirac]
  rw [ProbabilityTheory.charFun_gaussianReal
    (μ := 0) (v := lkVariance σ)]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold lkExponent
  rw [← lk_integral_jump_truncate hν k t]
  push_cast
  simp only [Real.inner_apply, lkVariance_coe]
  push_cast
  ring

lemma lk_charFun_truncatedLaw_tendsto {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ t : ℝ) :
    Filter.Tendsto (fun k : ℕ ↦ charFun (lkTruncatedLaw γ σ ν k) t) Filter.atTop
      (𝓝 (Complex.exp (lkExponent γ σ ν t))) := by
  have h_exp : Filter.Tendsto
      (fun k : ℕ ↦ Complex.exp (lkExponent γ σ (lkTruncate ν k) t)) Filter.atTop
      (𝓝 (Complex.exp (lkExponent γ σ ν t))) := by
    have h := ((by fun_prop : Continuous Complex.exp).tendsto (lkExponent γ σ ν t)).comp
      (lk_exponent_truncate_tendsto hν γ σ t)
    exact h.congr' <| Filter.Eventually.of_forall fun k ↦ by rfl
  refine h_exp.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  exact (lk_charFun_truncatedLaw hν γ σ t k).symm

end MetaMathlibExt
