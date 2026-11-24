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
public import Def.Probability.LevyKhintchin.Part7
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

lemma lk_exists_convolution_root {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, charFun (ρ : Measure ℝ) t =
        Complex.exp (lkExponent γ σ ν t / (n : ℝ)) := by
  obtain ⟨ρ, hρ⟩ := lk_exists_probabilityMeasure_charFun (lk_root_moment hν n)
    (γ / (n : ℝ)) (lkRootSigma σ n)
  refine ⟨ρ, fun t ↦ ?_⟩
  rw [hρ, lk_root_exponent γ σ t ν hn]

lemma lk_infinitelyDivisible_of_charFun {μ ν : Measure ℝ}
    (hμ : IsProbabilityMeasure μ)
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ : ℝ) (hchar : ∀ t : ℝ, charFun μ t = Complex.exp (lkExponent γ σ ν t)) :
    ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ := by
  intro n hn
  obtain ⟨ρ, hρ⟩ := lk_exists_convolution_root hν γ σ hn
  have h_eq : μ = lkConvPow (ρ : Measure ℝ) n := by
    let _ := lkConvPow_probability (ρ : Measure ℝ) n
    apply Measure.ext_of_charFun
    funext t
    rw [hchar, lk_charFun_convPow, hρ, lk_exp_div_pow _ hn]
  have h_pow := lkConvPow_succ_iterate (ρ : Measure ℝ) (n - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h_pow
  exact ⟨ρ, inferInstance, h_eq.trans h_pow⟩

end MetaMathlibExt
