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
public import Theorem.Probability.LevyKhintchin.Part14
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

noncomputable def lkCanonicalIntegrandBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (lkCanonicalIntegrand t)
    (lk_canonicalIntegrand_continuous t)
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|))
    (lk_norm_canonicalIntegrand_le t)

noncomputable def lkCanonicalIntegrandReBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ (lkCanonicalIntegrand t x).re)
    (Complex.continuous_re.comp (lk_canonicalIntegrand_continuous t))
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|)) fun x ↦
      (Complex.abs_re_le_norm _).trans (lk_norm_canonicalIntegrand_le t x)

noncomputable def lkCanonicalIntegrandImBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ (lkCanonicalIntegrand t x).im)
    (Complex.continuous_im.comp (lk_canonicalIntegrand_continuous t))
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|)) fun x ↦
      (Complex.abs_im_le_norm _).trans (lk_norm_canonicalIntegrand_le t x)

noncomputable def lkSmoothTruncation (x : ℝ) : ℝ :=
  x / (1 + x ^ 2)

noncomputable def lkDrift (rho : Measure ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * ∫ x, lkSmoothTruncation x ∂rho

end MetaMathlibExt
