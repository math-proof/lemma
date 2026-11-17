/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Theorem.Analysis.Complex.HartogsExtension

@[expose] public section

namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

noncomputable def hartogsextBarPartial
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  (2 : ℂ)⁻¹ *
    (fderiv ℝ f x (EuclideanSpace.single i 1) +
      Complex.I * fderiv ℝ f x (EuclideanSpace.single i Complex.I))

/-- The Wirtinger derivative `∂f/∂z̄` of a real-differentiable complex-valued function. -/
noncomputable def barDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

noncomputable def hartogsextBarEvalCLM
    {n : ℕ} (i : Fin n) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ) (2 : ℂ)⁻¹).comp
    ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)) +
      ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp
        (ContinuousLinearMap.apply ℝ ℂ
          (EuclideanSpace.single i Complex.I)))

end Complex.HartogsWanted
