/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Theorem.Analysis.Complex.HartogsExtension


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
