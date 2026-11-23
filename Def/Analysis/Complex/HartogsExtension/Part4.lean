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
public import Theorem.Analysis.Complex.HartogsExtension.Part4

@[expose] public section

namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

noncomputable def hartogsextSingleCLM
    {n : ℕ} (i : Fin n) : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  ((ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)).flip)
      (EuclideanSpace.single i 1)

end Complex.HartogsWanted
