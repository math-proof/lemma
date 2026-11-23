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
public import Theorem.Analysis.Complex.HartogsExtension.Part3

@[expose] public section

namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

noncomputable def hartogsextSlice
    {n : ℕ} (i : Fin n) (g : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) : ℂ :=
  g (hartogsextReplace i x z)

end Complex.HartogsWanted
