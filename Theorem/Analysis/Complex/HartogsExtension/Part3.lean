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
public import Def.Analysis.Complex.HartogsExtension.Part2

public section

namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsextReplace_apply
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    WithLp.ofLp (hartogsextReplace i x z) i = z := by
  simp [hartogsextReplace]

theorem hartogsextReplace_self
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextReplace i x (WithLp.ofLp x i) = x := by
  simp [hartogsextReplace]

theorem hartogsextReplace_sub
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    hartogsextReplace i x (WithLp.ofLp x i - t) =
      x - EuclideanSpace.single i t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [hartogsextReplace, PiLp.add_apply, PiLp.sub_apply,
      PiLp.single_eq_same]
    abel
  · simp only [hartogsextReplace, PiLp.add_apply, PiLp.sub_apply,
      PiLp.single_eq_of_ne (p := 2) hji]
    rw [add_zero, sub_zero]

end Complex.HartogsWanted
