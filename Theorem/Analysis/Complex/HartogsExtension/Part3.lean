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
import Def.Analysis.Complex.HartogsExtension.Part2


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
