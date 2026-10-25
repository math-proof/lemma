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
import Def.Analysis.Complex.HartogsExtension.Part5


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsext_cauchyGreenKernel_locallyIntegrable :
    LocallyIntegrable hartogsextCauchyGreenKernel (volume : Measure ℂ) := by
  refine locallyIntegrable_of_norm_le_rpow
    (E := ℂ) (F := ℂ) (μ := volume) (C := Real.pi⁻¹) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · apply ae_of_all
    intro z
    simp only [hartogsextCauchyGreenKernel, norm_mul, norm_inv, Real.rpow_neg_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact le_rfl
  · change AEStronglyMeasurable (fun z : ℂ ↦ (Real.pi : ℂ)⁻¹ * z⁻¹) volume
    exact (measurable_const.mul measurable_id.inv).aestronglyMeasurable

end Complex.HartogsWanted
