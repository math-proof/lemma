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
public import Def.Analysis.Complex.HartogsExtension.Part5


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
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
