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
public import Def.Analysis.Complex.HartogsExtension.Part4


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsextSingleCLM_apply
    {n : ℕ} (i : Fin n) (z : ℂ) :
    hartogsextSingleCLM i z = EuclideanSpace.single i z := by
  change z • EuclideanSpace.single i 1 = EuclideanSpace.single i z
  exact (hartogsext_single_eq_smul i z).symm

theorem hartogsextReplace_hasFDerivAt
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    HasFDerivAt (hartogsextReplace i x) (hartogsextSingleCLM i) z := by
  let S := hartogsextSingleCLM i
  have haff : HasFDerivAt
      (fun w ↦ (x - S (WithLp.ofLp x i)) + S w) S z :=
    (S.hasFDerivAt (x := z)).const_add (x - S (WithLp.ofLp x i))
  apply haff.congr_of_eventuallyEq
  filter_upwards with w
  rw [hartogsextReplace, hartogsext_single_eq_smul]
  change x + S (w - WithLp.ofLp x i) = x - S (WithLp.ofLp x i) + S w
  rw [map_sub]
  abel

theorem hartogsext_contDiff_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    ContDiff ℝ 1 (hartogsextSlice i g x) := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun z ↦ ((hg.differentiable (by norm_num)
    (hartogsextReplace i x z)).comp z
      (hartogsextReplace_hasFDerivAt i x z).differentiableAt), ?_⟩
  have hrep : ContDiff ℝ 1 (hartogsextReplace i x) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z ↦ (hartogsextReplace_hasFDerivAt i x z).differentiableAt, ?_⟩
    have hfd : fderiv ℝ (hartogsextReplace i x) = fun _ ↦ hartogsextSingleCLM i := by
      funext z
      exact (hartogsextReplace_hasFDerivAt i x z).fderiv
    rw [hfd]
    exact continuous_const
  have hcomp : ContDiff ℝ 1 (g ∘ hartogsextReplace i x) := hg.comp hrep
  have hslice : hartogsextSlice i g x = g ∘ hartogsextReplace i x := by rfl
  rw [hslice]
  exact hcomp.continuous_fderiv (by norm_num)

theorem hartogsext_hasCompactSupport_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    HasCompactSupport (hartogsextSlice i g x) := by
  have himage : IsCompact
      ((fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g) :=
    hgc.isCompact.image (by fun_prop)
  obtain ⟨R, hRpos, hR⟩ := himage.isBounded.exists_pos_norm_lt
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy : hartogsextReplace i x z ∈ tsupport g :=
    subset_tsupport g hz
  have hzimage : z ∈
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g := by
    refine ⟨hartogsextReplace i x z, hy, hartogsextReplace_apply i x z⟩
  exact (hR _ hzimage).le

theorem hartogsext_barDeriv_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    barDeriv (hartogsextSlice i g x) z =
      hartogsextBarPartial i g (hartogsextReplace i x z) := by
  have hcomp := (hg.differentiable (by norm_num)
    (hartogsextReplace i x z)).hasFDerivAt.comp z
      (hartogsextReplace_hasFDerivAt i x z)
  have hcomp' : HasFDerivAt (hartogsextSlice i g x)
      ((fderiv ℝ g (hartogsextReplace i x z)).comp (hartogsextSingleCLM i)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with w
    rfl
  rw [barDeriv, hartogsextBarPartial, hcomp'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hartogsextSingleCLM_apply]

end Complex.HartogsWanted
