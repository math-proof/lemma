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
import Def.Analysis.Complex.HartogsExtension.Part6


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsext_contDiff_uncurry_slice
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n) :
    ContDiff ℝ 1 (Function.uncurry (hartogsextSlice i g)) := by
  change ContDiff ℝ 1 (fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
    g (hartogsextReplace i q.1 q.2))
  apply hg.comp
  unfold hartogsextReplace
  rw [show (fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
      q.1 + EuclideanSpace.single i (q.2 - (WithLp.ofLp q.1) i)) =
      fun q : EuclideanSpace ℂ (Fin n) × ℂ ↦
        q.1 + (q.2 - (WithLp.ofLp q.1) i) •
        EuclideanSpace.single i 1 by
    funext q
    rw [hartogsext_single_eq_smul]]
  fun_prop

theorem hartogsext_slice_uniform_support
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (i : Fin n) :
    ∃ R : ℝ, 0 < R ∧ ∀ x z, z ∉ Metric.closedBall 0 R →
      hartogsextSlice i g x z = 0 := by
  have himage : IsCompact
      ((fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i) '' tsupport g) :=
    hgc.isCompact.image (by fun_prop)
  obtain ⟨R, hRpos, hR⟩ := himage.isBounded.exists_pos_norm_lt
  refine ⟨R, hRpos, ?_⟩
  intro x z hz
  apply Classical.byContradiction
  intro hgz
  have hy : hartogsextReplace i x z ∈ tsupport g :=
    subset_tsupport g hgz
  have hzimage : z ∈
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) '' tsupport g := by
    refine ⟨hartogsextReplace i x z, hy, ?_⟩
    exact hartogsextReplace_apply i x z
  have hznorm := hR _ hzimage
  apply hz
  simpa [Metric.mem_closedBall, dist_zero_right] using hznorm.le

theorem hartogsext_contDiff_partialCauchyGreen
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n) :
    ContDiff ℝ 1 (hartogsextPartialCauchyGreen i g) := by
  obtain ⟨R, hRpos, hsupport⟩ := hartogsext_slice_uniform_support hgc i
  have hparam := hartogsext_contDiff_uncurry_slice hg i
  have hcoord : ContDiffOn ℝ 1
      (fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i) Set.univ := by
    change ContDiffOn ℝ 1
      ((EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ) Set.univ
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ |>.contDiff.contDiffOn
  have hconv := contDiffOn_convolution_right_with_param_comp
    (n := 1) (ContinuousLinearMap.mul ℝ ℂ)
    (s := Set.univ) (k := Metric.closedBall (0 : ℂ) R)
    (v := fun x : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp x i)
    hcoord isOpen_univ (isCompact_closedBall (0 : ℂ) R)
    (fun p z hp hz ↦ hsupport p z hz)
    hartogsext_cauchyGreenKernel_locallyIntegrable hparam.contDiffOn
  change ContDiff ℝ 1 (fun x : EuclideanSpace ℂ (Fin n) ↦
    (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
      hartogsextSlice i g x) (WithLp.ofLp x i))
  have hconv' : ContDiffOn ℝ 1
      (fun x : EuclideanSpace ℂ (Fin n) ↦
        (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          hartogsextSlice i g x) (WithLp.ofLp x i)) Set.univ :=
    hconv.of_le (by norm_num)
  simpa only [contDiffOn_univ] using hconv'

end Complex.HartogsWanted
