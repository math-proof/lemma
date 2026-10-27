/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.Zorn
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part12
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal

/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/


noncomputable section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

universe u

theorem spectralMulExtend_eLpNorm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (f : spectrum ℂ T → ℂ) :
    eLpNorm (spectralMulExtend T hT i f) 2 (spectralMulSumMeasure T hT) =
      eLpNorm f 2 (spectralMulMeasure T hT (i : E)) := by
  rw [spectralMulExtend, eLpNorm_indicator_eq_eLpNorm_restrict
      (spectralMulFiber_measurableSet T hT i),
    spectralMulSumMeasure_restrict_fiber, spectralMulFiberMeasure,
    (measurableEmbedding_prodMk_left i).eLpNorm_map_measure]
  rfl

theorem spectralMulExtend_congr_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    {f g : spectrum ℂ T → ℂ} (hfg : f =ᵐ[spectralMulMeasure T hT (i : E)] g) :
    spectralMulExtend T hT i f =ᵐ[spectralMulSumMeasure T hT]
      spectralMulExtend T hT i g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (spectralMulFiber T hT i)
  · rw [spectralMulSumMeasure_restrict_fiber, spectralMulFiberMeasure]
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    filter_upwards [hfg] with z hz
    simpa [spectralMulExtend, spectralMulFiber] using hz
  · apply (ae_restrict_iff' (spectralMulFiber_measurableSet T hT i).compl).mpr
    filter_upwards with x hx
    have hxi : x.1 ≠ i := by simpa [spectralMulFiber] using hx
    simp [spectralMulExtend, spectralMulFiber, hxi]

theorem spectralMulExtend_memLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (f : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    MemLp (spectralMulExtend T hT i f) 2 (spectralMulSumMeasure T hT) := by
  rw [memLp_iff, spectralMulExtend_eLpNorm]
  exact Lp.eLpNorm_lt_top f

end
