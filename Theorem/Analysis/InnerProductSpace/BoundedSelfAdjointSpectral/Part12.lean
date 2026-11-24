module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Order.Zorn
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part12
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
      (spectralMulFiber_measurableSet T hT i).nullMeasurableSet,
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
